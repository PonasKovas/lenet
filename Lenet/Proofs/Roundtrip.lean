import Std.Tactic.BVDecide
import Lenet.Proofs.Codec

/-!
# Codec roundtrip: commands, headers, and the full wire datagram

Builds on the reader primitives of `Proofs/Codec.lean` with a small
reader/writer algebra:

* `Writes w s` - the writer appends exactly `s` to any buffer.
* `Reads r s v` - the reader, positioned at `s` inside *any* surrounding
  buffer `pre ++ s ++ post`, yields `v` and advances exactly past `s`.
* `RoundTrip w r v n` - some `n`-byte `s` is both.

`RoundTrip.step` is the composition lemma (sequential fields compose; the
byte count is stated in offset form `n2 + n1` so Lean's Nat offset
unification solves it from the target), which lets every decoder be peeled
field by field (`rt_field` / `rt_body`).

Results, bottom-up:

* `rt_connectParams`, `rt_fragmentParams`, `rt_command` - every command
  kind roundtrips (payload ≤ 0xFFFF, `Command.WellFormed`); the raw command
  byte's number/flag split is a bit-vector fact (`rawCommandByte_*`).
* `rt_header` - canonical headers (`Header.Canonical`: 12-bit peer ID, 2-bit
  session) roundtrip, with or without `sentTime`.
* `parseCommands_cmdsBytes` - `Datagram.parseCommands` recovers exactly the
  command sequence from its concatenated wire bytes.
* `wire_roundtrip` - **the send/receive pair the host actually uses**:
  `decode checksumEnabled (some connectIdOf)` on
  `encode connectId` returns the datagram (checksum field replaced
  by the CRC the encoder computed), *including passing checksum
  verification* whenever the receiver's key for the header's peer ID equals
  the sender's `connectId`.

The preconditions are exactly the invariants the send path maintains, and
they are necessary: `encode` truncates payload lengths to 16 bits and
`Header.encode` masks the peer ID to 12 bits and the session to 2. (The one
send-path header that is *not* canonical is the pre-negotiation one, session
`0xFF`, which goes out as `3` - ENet parity; the receiver tolerates any
session while the peer ID is unset, see `Host.handleDatagram`.)
-/

namespace Lenet.Proofs

open ReaderM WriterM Protocol

/-! ## Reader/writer algebra -/

/-- `r` reads exactly `s`, yielding `v`, wherever `s` sits in the buffer. -/
def Reads {α} (r : ReaderM α) (s : ByteArray) (v : α) : Prop :=
  ∀ pre post : ByteArray, EStateM.run r { bytes := pre ++ s ++ post, offset := pre.size } =
    .ok v { bytes := pre ++ s ++ post, offset := pre.size + s.size }

/-- `w` appends exactly `s`, whatever the buffer. -/
def Writes (w : WriterM Unit) (s : ByteArray) : Prop := ∀ b, runW w b = b ++ s

/-- `w` and `r` are inverse on some `n`-byte encoding of `v`. -/
structure RoundTrip {α} (w : WriterM Unit) (r : ReaderM α) (v : α) (n : Nat) : Prop where
  intro ::
  bytes_ex : ∃ s : ByteArray, s.size = n ∧ Writes w s ∧ Reads r s v

theorem Reads.bind {α β} {r : ReaderM α} {f : α → ReaderM β} {s1 s2 : ByteArray} {a : α} {b : β}
    (h1 : Reads r s1 a) (h2 : Reads (f a) s2 b) : Reads (r >>= f) (s1 ++ s2) b := by
  intro pre post
  have e1 : pre ++ (s1 ++ s2) ++ post = pre ++ s1 ++ (s2 ++ post) := by
    simp [ByteArray.append_assoc]
  have e2 : pre ++ (s1 ++ s2) ++ post = (pre ++ s1) ++ s2 ++ post := by
    simp [ByteArray.append_assoc]
  have r1 := h1 pre (s2 ++ post)
  have r2 := h2 (pre ++ s1) post
  rw [← e1] at r1
  rw [← e2, ByteArray.size_append] at r2
  rw [EStateM.run_bind, r1]
  simp only []
  rw [r2, ByteArray.size_append, Nat.add_assoc]

theorem Reads.pure {α} (v : α) : Reads (Pure.pure v) ByteArray.empty v := by
  intro pre post
  simp [ByteArray.append_empty]

theorem Writes.bind {w1 w2 : WriterM Unit} {s1 s2 : ByteArray}
    (h1 : Writes w1 s1) (h2 : Writes w2 s2) : Writes (w1 >>= fun _ => w2) (s1 ++ s2) := by
  intro b
  show runW w2 (runW w1 b) = _
  rw [h1, h2, ByteArray.append_assoc]

theorem RoundTrip.bind {α β} {w1 w2 : WriterM Unit} {r : ReaderM α} {f : α → ReaderM β}
    {a : α} {b : β} {n1 n2 : Nat}
    (h1 : RoundTrip w1 r a n1) (h2 : RoundTrip w2 (f a) b n2) :
    RoundTrip (w1 >>= fun _ => w2) (r >>= f) b (n1 + n2) := by
  obtain ⟨s1, hs1, hw1, hr1⟩ := h1
  obtain ⟨s2, hs2, hw2, hr2⟩ := h2
  exact ⟨s1 ++ s2, by simp [ByteArray.size_append, hs1, hs2], hw1.bind hw2, hr1.bind hr2⟩

theorem RoundTrip.map {α β} {w : WriterM Unit} {r : ReaderM α} {a : α} {n : Nat}
    (g : α → β) (h : RoundTrip w r a n) :
    RoundTrip w (r >>= fun x => Pure.pure (g x)) (g a) n := by
  obtain ⟨s, hs, hw, hr⟩ := h
  refine ⟨s ++ ByteArray.empty, by simp [hs], ?_, hr.bind (Reads.pure _)⟩
  intro b; rw [ByteArray.append_empty]; exact hw b

/-! ## Primitive fields -/

/-- Indexing into the middle block of `pre ++ s ++ post`. -/
theorem mid_get {pre s post : ByteArray} {i : Nat} (h : i < s.size) :
    (pre ++ s ++ post)[pre.size + i]'(by simp [ByteArray.size_append]; omega) = s[i] := by
  rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega),
      ByteArray.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem push_writes (b : ByteArray) (v : UInt8) : b.push v = b ++ ByteArray.empty.push v := by
  have := push_append b ByteArray.empty v
  rwa [ByteArray.append_empty] at this

theorem rt_u8 (v : UInt8) : RoundTrip (writeUInt8 v) readUInt8 v 1 := by
  refine ⟨ByteArray.empty.push v, by simp, fun b => push_writes b v, fun pre post => ?_⟩
  rw [readUInt8_ok (by simp [ByteArray.size_append]; omega)]
  have := mid_get (pre := pre) (post := post) (s := ByteArray.empty.push v) (i := 0) (by simp)
  simp only [Nat.add_zero] at this
  rw [this, show (ByteArray.empty.push v)[0] = v from push_get_last (b := ByteArray.empty) v]
  simp [ByteArray.size_push]

theorem rt_u16 (v : UInt16) : RoundTrip (writeUInt16BE v) readUInt16BE v 2 := by
  refine ⟨twoBytes v, by simp, fun b => ?_, fun pre post => ?_⟩
  · simp only [runW_writeUInt16BE, twoBytes]
    rw [push_writes b, push_append]
  · rw [readUInt16BE_ok (by simp [ByteArray.size_append])]
    have h0 := mid_get (pre := pre) (post := post) (s := twoBytes v) (i := 0) (by simp)
    have h1 := mid_get (pre := pre) (post := post) (s := twoBytes v) (i := 1) (by simp)
    simp only [Nat.add_zero] at h0
    rw [h0, h1, twoBytes_get_zero, twoBytes_get_one, twoBytes_size]
    congr 1
    bv_decide

theorem writes_u32 (v : UInt32) : Writes (writeUInt32BE v) (fourBytes v) := fun b => by
  simp only [runW_writeUInt32BE, fourBytes]
  rw [push_writes b, push_append, push_append, push_append]

theorem reads_u32 (v : UInt32) : Reads readUInt32BE (fourBytes v) v := by
  intro pre post
  rw [readUInt32BE_ok (by simp [ByteArray.size_append])]
  have h0 := mid_get (pre := pre) (post := post) (s := fourBytes v) (i := 0) (by simp)
  have h1 := mid_get (pre := pre) (post := post) (s := fourBytes v) (i := 1) (by simp)
  have h2 := mid_get (pre := pre) (post := post) (s := fourBytes v) (i := 2) (by simp)
  have h3 := mid_get (pre := pre) (post := post) (s := fourBytes v) (i := 3) (by simp)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3, fourBytes_get_zero, fourBytes_get_one, fourBytes_get_two,
    fourBytes_get_three, fourBytes_size]
  congr 1
  bv_decide

theorem rt_u32 (v : UInt32) : RoundTrip (writeUInt32BE v) readUInt32BE v 4 :=
  ⟨fourBytes v, by simp, writes_u32 v, reads_u32 v⟩

theorem reads_bytes (d : ByteArray) : Reads (readBytes d.size) d d := by
  intro pre post
  rw [readBytes_ok (by simp [ByteArray.size_append])]
  rw [ByteArray.append_assoc, ByteArray.extract_append]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left]
  rw [ByteArray.extract_append]
  simp [ByteArray.ext_iff, ByteArray.data_extract, ByteArray.data_append]

theorem rt_bytes (d : ByteArray) : RoundTrip (writeBytes d) (readBytes d.size) d d.size :=
  ⟨d, rfl, fun _ => rfl, reads_bytes d⟩

/-! ## Composite blocks and commands -/

/-- `bind` with the byte count in offset form (`n2 + n1`), so Lean's Nat
offset unification solves the remaining count from the target. -/
theorem RoundTrip.step {α β} {w1 w2 : WriterM Unit} {r : ReaderM α} {f : α → ReaderM β}
    {a : α} {b : β} {n1 n2 : Nat}
    (h1 : RoundTrip w1 r a n1) (h2 : RoundTrip w2 (f a) b n2) :
    RoundTrip (w1 >>= fun _ => w2) (r >>= f) b (n2 + n1) := Nat.add_comm n1 n2 ▸ h1.bind h2

/-- The final field, whose value the decoder wraps in `pure`. -/
theorem RoundTrip.last {α β} {w : WriterM Unit} {r : ReaderM α} {a : α} {n : Nat}
    {g : α → β} {b : β} (h : RoundTrip w r a n) (hb : g a = b) :
    RoundTrip w (r >>= fun x => Pure.pure (g x)) b n := hb ▸ h.map g

/-- Peel one fixed-width field off a matching encoder/decoder pair. -/
macro "rt_field" : tactic => `(tactic| first
  | with_reducible refine (rt_u32 _).last ?_
  | with_reducible refine (rt_u16 _).last ?_
  | with_reducible refine (rt_u8 _).last ?_
  | with_reducible refine (rt_u32 _).step ?_
  | with_reducible refine (rt_u16 _).step ?_
  | with_reducible refine (rt_u8 _).step ?_)

theorem rt_connectParams (p : ConnectParams) :
    RoundTrip p.encode ConnectParams.decode p 40 := by
  unfold ConnectParams.encode ConnectParams.decode
  repeat rt_field
  all_goals rfl

/-- The wire length field (`UInt16`) recovers the payload size exactly when
it fits - the roundtrip precondition. -/
theorem toUInt16_toNat_of_lt {n : Nat} (h : n < 65536) : n.toUInt16.toNat = n := by
  simp [Nat.toUInt16]; omega

theorem rt_payload {d : ByteArray} (h : d.size < 65536) :
    RoundTrip (writeBytes d) (readBytes d.size.toUInt16.toNat) d d.size := by
  rw [toUInt16_toNat_of_lt h]; exact rt_bytes d

theorem rt_fragmentParams (p : FragmentParams) (h : p.data.size < 65536) :
    RoundTrip p.encode FragmentParams.decode p (p.data.size + 20) := by
  unfold FragmentParams.encode FragmentParams.decode
  repeat rt_field
  exact (rt_payload h).last rfl

/-- The raw command byte `Command.encode` writes. -/
abbrev rawCommandByte (b : CommandBody) (ack uns : Bool) : UInt8 :=
  b.commandNumber &&& Constants.commandMask |||
    ((if ack = true then Constants.commandFlagAcknowledge else 0) |||
      if uns = true then Constants.commandFlagUnsequenced else 0)

theorem commandNumber_le (b : CommandBody) : b.commandNumber ≤ 12 := by
  cases b <;> (simp only [CommandBody.commandNumber]; decide)

theorem rawCommandByte_mask (b : CommandBody) (ack uns : Bool) :
    rawCommandByte b ack uns &&& Constants.commandMask = b.commandNumber := by
  have h := commandNumber_le b
  simp only [rawCommandByte, Constants.commandMask, Constants.commandFlagAcknowledge,
    Constants.commandFlagUnsequenced]
  generalize b.commandNumber = n at h ⊢
  cases ack <;> cases uns <;> simp only [Bool.false_eq_true, if_true, if_false] <;> bv_decide

theorem rawCommandByte_ack (b : CommandBody) (ack uns : Bool) :
    (rawCommandByte b ack uns &&& Constants.commandFlagAcknowledge != 0) = ack := by
  have h := commandNumber_le b
  simp only [rawCommandByte, Constants.commandMask, Constants.commandFlagAcknowledge,
    Constants.commandFlagUnsequenced]
  generalize b.commandNumber = n at h ⊢
  cases ack <;> cases uns <;> simp only [Bool.false_eq_true, if_true, if_false, bne_iff_ne,
    bne_eq_false_iff_eq, ne_eq] <;> bv_decide

theorem rawCommandByte_uns (b : CommandBody) (ack uns : Bool) :
    (rawCommandByte b ack uns &&& Constants.commandFlagUnsequenced != 0) = uns := by
  have h := commandNumber_le b
  simp only [rawCommandByte, Constants.commandMask, Constants.commandFlagAcknowledge,
    Constants.commandFlagUnsequenced]
  generalize b.commandNumber = n at h ⊢
  cases ack <;> cases uns <;> simp only [Bool.false_eq_true, if_true, if_false, bne_iff_ne,
    bne_eq_false_iff_eq, ne_eq] <;> bv_decide

theorem rt_pure {α} (v : α) : RoundTrip (Pure.pure ()) (Pure.pure v) v 0 :=
  ⟨ByteArray.empty, rfl, fun b => by simp [runW, ByteArray.append_empty]; rfl, Reads.pure v⟩

/-- `rt_field` extended with the composite blocks (connect/fragment params,
length-prefixed payloads, the empty body). -/
macro "rt_body" : tactic => `(tactic| first
  | rt_field
  | with_reducible refine (rt_connectParams _).step ?_
  | with_reducible refine (rt_connectParams _).last ?_
  | with_reducible refine (rt_fragmentParams _ ‹_›).last ?_
  | with_reducible refine (rt_payload ‹_›).last ?_
  | with_reducible exact rt_pure _)

/-- Every command kind roundtrips, in exactly `Command.wireSize` bytes
(stated here as payload + fixed body + 4-byte command header). -/
theorem rt_command (cmd : Command) (h : cmd.body.payloadSize < 65536) :
    RoundTrip cmd.encode Command.decode cmd
      (cmd.body.payloadSize + cmd.body.fixedWireSize + 4) := by
  obtain ⟨ch, seq, ack, uns, body⟩ := cmd
  unfold Command.encode Command.decode
  simp only []
  rt_field
  rt_field
  rt_field
  simp only [rawCommandByte_mask, rawCommandByte_ack, rawCommandByte_uns]
  cases body <;> simp only [CommandBody.commandNumber, pure_bind, Constants.commandAcknowledge,
    Constants.commandConnect, Constants.commandVerifyConnect, Constants.commandDisconnect,
    Constants.commandPing, Constants.commandSendReliable, Constants.commandSendUnreliable,
    Constants.commandSendFragment, Constants.commandSendUnsequenced, Constants.commandBandwidthLimit,
    Constants.commandThrottleConfigure, Constants.commandSendUnreliableFragment,
    CommandBody.encode, CommandBody.payloadSize, CommandBody.fixedWireSize] at h ⊢
  all_goals repeat rt_body
  all_goals rfl

/-! ## Command sequences -/

/-- A command the send path can put on the wire: its payload length fits the
16-bit length field. -/
def _root_.Lenet.Protocol.Command.WellFormed (cmd : Command) : Prop := cmd.body.payloadSize < 65536

/-- The wire bytes of one command. -/
def cmdBytes (cmd : Command) : ByteArray := runW cmd.encode ByteArray.empty

/-- The wire bytes of a command sequence. -/
def cmdsBytes : List Command → ByteArray
  | [] => ByteArray.empty
  | c :: cs => cmdBytes c ++ cmdsBytes cs

theorem cmdBytes_spec {cmd : Command} (h : cmd.WellFormed) :
    (cmdBytes cmd).size = cmd.wireSize ∧ Writes cmd.encode (cmdBytes cmd) ∧
      Reads Command.decode (cmdBytes cmd) cmd := by
  obtain ⟨s, hs, hw, hr⟩ := rt_command cmd h
  have e : cmdBytes cmd = s := by
    rw [cmdBytes, hw, ByteArray.empty_append]
  subst e
  refine ⟨?_, hw, hr⟩
  rw [hs, Command.wireSize]; omega

/-- The loop body `Datagram.encode` runs over the commands. -/
abbrev encodeLoopBody : Command → PUnit → WriterM (ForInStep PUnit) :=
  fun cmd _ => do cmd.encode; pure (ForInStep.yield PUnit.unit)

theorem writes_forIn_list : ∀ (l : List Command), (∀ c ∈ l, c.WellFormed) →
    Writes (forIn l PUnit.unit encodeLoopBody >>= fun _ => pure ()) (cmdsBytes l)
  | [], _ => fun b => by simp [cmdsBytes, ByteArray.append_empty]
  | c :: cs, h => fun b => by
    have ih := writes_forIn_list cs (fun x hx => h x (List.mem_cons_of_mem c hx))
    rw [List.forIn_cons]
    have hc := (cmdBytes_spec (h c List.mem_cons_self)).2.1
    show runW (forIn cs PUnit.unit encodeLoopBody >>= fun _ => pure ()) (runW c.encode b) = _
    rw [ih, hc, cmdsBytes, ByteArray.append_assoc]

theorem writes_commands (cmds : Array Command) (h : ∀ c ∈ cmds, c.WellFormed) :
    Writes (forIn cmds PUnit.unit encodeLoopBody >>= fun _ => pure ()) (cmdsBytes cmds.toList) := by
  rw [← Array.forIn_toList]
  exact writes_forIn_list _ (fun c hc => h c (Array.mem_toList_iff.mp hc))

theorem decode_cmdBytes {cmd : Command} (h : cmd.WellFormed) (tail : ByteArray) :
    ReaderM.run Command.decode (cmdBytes cmd ++ tail) = .ok cmd := by
  have hr := (cmdBytes_spec h).2.2 ByteArray.empty tail
  rw [ByteArray.empty_append] at hr
  simp only [ReaderM.run]
  rw [show ByteArray.empty.size = 0 from rfl] at hr
  rw [hr]

theorem cmdsBytes_size_ge : ∀ (l : List Command), (∀ c ∈ l, c.WellFormed) →
    4 * l.length ≤ (cmdsBytes l).size
  | [], _ => by simp [cmdsBytes]
  | c :: cs, h => by
    have ih := cmdsBytes_size_ge cs (fun x hx => h x (List.mem_cons_of_mem c hx))
    have hc := (cmdBytes_spec (h c List.mem_cons_self)).1
    simp only [cmdsBytes, ByteArray.size_append, hc, List.length_cons, Command.wireSize]
    omega

theorem go_cmdsBytes : ∀ (l : List Command) (fuel : Nat) (acc : Array Command),
    (∀ c ∈ l, c.WellFormed) → l.length ≤ fuel →
      Datagram.parseCommands.go fuel (cmdsBytes l) acc = acc ++ l.toArray
  | [], fuel, acc, _, _ => by
    rw [go_eq_of_size_zero fuel _ acc rfl]; simp
  | c :: cs, fuel + 1, acc, h, hl => by
    have hwf := h c List.mem_cons_self
    have ⟨hs, _, _⟩ := cmdBytes_spec hwf
    have hne : (cmdsBytes (c :: cs)).size ≠ 0 := by
      simp only [cmdsBytes, ByteArray.size_append, hs, Command.wireSize]; omega
    have hb : ((cmdsBytes (c :: cs)).size == 0) = false := by simp [hne]
    simp only [Datagram.parseCommands.go, hb, Bool.false_eq_true, if_false]
    rw [show cmdsBytes (c :: cs) = cmdBytes c ++ cmdsBytes cs from rfl, decode_cmdBytes hwf]
    simp only []
    rw [ByteArray.extract_append_eq_right (by rw [hs]) (by simp [ByteArray.size_append, hs])]
    rw [go_cmdsBytes cs fuel (acc.push c) (fun x hx => h x (List.mem_cons_of_mem c hx))
      (by simp at hl; omega)]
    simp

/-- **Command-sequence roundtrip**: parsing the concatenated wire bytes of
well-formed commands recovers exactly those commands, in order. -/
theorem parseCommands_cmdsBytes (l : List Command) (h : ∀ c ∈ l, c.WellFormed) :
    Datagram.parseCommands (cmdsBytes l) = l.toArray := by
  have := cmdsBytes_size_ge l h
  rw [Datagram.parseCommands, go_cmdsBytes l _ #[] h (by omega)]
  simp

/-! ## Header -/

/-- A header the send path produces: the peer ID fits its 12 bits and the
session its 2 bits (`Header.encode` masks both; values outside would be
silently truncated, so roundtrip needs exactly this). -/
def _root_.Lenet.Protocol.Header.Canonical (h : Header) : Prop :=
  h.peerId < 4096 ∧ h.session < 4

/-- The raw peer-ID word `Header.encode` writes. -/
abbrev rawHeaderWord (pid : UInt16) (ses : UInt8) (comp st : Bool) : UInt16 :=
  pid &&& ~~~(Constants.headerFlagMask ||| Constants.headerSessionMask) |||
    ses.toUInt16 <<< Constants.headerSessionShift.toUInt16 &&& Constants.headerSessionMask |||
    ((if comp = true then Constants.headerFlagCompressed else 0) |||
      if st = true then Constants.headerFlagSentTime else 0)

theorem rawHeaderWord_peerId {pid : UInt16} (ses : UInt8) (comp st : Bool) (hp : pid < 4096) :
    rawHeaderWord pid ses comp st &&& ~~~(Constants.headerFlagMask ||| Constants.headerSessionMask)
      = pid := by
  simp only [rawHeaderWord, Constants.headerFlagMask, Constants.headerSessionMask,
    Constants.headerFlagCompressed, Constants.headerFlagSentTime, Constants.headerSessionShift,
    show (12 : Nat).toUInt16 = 12 from rfl]
  cases comp <;> cases st <;> simp only [Bool.false_eq_true, if_true, if_false] <;> bv_decide

theorem rawHeaderWord_session (pid : UInt16) {ses : UInt8} (comp st : Bool) (hs : ses < 4) :
    ((rawHeaderWord pid ses comp st &&& Constants.headerSessionMask) >>>
      Constants.headerSessionShift.toUInt16).toUInt8 = ses := by
  simp only [rawHeaderWord, Constants.headerFlagMask, Constants.headerSessionMask,
    Constants.headerFlagCompressed, Constants.headerFlagSentTime, Constants.headerSessionShift,
    show (12 : Nat).toUInt16 = 12 from rfl]
  cases comp <;> cases st <;> simp only [Bool.false_eq_true, if_true, if_false] <;> bv_decide

theorem rawHeaderWord_compressed (pid : UInt16) (ses : UInt8) (comp st : Bool) :
    (rawHeaderWord pid ses comp st &&& Constants.headerFlagCompressed != 0) = comp := by
  simp only [rawHeaderWord, Constants.headerFlagMask, Constants.headerSessionMask,
    Constants.headerFlagCompressed, Constants.headerFlagSentTime, Constants.headerSessionShift,
    show (12 : Nat).toUInt16 = 12 from rfl]
  cases comp <;> cases st <;> simp only [Bool.false_eq_true, if_true, if_false, bne_iff_ne,
    bne_eq_false_iff_eq, ne_eq] <;> bv_decide

theorem rawHeaderWord_sentTime (pid : UInt16) (ses : UInt8) (comp st : Bool) :
    (rawHeaderWord pid ses comp st &&& Constants.headerFlagSentTime != 0) = st := by
  simp only [rawHeaderWord, Constants.headerFlagMask, Constants.headerSessionMask,
    Constants.headerFlagCompressed, Constants.headerFlagSentTime, Constants.headerSessionShift,
    show (12 : Nat).toUInt16 = 12 from rfl]
  cases comp <;> cases st <;> simp only [Bool.false_eq_true, if_true, if_false, bne_iff_ne,
    bne_eq_false_iff_eq, ne_eq] <;> bv_decide

theorem rt_header (h : Header) (hc : h.Canonical) :
    RoundTrip h.encode Header.decode h ((if h.sentTime.isSome then 2 else 0) + 2) := by
  obtain ⟨pid, ses, comp, st⟩ := h
  obtain ⟨hp, hs⟩ := hc
  unfold Header.encode Header.decode
  simp only []
  rt_field
  simp only [rawHeaderWord_peerId _ _ _ hp, rawHeaderWord_session _ _ _ hs,
    rawHeaderWord_compressed, rawHeaderWord_sentTime]
  cases st <;> simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false,
    if_true, pure_bind]
  · exact rt_pure _
  · exact (rt_u16 _).last rfl

/-! ## Datagram (the wire path: `encode` / `decode`) -/

/-- Run a reader whose bytes sit at a known position in the buffer. -/
theorem Reads.run_eq {α} {r : ReaderM α} {s : ByteArray} {v : α} (h : Reads r s v)
    {buf pre post : ByteArray} {off : Nat} (hb : buf = pre ++ s ++ post) (ho : off = pre.size) :
    EStateM.run r { bytes := buf, offset := off } =
      .ok v { bytes := buf, offset := pre.size + s.size } := by
  subst hb ho; exact h pre post

theorem RoundTrip.writes {α} {w : WriterM Unit} {r : ReaderM α} {v : α} {n : Nat}
    (h : RoundTrip w r v n) : Writes w (runW w ByteArray.empty) ∧ Reads r (runW w ByteArray.empty) v ∧
      (runW w ByteArray.empty).size = n := by
  obtain ⟨s, hs, hw, hr⟩ := h
  have e : runW w ByteArray.empty = s := by rw [hw, ByteArray.empty_append]
  rw [e]; exact ⟨hw, hr, hs⟩

/-- The header's wire bytes. -/
def headerBytes (h : Header) : ByteArray := runW h.encode ByteArray.empty

/-- The checksum `Datagram.encode` stores: CRC over header + key placeholder + commands. -/
def wireChecksum (d : Datagram) (connectId : UInt32) : UInt32 :=
  Datagram.computeChecksum (headerBytes d.header) (cmdsBytes d.commands.toList) connectId

theorem encode_eq (d : Datagram) (connectId : UInt32) (hcomp : d.header.compressed = false)
    (hcmds : ∀ c ∈ d.commands, c.WellFormed) :
    d.encode connectId =
      match d.checksum with
      | none => headerBytes d.header ++ cmdsBytes d.commands.toList
      | some _ => headerBytes d.header ++ fourBytes (wireChecksum d connectId) ++
          cmdsBytes d.commands.toList := by
  obtain ⟨hdr, cs, cmds⟩ := d
  have hw := writes_commands cmds hcmds
  have hh : { hdr with compressed := false } = hdr := by cases hdr; simp_all
  unfold Datagram.encode
  have hrun : ∀ w : WriterM Unit, WriterM.run w = runW w ByteArray.empty := fun _ => rfl
  have hc : WriterM.run (forIn cmds PUnit.unit encodeLoopBody >>= fun _ => pure ()) =
      cmdsBytes cmds.toList := by
    rw [hrun, hw, ByteArray.empty_append]
  simp only [hh]
  cases cs with
  | none =>
    show runW (writeBytes _) (runW hdr.encode ByteArray.empty) = _
    rw [hc]; rfl
  | some _ =>
    show runW (writeBytes _) (runW (writeUInt32BE _) (runW hdr.encode ByteArray.empty)) = _
    rw [hc, runW_writeBytes, writes_u32]
    rfl

theorem run_remaining (c : ReadCursor) :
    EStateM.run ReaderM.remaining c = .ok (c.bytes.size - c.offset) c := rfl

/-- **Wire roundtrip** for the host's actual send/receive pair
(`Host.pollPeer` encodes with `encode connectId`, `Host.handleDatagram`
decodes with `decode checksumEnabled (some connectIdOf)`).

A datagram with a canonical header and well-formed commands decodes to
itself, the checksum field carrying the CRC the encoder computed. With
checksums on, this includes *passing verification*: the receiver's key for
the header's peer ID must equal the sender's `connectId` (`hkey`) - the
connectID agreement the handshake establishes. -/
theorem wire_roundtrip (d : Datagram) (connectId : UInt32) (cidOf : UInt16 → UInt32)
    (hc : d.header.Canonical) (hcomp : d.header.compressed = false)
    (hcmds : ∀ c ∈ d.commands, c.WellFormed)
    (hkey : d.checksum.isSome → cidOf d.header.peerId = connectId) :
    ReaderM.run (Datagram.decode d.checksum.isSome (some cidOf))
        (d.encode connectId) =
      .ok { d with checksum := d.checksum.map fun _ => wireChecksum d connectId } := by
  rw [encode_eq d connectId hcomp hcmds]
  have hparse := parseCommands_cmdsBytes d.commands.toList
    (fun c hc' => hcmds c (Array.mem_toList_iff.mp hc'))
  obtain ⟨hdr, cs, cmds⟩ := d
  have ⟨_, hR, _⟩ := (rt_header hdr hc).writes
  simp only [] at hcomp hparse hkey ⊢
  have hB := reads_bytes (cmdsBytes cmds.toList)
  cases cs with
  | none =>
    simp only [ReaderM.run, Datagram.decode, EStateM.run_bind, Option.isSome_none,
      Bool.false_eq_true, if_false]
    rw [hR.run_eq (pre := ByteArray.empty) (post := cmdsBytes cmds.toList) (off := 0)
      (by simp [headerBytes]) rfl]
    simp only [EStateM.run_get, EStateM.run_pure, run_remaining]
    rw [show (headerBytes hdr ++ cmdsBytes cmds.toList).size -
        (ByteArray.empty.size + (runW hdr.encode ByteArray.empty).size) = (cmdsBytes cmds.toList).size
        by simp [headerBytes, ByteArray.size_append]]
    rw [hB.run_eq (pre := headerBytes hdr) (post := ByteArray.empty) (by simp) (by simp [headerBytes])]
    simp only [hcomp, Bool.false_eq_true, if_false, EStateM.run_pure, hparse, Option.map_none,
      Array.toArray_toList]
  | some v =>
    have hk := hkey rfl
    generalize hW : wireChecksum { header := hdr, checksum := some v, commands := cmds } connectId = W
    simp only [ReaderM.run, Datagram.decode, EStateM.run_bind, Option.isSome_some, if_true]
    rw [hR.run_eq (pre := ByteArray.empty)
      (post := fourBytes W ++ cmdsBytes cmds.toList) (off := 0)
      (by simp [headerBytes, ByteArray.append_assoc]) rfl]
    simp only [EStateM.run_get, EStateM.run_pure]
    rw [(reads_u32 _).run_eq (pre := headerBytes hdr) (post := cmdsBytes cmds.toList) rfl
      (by simp [headerBytes])]
    simp only [run_remaining]
    rw [show (headerBytes hdr ++ fourBytes W ++ cmdsBytes cmds.toList).size -
        ((headerBytes hdr).size + (fourBytes W).size) = (cmdsBytes cmds.toList).size
        by simp [ByteArray.size_append]]
    rw [hB.run_eq (pre := headerBytes hdr ++ fourBytes W) (post := ByteArray.empty)
      (off := (headerBytes hdr).size + (fourBytes W).size) (by simp) (by simp [ByteArray.size_append])]
    simp only [hcomp, Bool.false_eq_true, if_false, EStateM.run_bind, EStateM.run_get]
    have hx : (headerBytes hdr ++ fourBytes W ++ cmdsBytes cmds.toList).extract 0
        (ByteArray.empty.size + (runW hdr.encode ByteArray.empty).size) = headerBytes hdr := by
      rw [ByteArray.append_assoc]
      exact ByteArray.extract_append_eq_left (by simp [headerBytes])
    unfold wireChecksum at hW
    simp only [] at hW
    rw [hx, hk, hW]
    simp [hparse]
