import Lenet.Proofs.HostEvents

/-!
# The sender-side window span

A channel's reliable commands in flight (sent, not yet acknowledged) span at
most six windows: every one of them is at most five windows and a part
behind the last one sent (`run_span`, `SpanInv.windows`). That keeps them
inside the receiver's window (`Proofs/Connection`, `run_ahead_admitted`);
ENet's sender, with seven, can get past it.

The argument: first sends of a channel's reliable commands go out in
sequence order, and the first command of window `w` only goes when windows
`w .. w+10` are empty (`canSendReliable`), so what is in flight sits in
`w-5 .. w`. That needs the window counters to count exactly what is in
flight, which is the other half of the invariant.

`ChanOk` is the invariant for one channel, over the numbers of its commands
never sent (`pendSeqs`, consecutive after the frontier) and of those in
flight (`inflSeqs`, distinct, within the span, counted exactly by the window
counters). `QueueOk` lifts it to a peer, plus three facts the channel steps
need: what is in flight was sent and asks for an ACK, only control and
reliable data commands ask for one, and a free slot holds no data command
asking for one, so a new connection's fresh channels start clean.
`SpanInv` is `QueueOk` for a peer, and `HostInv` for every peer of a host.

Every writer of the four fields it reads keeps it: queuing a packet
(`enqueue_spanInv`), ACKs (`removeSentReliableCommand_spanInv`), packing
(`packOutgoingCommands_spanInv`, the heart of it: `PackInv` says a first
send held back sets `reliableHeld`, which holds back every later one),
retransmission (`checkPeerTimeouts_spanInv`), the receive path (which only
touches receive fields), the handshake, disconnects and resets. `run_inv`
puts them together over the same operations as `run_wf`
(Proofs/HostEvents.lean), and `disconnectNow_inv`, `resetPeer_inv` cover
the two calls `Op` leaves out.
-/

namespace Lenet.Proofs

open Peer

/-! ## Sequence arithmetic -/

theorem toNat_sub16 (a b : UInt16) : (a - b).toNat = (65536 - b.toNat + a.toNat) % 65536 :=
  UInt16.toNat_sub a b

theorem windowIndex_eq (s : UInt16) : Channel.windowIndex s = s.toNat / 4096 := by
  have := s.toNat_lt
  simp only [Channel.windowIndex, Constants.reliableWindowSize, Constants.reliableWindows]
  omega

/-- The step of the span bound when the next command goes out. Past a window
boundary, the window six back must be empty (`canSendReliable`). -/
theorem span_step (S s : UInt16) (h : (S - s).toNat ≤ S.toNat % 4096 + 20480)
    (hw : (S + 1).toNat % 4096 = 0 → Channel.windowIndex s ≠ (Channel.windowIndex (S + 1) + 10) % 16) :
    (S + 1 - s).toNat ≤ (S + 1).toNat % 4096 + 20480 := by
  rw [windowIndex_eq, windowIndex_eq] at hw
  rw [toNat_sub16] at h ⊢
  have hS := S.toNat_lt
  have hs := s.toNat_lt
  simp only [UInt16.toNat_add, UInt16.toNat_one] at hw ⊢
  omega

theorem span_ne (S s : UInt16) (h : (S - s).toNat ≤ S.toNat % 4096 + 20480) : s ≠ S + 1 := by
  rintro rfl
  rw [toNat_sub16] at h
  have hS := S.toNat_lt
  simp only [UInt16.toNat_add, UInt16.toNat_one] at h
  omega


/-- A pigeonhole bound: distinct in-flight numbers within the span are at
most the span's size, far below a window counter's `UInt16` limit. -/
theorem span_length (S : UInt16) (l : List UInt16) (hnd : l.Nodup)
    (h : ∀ s ∈ l, (S - s).toNat ≤ S.toNat % 4096 + 20480) : l.length ≤ 28672 := by
  have hinj : ∀ a b : UInt16, (S - a).toNat = (S - b).toNat → a = b := by
    intro a b hab
    have := UInt16.toNat_inj.mp hab
    have : S - (S - a) = S - (S - b) := by rw [this]
    simpa using this
  have hmap : (l.map fun s => (S - s).toNat).Nodup := by
    unfold List.Nodup at hnd ⊢
    rw [List.pairwise_map]
    exact hnd.imp fun hab he => hab (hinj _ _ he)
  have hsub : (l.map fun s => (S - s).toNat) ⊆ List.range 28672 := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
    have := h s hs
    rw [List.mem_range]; omega
  have := hmap.length_le_of_subset hsub
  simpa using this

/-! ## The per-channel invariant -/

/-- A reliable data command: what may ask for an ACK on a data channel. -/
def reliableBody : Protocol.CommandBody → Bool
  | .sendReliable .. | .sendFragment .. => true
  | _ => false

def seqOf (o : OutgoingCommand) : UInt16 := o.command.reliableSequenceNumber

/-- Queued on channel `c` and never sent. -/
def isPend (c : Nat) (o : OutgoingCommand) : Bool :=
  o.sendAttempts == 0 && o.command.acknowledge && o.command.channelId.toNat == c

/-- Sent on channel `c` and not acknowledged yet: in `sentReliableCommands`,
or queued again for retransmission. -/
def isInfl (c : Nat) (o : OutgoingCommand) : Bool :=
  o.sendAttempts != 0 && o.command.acknowledge && o.command.channelId.toNat == c

/-- The sequence numbers of channel `c`'s reliable commands never sent, in
queue order. -/
def pendSeqs (c : Nat) (out : List OutgoingCommand) : List UInt16 := (out.filter (isPend c)).map seqOf

/-- The sequence numbers of channel `c`'s reliable commands in flight. -/
def inflSeqs (c : Nat) (sent out : List OutgoingCommand) : List UInt16 :=
  ((sent ++ out).filter (isInfl c)).map seqOf

/-- The last sequence number sent on a channel: the last one numbered, minus
the ones still waiting. -/
def frontier (ch : Channel) (pend : List UInt16) : UInt16 :=
  ch.outgoingReliableSequenceNumber - pend.length.toUInt16

/-- **The sender side of one channel.** The commands never sent carry the
numbers right after the frontier, in order (so they go out in sequence
order); every command in flight is at most five windows and a part behind
the frontier and appears once; each window counter counts exactly the
commands in flight in its window. -/
structure ChanOk (ch : Channel) (pend infl : List UInt16) : Prop where
  consecutive : pend = (List.range pend.length).map fun i => frontier ch pend + 1 + i.toUInt16
  span : ∀ s ∈ infl, (frontier ch pend - s).toNat ≤ (frontier ch pend).toNat % 4096 + 20480
  nodup : infl.Nodup
  count : ∀ w (hw : w < Constants.reliableWindows),
    ch.reliableWindows[w].toNat = infl.countP fun s => Channel.windowIndex s == w

theorem ChanOk.perm {ch : Channel} {pend infl infl' : List UInt16} (h : ChanOk ch pend infl)
    (hp : infl.Perm infl') : ChanOk ch pend infl' where
  consecutive := h.consecutive
  span s hs := h.span s (hp.mem_iff.mpr hs)
  nodup := hp.nodup_iff.mp h.nodup
  count w hw := by rw [h.count w hw, hp.countP_eq]

/-- The invariant reads only a channel's outgoing counter and windows. -/
theorem ChanOk.congr {ch ch' : Channel} {pend infl : List UInt16} (h : ChanOk ch pend infl)
    (ho : ch'.outgoingReliableSequenceNumber = ch.outgoingReliableSequenceNumber)
    (hw : ch'.reliableWindows = ch.reliableWindows) : ChanOk ch' pend infl := by
  have hf : frontier ch' pend = frontier ch pend := by simp [frontier, ho]
  exact ⟨hf ▸ h.consecutive, hf ▸ h.span, h.nodup, hw ▸ h.count⟩

theorem chanOk_default : ChanOk ({} : Channel) [] [] where
  consecutive := rfl
  span s hs := by simp at hs
  nodup := List.nodup_nil
  count w hw := by simp [Vector.getElem_replicate]

/-- Closes a goal of `UInt16` arithmetic by going to `Nat`. -/
macro "u16_omega" : tactic => `(tactic| (
  apply UInt16.toNat.inj
  simp only [UInt16.toNat_sub, UInt16.toNat_add, UInt16.toNat_one, Nat.toUInt16, UInt16.toNat_ofNat', Nat.reducePow]
  omega))

/-- Past a window boundary, `canSendReliable` finds the window six back
(ten ahead, cyclically) empty. -/
theorem canSend_free {ch : Channel} {x : UInt16} (h : ch.canSendReliable x = true) (hx : x.toNat % 4096 = 0) :
    ch.reliableWindows[(Channel.windowIndex x + 10) % Constants.reliableWindows]'(Channel.modWindowIndex_lt _) = 0 := by
  unfold Channel.canSendReliable Channel.isWindowRangeInUse at h
  dsimp only at h
  split at h
  · next hne => exact absurd hx (by simpa [Constants.reliableWindowSize] using hne)
  · split at h
    · cases h
    · simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range] at h
      have := h 10 (by decide)
      simp only [Channel.windowIndex] at this ⊢
      simpa using this

theorem countP_zero {l : List UInt16} {p : UInt16 → Bool} (h : l.countP p = 0) : ∀ s ∈ l, p s = false := by
  intro s hs
  rw [List.countP_eq_zero] at h
  simpa using h s hs

theorem frontier_cons (ch : Channel) (x : UInt16) (pend : List UInt16) :
    frontier ch pend = frontier ch (x :: pend) + 1 := by
  simp only [frontier, List.length_cons]
  have := ch.outgoingReliableSequenceNumber.toNat_lt
  u16_omega

theorem countP_le_length16 (l : List UInt16) (p : UInt16 → Bool) : l.countP p ≤ l.length :=
  List.countP_le_length

/-- **A first send** takes the next number after the frontier, which moves
up by one; the window counter counts it. -/
theorem ChanOk.send {ch : Channel} {x : UInt16} {pend infl : List UInt16} (h : ChanOk ch (x :: pend) infl)
    (hcan : ch.canSendReliable x = true) : ChanOk (ch.acquireReliableWindow x) pend (x :: infl) := by
  obtain ⟨hcons, hspan, hnd, hcnt⟩ := h
  have hfr : frontier (ch.acquireReliableWindow x) pend = frontier ch (x :: pend) + 1 := frontier_cons ch x pend
  suffices ∀ S, frontier (ch.acquireReliableWindow x) pend = S + 1 →
      (x :: pend = (List.range (x :: pend).length).map fun i => S + 1 + i.toUInt16) →
      (∀ s ∈ infl, (S - s).toNat ≤ S.toNat % 4096 + 20480) →
      ChanOk (ch.acquireReliableWindow x) pend (x :: infl) from this _ hfr hcons hspan
  clear hfr hcons hspan
  intro S hfr hcons hspan
  suffices ChanOk' : pend = (List.range pend.length).map (fun i => S + 1 + 1 + i.toUInt16) ∧
      (∀ s ∈ x :: infl, (S + 1 - s).toNat ≤ (S + 1).toNat % 4096 + 20480) ∧ (x :: infl).Nodup ∧
      ∀ w (hw : w < Constants.reliableWindows),
        (ch.acquireReliableWindow x).reliableWindows[w].toNat = (x :: infl).countP fun s => Channel.windowIndex s == w by
    obtain ⟨a, b, c, d⟩ := ChanOk'
    exact ⟨hfr ▸ a, hfr ▸ b, c, d⟩
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons.injEq] at hcons
  obtain ⟨hx, hpend⟩ := hcons
  have hx : x = S + 1 := by rw [hx]; u16_omega
  subst hx
  have hlen := span_length S infl hnd hspan
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv => lhs; rw [hpend]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    u16_omega
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · refine span_step S s (hspan s hs) fun hb he => ?_
      have hfree := canSend_free hcan hb
      have hc := hcnt _ (Channel.modWindowIndex_lt (Channel.windowIndex (S + 1) + 10))
      rw [hfree] at hc
      have := countP_zero hc.symm s hs
      simp [he, Constants.reliableWindows] at this
  · exact List.nodup_cons.mpr ⟨fun hm => span_ne S _ (hspan _ hm) rfl, hnd⟩
  · intro w hw
    unfold Channel.acquireReliableWindow
    dsimp only
    rw [Vector.getElem_set, List.countP_cons]
    split
    · next he =>
      subst he
      have hc := hcnt _ (Channel.windowIndex_lt (S + 1))
      have := countP_le_length16 infl fun s => Channel.windowIndex s == Channel.windowIndex (S + 1)
      simp only [UInt16.toNat_add, UInt16.toNat_one, beq_self_eq_true, if_true]
      omega
    · next he =>
      have : (Channel.windowIndex (S + 1) == w) = false := by simpa using he
      rw [hcnt w hw, this]; rfl

/-- **An ACK** retires a command in flight. -/
theorem ChanOk.release {ch : Channel} {x : UInt16} {pend infl : List UInt16} (h : ChanOk ch pend (x :: infl)) :
    ChanOk (ch.releaseReliableWindow x) pend infl := by
  obtain ⟨hcons, hspan, hnd, hcnt⟩ := h
  have hc := hcnt _ (Channel.windowIndex_lt x)
  rw [List.countP_cons] at hc
  simp only [beq_self_eq_true, if_true] at hc
  unfold Channel.releaseReliableWindow
  dsimp only
  rw [if_neg (by intro h0; rw [beq_iff_eq] at h0; rw [h0] at hc; simp at hc)]
  refine ⟨hcons, fun s hs => hspan s (List.mem_cons_of_mem _ hs), (List.nodup_cons.mp hnd).2, ?_⟩
  intro w hw
  rw [Vector.getElem_set]
  split
  · next he =>
    subst he
    rw [UInt16.toNat_sub_of_le _ _ (by rw [UInt16.le_iff_toNat_le]; simp; omega)]
    simp; omega
  · next he =>
    have hcw := hcnt w hw
    rw [List.countP_cons] at hcw
    have : (Channel.windowIndex x == w) = false := by simpa using he
    rw [this] at hcw
    simpa using hcw

/-- **Queuing** `n` reliable commands numbers them after the last one. -/
theorem ChanOk.enqueue {ch ch' : Channel} {pend infl : List UInt16} (h : ChanOk ch pend infl) (n : Nat)
    (ho : ch'.outgoingReliableSequenceNumber = ch.outgoingReliableSequenceNumber + n.toUInt16)
    (hw : ch'.reliableWindows = ch.reliableWindows) :
    ChanOk ch' (pend ++ (List.range n).map fun i => ch.outgoingReliableSequenceNumber + 1 + i.toUInt16) infl := by
  obtain ⟨hcons, hspan, hnd, hcnt⟩ := h
  have hfr : frontier ch' (pend ++ (List.range n).map fun i => ch.outgoingReliableSequenceNumber + 1 + i.toUInt16) =
      frontier ch pend := by
    simp only [frontier, ho, List.length_append, List.length_map, List.length_range]
    have := ch.outgoingReliableSequenceNumber.toNat_lt
    u16_omega
  refine ⟨?_, hfr ▸ hspan, hnd, hw ▸ hcnt⟩
  rw [hfr, List.length_append, List.length_map, List.length_range, List.range_add, List.map_append, ← hcons,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, frontier]
  have := ch.outgoingReliableSequenceNumber.toNat_lt
  u16_omega

/-! ## The per-peer invariant -/

/-- A command asks for an ACK only as a control command (channel 0xFF) or a
reliable data command. -/
def BodyOk (o : OutgoingCommand) : Prop :=
  o.command.acknowledge = true → o.command.channelId = 0xFF ∨ reliableBody o.command.body = true

/-- The sender side of a peer with state `s`, channels `chs`, in-flight
commands `sent` and queue `out`: what is in flight was sent and asks for an
ACK; only control and reliable data commands ask for one; a free slot holds
no data command asking for one (so a new connection's fresh channels start
clean); and every data channel keeps `ChanOk`. -/
structure QueueOk (s : PeerState) (chs : Array Channel) (sent out : List OutgoingCommand) : Prop where
  inFlight : ∀ o ∈ sent, o.sendAttempts ≠ 0 ∧ o.command.acknowledge = true
  body : ∀ o ∈ sent ++ out, BodyOk o
  fresh : s = .disconnected → ∀ o ∈ sent ++ out, o.command.acknowledge = true → o.command.channelId = 0xFF
  chans : ∀ c (hc : c < chs.size), c < 255 → ChanOk chs[c] (pendSeqs c out) (inflSeqs c sent out)

/-- **The invariant**, for a peer. -/
def SpanInv (p : Peer) : Prop :=
  QueueOk p.state p.channels p.sentReliableCommands.toList p.outgoingCommands.toList

/-- The invariant reads only these four fields; a peer that leaves the free
state may do so. -/
theorem SpanInv.of {p q : Peer} (h : SpanInv p) (hs : q.state = .disconnected → p.state = .disconnected)
    (hc : q.channels = p.channels) (hsent : q.sentReliableCommands = p.sentReliableCommands)
    (hout : q.outgoingCommands = p.outgoingCommands) : SpanInv q := by
  unfold SpanInv at *
  rw [hc, hsent, hout]
  exact ⟨h.inFlight, h.body, fun hq => h.fresh (hs hq), h.chans⟩

/-- Channels with the same outgoing counters and windows. -/
def SameSend (a b : Array Channel) : Prop :=
  b.size = a.size ∧ ∀ c (ha : c < a.size) (hb : c < b.size),
    b[c].outgoingReliableSequenceNumber = a[c].outgoingReliableSequenceNumber ∧ b[c].reliableWindows = a[c].reliableWindows

theorem SameSend.rfl' (a : Array Channel) : SameSend a a := ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem QueueOk.sameSend {s chs chs' sent out} (h : QueueOk s chs sent out) (hc : SameSend chs chs') :
    QueueOk s chs' sent out :=
  ⟨h.inFlight, h.body, h.fresh, fun c hc' h255 =>
    have ha : c < chs.size := hc.1 ▸ hc'
    (h.chans c ha h255).congr (hc.2 c ha hc').1 (hc.2 c ha hc').2⟩

/-- Nothing queued, no channels: a reset slot. -/
theorem queueOk_empty (s : PeerState) : QueueOk s #[] [] [] :=
  ⟨by simp, by simp, by simp, fun c hc => by simp at hc⟩

theorem spanInv_reset (p : Peer) : SpanInv p.reset := queueOk_empty _

theorem spanInv_resetQueues (p : Peer) : SpanInv p.resetQueues := queueOk_empty _

theorem isPend_ctrl {c : Nat} (hc : c < 255) {o : OutgoingCommand} (ho : o.command.channelId = 0xFF) :
    isPend c o = false := by
  simp only [isPend, ho]
  have : (0xFF : UInt8).toNat = 255 := rfl
  simp [this]; omega

theorem isInfl_ctrl {c : Nat} (hc : c < 255) {o : OutgoingCommand} (ho : o.command.channelId = 0xFF) :
    isInfl c o = false := by
  simp only [isInfl, ho]
  have : (0xFF : UInt8).toNat = 255 := rfl
  simp [this]; omega

theorem isPend_noack {c : Nat} {o : OutgoingCommand} (ho : o.command.acknowledge = false) : isPend c o = false := by
  simp [isPend, ho]

theorem isInfl_noack {c : Nat} {o : OutgoingCommand} (ho : o.command.acknowledge = false) : isInfl c o = false := by
  simp [isInfl, ho]

theorem isInfl_fresh {c : Nat} {o : OutgoingCommand} (ho : o.sendAttempts = 0) : isInfl c o = false := by
  simp [isInfl, ho]

/-- Queuing a command that is neither pending nor in flight on any data
channel: a control command or one that asks for no ACK. -/
theorem QueueOk.push {s chs sent out} (h : QueueOk s chs sent out) (o : OutgoingCommand) (h0 : o.sendAttempts = 0)
    (hb : BodyOk o) (hf : s = .disconnected → o.command.acknowledge = true → o.command.channelId = 0xFF)
    (hp : ∀ c, c < 255 → isPend c o = false) : QueueOk s chs sent (out ++ [o]) := by
  refine ⟨h.inFlight, fun x hx => ?_, fun hs x hx => ?_, fun c hc h255 => ?_⟩
  · rw [← List.append_assoc] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.body x hx
    · simp at hx; subst hx; exact hb
  · rw [← List.append_assoc] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.fresh hs x hx
    · simp at hx; subst hx; exact hf hs
  · have := h.chans c hc h255
    simp only [pendSeqs, inflSeqs, ← List.append_assoc, List.filter_append, List.filter_cons, List.filter_nil,
      hp c h255, isInfl_fresh h0, List.append_nil, Bool.false_eq_true, if_false] at this ⊢
    exact this

theorem QueueOk.pushCtrl {s chs sent out} (h : QueueOk s chs sent out) (o : OutgoingCommand) (h0 : o.sendAttempts = 0)
    (ho : o.command.channelId = 0xFF) : QueueOk s chs sent (out ++ [o]) :=
  h.push o h0 (fun _ => .inl ho) (fun _ _ => ho) fun _ hc => isPend_ctrl hc ho

theorem queueControlCommand_spanInv {p : Peer} (h : SpanInv p) (body : Protocol.CommandBody) :
    SpanInv (p.queueControlCommand body) := by
  unfold SpanInv queueControlCommand queueOutgoingCommand
  simp only [Array.toList_push]
  exact h.pushCtrl _ rfl rfl

theorem sendLastDisconnect_spanInv {p : Peer} (h : SpanInv p) (d : UInt32) : SpanInv (p.sendLastDisconnect d) := by
  unfold SpanInv sendLastDisconnect queueOutgoingCommand
  simp only [Array.toList_push]
  have h' : SpanInv { p with outgoingControlSeq := p.outgoingControlSeq + 1, state := .zombie } :=
    h.of (by simp) rfl rfl rfl
  exact h'.pushCtrl _ rfl (by rfl)

theorem queueDisconnect_spanInv {p : Peer} (h : SpanInv p) (d : UInt32) : SpanInv (p.queueDisconnect d) := by
  unfold queueDisconnect
  split
  any_goals exact h
  simp only [Bool.or_eq_true]
  split
  · exact queueControlCommand_spanInv (p := { p.resetQueues with state := .disconnecting })
      ((spanInv_resetQueues p).of (by simp) rfl rfl rfl) _
  · exact sendLastDisconnect_spanInv (spanInv_resetQueues p) _

theorem disconnectNow_spanInv {p : Peer} (h : SpanInv p) (d : UInt32) : SpanInv (p.disconnectNow d) := by
  unfold disconnectNow
  split
  · exact h
  · exact h
  · exact spanInv_reset _
  · exact sendLastDisconnect_spanInv (spanInv_resetQueues p) _

/-! ## Acknowledgements -/

theorem perm_eraseIdx {α} (l : List α) (i : Nat) (h : i < l.length) : l.Perm (l[i] :: l.eraseIdx i) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => lhs; rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons h]
  exact List.perm_middle

theorem filter_eraseIdx_of_false {α} (l : List α) (p : α → Bool) (i : Nat) (h : i < l.length)
    (hp : p l[i] = false) : (l.eraseIdx i).filter p = l.filter p := by
  have hl : l.filter p = (l.take i).filter p ++ (l.drop (i + 1)).filter p := by
    conv => lhs; rw [← List.take_append_drop i l, List.drop_eq_getElem_cons h]
    rw [List.filter_append, List.filter_cons, hp]
    rfl
  rw [hl, List.eraseIdx_eq_take_drop_succ, List.filter_append]

theorem inflSeqs_perm {c : Nat} {sent out sent' out' : List OutgoingCommand} {x : OutgoingCommand}
    (hperm : (sent ++ out).Perm (x :: (sent' ++ out'))) :
    (inflSeqs c sent out).Perm ((if isInfl c x then [seqOf x] else []) ++ inflSeqs c sent' out') := by
  unfold inflSeqs
  have := (hperm.filter (isInfl c)).map seqOf
  rw [List.filter_cons] at this
  by_cases hx : isInfl c x = true <;> simp [hx] at this ⊢ <;> exact this

/-- Retiring command `x` from what is in flight (its ACK came), with its
window counter. -/
theorem QueueOk.retire {s chs sent out sent' out'} (h : QueueOk s chs sent out) (x : OutgoingCommand)
    (cid : UInt8) (seq : UInt16) (hcid : x.command.channelId = cid) (hseq : seqOf x = seq)
    (hx : x.sendAttempts ≠ 0 ∧ x.command.acknowledge = true)
    (hperm : (sent ++ out).Perm (x :: (sent' ++ out'))) (hsub : ∀ o ∈ sent', o ∈ sent)
    (hpend : ∀ c, c < 255 → out'.filter (isPend c) = out.filter (isPend c)) :
    QueueOk s (chs.modify cid.toNat (·.releaseReliableWindow seq)) sent' out' := by
  subst hseq hcid
  have hmem : ∀ o ∈ sent' ++ out', o ∈ sent ++ out := fun o ho =>
    hperm.symm.mem_iff.mp (List.mem_cons_of_mem _ ho)
  refine ⟨fun o ho => h.inFlight o (hsub o ho), fun o ho => h.body o (hmem o ho),
    fun hs o ho => h.fresh hs o (hmem o ho), fun c hc h255 => ?_⟩
  have hc' : c < chs.size := by simpa using hc
  have hch := h.chans c hc' h255
  have hp : pendSeqs c out' = pendSeqs c out := by unfold pendSeqs; rw [hpend c h255]
  rw [hp]
  have hi := inflSeqs_perm (c := c) hperm
  rw [Array.getElem_modify]
  split
  · next he =>
    have : isInfl c x = true := by simp [isInfl, hx.1, hx.2, he]
    rw [this] at hi
    exact (hch.perm (by simpa using hi)).release
  · next he =>
    have : isInfl c x = false := by simp [isInfl]; intro _ _ h; exact he (h ▸ rfl)
    rw [this] at hi
    exact hch.perm (by simpa using hi)

theorem removeSentReliableCommand_spanInv {p : Peer} (h : SpanInv p) (channelId : UInt8) (seq : UInt16) :
    SpanInv (p.removeSentReliableCommand channelId seq).1 := by
  unfold removeSentReliableCommand
  dsimp only
  split
  · next i hi =>
    have hit := (Array.findFinIdx?_eq_some_iff.mp hi).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hit
    have hlt : i.1 < p.sentReliableCommands.toList.length := by simp
    unfold SpanInv
    dsimp only
    rw [Array.toList_eraseIdx]
    refine h.retire p.sentReliableCommands[i] channelId seq hit.1 hit.2
      (h.inFlight _ (by simp)) ?_ (fun o ho => List.mem_of_mem_eraseIdx ho) fun _ _ => rfl
    have := perm_eraseIdx _ _ hlt
    simp only [Array.getElem_toList] at this
    exact this.append_right _
  · split
    · next i hi =>
      have hit := (Array.findFinIdx?_eq_some_iff.mp hi).1
      split
      · exact h
      · next h0 =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hit h0
        have hisIt : p.outgoingCommands[i].command.channelId = channelId ∧
            p.outgoingCommands[i].command.reliableSequenceNumber = seq := by
          rcases hit.2 with h0' | h'
          · exact absurd h0' h0
          · exact h'
        have hlt : i.1 < p.outgoingCommands.toList.length := by simp
        unfold SpanInv
        dsimp only
        rw [Array.toList_eraseIdx]
        refine h.retire p.outgoingCommands[i] channelId seq hisIt.1 hisIt.2 ⟨h0, hit.1⟩ ?_ (fun o ho => ho)
          fun c _ => filter_eraseIdx_of_false _ _ _ hlt (by simp [isPend]; intro h; exact absurd h h0)
        have := perm_eraseIdx _ _ hlt
        simp only [Array.getElem_toList] at this
        exact (this.append_left _).trans List.perm_middle
    · exact h

/-! ## Queuing packets -/

theorem pendSeqs_append (c : Nat) (a b : List OutgoingCommand) :
    pendSeqs c (a ++ b) = pendSeqs c a ++ pendSeqs c b := by
  simp [pendSeqs, List.filter_append]

theorem inflSeqs_fresh (c : Nat) (sent out L : List OutgoingCommand) (h0 : ∀ o ∈ L, o.sendAttempts = 0) :
    inflSeqs c sent (out ++ L) = inflSeqs c sent out := by
  unfold inflSeqs
  have : L.filter (isInfl c) = [] := List.filter_eq_nil_iff.mpr fun o ho => by simp [isInfl, h0 o ho]
  simp [← List.append_assoc, List.filter_append, this]

/-- Queuing new commands `L` on channel `cid`, whose channel becomes `ch'`:
on a data channel, the reliable ones take the next `n` numbers. -/
theorem QueueOk.enqueue {s chs sent out} (h : QueueOk s chs sent out) (hs : s ≠ .disconnected)
    (cid : UInt8) (hcid : cid.toNat < chs.size) (ch' : Channel) (L : List OutgoingCommand)
    (h0 : ∀ o ∈ L, o.sendAttempts = 0) (hon : ∀ o ∈ L, o.command.channelId = cid) (hb : ∀ o ∈ L, BodyOk o)
    (hnum : cid.toNat < 255 → ∃ n, ch'.outgoingReliableSequenceNumber = chs[cid.toNat].outgoingReliableSequenceNumber + n.toUInt16 ∧
      ch'.reliableWindows = chs[cid.toNat].reliableWindows ∧
      pendSeqs cid.toNat L = (List.range n).map fun i => chs[cid.toNat].outgoingReliableSequenceNumber + 1 + i.toUInt16) :
    QueueOk s (chs.setIfInBounds cid.toNat ch') sent (out ++ L) := by
  refine ⟨h.inFlight, fun o ho => ?_, fun hs' => absurd hs' hs, fun c hc h255 => ?_⟩
  · rw [← List.append_assoc] at ho
    rcases List.mem_append.mp ho with ho | ho
    · exact h.body o ho
    · exact hb o ho
  · have hc' : c < chs.size := by simpa using hc
    rw [pendSeqs_append, inflSeqs_fresh _ _ _ _ h0, Array.getElem_setIfInBounds hc']
    have hch := h.chans c hc' h255
    split
    · next he =>
      subst he
      obtain ⟨n, ho, hw, hp⟩ := hnum h255
      rw [hp]
      exact hch.enqueue n ho hw
    · next he =>
      have hL : pendSeqs c L = [] := by
        simp only [pendSeqs, List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro o ho; simp [isPend, hon o ho]; intro _ _ h; exact he h
      rw [hL, List.append_nil]; exact hch

theorem foldl_queue (xs : List OutgoingCommand) (q : Peer) :
    (xs.foldl queueOutgoingCommand q).outgoingCommands.toList = q.outgoingCommands.toList ++ xs ∧
      (xs.foldl queueOutgoingCommand q).sentReliableCommands = q.sentReliableCommands ∧
      (xs.foldl queueOutgoingCommand q).channels = q.channels ∧
      (xs.foldl queueOutgoingCommand q).state = q.state := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (q.queueOutgoingCommand x)
    refine ⟨?_, h2, h3, h4⟩
    rw [h1]; simp [queueOutgoingCommand]

theorem maxFragmentPayload_pos (p : Peer) (cs : Bool) : 0 < p.maxFragmentPayload cs := by
  unfold maxFragmentPayload; dsimp only; cases cs <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split <;> omega

theorem enqueue_spanInv {p : Peer} (h : SpanInv p) (hs : p.state ≠ .disconnected) (channelId : UInt8)
    (packet : Packet) (cs : Bool) : SpanInv (p.enqueue channelId packet cs) := by
  unfold enqueue
  split
  · exact h
  · next channel hget =>
    have hlt : channelId.toNat < p.channels.size := (Array.getElem?_eq_some_iff.mp hget).1
    have hch : p.channels[channelId.toNat] = channel := (Array.getElem?_eq_some_iff.mp hget).2
    dsimp only
    split
    · next hbig =>
      have hlen := maxFragmentPayload_pos p cs
      generalize hn : (packet.data.size + p.maxFragmentPayload cs - 1) / p.maxFragmentPayload cs = n
      have hn1 : 1 ≤ n := by
        rw [← hn, Nat.le_div_iff_mul_le hlen]; omega
      generalize hfc : fragmentCommands channel channelId packet (p.maxFragmentPayload cs) n = fc
      obtain ⟨ch', frags⟩ := fc
      dsimp only
      obtain ⟨e1, e2, e3, e4⟩ := foldl_queue frags.toList { p with channels := p.channels.setIfInBounds channelId.toNat ch' }
      rw [Array.foldl_toList] at e1 e2 e3 e4
      unfold SpanInv
      rw [e1, e2, e3, e4]
      unfold fragmentCommands at hfc
      dsimp only at hfc
      simp only [Prod.mk.injEq] at hfc
      obtain ⟨hch', hfr⟩ := hfc
      subst hfr
      refine h.enqueue hs channelId hlt ch' _ ?_ ?_ ?_ ?_
      · intro o ho; simp at ho; obtain ⟨i, _, rfl⟩ := ho; rfl
      · intro o ho; simp at ho; obtain ⟨i, _, rfl⟩ := ho; rfl
      · intro o ho; simp at ho; obtain ⟨i, _, rfl⟩ := ho
        intro hack
        right
        split <;> simp_all [reliableBody]
      · intro _
        rw [hch]
        split at hch'
        · next hu =>
          refine ⟨0, ?_, ?_, ?_⟩
          · subst hch'; simp [Channel.nextUnreliableSequenceNumber]
          · subst hch'; rfl
          · simp [pendSeqs, isPend, hu]
        · next hu =>
          refine ⟨n, ?_, ?_, ?_⟩
          · subst hch'; simp only [Channel.nextReliableSequenceNumber]
            have := channel.outgoingReliableSequenceNumber.toNat_lt
            u16_omega
          · subst hch'; rfl
          · simp only [pendSeqs, Array.toList_map, Array.toList_range, List.filter_map, List.map_map]
            rw [List.filter_eq_self.mpr (fun i _ => by simp [isPend, hu])]
            apply List.map_congr_left
            intro i _
            simp [seqOf, hu, Channel.nextReliableSequenceNumber]
    · next hsmall =>
      generalize hpc : p.packetCommand channel channelId packet = pc
      obtain ⟨p', ch', cmd⟩ := pc
      dsimp only
      have hp' : p'.channels = p.channels ∧ p'.state = p.state ∧ p'.outgoingCommands = p.outgoingCommands ∧
          p'.sentReliableCommands = p.sentReliableCommands := by
        unfold packetCommand at hpc
        dsimp only at hpc
        split at hpc <;> (try split at hpc) <;> (simp only [Prod.mk.injEq] at hpc; obtain ⟨rfl, _, _⟩ := hpc; simp)
      unfold SpanInv queueOutgoingCommand
      simp only [Array.toList_push, hp'.1, hp'.2.1, hp'.2.2.1, hp'.2.2.2]
      refine h.enqueue hs channelId hlt ch' _ (by simp) ?_ ?_ ?_
      · unfold packetCommand at hpc
        dsimp only at hpc
        intro o ho; simp at ho; subst ho
        split at hpc <;> (try split at hpc) <;> (simp only [Prod.mk.injEq] at hpc; obtain ⟨_, _, rfl⟩ := hpc; rfl)
      · unfold packetCommand at hpc
        dsimp only at hpc
        intro o ho; simp at ho; subst ho
        intro hack; right
        split at hpc <;> (try split at hpc) <;> (simp only [Prod.mk.injEq] at hpc; obtain ⟨_, _, rfl⟩ := hpc) <;>
          simp_all [reliableBody]
      · intro _
        rw [hch]
        unfold packetCommand at hpc
        dsimp only at hpc
        split at hpc <;> (try split at hpc)
        all_goals
          simp only [Prod.mk.injEq] at hpc
          obtain ⟨_, rfl, rfl⟩ := hpc
          first
            | (refine ⟨1, ?_, rfl, ?_⟩ <;>
                simp [pendSeqs, isPend, seqOf, Channel.nextReliableSequenceNumber]; done)
            | (refine ⟨0, ?_, rfl, ?_⟩ <;> simp [pendSeqs, isPend, Channel.nextUnreliableSequenceNumber]; done)

/-! ## Packing -/

/-- A reliable data command never sent. -/
def PendData (o : OutgoingCommand) : Prop :=
  o.sendAttempts = 0 ∧ o.command.acknowledge = true ∧ o.command.channelId ≠ 0xFF

theorem pendData_of_isPend {c : Nat} (hc : c < 255) {o : OutgoingCommand} (h : isPend c o = true) : PendData o := by
  simp only [isPend, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, fun he => ?_⟩
  rw [he] at h; have : (0xFF : UInt8).toNat = 255 := rfl; omega

/-- Dropping or packing a command that nothing counts: one asking for no
ACK, or a control command. -/
theorem QueueOk.drop {s chs sent rem xs} {x : OutgoingCommand} (h : QueueOk s chs sent (rem ++ x :: xs))
    (hx : ∀ c, c < 255 → isPend c x = false ∧ isInfl c x = false) : QueueOk s chs sent (rem ++ xs) := by
  have hmem : ∀ o ∈ sent ++ (rem ++ xs), o ∈ sent ++ (rem ++ x :: xs) := by
    intro o ho; simp only [List.mem_append, List.mem_cons] at ho ⊢
    rcases ho with ho | ho | ho <;> simp [ho]
  refine ⟨h.inFlight, fun o ho => h.body o (hmem o ho), fun hs o ho => h.fresh hs o (hmem o ho),
    fun c hc h255 => ?_⟩
  have := h.chans c hc h255
  simp only [pendSeqs, inflSeqs, List.filter_append, List.filter_cons, (hx c h255).1, (hx c h255).2,
    Bool.false_eq_true, if_false] at this ⊢
  exact this

theorem drop_noack {x : OutgoingCommand} (hx : x.command.acknowledge = false) :
    ∀ c, c < 255 → isPend c x = false ∧ isInfl c x = false :=
  fun _ _ => ⟨isPend_noack hx, isInfl_noack hx⟩

theorem perm_mid3 {α} (A B C : List α) (a : α) : (A ++ (B ++ a :: C)).Perm (a :: (A ++ (B ++ C))) := by
  rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_middle

theorem perm_end {α} (A B : List α) (a : α) : (A ++ [a] ++ B).Perm (a :: (A ++ B)) := by
  rw [List.append_assoc, List.singleton_append]; exact List.perm_middle

/-- The command `x` once sent. -/
def sentOnce (x : OutgoingCommand) (t r : UInt32) : OutgoingCommand :=
  { x with sendAttempts := x.sendAttempts + 1, sentTime := t, roundTripTimeout := r }

theorem inflSeqs_take (c : Nat) (sent rem xs : List OutgoingCommand) (x : OutgoingCommand) :
    (inflSeqs c sent (rem ++ x :: xs)).Perm
      ((if isInfl c x then [seqOf x] else []) ++ inflSeqs c sent (rem ++ xs)) := by
  unfold inflSeqs
  simp only [List.filter_append, List.filter_cons, List.map_append]
  split
  · simp only [List.map_cons, List.singleton_append]; exact perm_mid3 _ _ _ _
  · simp

theorem inflSeqs_sentOnce (c : Nat) (sent rem xs : List OutgoingCommand) {x : OutgoingCommand}
    (hack : x.command.acknowledge = true) (t r : UInt32) :
    (inflSeqs c (sent ++ [sentOnce x t r]) (rem ++ xs)).Perm
      ((if x.command.channelId.toNat == c then [seqOf x] else []) ++ inflSeqs c sent (rem ++ xs)) := by
  unfold inflSeqs
  simp only [List.filter_append, List.filter_cons, List.filter_nil, List.map_append]
  have : isInfl c (sentOnce x t r) = (x.command.channelId.toNat == c) := by
    simp [isInfl, sentOnce, hack]
  rw [this]
  split
  · simp only [List.singleton_append]; exact perm_end _ _ _
  · simp

/-- Sending command `x` keeps what does not depend on the channels. -/
theorem QueueOk.sendOne_of {s chs chs' sent rem xs} {x : OutgoingCommand} (h : QueueOk s chs sent (rem ++ x :: xs))
    (hack : x.command.acknowledge = true) (t r : UInt32)
    (hchans : ∀ c (hc : c < chs'.size), c < 255 →
      ChanOk chs'[c] (pendSeqs c (rem ++ xs)) (inflSeqs c (sent ++ [sentOnce x t r]) (rem ++ xs))) :
    QueueOk s chs' (sent ++ [sentOnce x t r]) (rem ++ xs) := by
  have hmem' : ∀ o ∈ (sent ++ [sentOnce x t r]) ++ (rem ++ xs), o.command = x.command ∨ o ∈ sent ++ (rem ++ x :: xs) := by
    intro o ho
    rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_append] at ho
    rcases ho with (ho | rfl) | ho | ho
    · exact .inr (by simp [ho])
    · exact .inl rfl
    · exact .inr (by simp [ho])
    · exact .inr (by simp [ho])
  have hxmem : x ∈ sent ++ (rem ++ x :: xs) := by simp
  refine ⟨fun o ho => ?_, fun o ho => ?_, fun hs o ho => ?_, hchans⟩
  · rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact h.inFlight o ho
    · exact ⟨by simp [sentOnce], hack⟩
  · rcases hmem' o ho with he | ho
    · unfold BodyOk; rw [he]; exact h.body x hxmem
    · exact h.body o ho
  · rcases hmem' o ho with he | ho
    · rw [he]; exact h.fresh hs x hxmem
    · exact h.fresh hs o ho

/-- **A retransmission** leaves the channels as they are. -/
theorem QueueOk.resend {s chs sent rem xs} {x : OutgoingCommand} (h : QueueOk s chs sent (rem ++ x :: xs))
    (hack : x.command.acknowledge = true) (h0 : x.sendAttempts ≠ 0) (t r : UInt32) :
    QueueOk s chs (sent ++ [sentOnce x t r]) (rem ++ xs) := by
  refine h.sendOne_of hack t r fun c hc h255 => ?_
  have hch := h.chans c hc h255
  have hpend : pendSeqs c (rem ++ x :: xs) = pendSeqs c (rem ++ xs) := by
    simp [pendSeqs, List.filter_append, isPend, h0]
  rw [hpend] at hch
  have hxi : isInfl c x = (x.command.channelId.toNat == c) := by simp [isInfl, h0, hack]
  have hi := inflSeqs_take c sent rem xs x
  rw [hxi] at hi
  exact (hch.perm hi).perm (inflSeqs_sentOnce c sent rem xs hack t r).symm

/-- **A first send**, in sequence order (nothing of its channel waits in
front of it) and admitted by `canSendReliable`. -/
theorem QueueOk.sendFirst {s chs sent rem xs} {x : OutgoingCommand} (h : QueueOk s chs sent (rem ++ x :: xs))
    (hack : x.command.acknowledge = true) (h0 : x.sendAttempts = 0) (t r : UInt32)
    (hfirst : x.command.channelId.toNat < 255 → ∀ hc : x.command.channelId.toNat < chs.size,
      rem.filter (isPend x.command.channelId.toNat) = [] ∧
        chs[x.command.channelId.toNat].canSendReliable x.command.reliableSequenceNumber = true) :
    QueueOk s (chs.modify x.command.channelId.toNat (·.acquireReliableWindow x.command.reliableSequenceNumber))
      (sent ++ [sentOnce x t r]) (rem ++ xs) := by
  refine h.sendOne_of hack t r fun c hc h255 => ?_
  have hc' : c < chs.size := by simpa using hc
  have hch := h.chans c hc' h255
  have hi := inflSeqs_take c sent rem xs x
  rw [isInfl_fresh h0] at hi
  have hi' := inflSeqs_sentOnce c sent rem xs hack t r
  rw [Array.getElem_modify]
  split
  · next he =>
    subst he
    obtain ⟨hrem, hcan⟩ := hfirst h255 hc'
    have hpend : pendSeqs x.command.channelId.toNat (rem ++ x :: xs) =
        seqOf x :: pendSeqs x.command.channelId.toNat (rem ++ xs) := by
      simp [pendSeqs, List.filter_append, hrem, isPend, h0, hack]
    rw [hpend] at hch
    rw [beq_self_eq_true] at hi'
    exact ((hch.perm (by simpa using hi)).send hcan).perm (by simpa using hi'.symm)
  · next he =>
    have hpend : pendSeqs c (rem ++ x :: xs) = pendSeqs c (rem ++ xs) := by
      simp [pendSeqs, List.filter_append, isPend, h0, hack, he]
    rw [hpend] at hch
    have : (x.command.channelId.toNat == c) = false := by simpa using he
    rw [this] at hi'
    exact (hch.perm (by simpa using hi)).perm (by simpa using hi'.symm)

open Host in
/-- Packing part way through the queue, with `xs` left to scan. Deferring a
reliable data command never sent always sets `reliableHeld`, and
`windowWrap` only comes with it: once one of a channel's first sends is
held back, no later one goes in this pass. -/
structure PackInv (s : PeerState) (st : PackState) (xs : List OutgoingCommand) : Prop where
  queue : QueueOk s st.channels st.sentReliables.toList (st.remainingOutgoing.toList ++ xs)
  held : ∀ o ∈ st.remainingOutgoing, PendData o → st.reliableHeld = true
  wrap : st.windowWrap = true → st.reliableHeld = true

open Host in
/-- The fields `PackInv` reads. -/
def PackState.Same (a b : PackState) : Prop :=
  b.remainingOutgoing = a.remainingOutgoing ∧ b.sentReliables = a.sentReliables ∧ b.channels = a.channels ∧
    b.windowWrap = a.windowWrap ∧ b.reliableHeld = a.reliableHeld

theorem PackInv.same {s st st' xs} (h : PackInv s st xs) (hs : PackState.Same st st') : PackInv s st' xs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  exact ⟨h1 ▸ h2 ▸ h3 ▸ h.queue, h1 ▸ h5 ▸ h.held, h4 ▸ h5 ▸ h.wrap⟩

theorem nextDatagram_same (st : Host.PackState) : PackState.Same st st.nextDatagram := by
  unfold Host.PackState.nextDatagram; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem pack_same (st : Host.PackState) (cmd) : PackState.Same st (st.pack cmd) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem packUnreliable_same (p : Peer) (st : Host.PackState) (cmd) : PackState.Same st (st.packUnreliable p cmd) := by
  unfold Host.PackState.packUnreliable
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem PackState.Same.rfl' (a : Host.PackState) : PackState.Same a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem PackState.Same.trans {a b c : Host.PackState} (h1 : PackState.Same a b) (h2 : PackState.Same b c) :
    PackState.Same a c := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩

theorem same_ite_next (st : Host.PackState) (c : Bool) :
    PackState.Same st (if c = true then st else st.nextDatagram) := by
  split
  · exact .rfl' _
  · exact nextDatagram_same st

theorem packAck_same (mtu : UInt32) (st : Host.PackState) (ack) : PackState.Same st (Host.PackState.packAck mtu st ack) := by
  have key : ∀ (st1 : Host.PackState), PackState.Same st st1 → ∀ (c : Bool) (cmd : Protocol.Command),
      PackState.Same st (if c = true then { st1.pack cmd with packedAcks := st1.packedAcks + 1 } else st1) := by
    intro st1 h1 c cmd
    split
    · exact h1.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact h1
  unfold Host.PackState.packAck
  exact key _ (same_ite_next st _) _ _

/-- Deferring `x`, possibly setting the flags. -/
theorem PackInv.defer {s st xs x} (h : PackInv s st (x :: xs)) (st' : Host.PackState)
    (h1 : st'.remainingOutgoing = st.remainingOutgoing) (h2 : st'.sentReliables = st.sentReliables)
    (h3 : st'.channels = st.channels) (hheld : st.reliableHeld = true → st'.reliableHeld = true)
    (hw : st'.windowWrap = true → st'.reliableHeld = true) (hx : PendData x → st'.reliableHeld = true) :
    PackInv s (st'.defer x) xs := by
  refine ⟨?_, fun o ho hpd => ?_, hw⟩
  · simp only [Host.PackState.defer, Array.toList_push, List.append_assoc, List.singleton_append, h1, h2, h3]
    exact h.queue
  · simp only [Host.PackState.defer, Array.mem_push] at ho
    rcases ho with ho | rfl
    · exact hheld (h.held o (h1 ▸ ho) hpd)
    · exact hx hpd

theorem PackInv.drop {s st xs x} (h : PackInv s st (x :: xs)) (hx : ∀ c, c < 255 → isPend c x = false ∧ isInfl c x = false) :
    PackInv s st xs :=
  ⟨h.queue.drop hx, h.held, h.wrap⟩

theorem carriesPacket_of {cmd : Protocol.Command} (h : reliableBody cmd.body = true) :
    Host.PackState.carriesPacket cmd = true := by
  unfold reliableBody at h; unfold Host.PackState.carriesPacket; split at h <;> simp_all

theorem continuesDroppedSet_body {st : Host.PackState} {cmd : Protocol.Command} (h : st.continuesDroppedSet cmd = true) :
    reliableBody cmd.body = false := by
  unfold Host.PackState.continuesDroppedSet at h
  split at h
  · next f heq => rw [heq]; rfl
  · cases h

theorem ctrl_ne {c : UInt8} (h : c.toNat < 255) : c ≠ 0xFF := by
  intro he; subst he; exact absurd h (by decide)

/-- **One command of the pass.** -/
theorem packCommand_packInv (p : Peer) (now : UInt32) {s st x xs} (h : PackInv s st (x :: xs)) :
    PackInv s (st.packCommand p now x) xs := by
  have hbody : BodyOk x := h.queue.body x (by simp)
  have hrd : PendData x → (x.command.acknowledge && Host.PackState.carriesPacket x.command) = true := by
    intro ⟨_, hack, hne⟩
    rcases hbody hack with he | hb
    · exact absurd he hne
    · simp [hack, carriesPacket_of hb]
  have hdrop : st.continuesDroppedSet x.command = true → ∀ c, c < 255 → isPend c x = false ∧ isInfl c x = false := by
    intro hd c hc
    have hrb := continuesDroppedSet_body hd
    cases hack : x.command.acknowledge
    · exact drop_noack hack c hc
    · rcases hbody hack with he | hb
      · exact ⟨isPend_ctrl hc he, isInfl_ctrl hc he⟩
      · rw [hrb] at hb; cases hb
  -- a datagram closed on the way keeps what `PackInv` reads
  have hst1 : ∀ c : Bool, PackInv s (if c = true then st else st.nextDatagram) (x :: xs) :=
    fun c => h.same (same_ite_next st c)
  unfold Host.PackState.packCommand
  dsimp only
  cases hack : x.command.acknowledge
  · have hnp : ¬ PendData x := fun hp => by rw [hp.2.1] at hack; cases hack
    simp only [Bool.false_and, Bool.false_eq_true, if_false, Option.isSome_none, Option.any_none, Bool.not_false,
      if_true, Bool.or_false]
    have tail : ∀ st1, PackInv s st1 (x :: xs) → PackInv s
        (if (!st1.fits p.mtu x.command) = true then st1.defer x else st1.packUnreliable p x.command) xs := by
      intro st1 h1
      split
      · exact h1.defer st1 rfl rfl rfl id h1.wrap fun hp => absurd hp hnp
      · exact (h1.same (packUnreliable_same p st1 _)).drop (drop_noack hack)
    split
    · exact h.drop (drop_noack hack)
    · exact tail _ (hst1 _)
  · simp only [Bool.true_and, if_true, Bool.not_true, Bool.false_eq_true, if_false]
    split
    · exact h.drop (hdrop ‹_›)
    split
    · next hB =>
      simp only [Bool.and_eq_true] at hB
      exact h.defer st rfl rfl rfl id h.wrap fun _ => hB.2
    split
    · next hC =>
      simp only [Bool.and_eq_true] at hC
      exact h.defer st rfl rfl rfl id h.wrap fun _ => h.wrap hC.2
    split
    · exact h.defer _ rfl rfl rfl (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    split
    · exact h.defer _ rfl rfl rfl (fun _ => rfl) (fun _ => rfl) fun _ => rfl
    next hB hC hD hE =>
    generalize hs1 : (if st.fits p.mtu x.command = true then st else st.nextDatagram) = st1
    have h1 : PackInv s st1 (x :: xs) := hs1 ▸ hst1 _
    have hsame : PackState.Same st st1 := hs1 ▸ same_ite_next st _
    split
    · refine h1.defer _ rfl rfl rfl (fun hh => by simp [hh]) (fun hw => by simp [h1.wrap hw]) fun hp => ?_
      have := hrd hp
      simp only [Bool.and_eq_true] at this
      simp [this.2]
    -- the first send of a data channel's command goes in sequence order
    have hfirst : x.command.channelId.toNat < 255 → ∀ hc : x.command.channelId.toNat < st1.channels.size,
        st1.remainingOutgoing.toList.filter (isPend x.command.channelId.toNat) = [] ∧
          (x.sendAttempts = 0 → st1.channels[x.command.channelId.toNat].canSendReliable
            x.command.reliableSequenceNumber = true) := by
      intro h255 hc
      have hcp : Host.PackState.carriesPacket x.command = true := by
        rcases hbody hack with he | hb
        · exact absurd he (ctrl_ne h255)
        · exact carriesPacket_of hb
      have hheld : st1.reliableHeld = false := by
        rw [hsame.2.2.2.2]; simpa [hcp] using hB
      refine ⟨List.filter_eq_nil_iff.mpr fun o ho hpo => ?_, fun h0 => ?_⟩
      · have := h1.held o (Array.mem_toList_iff.mp ho) (pendData_of_isPend h255 hpo)
        rw [hheld] at this; cases this
      · have hc' : x.command.channelId.toNat < st.channels.size := hsame.2.2.1 ▸ hc
        rw [Array.getElem?_eq_getElem hc'] at hD
        simp only [Option.any_some, h0, beq_self_eq_true, Bool.true_and, Bool.not_eq_true',
          Bool.not_eq_false] at hD
        have : st1.channels[x.command.channelId.toNat] = st.channels[x.command.channelId.toNat] := by
          simp only [hsame.2.2.1]
        rw [this]
        simpa using hD
    by_cases h0 : x.sendAttempts = 0
    · have h0' : (x.sendAttempts == 0) = true := by simp [h0]
      simp only [h0', if_true]
      refine ⟨?_, h1.held, h1.wrap⟩
      simp only [Host.PackState.pack, Array.toList_push]
      exact h1.queue.sendFirst hack h0 now _ fun h255 hc => ⟨(hfirst h255 hc).1, (hfirst h255 hc).2 h0⟩
    · have h0' : (x.sendAttempts == 0) = false := by simp [h0]
      simp only [h0', Bool.false_eq_true, if_false]
      refine ⟨?_, h1.held, h1.wrap⟩
      simp only [Host.PackState.pack, Array.toList_push]
      exact h1.queue.resend hack h0 now _

theorem foldl_packCommand (p : Peer) (now : UInt32) {s} :
    ∀ (xs : List OutgoingCommand) (st : Host.PackState), PackInv s st xs →
      PackInv s (xs.foldl (Host.PackState.packCommand p now) st) []
  | [], _, h => h
  | _ :: xs, _, h => foldl_packCommand p now xs _ (packCommand_packInv p now h)

theorem foldl_packAck_same (mtu : UInt32) :
    ∀ (acks : List Acknowledgement) (st : Host.PackState), PackState.Same st (acks.foldl (Host.PackState.packAck mtu) st)
  | [], st => .rfl' st
  | a :: acks, st => (packAck_same mtu st a).trans (foldl_packAck_same mtu acks _)

/-- **A packing pass keeps the invariant.** -/
theorem packOutgoingCommands_spanInv {p : Peer} (h : SpanInv p) (now : UInt32) (hc : Bool) :
    SpanInv (Host.packOutgoingCommands p now hc).1 := by
  unfold Host.packOutgoingCommands
  dsimp only
  have h0 : PackInv p.state ({ packetSize := Host.PackState.headerSize hc, emptySize := Host.PackState.headerSize hc, sentReliables := p.sentReliableCommands, channels := p.channels, throttleCounter := p.packetThrottleCounter } : Host.PackState) p.outgoingCommands.toList :=
    ⟨by simp only [List.nil_append]; exact h, fun o ho => by simp at ho, fun hw => by cases hw⟩
  have h1 := h0.same (foldl_packAck_same p.mtu p.acknowledgements.toList _)
  rw [Array.foldl_toList] at h1
  have h2 := foldl_packCommand
    { p with sentReliableCommands := #[], channels := #[] } now p.outgoingCommands.toList _ h1
  rw [Array.foldl_toList] at h2
  have := h2.queue
  rw [List.append_nil] at this
  exact this

theorem pollPeer_go_spanInv (now : UInt32) (cs : Bool) :
    ∀ (fuel : Nat) (p : Peer) (ds), SpanInv p → SpanInv (Host.pollPeer.go now cs fuel p ds).1
  | 0, _, _, h => h
  | fuel + 1, p, ds, h => by
    unfold Host.pollPeer.go
    dsimp only
    have h1 : SpanInv (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p) := by
      split
      · exact queueDisconnect_spanInv h _
      · exact h
    generalize (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p) = q at h1 ⊢
    have h2 := packOutgoingCommands_spanInv h1 now cs
    generalize Host.packOutgoingCommands q now cs = r at h2 ⊢
    obtain ⟨q', cmds⟩ := r
    dsimp only at h2 ⊢
    split
    · exact pollPeer_go_spanInv now cs fuel _ _ h2
    · split
      · exact spanInv_reset _
      · split
        · exact spanInv_reset _
        · exact h2

theorem pollPeer_spanInv {p : Peer} (h : SpanInv p) (now cs) : SpanInv (Host.pollPeer p now cs).1 := by
  unfold Host.pollPeer
  split
  · exact h
  · exact pollPeer_go_spanInv now cs _ _ _ h

/-! ## Retransmission -/

/-- What `QueueOk` reads of a command. -/
def key (o : OutgoingCommand) : Protocol.Command × Nat := (o.command, o.sendAttempts)

theorem mem_of_key {l l' : List OutgoingCommand} (hp : (l.map key).Perm (l'.map key)) {o : OutgoingCommand}
    (ho : o ∈ l) : ∃ o' ∈ l', key o' = key o := by
  have : key o ∈ l'.map key := hp.mem_iff.mp (List.mem_map_of_mem ho)
  simpa using this

theorem infl_key (c : Nat) (l : List OutgoingCommand) :
    (l.filter (isInfl c)).map seqOf =
      ((l.map key).filter fun k => k.2 != 0 && k.1.acknowledge && k.1.channelId.toNat == c).map
        (·.1.reliableSequenceNumber) := by
  rw [List.filter_map, List.map_map]; rfl

theorem pend_key (c : Nat) (l : List OutgoingCommand) :
    (l.filter (isPend c)).map seqOf =
      ((l.map key).filter fun k => k.2 == 0 && k.1.acknowledge && k.1.channelId.toNat == c).map
        (·.1.reliableSequenceNumber) := by
  rw [List.filter_map, List.map_map]; rfl

/-- **Queuing commands again**, as `checkPeerTimeouts` does: what was in
flight is split into what stays and what goes back to the front of the
queue, with only its timeout changed. -/
theorem QueueOk.requeue {s chs sent out still retx} (h : QueueOk s chs sent out)
    (hp : ((still ++ retx).map key).Perm (sent.map key)) : QueueOk s chs still (retx ++ out) := by
  have hmem : ∀ o ∈ still ++ retx, ∃ o' ∈ sent, key o' = key o := fun o ho => mem_of_key hp ho
  have hmem' : ∀ o ∈ still ++ (retx ++ out), (∃ o' ∈ sent, key o' = key o) ∨ o ∈ out := by
    intro o ho
    rw [← List.append_assoc, List.mem_append] at ho
    rcases ho with ho | ho
    · exact .inl (hmem o ho)
    · exact .inr ho
  have hk : ∀ {o o' : OutgoingCommand}, key o' = key o → o'.command = o.command ∧ o'.sendAttempts = o.sendAttempts :=
    fun he => Prod.mk.inj he
  refine ⟨fun o ho => ?_, fun o ho => ?_, fun hs o ho => ?_, fun c hc h255 => ?_⟩
  · obtain ⟨o', ho', he⟩ := hmem o (List.mem_append_left _ ho)
    obtain ⟨e1, e2⟩ := hk he
    rw [← e1, ← e2]; exact h.inFlight o' ho'
  · rcases hmem' o ho with ⟨o', ho', he⟩ | ho
    · unfold BodyOk; rw [← (hk he).1]; exact h.body o' (List.mem_append_left _ ho')
    · exact h.body o (List.mem_append_right _ ho)
  · rcases hmem' o ho with ⟨o', ho', he⟩ | ho
    · rw [← (hk he).1]; exact h.fresh hs o' (List.mem_append_left _ ho')
    · exact h.fresh hs o (List.mem_append_right _ ho)
  · have hch := h.chans c hc h255
    have hpend : pendSeqs c (retx ++ out) = pendSeqs c out := by
      rw [pendSeqs_append]
      have : pendSeqs c retx = [] := by
        simp only [pendSeqs, List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro o ho
        obtain ⟨o', ho', he⟩ := hmem o (List.mem_append_right _ ho)
        have := (h.inFlight o' ho').1
        simp [isPend, ← (hk he).2, this]
      rw [this, List.nil_append]
    rw [hpend]
    refine hch.perm ?_
    unfold inflSeqs
    rw [infl_key, infl_key, ← List.append_assoc, List.map_append, List.map_append]
    exact ((hp.symm.append_right _).filter _).map _

theorem scan_fold (f : Host.TimeoutScan → OutgoingCommand → Host.TimeoutScan)
    (hsticky : ∀ sc o, sc.timedOut = true → f sc o = sc)
    (hstep : ∀ sc o, sc.timedOut = false → (f sc o).timedOut = false →
      (((f sc o).stillInFlight.toList ++ (f sc o).retransmits.toList).map key).Perm
        ((sc.stillInFlight.toList ++ sc.retransmits.toList ++ [o]).map key)) :
    ∀ (l : List OutgoingCommand) sc, (l.foldl f sc).timedOut = false →
      sc.timedOut = false ∧ (((l.foldl f sc).stillInFlight.toList ++ (l.foldl f sc).retransmits.toList).map key).Perm
        ((sc.stillInFlight.toList ++ sc.retransmits.toList ++ l).map key)
  | [], sc, h => ⟨h, by simp⟩
  | o :: l, sc, h => by
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h1, hp⟩ := scan_fold f hsticky hstep l _ h
    have h0 : sc.timedOut = false := by
      cases hs : sc.timedOut
      · rfl
      · rw [hsticky sc o hs, hs] at h1; cases h1
    refine ⟨h0, hp.trans ?_⟩
    have := (hstep sc o h0 h1).append_right (l.map key)
    simpa [List.map_append] using this

/-- One command of the timeout scan (the body of `checkPeerTimeouts`' fold
once the peer has not timed out yet): it stays in flight, times the peer
out, or goes back to the queue with its timeout doubled. -/
def scanStep (sc : Host.TimeoutScan) (o : OutgoingCommand) (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (e : UInt32) : Host.TimeoutScan :=
  if c1 then { sc with stillInFlight := sc.stillInFlight.push o }
  else if c2 then { sc with timedOut := true }
  else { sc with earliestTimeout := e, retransmits := sc.retransmits.push { o with roundTripTimeout := o.roundTripTimeout * 2 } }

theorem step_shape (sc : Host.TimeoutScan) (o : OutgoingCommand) (c1 c2 : Prop) [Decidable c1] [Decidable c2]
    (e : UInt32) (hr : (scanStep sc o c1 c2 e).timedOut = false) :
    (((scanStep sc o c1 c2 e).stillInFlight.toList ++ (scanStep sc o c1 c2 e).retransmits.toList).map key).Perm
      ((sc.stillInFlight.toList ++ sc.retransmits.toList ++ [o]).map key) := by
  unfold scanStep at hr ⊢
  split
  · simp only [Array.toList_push, List.map_append, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  · split
    · next h1 h2 => rw [if_neg h1, if_pos h2] at hr; cases hr
    · simp only [Array.toList_push, List.map_append, List.append_assoc]
      exact .refl _

theorem checkPeerTimeouts_spanInv {p : Peer} (h : SpanInv p) (now : UInt32) :
    SpanInv (Host.checkPeerTimeouts p now).1 := by
  unfold Host.checkPeerTimeouts
  dsimp only
  split
  · exact spanInv_reset _
  · next hto =>
    rw [← Array.foldl_toList] at hto ⊢
    simp only [Bool.not_eq_true] at hto
    obtain ⟨_, hp⟩ := scan_fold _ (fun sc o hs => by simp [hs]) (fun sc o hs hs' => by
        have hn : ¬ sc.timedOut = true := by simp [hs]
        rw [if_neg hn] at hs' ⊢
        exact step_shape sc o _ _ _ hs'
        ) _ _ hto
    unfold SpanInv
    dsimp only
    rw [Array.toList_append]
    exact h.requeue (by simpa using hp)

theorem checkPeerPing_spanInv {p : Peer} (h : SpanInv p) (now : UInt32) : SpanInv (Host.checkPeerPing p now) := by
  unfold Host.checkPeerPing
  split
  · exact queueControlCommand_spanInv h _
  · exact h

/-! ## Receiving -/

/-- A channel step that leaves the sender side alone. -/
def SendKept (c c' : Channel) : Prop :=
  c'.outgoingReliableSequenceNumber = c.outgoingReliableSequenceNumber ∧ c'.reliableWindows = c.reliableWindows

theorem receiveReliableSpan_kept (c : Channel) (seq span packet) : SendKept c (c.receiveReliableSpan seq span packet).1 := by
  unfold Channel.receiveReliableSpan
  dsimp only
  (repeat' split) <;> exact ⟨rfl, rfl⟩

theorem releaseStagedUnreliable_kept (c : Channel) (old : UInt16) (advance : Nat) :
    SendKept c (c.releaseStagedUnreliable old advance).1 := by
  unfold Channel.releaseStagedUnreliable
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    generalize Channel.eraseAfter _ _ _ _ = er
    obtain ⟨_, _, _⟩ := er
    dsimp only
    refine Array.foldl_induction (motive := fun _ (r : Channel × Array Packet) => SendKept c r.1) ⟨rfl, rfl⟩ ?_
    intro i r hr
    obtain ⟨ch, rel⟩ := r
    simp only [] at hr ⊢
    split
    · exact hr
    · exact hr

theorem receiveReliableAndRelease_kept (c : Channel) (seq span packet) :
    SendKept c (c.receiveReliableAndRelease seq span packet).1 := by
  unfold Channel.receiveReliableAndRelease
  have h1 := receiveReliableSpan_kept c seq span packet
  dsimp only
  generalize c.receiveReliableSpan seq span packet = r at h1 ⊢
  obtain ⟨c', d⟩ := r
  dsimp only at h1 ⊢
  split
  · exact h1
  · have h2 := releaseStagedUnreliable_kept c' c.incomingReliableSequenceNumber (d.foldl (fun n d => n + d.1) 0)
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem receiveUnreliable_kept (c : Channel) (rs seq packet) : SendKept c (c.receiveUnreliable rs seq packet).1 := by
  unfold Channel.receiveUnreliable
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem pruneAssemblers_spanInv {p : Peer} (h : SpanInv p) (c : UInt8) : SpanInv (p.pruneAssemblers c) := by
  unfold pruneAssemblers
  split
  · split
    · exact h
    · exact h.of (fun hs => hs) rfl rfl rfl
  · exact h

theorem receiveOnChannel_spanInv {p : Peer} (h : SpanInv p) (channelId : UInt8)
    (receive : Channel → Channel × Array Packet) (hr : ∀ c, SendKept c (receive c).1) :
    SpanInv (p.receiveOnChannel channelId receive).1 := by
  by_cases hlt : channelId.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ hlt]
    dsimp only
    refine pruneAssemblers_spanInv ?_ _
    refine QueueOk.sameSend h ⟨by simp, fun c ha hb => ?_⟩
    simp only [Array.getElem_set]
    split
    · next he => subst he; exact hr _
    · exact ⟨rfl, rfl⟩
  · rw [receiveOnChannel_out _ _ _ hlt]; exact h

/-- A peer step that leaves the four fields `SpanInv` reads alone. -/
def Kept (p q : Peer) : Prop :=
  q.state = p.state ∧ q.channels = p.channels ∧ q.sentReliableCommands = p.sentReliableCommands ∧
    q.outgoingCommands = p.outgoingCommands

theorem SpanInv.kept {p q : Peer} (h : SpanInv p) (hk : Kept p q) : SpanInv q :=
  h.of (fun hs => hk.1 ▸ hs) hk.2.1 hk.2.2.1 hk.2.2.2

theorem throttle_kept (p : Peer) (r) : Kept p (p.throttle r) := by
  unfold throttle; split <;> (try split) <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem updateRtt_kept (p : Peer) (n r) : Kept p (p.updateRtt n r) := by
  unfold updateRtt; dsimp only
  have ht := throttle_kept p (max r 1)
  split
  · generalize p.throttle (max r 1) = q at ht
    split <;> (split <;> exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩)
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem handleData_spanInv {p : Peer} (h : SpanInv p) (cmd : Protocol.Command) : SpanInv (p.handleData cmd).1 := by
  unfold handleData
  split
  · exact receiveOnChannel_spanInv h _ _ fun c => receiveReliableAndRelease_kept c _ _ _
  · exact receiveOnChannel_spanInv h _ _ fun c => receiveUnreliable_kept c _ _ _
  · split
    · exact h.kept ⟨rfl, rfl, rfl, rfl⟩
    · exact h
  · exact h

theorem handleHeldData_spanInv {p : Peer} (h : SpanInv p) (cmd : Protocol.Command) :
    SpanInv (p.handleHeldData cmd).1 := by
  rcases handleHeldData_cases p cmd with he | he <;> rw [he]
  · exact h
  · exact handleData_spanInv h _

theorem handleFragment_spanInv {p : Peer} (h : SpanInv p) (channelId : UInt8) (reliableSeq : UInt16)
    (params : Protocol.FragmentParams) (unreliable : Bool) :
    SpanInv (p.handleFragment channelId reliableSeq params unreliable).1 := by
  have hfa : ∀ ys, SpanInv { p with fragmentAssemblers := ys } := fun _ => h.kept ⟨rfl, rfl, rfl, rfl⟩
  unfold handleFragment
  split
  · exact h
  split
  · exact h
  dsimp only
  generalize absorbFragment p.fragmentAssemblers (fragmentOrigin channelId reliableSeq unreliable) params _ _ = ab
  obtain ⟨xs, i?⟩ := ab
  cases i? with
  | none => exact hfa _
  | some i =>
    dsimp only
    split
    · rw [takeAt_eq]
      dsimp only
      split
      · split <;> exact hfa _
      · split
        · exact hfa _
        · refine receiveOnChannel_spanInv (hfa _) _ _ fun c => ?_
          split
          · exact receiveUnreliable_kept c _ _ _
          · exact receiveReliableAndRelease_kept c _ _ _
        · exact hfa _
    · exact hfa _

theorem handleAcknowledge_spanInv {p : Peer} (h : SpanInv p) (now : UInt32) (channelId : UInt8) (seq sentTime : UInt16) :
    SpanInv (p.handleAcknowledge now channelId seq sentTime).1 := by
  unfold handleAcknowledge
  dsimp only
  split
  · exact h
  split
  · exact h
  have hq := removeSentReliableCommand_spanInv (h.kept (updateRtt_kept p now (Time.difference now (Time.fromWire now sentTime))))
    channelId seq
  generalize (p.updateRtt now _).removeSentReliableCommand channelId seq = q at hq ⊢
  obtain ⟨q, acked⟩ := q
  dsimp only at hq ⊢
  split
  · split
    · exact hq.of (by simp) rfl rfl rfl
    · exact hq
  · split
    · exact spanInv_reset _
    · exact hq
  · split
    · exact queueDisconnect_spanInv hq _
    · exact hq
  · exact hq

theorem handleDisconnect_spanInv {p : Peer} (h : SpanInv p) (d : UInt32) : SpanInv (p.handleDisconnect d).1 := by
  unfold handleDisconnect
  split
  · exact h
  · exact h
  · exact h
  · exact (spanInv_resetQueues p).of (by simp) rfl rfl rfl
  · exact (spanInv_resetQueues p).of (by simp) rfl rfl rfl
  · exact spanInv_reset _
  · exact spanInv_reset _

theorem QueueOk.take {s chs sent out} (h : QueueOk s chs sent out) (n : Nat) : QueueOk s (chs.take n) sent out :=
  ⟨h.inFlight, h.body, h.fresh, fun c hc h255 => by
    have hc' : c < chs.size := by simp at hc; omega
    simp only [Array.take_eq_extract, Array.getElem_extract, Nat.zero_add]
    exact h.chans c hc' h255⟩

theorem handleVerifyConnect_spanInv {p : Peer} (h : SpanInv p) (params : Protocol.ConnectParams) :
    SpanInv (p.handleVerifyConnect params).1 := by
  unfold handleVerifyConnect
  split
  · exact h
  split
  · exact spanInv_reset _
  dsimp only
  have hq := removeSentReliableCommand_spanInv h 0xFF 1
  generalize p.removeSentReliableCommand 0xFF 1 = q at hq ⊢
  obtain ⟨q, _⟩ := q
  exact ⟨hq.inFlight, hq.body, (fun hs => by cases hs), (hq.take _).chans⟩

theorem applyCommand_spanInv {p : Peer} (h : SpanInv p) (now : UInt32) (cmd : Protocol.Command) :
    SpanInv (p.applyCommand now cmd).1 := by
  unfold applyCommand
  dsimp only
  split
  all_goals (repeat' split) <;> first
    | exact handleAcknowledge_spanInv h _ _ _ _
    | exact handleDisconnect_spanInv h _
    | exact handleVerifyConnect_spanInv h _
    | exact handleData_spanInv h _
    | exact handleHeldData_spanInv h _
    | exact handleFragment_spanInv h _ _ _ _
    | exact h
    | exact h.kept ⟨rfl, rfl, rfl, rfl⟩

theorem handleCommand_spanInv {p : Peer} (h : SpanInv p) (now : UInt32) (cmd : Protocol.Command) (st : Option UInt16) :
    SpanInv (p.handleCommand now cmd st).1 := by
  unfold handleCommand
  have ha := applyCommand_spanInv h now cmd
  generalize p.applyCommand now cmd = r at ha ⊢
  obtain ⟨q, es, acc⟩ := r
  dsimp only at ha ⊢
  split
  · exact ha
  split
  · exact ha
  split
  · exact ha
  · split
    · exact ha.kept ⟨rfl, rfl, rfl, rfl⟩
    · exact ha

theorem readCommands_spanInv (now : UInt32) (st : Option UInt16) :
    ∀ (xs : List Protocol.Command) (acc : Peer × Array Event × Bool × Bool), SpanInv acc.1 →
      SpanInv (xs.foldl (Host.readCommand now st) acc).1
  | [], _, h => h
  | cmd :: xs, ⟨p, es, reading, bw⟩, h => by
    rw [List.foldl_cons]
    refine readCommands_spanInv now st xs _ ?_
    unfold Host.readCommand
    cases reading
    · exact h
    · exact handleCommand_spanInv h now cmd st

theorem handlePeerDatagram_spanInv {p : Peer} (h : SpanInv p) (now fromAddr datagram bw) :
    SpanInv (Host.handlePeerDatagram p now fromAddr datagram bw).1 := by
  unfold Host.handlePeerDatagram
  have h2 := readCommands_spanInv now datagram.header.sentTime datagram.commands.toList
    ({ p with address := fromAddr }, #[], true, false) (h.kept ⟨rfl, rfl, rfl, rfl⟩)
  rw [Array.foldl_toList] at h2
  dsimp only
  generalize Array.foldl _ _ datagram.commands = r at h2 ⊢
  split
  · exact h2.kept ⟨rfl, rfl, rfl, rfl⟩
  · exact h2

/-! ## The host -/

/-- A new connection's fresh channels: the free slot held no data command
asking for an ACK. -/
theorem QueueOk.fresh_channels {chs sent out} (h : QueueOk .disconnected chs sent out) (s' : PeerState) (n : Nat) :
    QueueOk s' (Array.replicate n {}) sent out := by
  have hctrl := h.fresh rfl
  refine ⟨h.inFlight, h.body, fun _ o ho hack => hctrl o ho hack, fun c hc h255 => ?_⟩
  have hp : pendSeqs c out = [] := by
    simp only [pendSeqs, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    cases hack : o.command.acknowledge
    · exact by simp [isPend_noack hack]
    · simp [isPend_ctrl h255 (hctrl o (List.mem_append_right _ ho) hack)]
  have hi : inflSeqs c sent out = [] := by
    simp only [inflSeqs, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    cases hack : o.command.acknowledge
    · exact by simp [isInfl_noack hack]
    · simp [isInfl_ctrl h255 (hctrl o ho hack)]
  rw [hp, hi, Array.getElem_replicate]
  exact chanOk_default

/-- Every peer slot keeps the invariant. -/
def HostInv (h : Host) : Prop := ∀ p ∈ h.peers, SpanInv p

theorem mem_modify_or' {α} {xs : Array α} {i : Nat} {f : α → α} {x : α}
    (hx : x ∈ xs.modify i f) : x ∈ xs ∨ ∃ y ∈ xs, x = f y := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [Array.getElem_modify]
  split
  · next he => subst he; exact .inr ⟨_, Array.getElem_mem (by simpa using hj), rfl⟩
  · exact .inl (Array.getElem_mem _)

theorem HostInv.modify {h : Host} (hi : HostInv h) (i : Nat) (f : Peer → Peer) (hf : ∀ p ∈ h.peers, SpanInv p → SpanInv (f p)) :
    ∀ q ∈ h.peers.modify i f, SpanInv q := by
  intro q hq
  rcases mem_modify_or' hq with hq | ⟨p, hp, rfl⟩
  · exact hi q hq
  · exact hf p hp (hi p hp)

theorem HostInv.map {h : Host} (hi : HostInv h) (f : Peer → Peer) (hf : ∀ p ∈ h.peers, SpanInv p → SpanInv (f p)) :
    ∀ q ∈ h.peers.map f, SpanInv q := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
  exact hf p hp (hi p hp)

theorem freeSlot_state {h : Host} {slot} (hs : h.freeSlot? = some slot) : h.peers[slot.1].state = .disconnected := by
  unfold Host.freeSlot? at hs
  exact peerState_beq.mp (Array.findFinIdx?_eq_some_iff.mp hs).1

theorem handleIncomingConnect_inv {h : Host} (hi : HostInv h) (fromAddr params data) :
    HostInv (h.handleIncomingConnect fromAddr params data) := by
  unfold Host.handleIncomingConnect
  dsimp only
  split
  · exact hi
  split
  · exact hi
  · next slot hslot =>
    have hfree := freeSlot_state hslot
    have hp := hi _ (Array.getElem_mem slot.2)
    intro q hq
    rw [modifyPeer_peers] at hq
    refine hi.modify _ _ (fun _ _ _ => ?_) q hq
    refine queueControlCommand_spanInv ?_ _
    unfold SpanInv at hp ⊢
    rw [hfree] at hp
    exact hp.fresh_channels _ _

theorem handleDatagram_inv {h : Host} (hi : HostInv h) (now fromAddr bytes) :
    HostInv (h.handleDatagram now fromAddr bytes).1 := by
  unfold Host.handleDatagram
  dsimp only
  split
  · exact hi
  · split
    · split
      · exact handleIncomingConnect_inv hi _ _ _
      · exact hi
    · split
      · exact hi
      · split
        · exact hi
        · rw [withPeer_eq]
          exact fun q hq => hi.modify _ _ (fun p _ hp => handlePeerDatagram_spanInv hp _ _ _ _) q hq

theorem limitPeers_inv (elapsed : Nat) : ∀ (fuel : Nat) budget limited needs (peers : Array Peer),
    (∀ p ∈ peers, SpanInv p) →
      ∀ q ∈ (Host.outgoingThrottleLimits.limitPeers elapsed budget limited needs peers fuel).1, SpanInv q
  | 0, _, _, _, _, h => h
  | fuel + 1, budget, limited, needs, peers, h => by
    unfold Host.outgoingThrottleLimits.limitPeers
    split
    · exact h
    · dsimp only
      refine limitPeers_inv elapsed fuel _ _ _ _ ?_
      refine Array.foldl_induction (motive := fun _ (r : Array Peer × Host.OutgoingBudget × Array UInt16) =>
        ∀ q ∈ r.1, SpanInv q) (fun q hq => by simp at hq) ?_
      intro i r hr
      obtain ⟨acc, bud, lim⟩ := r
      dsimp only at hr ⊢
      have hpi := h _ (Array.getElem_mem i.2)
      split
      · intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · exact hr q hq
        · exact hpi
      · intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · exact hr q hq
        · exact hpi.kept ⟨rfl, rfl, rfl, rfl⟩

theorem ite_map_inv {c : Prop} [Decidable c] {A : Array Peer} (hA : ∀ q ∈ A, SpanInv q) (f : Peer → Peer)
    (hf : ∀ p, SpanInv p → SpanInv (f p)) : ∀ q ∈ (if c then A else A.map f), SpanInv q := by
  intro q hq
  split at hq
  · exact hA q hq
  · obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
    exact hf p (hA p hp)

theorem outgoingThrottleLimits_inv {h : Host} (hi : HostInv h) (elapsed : Nat) :
    ∀ q ∈ h.outgoingThrottleLimits elapsed, SpanInv q := by
  unfold Host.outgoingThrottleLimits
  dsimp only
  split
  all_goals
    refine ite_map_inv (limitPeers_inv _ _ _ _ _ _ hi) _ fun p hp => ?_
    split
    · exact hp.kept ⟨rfl, rfl, rfl, rfl⟩
    · exact hp

theorem bandwidthThrottle_inv {h : Host} (hi : HostInv h) (now : UInt32) : HostInv (h.bandwidthThrottle now) := by
  unfold Host.bandwidthThrottle
  split
  · exact hi
  · dsimp only
    split
    · exact hi
    · have hl := outgoingThrottleLimits_inv hi (Time.difference now h.bandwidthThrottleEpoch).toNat
      split
      · exact hl
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
        split
        · exact queueControlCommand_spanInv (hl p hp) _
        · exact hl p hp

theorem checkTimeoutsAndPings_inv {h : Host} (hi : HostInv h) (now : UInt32) :
    HostInv (h.checkTimeoutsAndPings now).1 := by
  unfold Host.checkTimeoutsAndPings
  let F (p : Peer) : Peer :=
    if p.state == .disconnected ∨ p.state == .zombie then p
    else match Host.checkPeerTimeouts p now with
      | (q, some _) => q
      | (q, none) => Host.checkPeerPing q now
  let E (p : Peer) : Array Event :=
    if p.state == .disconnected ∨ p.state == .zombie then #[] else (Host.checkPeerTimeouts p now).2.toArray
  rw [mapPeers_eq _ _ _ F (fun p s => s ++ E p)]
  · refine fun q hq => hi.map F (fun p _ hp => ?_) q hq
    simp only [F]
    split
    · exact hp
    · have hc := checkPeerTimeouts_spanInv hp now
      generalize Host.checkPeerTimeouts p now = c at hc ⊢
      obtain ⟨q, _ | e⟩ := c
      · exact checkPeerPing_spanInv hc now
      · exact hc
  · intro p s
    simp only [F, E]
    split
    · simp
    · generalize Host.checkPeerTimeouts p now = c
      obtain ⟨q, _ | e⟩ := c <;> simp

theorem pollOutgoing_inv {h : Host} (hi : HostInv h) (now : UInt32) : HostInv (h.pollOutgoing now).1 := by
  unfold Host.pollOutgoing
  dsimp only
  rw [mapPeers_eq _ _ _ (fun p => (Host.pollPeer p now h.checksumEnabled).1)
    (fun p s => (s.1 ++ (Host.pollPeer p now h.checksumEnabled).2.1, s.2 ++ (Host.pollPeer p now h.checksumEnabled).2.2))
    (fun p s => rfl)]
  exact fun q hq => hi.map _ (fun p _ hp => pollPeer_spanInv hp _ _) q hq

theorem service_inv {h : Host} (hi : HostInv h) (now : UInt32) : HostInv (h.service now).1 := by
  unfold Host.service
  dsimp only
  exact pollOutgoing_inv (checkTimeoutsAndPings_inv (bandwidthThrottle_inv hi now) now) now

theorem sendError_connected {p : Peer} {c pk cs} (h : p.sendError? c pk cs = none) : p.state ≠ .disconnected := by
  unfold sendError? at h
  dsimp only at h
  split at h
  · cases h
  · next hs => intro hd; rw [hd] at hs; exact hs (by decide)

theorem trySend_inv {h : Host} (hi : HostInv h) (id c pk) : HostInv (h.trySend id c pk).1 := by
  unfold Host.trySend
  rw [withPeer_eq]
  intro q hq
  dsimp only at hq
  refine hi.modify _ _ (fun p _ hp => ?_) q hq
  split
  · exact hp
  · next he => exact enqueue_spanInv hp (sendError_connected he) _ _ _

theorem broadcast_inv {h : Host} (hi : HostInv h) (c pk) : HostInv (h.broadcast c pk) := by
  unfold Host.broadcast
  dsimp only
  rw [mapPeers_eq _ _ _ (fun p =>
      if p.state == .connected && (p.sendError? c pk h.checksumEnabled).isNone then
        p.enqueue c pk h.checksumEnabled
      else p) (fun _ _ => ()) (fun p s => by split <;> simp [*])]
  refine fun q hq => hi.map _ (fun p _ hp => ?_) q hq
  split
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    exact enqueue_spanInv hp (by rw [peerState_beq.mp hc.1]; decide) _ _ _
  · exact hp

theorem modify_inv {h : Host} (hi : HostInv h) (id : UInt16) (f : Peer → Peer) (hf : ∀ p, SpanInv p → SpanInv (f p)) :
    HostInv (h.modifyPeer id f) := by
  intro q hq
  rw [modifyPeer_peers] at hq
  exact hi.modify _ _ (fun p _ hp => hf p hp) q hq

theorem connect_inv {h h' : Host} {id} (hi : HostInv h) {addr n d} (hc : h.connect addr n d = .ok (h', id)) :
    HostInv h' := by
  unfold Host.connect at hc
  have hp := random_peers h
  rcases hr : h.random with ⟨h2, cid⟩
  rw [hr] at hc hp
  simp only at hp
  split at hc
  · next slot hslot =>
    have hfree := freeSlot_state hslot
    cases hc
    intro q hq
    rw [modifyPeer_peers, hp] at hq
    refine hi.modify _ _ (fun _ _ _ => ?_) q hq
    refine queueControlCommand_spanInv ?_ _
    have hsp := hi _ (Array.getElem_mem slot.2)
    unfold SpanInv at hsp ⊢
    rw [hfree] at hsp
    exact hsp.fresh_channels _ _
  · cases hc

theorem Op.apply_inv {h : Host} (hi : HostInv h) : ∀ op : Op, HostInv (op.apply h).1
  | .datagram .. => handleDatagram_inv hi _ _ _
  | .service .. => service_inv hi _
  | .connect addr n d => by
    simp only [Op.apply]
    split
    · next hc => exact connect_inv hi hc
    · exact hi
  | .send .. => trySend_inv hi _ _ _
  | .broadcast .. => broadcast_inv hi _ _
  | .disconnect .. => modify_inv hi _ _ fun _ hp => queueDisconnect_spanInv hp _
  | .disconnectLater id d => modify_inv hi _ _ fun p hp => by
    split
    · exact hp.of (by simp) rfl rfl rfl
    · exact queueDisconnect_spanInv hp _
  | .throttleConfigure .. => modify_inv hi _ _ fun p hp => by
    split
    · exact hp
    · exact queueControlCommand_spanInv (hp.kept ⟨rfl, rfl, rfl, rfl⟩) _
  | .setPeerTimeout .. => modify_inv hi _ _ fun _ hp => hp.kept ⟨rfl, rfl, rfl, rfl⟩
  | .ping .. => modify_inv hi _ _ fun p hp => by
    split
    · exact queueControlCommand_spanInv hp _
    · exact hp
  | .setPingInterval .. => modify_inv hi _ _ fun _ hp => hp.kept ⟨rfl, rfl, rfl, rfl⟩
  | .bandwidthLimit .. => hi
  | .setChannelLimit .. => hi

/-- The two calls `Op` leaves out keep the invariant too. -/
theorem disconnectNow_inv {h : Host} (hi : HostInv h) (id d) : HostInv (h.disconnectNow id d) :=
  modify_inv hi _ _ fun _ hp => disconnectNow_spanInv hp _

theorem resetPeer_inv {h : Host} (hi : HostInv h) (id) : HostInv (h.resetPeer id) :=
  modify_inv hi _ _ fun p _ => spanInv_reset p

theorem create_inv (address peerCount channelLimit inBw outBw seed mtu) :
    HostInv (Host.create address peerCount channelLimit inBw outBw seed mtu) := by
  intro p hp
  simp only [Host.create, Array.mem_map, Array.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  exact queueOk_empty _

theorem run_inv : ∀ (ops : List Op) {h : Host}, HostInv h → HostInv (run h ops).1
  | [], _, hi => hi
  | op :: ops, _, hi => run_inv ops (Op.apply_inv hi op)

/-! ## What the invariant says -/

/-- The last reliable sequence number sent on channel `c` of `p`. -/
def sentFrontier (p : Peer) (c : Nat) (hc : c < p.channels.size) : UInt16 :=
  frontier p.channels[c] (pendSeqs c p.outgoingCommands.toList)

/-- The sequence numbers of channel `c`'s reliable commands in flight. -/
def inFlight (p : Peer) (c : Nat) : List UInt16 :=
  inflSeqs c p.sentReliableCommands.toList p.outgoingCommands.toList

/-- In flight means at most six windows back from the last command sent. -/
theorem SpanInv.span {p : Peer} (h : SpanInv p) (c : Nat) (hc : c < p.channels.size) (h255 : c < 255) :
    ∀ s ∈ inFlight p c, (sentFrontier p c hc - s).toNat < 6 * Constants.reliableWindowSize := by
  intro s hs
  have := (h.chans c hc h255).span s hs
  simp only [Constants.reliableWindowSize]
  unfold sentFrontier
  omega

/-- ... so the windows of the commands in flight are the frontier's window
and at most five before it. -/
theorem SpanInv.windows {p : Peer} (h : SpanInv p) (c : Nat) (hc : c < p.channels.size) (h255 : c < 255) :
    ∀ s ∈ inFlight p c, ∃ k ≤ 5,
      Channel.windowIndex s = (Channel.windowIndex (sentFrontier p c hc) + Constants.reliableWindows - k) %
        Constants.reliableWindows := by
  intro s hs
  have hb := (h.chans c hc h255).span s hs
  unfold sentFrontier
  generalize frontier p.channels[c] (pendSeqs c p.outgoingCommands.toList) = S at hb ⊢
  rw [windowIndex_eq, windowIndex_eq]
  rw [toNat_sub16] at hb
  have := S.toNat_lt; have := s.toNat_lt
  refine ⟨(S.toNat / 4096 + 16 - s.toNat / 4096) % 16, by omega, ?_⟩
  simp only [Constants.reliableWindows]
  omega

/-- A channel's commands never sent carry the numbers right after the
frontier, in queue order: first sends go out in sequence order. -/
theorem SpanInv.consecutive {p : Peer} (h : SpanInv p) (c : Nat) (hc : c < p.channels.size) (h255 : c < 255) :
    pendSeqs c p.outgoingCommands.toList =
      (List.range (pendSeqs c p.outgoingCommands.toList).length).map fun i => sentFrontier p c hc + 1 + i.toUInt16 :=
  (h.chans c hc h255).consecutive

/-- Each window counter counts exactly the channel's commands in flight in
its window, and no number is in flight twice. -/
theorem SpanInv.counters {p : Peer} (h : SpanInv p) (c : Nat) (hc : c < p.channels.size) (h255 : c < 255) :
    (inFlight p c).Nodup ∧ ∀ w (hw : w < Constants.reliableWindows),
      p.channels[c].reliableWindows[w].toNat = (inFlight p c).countP fun s => Channel.windowIndex s == w :=
  ⟨(h.chans c hc h255).nodup, (h.chans c hc h255).count⟩

/-- **The sender-side window span.** From `Host.create`, after any sequence
of received datagrams, `service` calls and application calls, the reliable
commands in flight on every data channel of every peer lie within six
windows ending at the last one sent (`SpanInv.windows` names them). -/
theorem run_span (address peerCount channelLimit inBw outBw seed mtu) (ops : List Op) :
    let h := (run (Host.create address peerCount channelLimit inBw outBw seed mtu) ops).1
    ∀ p ∈ h.peers, ∀ c (hc : c < p.channels.size), c < 255 →
      ∀ s ∈ inFlight p c, (sentFrontier p c hc - s).toNat < 6 * Constants.reliableWindowSize := by
  intro h p hp c hc h255
  exact (run_inv ops (create_inv address peerCount channelLimit inBw outBw seed mtu) p hp).span c hc h255

end Lenet.Proofs
