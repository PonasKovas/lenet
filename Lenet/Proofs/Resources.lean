import Lenet.Constants
import Lenet.Host
import Lenet.Channel
import Lenet.Proofs.Reassembly
import Lenet.Proofs.Channel
import Lenet.Proofs.Receive

/-!
# Resource-safety proofs

Robustness against hostile input (deliberately stricter than
ENet, whose pending-assembler growth is bounded only by its window span).
The attacker-controlled memory surfaces and their bounds:

1. **Fragment assemblers** (`Peer.fragmentAssemblers`): capped at
   `maximumFragmentAssemblers` concurrent assemblies
   (`handleFragment_cap_preserved`); every assembler is created by
   `FragmentAssembler.init`, whose validation pins `totalLength ≤
   maxPacketSize` and the bitset to `fragmentCount` bytes (`init_bounds`;
   the create-guard additionally bounds fragmentCount by
   `maximumReceivedFragmentCount`), and `addFragment` never resizes the
   bitset (`addFragment_size_preserved`). An assembler stores only the
   fragments that arrived. Over the whole array: every assembler keeps
   `Proofs.Inv` (Proofs/Reassembly.lean) and those bounds, and the cap
   holds (`AssemblersOk`, `handleFragment_assemblersOk`), so each one stores
   at most `maximumReceivedFragmentCount` fragments carrying at most
   `maximumPacketSize` bytes (`assemblerOk_footprint`). What the sets under
   way claim, in bytes: under `maximumWaitingData + maximumPacketSize`
   (`handleFragment_waiting`, `waitingOk_footprint`), ENet's budget.
2. **Staged reliable packets** (`Channel.stagedReliable`): at most
   `(freeReliableWindows - 1) * reliableWindowSize` per channel
   (`stagedReliableInv_size`), whatever the sender does. The receive-window
   gate drops out-of-window seqs, the duplicate check keeps keys distinct,
   and an in-order delivery drops the entries its span jumped over, so
   staged keys stay distinct and inside the window
   (`StagedReliableInv`, kept by every receive:
   `receiveReliableAndRelease_stagedReliableInv`,
   `receiveUnreliable_stagedReliableInv`), and lifted to every channel of
   a peer through each writer of `Peer.channels` (`PeerStagedInv`,
   `peerStagedInv_size`). The replay corpus asserts the bound too.
3. **Staged unreliable packets** (`Channel.stagedUnreliable`): capped at
   `maximumStagedUnreliable` by `Channel.receiveUnreliable`, the only place
   that grows it; asserted by the replay corpus.
4. **Acknowledgement queue**: production is coupled to the driver's pump
   rate (≤ 32 acks per received datagram) and the packing loop drains up to
   `maximumPacketCommands` per tick; growth beyond a well-behaved pump is
   the same exposure as ENet's - documented, not capped (capping drops ACKs
   and forces retransmissions for no robustness gain).

The mutators of `fragmentAssemblers` are `Peer.handleFragment` (via
`absorbFragment`, then replacing or erasing the set's assembler) and
`Peer.receiveOnChannel`, which only prunes (`Peer.reset` clears the
field). `Proofs/ResourcesRun` carries every bound here through every host
operation from `Host.create` on (`runApp_resources`); the replay corpus
asserts them after every service step of every scenario too.
-/

namespace Lenet.Proofs

open Peer FragmentAssembler

/-! ## Per-assembler allocation bounds -/

/-- A successfully created assembler allocates only its `fragmentCount`-slot
bitset, and `init`'s validation pins `totalLength ≤ maxPacketSize` and
`fragmentCount ≤ maximumFragmentCount`. -/
theorem init_bounds {ssn : UInt16} {tl fc maxPacketSize : Nat} {a : FragmentAssembler}
    (h : FragmentAssembler.init ssn tl fc maxPacketSize = .ok a) :
    a.received.size = fc ∧ tl ≤ maxPacketSize ∧ fc ≤ Constants.maximumFragmentCount := by
  unfold FragmentAssembler.init at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals cases h
  next h2 h3 _ =>
  exact ⟨zeros_size fc, by omega, by omega⟩

/-! ## Size preservation through `addFragment` -/

/-- `addFragment` never resizes the bitset. -/
theorem addFragment_size_preserved {a a' : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {r : Option ByteArray} (h : a.addFragment n off d = .ok (a', r)) :
    a'.received.size = a.received.size := by
  obtain ⟨-, -, -, hn, hc⟩ := addFragment_ok_cases h
  rcases hc with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · rfl
  · exact byteArray_size_set _ _ _ _

/-! ## The assembler concurrency cap -/

/-- `assemblerRoom` leaves room for one more assembler under the cap. -/
theorem assemblerRoom_size {xs room : Array FragmentAssembler}
    (h : assemblerRoom xs = some room)
    (hcap : xs.size ≤ Constants.maximumFragmentAssemblers) :
    room.size < Constants.maximumFragmentAssemblers := by
  unfold assemblerRoom at h
  split at h
  · next hlt =>
    cases h
    exact hlt
  · split at h
    · next i _ =>
      cases h
      rw [Array.size_eraseIdx]
      have := i.isLt
      omega
    · cases h

/-- `absorbFragment` never grows the array beyond the cap. -/
theorem absorbFragment_cap_preserved (xs : Array FragmentAssembler) (origin : FragmentOrigin)
    (params : Protocol.FragmentParams) (held : Unit → Nat) (next : Bool)
    (hcap : xs.size ≤ Constants.maximumFragmentAssemblers) :
    (absorbFragment xs origin params held next).1.size ≤ Constants.maximumFragmentAssemblers := by
  unfold absorbFragment
  split
  · exact hcap
  · split
    · exact hcap
    · split
      · exact hcap
      · next room hroom =>
        have hlt := assemblerRoom_size hroom hcap
        split
        · exact hcap
        split
        · exact hcap
        split
        · exact hcap
        split
        · simp only [Array.size_push]
          omega
        · exact hcap

/-- Pruning only removes assemblers. -/
theorem pruneAssemblers_size (p : Peer) (channelId : UInt8) :
    (p.pruneAssemblers channelId).fragmentAssemblers.size ≤ p.fragmentAssemblers.size := by
  unfold pruneAssemblers
  split
  · split
    · exact Nat.le_refl _
    · exact Array.size_filter_le
  · exact Nat.le_refl _

/-- Channel delivery never adds assemblers (it only prunes stale ones). -/
theorem receiveOnChannel_fragmentAssemblers_size (p : Peer) (channelId : UInt8)
    (receive : Channel → Channel × Array Packet) :
    (p.receiveOnChannel channelId receive).1.fragmentAssemblers.size ≤ p.fragmentAssemblers.size := by
  by_cases h : channelId.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ h]; exact pruneAssemblers_size _ _
  · rw [receiveOnChannel_out _ _ _ h]; exact Nat.le_refl _

/-- Where `handleFragment` can leave the assembler array: unchanged, the
absorbed array `xs`, `xs` with the set's assembler replaced by what
`addFragment` made of it, or `xs` without it (then maybe pruned by a
channel delivery). A property of all four, for whatever budget inputs
`absorbFragment` is given, holds afterwards. -/
theorem handleFragment_assemblers (p : Peer) (c : UInt8) (s : UInt16) (pr : Protocol.FragmentParams)
    (u : Bool) (P : Array FragmentAssembler → Prop) (h0 : P p.fragmentAssemblers)
    (habs : ∀ held next, P (absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).1)
    (hset : ∀ held next i (hi : i < (absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).1.size) w r,
      (absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).2 = some i →
      ((absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).1[i]).addFragment
        pr.fragmentNumber.toNat pr.fragmentOffset.toNat pr.data = .ok (w, r) →
      P ((absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).1.set i w hi))
    (herase : ∀ held next i (hi : i < (absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).1.size),
      (absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).2 = some i →
      P ((absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr held next).1.eraseIdx i hi))
    (hrecv : ∀ (q : Peer), P q.fragmentAssemblers → ∀ c recv, P (q.receiveOnChannel c recv).1.fragmentAssemblers) :
    P (p.handleFragment c s pr u).1.fragmentAssemblers := by
  unfold handleFragment
  split
  · exact h0
  split
  · exact h0
  dsimp only
  have habs := habs (fun _ => channelsStagedBytes p.channels) (deliversNext p.channels c pr.startSequenceNumber u)
  have hset := hset (fun _ => channelsStagedBytes p.channels) (deliversNext p.channels c pr.startSequenceNumber u)
  have herase := herase (fun _ => channelsStagedBytes p.channels) (deliversNext p.channels c pr.startSequenceNumber u)
  generalize hab : absorbFragment p.fragmentAssemblers (fragmentOrigin c s u) pr _ _ = ab at habs hset herase
  obtain ⟨xs, i?⟩ := ab
  dsimp only at habs hset herase ⊢
  cases i? with
  | none => exact habs
  | some i =>
    dsimp only
    split
    · next hi =>
      rw [takeAt_eq]
      dsimp only
      split
      · split
        · show P ((xs.set i default hi).eraseIdxIfInBounds i)
          rw [set_eraseIdxIfInBounds_same]; exact herase i hi rfl
        · rw [set_setIfInBounds_same, Array.set_getElem_self]; exact habs
      · split
        · next w heq => rw [set_setIfInBounds_same]; exact hset i hi w none rfl heq
        · next heq =>
          refine hrecv _ ?_ _ _
          show P ((xs.set i default hi).eraseIdxIfInBounds i)
          rw [set_eraseIdxIfInBounds_same]; exact herase i hi rfl
        · show P ((xs.set i default hi).eraseIdxIfInBounds i)
          rw [set_eraseIdxIfInBounds_same]; exact herase i hi rfl
    · exact habs

/-- `handleFragment` never grows the assembler array beyond the cap: the
absorbed array is capped (`absorbFragment_cap_preserved`), and replacing,
erasing and pruning never grow it. -/
theorem handleFragment_cap_preserved (p : Peer) (channelId : UInt8) (reliableSeq : UInt16)
    (params : Protocol.FragmentParams) (unreliable : Bool)
    (hcap : p.fragmentAssemblers.size ≤ Constants.maximumFragmentAssemblers) :
    (handleFragment p channelId reliableSeq params unreliable).1.fragmentAssemblers.size
      ≤ Constants.maximumFragmentAssemblers := by
  have hxs := fun held next => absorbFragment_cap_preserved p.fragmentAssemblers
    (fragmentOrigin channelId reliableSeq unreliable) params held next hcap
  refine handleFragment_assemblers p channelId reliableSeq params unreliable
    (fun ys => ys.size ≤ Constants.maximumFragmentAssemblers) hcap hxs ?_ ?_ ?_
  · intro held next i hi w r _ _; simpa using hxs held next
  · intro held next i hi _; simp only [Array.size_eraseIdx]; have := hxs held next; omega
  · intro q hq c recv; exact Nat.le_trans (receiveOnChannel_fragmentAssemblers_size _ _ _) hq

/-! ## Staged reliable packets -/

open Channel

/-! ## The staging bound -/

/-- `isReliableAhead` reads only the dispatch frontier. -/
theorem isReliableAhead_congr {c d : Channel}
    (h : c.incomingReliableSequenceNumber = d.incomingReliableSequenceNumber) (s : UInt16) :
    c.isReliableAhead s = d.isReliableAhead s := by
  simp [isReliableAhead, isIncomingReliableInWindow, h]

/-- The staging invariant: each staged entry is stored under the sequence
number it starts at, that number is still ahead of the frontier inside the
receive window, and the entry spans at least one sequence number. -/
def StagedReliableInv (c : Channel) : Prop :=
  ∀ (k : UInt16) (e : StagedReliable), c.stagedReliable[k]? = some e →
    e.seq = k ∧ c.isReliableAhead k = true ∧ 1 ≤ e.span

/-- The staging bound: distinct sequence numbers inside the window span
number at most the span. -/
theorem stagedReliableInv_size {c : Channel} (h : StagedReliableInv c) :
    c.stagedReliable.size ≤ (Constants.freeReliableWindows - 1) * Constants.reliableWindowSize := by
  let off (k : UInt16) : Nat := (k - c.incomingReliableSequenceNumber).toNat
  have hnd : c.stagedReliable.keys.Nodup :=
    Std.HashMap.distinct_keys.imp fun {a b} hab heq => by simp [heq] at hab
  have hnd' : (c.stagedReliable.keys.map off).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hnd.imp fun {a b} hab heq => hab ?_
    have : a - c.incomingReliableSequenceNumber = b - c.incomingReliableSequenceNumber :=
      UInt16.toNat_inj.mp heq
    rw [← UInt16.sub_add_cancel a c.incomingReliableSequenceNumber, this, UInt16.sub_add_cancel]
  have hsub : c.stagedReliable.keys.map off
      ⊆ List.range ((Constants.freeReliableWindows - 1) * Constants.reliableWindowSize) := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
    have hmem : k ∈ c.stagedReliable := Std.HashMap.mem_keys.mp hk
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (Std.HashMap.mem_iff_isSome_getElem?.mp hmem)
    exact List.mem_range.mpr (isReliableAhead_offset c k (h k e he).2.1)
  rw [← Std.HashMap.length_keys]
  simpa using hnd'.length_le_of_subset hsub

/-- Every reliable receive keeps the staging invariant: staging adds only an
admitted, new sequence number, and an in-order delivery keeps only the
entries still ahead of the new frontier. -/
theorem receiveReliableSpan_stagedReliableInv {c : Channel} (h : StagedReliableInv c)
    (seq : UInt16) (span : Nat) (packet : Packet) :
    StagedReliableInv (receiveReliableSpan c seq span packet).1 := by
  have hspans : ∀ (k : UInt16) (e : StagedReliable), c.stagedReliable[k]? = some e → 1 ≤ e.span :=
    fun k e he => (h k e he).2.2
  unfold receiveReliableSpan
  dsimp only
  split
  · exact h
  · next hwin =>
    split
    · exact h
    · next hdup =>
      split
      · next hnext =>
        dsimp only
        generalize hdr : drainContiguous _ c.stagedReliable = dr
        obtain ⟨newSeq, drained, rest, adv⟩ := dr
        dsimp only
        have hfull : drainContiguousLoop (seq + (max span 1 - 1).toUInt16) c.stagedReliable #[]
            c.stagedReliable.size 0 = (newSeq, drained, rest, adv) := by rw [← hdr]; rfl
        obtain ⟨-, -, hadv, -⟩ := drainContiguousLoop_advance _ _ _ _ _ _ _ _ _ hspans hfull
        have hseq : seq = c.incomingReliableSequenceNumber + 1 := by simpa using hnext
        intro k e he
        simp only [] at he
        rw [eraseAfter_get] at he
        split at he
        · cases he
        · next hnot =>
          have hrest : rest[k]? = some e := he
          have hold := h k e (drainContiguousLoop_get _ _ _ _ _ k e (by rw [hfull]; exact hrest))
          refine ⟨hold.1, isReliableAhead_after_advance hold.2.1 (by simpa using hnot) ?_, hold.2.2⟩
          show newSeq.toNat = (c.incomingReliableSequenceNumber.toNat + (max span 1 + adv)) % 65536
          rw [hadv, UInt16.toNat_add, hseq, UInt16.toNat_add]
          simp [UInt16.toNat_ofNat']
          omega
      · split
        · exact h
        · intro k e he
          simp only [] at he
          rw [Std.HashMap.getElem?_insert] at he
          split at he
          · next hk =>
            simp only [beq_iff_eq] at hk
            subst hk
            cases he
            refine ⟨rfl, ?_, Nat.le_max_right _ _⟩
            simp only [Bool.not_eq_true'] at hwin
            simp only [beq_iff_eq] at hdup
            show (c.isIncomingReliableInWindow seq && seq != c.incomingReliableSequenceNumber) = true
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
            exact ⟨by simpa using hwin, hdup⟩
          · exact h k e he

/-- Releasing staged unreliable packets leaves reliable staging and the
frontier alone. -/
theorem releaseStagedUnreliable_reliable (c : Channel) (old : UInt16) (advance : Nat) :
    (releaseStagedUnreliable c old advance).1.stagedReliable = c.stagedReliable ∧
      (releaseStagedUnreliable c old advance).1.incomingReliableSequenceNumber = c.incomingReliableSequenceNumber := by
  unfold releaseStagedUnreliable
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    generalize eraseAfter _ _ _ _ = er
    obtain ⟨_, _, _⟩ := er
    dsimp only
    refine Array.foldl_induction
      (motive := fun _ (r : Channel × Array Packet) => r.1.stagedReliable = c.stagedReliable ∧
        r.1.incomingReliableSequenceNumber = c.incomingReliableSequenceNumber)
      ⟨rfl, rfl⟩ ?_
    intro i r hr
    obtain ⟨ch, rel⟩ := r
    simp only [] at hr ⊢
    split <;> exact hr

/-- A fresh channel stages nothing. -/
theorem stagedReliableInv_default : StagedReliableInv ({} : Channel) := by
  simp [StagedReliableInv]

/-- The staging invariant reads only the staged map and the frontier. -/
theorem stagedReliableInv_of_same {c d : Channel} (hs : d.stagedReliable = c.stagedReliable)
    (hf : d.incomingReliableSequenceNumber = c.incomingReliableSequenceNumber)
    (h : StagedReliableInv c) : StagedReliableInv d := by
  intro k e he
  rw [hs] at he
  obtain ⟨h1, h2, h3⟩ := h k e he
  exact ⟨h1, by rw [isReliableAhead_congr hf]; exact h2, h3⟩

/-- The channel's reliable receive path keeps the staging invariant. -/
theorem receiveReliableAndRelease_stagedReliableInv {c : Channel} (h : StagedReliableInv c)
    (seq : UInt16) (span : Nat) (packet : Packet) : StagedReliableInv (receiveReliableAndRelease c seq span packet).1 := by
  have h' := receiveReliableSpan_stagedReliableInv h seq span packet
  unfold receiveReliableAndRelease
  dsimp only
  generalize receiveReliableSpan c seq span packet = r at h' ⊢
  obtain ⟨c', dels⟩ := r
  dsimp only at h' ⊢
  split
  · exact h'
  · exact stagedReliableInv_of_same (releaseStagedUnreliable_reliable c' _ _).1
      (releaseStagedUnreliable_reliable c' _ _).2 h'

/-- Unreliable receives never touch reliable staging. -/
theorem receiveUnreliable_stagedReliableInv {c : Channel} (h : StagedReliableInv c)
    (reliableSeq seq : UInt16) (packet : Packet) : StagedReliableInv (receiveUnreliable c reliableSeq seq packet).1 := by
  unfold receiveUnreliable
  repeat' split
  all_goals exact h

/-! ## The staging bound, per peer

The writers of `Peer.channels`: `Peer.receiveOnChannel` (every receive),
`Peer.send`, `Peer.removeSentReliableCommand`, `Host.packOutgoingCommands`,
the VERIFY_CONNECT handler (`take`), new connections (`replicate {}`) and
`Peer.reset`. Each keeps `PeerStagedInv`. -/

private theorem mem_set_or {α} {xs : Array α} {i : Nat} {h : i < xs.size} {v x : α}
    (hx : x ∈ xs.set i v h) : x ∈ xs ∨ x = v := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [Array.getElem_set]
  split
  · exact .inr rfl
  · exact .inl (Array.getElem_mem _)

private theorem mem_setIfInBounds_or {α} {xs : Array α} {i : Nat} {v x : α}
    (hx : x ∈ xs.setIfInBounds i v) : x ∈ xs ∨ x = v := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  have hj' : j < xs.size := by simpa using hj
  rw [Array.getElem_setIfInBounds hj']
  split
  · exact .inr rfl
  · exact .inl (Array.getElem_mem (by simpa using hj))

private theorem mem_modify_or {α} {xs : Array α} {i : Nat} {f : α → α} {x : α}
    (hx : x ∈ xs.modify i f) : x ∈ xs ∨ ∃ y ∈ xs, x = f y := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [Array.getElem_modify]
  split
  · next he => subst he; exact .inr ⟨_, Array.getElem_mem (by simpa using hj), rfl⟩
  · exact .inl (Array.getElem_mem _)

/-- Sender-side window accounting never touches reliable staging. -/
theorem acquireReliableWindow_stagedReliableInv {c : Channel} (h : StagedReliableInv c) (seq : UInt16) :
    StagedReliableInv (c.acquireReliableWindow seq) :=
  stagedReliableInv_of_same rfl rfl h

theorem releaseReliableWindow_stagedReliableInv {c : Channel} (h : StagedReliableInv c) (seq : UInt16) :
    StagedReliableInv (c.releaseReliableWindow seq) := by
  unfold releaseReliableWindow
  dsimp only
  split
  · exact h
  · exact stagedReliableInv_of_same rfl rfl h

/-- Every channel of the peer keeps the staging invariant. -/
def PeerStagedInv (p : Peer) : Prop := ∀ ch ∈ p.channels, StagedReliableInv ch

theorem peerStagedInv_of_channels {p q : Peer} (hc : q.channels = p.channels) (h : PeerStagedInv p) :
    PeerStagedInv q := fun ch hch => h ch (hc ▸ hch)

/-- The channels of a new connection (`Host.connect`, incoming CONNECT). -/
theorem peerStagedInv_replicate (n : Nat) : ∀ ch ∈ Array.replicate n ({} : Channel), StagedReliableInv ch := by
  intro ch hch
  rw [(Array.mem_replicate.mp hch).2]
  exact stagedReliableInv_default

/-- VERIFY_CONNECT keeps a prefix of the channels. -/
theorem peerStagedInv_take {xs : Array Channel} (h : ∀ ch ∈ xs, StagedReliableInv ch) (n : Nat) :
    ∀ ch ∈ xs.take n, StagedReliableInv ch := by
  intro ch hch
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hch
  simp only [Array.take_eq_extract, Array.getElem_extract, Nat.zero_add]
  exact h _ (Array.getElem_mem (by simp at hk; omega))

theorem peerStagedInv_reset (p : Peer) : PeerStagedInv p.reset := by
  intro ch hch
  simp [Peer.reset] at hch

theorem pruneAssemblers_channels (p : Peer) (channelId : UInt8) :
    (p.pruneAssemblers channelId).channels = p.channels := by
  unfold Peer.pruneAssemblers
  split
  · split <;> rfl
  · rfl

/-- A receive step that keeps the invariant keeps it for the whole peer. -/
theorem receiveOnChannel_peerStagedInv {p : Peer} (h : PeerStagedInv p) (channelId : UInt8)
    (receive : Channel → Channel × Array Packet)
    (hr : ∀ c, StagedReliableInv c → StagedReliableInv (receive c).1) :
    PeerStagedInv (p.receiveOnChannel channelId receive).1 := by
  by_cases hlt : channelId.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ hlt]
    intro ch hch
    simp only [pruneAssemblers_channels] at hch
    rcases mem_set_or hch with hch | rfl
    · exact h ch hch
    · exact hr _ (h _ (Array.getElem_mem hlt))
  · rw [receiveOnChannel_out _ _ _ hlt]; exact h

theorem handleData_peerStagedInv {p : Peer} (h : PeerStagedInv p) (cmd : Protocol.Command) :
    PeerStagedInv (p.handleData cmd).1 := by
  unfold Peer.handleData
  split
  · exact receiveOnChannel_peerStagedInv h _ _ fun c hc => receiveReliableAndRelease_stagedReliableInv hc _ _ _
  · exact receiveOnChannel_peerStagedInv h _ _ fun c hc => receiveUnreliable_stagedReliableInv hc _ _ _
  · split
    · exact peerStagedInv_of_channels rfl h
    · exact h
  · exact h

theorem handleFragment_peerStagedInv {p : Peer} (h : PeerStagedInv p) (channelId : UInt8)
    (reliableSeq : UInt16) (params : Protocol.FragmentParams) (unreliable : Bool) :
    PeerStagedInv (p.handleFragment channelId reliableSeq params unreliable).1 := by
  -- only the channel delivery touches the channels
  have hfa : ∀ ys, PeerStagedInv { p with fragmentAssemblers := ys } := fun _ => peerStagedInv_of_channels rfl h
  unfold Peer.handleFragment
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
        · refine receiveOnChannel_peerStagedInv (hfa _) _ _ fun c hc => ?_
          split
          · exact receiveUnreliable_stagedReliableInv hc _ _ _
          · exact receiveReliableAndRelease_stagedReliableInv hc _ _ _
        · exact hfa _
    · exact hfa _

theorem removeSentReliableCommand_peerStagedInv {p : Peer} (h : PeerStagedInv p) (channelId : UInt8)
    (seq : UInt16) : PeerStagedInv (p.removeSentReliableCommand channelId seq).1 := by
  unfold Peer.removeSentReliableCommand
  dsimp only
  have released : ∀ ch ∈ p.channels.modify channelId.toNat (·.releaseReliableWindow seq), StagedReliableInv ch := by
    intro ch hch
    rcases mem_modify_or hch with hch | ⟨c, hc, rfl⟩
    · exact h ch hch
    · exact releaseReliableWindow_stagedReliableInv (h c hc) seq
  split
  · exact released
  · split
    · split
      · exact h
      · exact released
    · exact h

theorem queueOutgoingCommand_channels (p : Peer) (cmd : OutgoingCommand) :
    (p.queueOutgoingCommand cmd).channels = p.channels := rfl

theorem fragmentCommands_stagedReliableInv {c : Channel} (h : StagedReliableInv c) (channelId : UInt8)
    (packet : Packet) (fragmentLength fragmentCount : Nat) :
    StagedReliableInv (Peer.fragmentCommands c channelId packet fragmentLength fragmentCount).1 := by
  unfold Peer.fragmentCommands
  dsimp only
  split <;> exact stagedReliableInv_of_same rfl rfl h

theorem packetCommand_stagedReliableInv (p : Peer) {c : Channel} (h : StagedReliableInv c)
    (channelId : UInt8) (packet : Packet) :
    StagedReliableInv (p.packetCommand c channelId packet).2.1 := by
  unfold Peer.packetCommand
  dsimp only
  split <;> (try split) <;> exact stagedReliableInv_of_same rfl rfl h

theorem foldl_queueOutgoingCommand_channels (q : Peer) (xs : Array OutgoingCommand) :
    (xs.foldl Peer.queueOutgoingCommand q).channels = q.channels :=
  Array.foldl_induction (motive := fun _ (r : Peer) => r.channels = q.channels) rfl
    (fun _ _ h => h)

theorem setIfInBounds_stagedReliableInv {xs : Array Channel} (h : ∀ ch ∈ xs, StagedReliableInv ch)
    (i : Nat) {c : Channel} (hc : StagedReliableInv c) :
    ∀ ch ∈ xs.setIfInBounds i c, StagedReliableInv ch := by
  intro ch hch
  rcases mem_setIfInBounds_or hch with hch | rfl
  · exact h ch hch
  · exact hc

theorem packetCommand_channels (p : Peer) (c : Channel) (channelId : UInt8) (packet : Packet) :
    (p.packetCommand c channelId packet).1.channels = p.channels := by
  unfold Peer.packetCommand
  dsimp only
  split <;> (try split) <;> rfl

/-- Queuing a packet only renumbers the channel's outgoing side. -/
theorem enqueue_peerStagedInv {p : Peer} (h : PeerStagedInv p) (channelId : UInt8)
    (packet : Packet) (hasChecksum : Bool) : PeerStagedInv (p.enqueue channelId packet hasChecksum) := by
  unfold Peer.enqueue
  split
  · exact h
  · next channel hget =>
    have hmem := Array.mem_of_getElem? hget
    dsimp only
    split
    all_goals
      intro ch hch
      simp only [foldl_queueOutgoingCommand_channels, queueOutgoingCommand_channels,
        packetCommand_channels] at hch
      refine setIfInBounds_stagedReliableInv h _ ?_ ch hch
      first
        | exact fragmentCommands_stagedReliableInv (h _ hmem) _ _ _ _
        | exact packetCommand_stagedReliableInv _ (h _ hmem) _ _

theorem send_peerStagedInv {p p' : Peer} (h : PeerStagedInv p) {channelId : UInt8} {packet : Packet}
    {hasChecksum : Bool} (hs : p.send channelId packet hasChecksum = .ok p') : PeerStagedInv p' := by
  unfold Peer.send at hs
  split at hs
  · cases hs
  · cases hs
    exact enqueue_peerStagedInv h _ _ _

theorem nextDatagram_channels (st : Host.PackState) : st.nextDatagram.channels = st.channels := by
  unfold Host.PackState.nextDatagram; split <;> rfl

theorem packAck_channels (mtu : UInt32) (st : Host.PackState) (ack : Acknowledgement) :
    (Host.PackState.packAck mtu st ack).channels = st.channels := by
  unfold Host.PackState.packAck
  dsimp only
  (repeat' split) <;> simp [Host.PackState.pack, nextDatagram_channels]

theorem packUnreliable_channels (p : Peer) (st : Host.PackState) (cmd : Protocol.Command) :
    (st.packUnreliable p cmd).channels = st.channels := by
  unfold Host.PackState.packUnreliable
  split
  · rfl
  · dsimp only
    split <;> rfl

theorem packCommand_stagedReliableInv (p : Peer) (now : UInt32) (st : Host.PackState)
    (outCmd : OutgoingCommand) (h : ∀ ch ∈ st.channels, StagedReliableInv ch) :
    ∀ ch ∈ (st.packCommand p now outCmd).channels, StagedReliableInv ch := by
  unfold Host.PackState.packCommand
  dsimp only
  -- a new datagram keeps the channels
  have h' : ∀ ch ∈ (if st.fits p.mtu outCmd.command then st else st.nextDatagram).channels,
      StagedReliableInv ch := by
    split
    · exact h
    · rw [nextDatagram_channels]; exact h
  generalize (if st.fits p.mtu outCmd.command then st else st.nextDatagram) = st' at h' ⊢
  repeat' split
  all_goals first
    | exact h
    | exact h'
    | (rw [packUnreliable_channels]; exact h')
    | (intro ch hch
       simp only at hch
       rcases mem_modify_or hch with hch | ⟨c, hc, rfl⟩
       · exact h' ch hch
       · exact acquireReliableWindow_stagedReliableInv (h' c hc) _)

/-- Packing a datagram only occupies sender-side windows. -/
theorem packOutgoingCommands_peerStagedInv {p : Peer} (h : PeerStagedInv p) (now : UInt32) (hc : Bool) :
    PeerStagedInv (Host.packOutgoingCommands p now hc).1 := by
  unfold Host.packOutgoingCommands
  intro ch hch
  simp only at hch
  refine Array.foldl_induction (motive := fun _ (st : Host.PackState) => ∀ ch ∈ st.channels, StagedReliableInv ch)
    ?_ (fun _ st hst => packCommand_stagedReliableInv p now st _ hst) ch hch
  refine Array.foldl_induction (motive := fun _ (st : Host.PackState) => ∀ ch ∈ st.channels, StagedReliableInv ch)
    ?_ (fun _ st hst => ?_)
  · exact h
  · rw [packAck_channels]
    exact hst

/-- The per-peer staging bound. -/
theorem peerStagedInv_size {p : Peer} (h : PeerStagedInv p) :
    ∀ ch ∈ p.channels,
      ch.stagedReliable.size ≤ (Constants.freeReliableWindows - 1) * Constants.reliableWindowSize :=
  fun ch hch => stagedReliableInv_size (h ch hch)

/-! ## Every assembler, per peer

The writers of `Peer.fragmentAssemblers` are `Peer.handleFragment` and
`Peer.receiveOnChannel` (pruning); `Peer.reset` and `Peer.resetQueues`
clear it. -/

open Peer FragmentAssembler

/-- `addFragment` keeps the set's shape. -/
theorem addFragment_shape {a a' : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {r : Option ByteArray} (h : a.addFragment n off d = .ok (a', r)) :
    a'.totalLength = a.totalLength ∧ a'.fragmentCount = a.fragmentCount := by
  unfold FragmentAssembler.addFragment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl⟩

/-- `init` builds the set it was asked for. -/
theorem init_shape {ssn : UInt16} {tl fc m : Nat} {a : FragmentAssembler}
    (h : FragmentAssembler.init ssn tl fc m = .ok a) : a.totalLength = tl ∧ a.fragmentCount = fc := by
  unfold FragmentAssembler.init at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl⟩

/-- One assembler: the reassembly invariant, and the allocation bounds its
creation enforced. -/
def AssemblerOk (a : FragmentAssembler) : Prop :=
  Inv a ∧ a.totalLength ≤ Constants.maximumPacketSize ∧
    a.fragmentCount ≤ Constants.maximumReceivedFragmentCount

theorem addFragment_ok {a a' : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {r : Option ByteArray} (ha : AssemblerOk a) (h : a.addFragment n off d = .ok (a', r)) :
    AssemblerOk a' := by
  obtain ⟨ht, hf⟩ := addFragment_shape h
  exact ⟨addFragment_inv ha.1 h, ht ▸ ha.2.1, hf ▸ ha.2.2⟩

/-- Making room only removes assemblers. -/
theorem assemblerRoom_sub {xs room : Array FragmentAssembler} (h : assemblerRoom xs = some room) :
    ∀ a ∈ room, a ∈ xs := by
  unfold assemblerRoom at h
  split at h
  · cases h; exact fun _ h => h
  · split at h
    · cases h; exact fun _ h => Array.mem_of_mem_eraseIdx h
    · cases h

/-- Absorbing a fragment keeps every assembler well formed. -/
theorem absorbFragment_ok {xs : Array FragmentAssembler} (hxs : ∀ a ∈ xs, AssemblerOk a)
    (origin : FragmentOrigin) (params : Protocol.FragmentParams) (held : Unit → Nat) (next : Bool) :
    ∀ a ∈ (absorbFragment xs origin params held next).1, AssemblerOk a := by
  unfold absorbFragment
  split
  · exact hxs
  · split
    · exact hxs
    · next hcount =>
      split
      · exact hxs
      · next room hroom =>
        split
        · exact hxs
        split
        · exact hxs
        split
        · exact hxs
        split
        · next newAsm hinit =>
          have hnew : AssemblerOk { newAsm with origin } := by
            obtain ⟨-, htl, -⟩ := init_bounds hinit
            obtain ⟨ht, hf⟩ := init_shape hinit
            have hi := init_inv hinit
            refine ⟨hi, ht ▸ htl, ?_⟩
            show newAsm.fragmentCount ≤ _
            rw [hf]
            omega
          intro a ha
          rcases Array.mem_push.mp ha with ha | rfl
          · exact hxs a (assemblerRoom_sub hroom a ha)
          · exact hnew
        · exact hxs

/-- The peer's assemblers: within the cap, each one well formed. -/
def AssemblersOk (p : Peer) : Prop :=
  p.fragmentAssemblers.size ≤ Constants.maximumFragmentAssemblers ∧
    ∀ a ∈ p.fragmentAssemblers, AssemblerOk a

theorem pruneAssemblers_ok {p : Peer} (h : ∀ a ∈ p.fragmentAssemblers, AssemblerOk a) (channelId : UInt8) :
    ∀ a ∈ (p.pruneAssemblers channelId).fragmentAssemblers, AssemblerOk a := by
  unfold pruneAssemblers
  split
  · split
    · exact h
    · intro a ha
      exact h a (Array.mem_filter.mp ha).1
  · exact h

theorem receiveOnChannel_ok {p : Peer} (h : ∀ a ∈ p.fragmentAssemblers, AssemblerOk a) (channelId : UInt8)
    (receive : Channel → Channel × Array Packet) :
    ∀ a ∈ (p.receiveOnChannel channelId receive).1.fragmentAssemblers, AssemblerOk a := by
  by_cases hc : channelId.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ hc]; refine pruneAssemblers_ok ?_ _; exact h
  · rw [receiveOnChannel_out _ _ _ hc]; exact h

theorem handleFragment_ok {p : Peer} (h : ∀ a ∈ p.fragmentAssemblers, AssemblerOk a) (channelId : UInt8)
    (reliableSeq : UInt16) (params : Protocol.FragmentParams) (unreliable : Bool) :
    ∀ a ∈ (handleFragment p channelId reliableSeq params unreliable).1.fragmentAssemblers, AssemblerOk a := by
  have hxs := fun held next => absorbFragment_ok h (fragmentOrigin channelId reliableSeq unreliable) params held next
  refine handleFragment_assemblers p channelId reliableSeq params unreliable
    (fun ys => ∀ a ∈ ys, AssemblerOk a) h hxs ?_ ?_ ?_
  · intro held next i hi w r _ hadd a ha
    rcases Array.mem_or_eq_of_mem_set (w := hi) ha with ha | rfl
    · exact hxs held next a ha
    · exact addFragment_ok (hxs held next _ (Array.getElem_mem hi)) hadd
  · intro held next i hi _ a ha; exact hxs held next a (Array.mem_of_mem_eraseIdx ha)
  · intro q hq c recv; exact receiveOnChannel_ok hq _ _

/-- The fragment path keeps the peer's assemblers within the cap and well
formed. -/
theorem handleFragment_assemblersOk {p : Peer} (h : AssemblersOk p) (channelId : UInt8)
    (reliableSeq : UInt16) (params : Protocol.FragmentParams) (unreliable : Bool) :
    AssemblersOk (handleFragment p channelId reliableSeq params unreliable).1 :=
  ⟨handleFragment_cap_preserved p channelId reliableSeq params unreliable h.1,
    handleFragment_ok h.2 channelId reliableSeq params unreliable⟩

/-- Channel delivery only prunes. -/
theorem receiveOnChannel_assemblersOk {p : Peer} (h : AssemblersOk p) (channelId : UInt8)
    (receive : Channel → Channel × Array Packet) :
    AssemblersOk (p.receiveOnChannel channelId receive).1 :=
  ⟨Nat.le_trans (receiveOnChannel_fragmentAssemblers_size _ _ _) h.1, receiveOnChannel_ok h.2 _ _⟩

theorem assemblersOk_reset (p : Peer) : AssemblersOk p.reset := by
  simp [AssemblersOk, Peer.reset, Constants.maximumFragmentAssemblers]

/-- Each assembler's memory: the fragments it stores, at most
`maximumReceivedFragmentCount` of them carrying at most `maximumPacketSize`
bytes between them, and a bitset of at most `maximumReceivedFragmentCount`
bytes. -/
theorem assemblerOk_footprint {a : FragmentAssembler} (h : AssemblerOk a) :
    (a.fragments.toList.map (·.2.size)).sum ≤ Constants.maximumPacketSize ∧
      a.fragments.size ≤ Constants.maximumReceivedFragmentCount ∧
      a.received.size ≤ Constants.maximumReceivedFragmentCount := by
  obtain ⟨⟨hr, hc, hf, hs, hb, -⟩, htl, hfc⟩ := h
  exact ⟨by omega, by omega, by omega⟩

/-! ## The waiting-data budget

ENet's `maximumWaitingData`: `absorbFragment` starts no set once the
assemblers hold that many bytes, so they never hold more than one packet
beyond it. Replacing a set's assembler in place keeps the count, because
the assemblers of one set agree on its length (`SetsAgree`: a set gets a
new assembler only when it has none). -/

theorem waitingBytes_eq (xs : Array FragmentAssembler) :
    waitingBytes xs = (xs.toList.map (·.totalLength)).sum := by
  unfold waitingBytes
  rw [← Array.foldl_toList]
  suffices ∀ (l : List FragmentAssembler) (n : Nat),
      l.foldl (fun n a => n + a.totalLength) n = n + (l.map (·.totalLength)).sum by
    simpa using this xs.toList 0
  intro l
  induction l with
  | nil => intro n; simp
  | cons a l ih => intro n; simp [ih]; omega

theorem waitingBytes_push (xs : Array FragmentAssembler) (a : FragmentAssembler) :
    waitingBytes (xs.push a) = waitingBytes xs + a.totalLength := by
  simp [waitingBytes_eq]

theorem waitingBytes_filter (xs : Array FragmentAssembler) (f : FragmentAssembler → Bool) :
    waitingBytes (xs.filter f) ≤ waitingBytes xs := by
  simp only [waitingBytes_eq, Array.toList_filter]
  induction xs.toList with
  | nil => simp
  | cons a l ih => by_cases h : f a <;> simp [h] <;> omega

/-- Assemblers of one set agree on its total length. -/
def SetsAgree (xs : Array FragmentAssembler) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, a.origin = b.origin → a.startSequenceNumber = b.startSequenceNumber →
    a.totalLength = b.totalLength

theorem SetsAgree.filter {xs : Array FragmentAssembler} (h : SetsAgree xs) (f : FragmentAssembler → Bool) :
    SetsAgree (xs.filter f) := fun a ha b hb =>
  h a (Array.mem_of_mem_filter ha) b (Array.mem_of_mem_filter hb)

/-- The budget: what the assemblers hold stays below `maximumWaitingData`
plus one packet. -/
def WaitingOk (xs : Array FragmentAssembler) : Prop :=
  SetsAgree xs ∧ waitingBytes xs < Constants.maximumWaitingData + Constants.maximumPacketSize

theorem WaitingOk.filter {xs : Array FragmentAssembler} (h : WaitingOk xs) (f : FragmentAssembler → Bool) :
    WaitingOk (xs.filter f) :=
  ⟨h.1.filter f, Nat.lt_of_le_of_lt (waitingBytes_filter xs f) h.2⟩

theorem init_start {ssn : UInt16} {tl fc m : Nat} {a : FragmentAssembler}
    (h : FragmentAssembler.init ssn tl fc m = .ok a) : a.startSequenceNumber = ssn := by
  unfold FragmentAssembler.init at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals cases h
  all_goals rfl

theorem addFragment_key {a a' : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {r : Option ByteArray} (h : a.addFragment n off d = .ok (a', r)) :
    a'.origin = a.origin ∧ a'.startSequenceNumber = a.startSequenceNumber ∧ a'.totalLength = a.totalLength := by
  unfold FragmentAssembler.addFragment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals cases h
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- Absorbing a fragment keeps the budget. -/
theorem absorbFragment_waiting {xs : Array FragmentAssembler} (hxs : WaitingOk xs)
    (origin : FragmentOrigin) (params : Protocol.FragmentParams) (held : Unit → Nat) (next : Bool) :
    WaitingOk (absorbFragment xs origin params held next).1 := by
  unfold absorbFragment
  split
  · exact hxs
  · next hfind =>
    split
    · exact hxs
    · split
      · exact hxs
      · next room hroom =>
        split
        · exact hxs
        · next hbudget =>
          split
          · exact hxs
          split
          · exact hxs
          split
          · next newAsm hinit =>
            have htl := (init_bounds hinit).2.1
            have hts := (init_shape hinit).1
            have hstart := init_start hinit
            have hnone : ∀ b ∈ xs, ¬(b.origin = origin ∧ b.startSequenceNumber = params.startSequenceNumber) := by
              intro b hb hk
              have := Array.findFinIdx?_eq_none_iff.mp hfind b hb
              simp [hk] at this
            refine ⟨?_, ?_⟩
            · intro a ha b hb ho hs
              rcases Array.mem_push.mp ha with ha | rfl <;> rcases Array.mem_push.mp hb with hb | rfl
              · exact hxs.1 a (assemblerRoom_sub hroom a ha) b (assemblerRoom_sub hroom b hb) ho hs
              · exact absurd ⟨ho, hs.trans hstart⟩ (hnone a (assemblerRoom_sub hroom a ha))
              · exact absurd ⟨ho.symm, hs.symm.trans hstart⟩ (hnone b (assemblerRoom_sub hroom b hb))
              · rfl
            · rw [waitingBytes_push]
              show waitingBytes room + newAsm.totalLength < _
              omega
          · exact hxs

theorem sum_le_of_sublist {l₁ l₂ : List Nat} (h : l₁.Sublist l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons _ _ ih => simp; omega
  | cons_cons _ _ ih => simp; omega

/-- Replacing an assembler by one of its set and length keeps the budget. -/
theorem WaitingOk.set {xs : Array FragmentAssembler} (h : WaitingOk xs) (i : Nat) (hi : i < xs.size)
    (w : FragmentAssembler) (ho : w.origin = xs[i].origin) (hs : w.startSequenceNumber = xs[i].startSequenceNumber)
    (ht : w.totalLength = xs[i].totalLength) : WaitingOk (xs.set i w hi) := by
  have hx : xs[i] ∈ xs := Array.getElem_mem hi
  refine ⟨fun a ha b hb hao has => ?_, ?_⟩
  · have ha' := Array.mem_or_eq_of_mem_set (w := hi) ha
    have hb' := Array.mem_or_eq_of_mem_set (w := hi) hb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact h.1 a ha' b hb' hao has
    · subst hb'; rw [ht]; exact h.1 a ha' _ hx (hao.trans ho) (has.trans hs)
    · subst ha'; rw [ht]; exact h.1 _ hx b hb' (ho.symm.trans hao) (hs.symm.trans has)
    · subst ha'; subst hb'; rfl
  · have : waitingBytes (xs.set i w hi) = waitingBytes xs := by
      simp only [waitingBytes_eq, Array.toList_set, List.map_set, ht]
      have hl : i < (xs.toList.map (·.totalLength)).length := by simpa using hi
      have : xs[i].totalLength = (xs.toList.map (·.totalLength))[i]'hl := by simp
      rw [this, List.set_getElem_self]
    rw [this]; exact h.2

theorem WaitingOk.eraseIdx {xs : Array FragmentAssembler} (h : WaitingOk xs) (i : Nat) (hi : i < xs.size) :
    WaitingOk (xs.eraseIdx i hi) := by
  refine ⟨fun a ha b hb => h.1 a (Array.mem_of_mem_eraseIdx ha) b (Array.mem_of_mem_eraseIdx hb), ?_⟩
  have : waitingBytes (xs.eraseIdx i hi) ≤ waitingBytes xs := by
    simp only [waitingBytes_eq, Array.toList_eraseIdx]
    exact sum_le_of_sublist ((List.eraseIdx_sublist _ _).map _)
  exact Nat.lt_of_le_of_lt this h.2

theorem pruneAssemblers_waiting {p : Peer} (h : WaitingOk p.fragmentAssemblers) (channelId : UInt8) :
    WaitingOk (p.pruneAssemblers channelId).fragmentAssemblers := by
  unfold pruneAssemblers
  split
  · split
    · exact h
    · exact h.filter _
  · exact h

theorem receiveOnChannel_waiting {p : Peer} (h : WaitingOk p.fragmentAssemblers) (channelId : UInt8)
    (receive : Channel → Channel × Array Packet) :
    WaitingOk (p.receiveOnChannel channelId receive).1.fragmentAssemblers := by
  by_cases hc : channelId.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ hc]; refine pruneAssemblers_waiting ?_ _; exact h
  · rw [receiveOnChannel_out _ _ _ hc]; exact h

/-- **The fragment path keeps the waiting-data budget.** -/
theorem handleFragment_waiting {p : Peer} (h : WaitingOk p.fragmentAssemblers) (channelId : UInt8)
    (reliableSeq : UInt16) (params : Protocol.FragmentParams) (unreliable : Bool) :
    WaitingOk (handleFragment p channelId reliableSeq params unreliable).1.fragmentAssemblers := by
  have hxs := fun held next => absorbFragment_waiting h (fragmentOrigin channelId reliableSeq unreliable) params held next
  refine handleFragment_assemblers p channelId reliableSeq params unreliable WaitingOk h hxs ?_ ?_ ?_
  · intro held next i hi w r _ hadd
    obtain ⟨ko, ks, kt⟩ := addFragment_key hadd
    exact (hxs held next).set i hi w ko ks kt
  · intro held next i hi _; exact (hxs held next).eraseIdx i hi
  · intro q hq c recv; exact receiveOnChannel_waiting hq _ _

theorem waitingOk_empty : WaitingOk #[] :=
  ⟨fun a ha => by simp at ha, by simp [waitingBytes, Constants.maximumWaitingData, Constants.maximumPacketSize]⟩

theorem waitingOk_reset (p : Peer) : WaitingOk p.reset.fragmentAssemblers := waitingOk_empty

theorem waitingOk_resetQueues (p : Peer) : WaitingOk p.resetQueues.fragmentAssemblers := waitingOk_empty

/-- The bytes a peer's assemblers can be made to hold: under 64 MB. -/
theorem waitingOk_footprint {xs : Array FragmentAssembler} (h : WaitingOk xs) :
    waitingBytes xs < Constants.maximumWaitingData + Constants.maximumPacketSize := h.2

end Lenet.Proofs
