import Lenet.Constants
import Lenet.Host
import Lenet.Channel
import Lenet.Proofs.Reassembly
import Lenet.Proofs.Channel

/-!
# Resource-safety proofs

Robustness against hostile input (deliberately stricter than
ENet, whose pending-assembler growth is bounded only by its window span).
The attacker-controlled memory surfaces and their bounds:

1. **Fragment assemblers** (`Peer.fragmentAssemblers`): capped at
   `maximumFragmentAssemblers` concurrent assemblies
   (`handleFragment_cap_preserved`); every assembler is created by
   `FragmentAssembler.init`, whose validation pins the allocation
   (`init_bounds`: buffer = totalLength ≤ maxPacketSize, bitset =
   fragmentCount; the create-guard additionally bounds fragmentCount by
   `maximumReceivedFragmentCount`), and `addFragment` never resizes
   (`addFragment_size_preserved`). Over the whole array: every assembler
   keeps `Proofs.Inv` (Proofs/Reassembly.lean) and those bounds, and the cap holds
   (`AssemblersOk`, `handleFragment_assemblersOk`,
   `assemblerOk_footprint`). Worst-case attacker-triggered footprint per
   peer: `cap × (maximumPacketSize + maximumReceivedFragmentCount)` - a
   constant, not a function of attack duration.
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
`absorbFragment` + `assemblerArrayAfterDeliver`) and
`Peer.receiveOnChannel`, which only prunes (`Peer.reset` clears the
field), so these theorems cover every growth path; the replay corpus
asserts the bounds after every service step of every scenario.
-/

namespace Lenet.Proofs

open Peer FragmentAssembler

/-! ## Per-assembler allocation bounds -/

/-- A successfully created assembler allocates exactly `totalLength` buffer
bytes and a `fragmentCount`-slot bitset, both validated by `init`
(the throws pin `totalLength ≤ maxPacketSize` and
`fragmentCount ≤ maximumFragmentCount`). -/
theorem init_bounds {ssn : UInt16} {tl fc maxPacketSize : Nat} {a : FragmentAssembler}
    (h : FragmentAssembler.init ssn tl fc maxPacketSize = .ok a) :
    a.buffer.size = tl ∧ tl ≤ maxPacketSize ∧ fc ≤ Constants.maximumFragmentCount := by
  unfold FragmentAssembler.init at h
  by_cases hc : fc = 0
  · simp [hc, Except.throw_eq', Except.bind_error'] at h
  by_cases hc2 : fc > Constants.maximumFragmentCount
  · simp [hc, hc2, Except.throw_eq', Except.bind_error'] at h
  by_cases hc3 : tl > maxPacketSize
  · simp [hc, hc2, hc3, Except.throw_eq', Except.bind_error'] at h
  by_cases hc4 : tl < fc
  · simp [hc, hc2, hc3, hc4, Except.throw_eq', Except.map_error'] at h
  have hc' : (fc == 0) = false := by simp [hc]
  have hc2' : (fc > Constants.maximumFragmentCount) = false := by simp [hc2]
  have hc3' : (tl > maxPacketSize) = false := by simp [hc3]
  have hc4' : (tl < fc) = false := by simp [hc4]
  simp only [hc', hc2', hc3', hc4', Bool.false_eq_true, reduceIte, Except.throw_eq',
    Except.pure_eq'] at h
  simp at h
  cases h
  refine ⟨?_, ?_, ?_⟩
  · simp [ByteArray.size]
  · omega
  · omega

/-! ## Size preservation through `addFragment` -/

/-- `addFragment` never resizes the bitset or the buffer. -/
theorem addFragment_size_preserved {a a' : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {r : Option ByteArray} (h : a.addFragment n off d = .ok (a', r)) :
    a'.received.size = a.received.size ∧ a'.buffer.size = a.buffer.size := by
  by_cases h1 : a.fragmentCount ≤ n
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = true from by simp [h1], reduceIte,
      Except.throw_eq', Except.bind_error'] at h
    cases h
  by_cases h2 : a.totalLength ≤ off
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = true from by simp [h2], reduceIte,
      Except.throw_eq', Except.bind_error'] at h
    cases h
  by_cases h3 : a.totalLength < off + d.size
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = false from by simp [h2],
      show (a.totalLength < off + d.size) = true from by simp [h3], reduceIte,
      Except.throw_eq', Except.bind_error'] at h
    cases h
  -- range checks passed; case on the bitset slot
  simp only [FragmentAssembler.addFragment,
    show (a.fragmentCount ≤ n) = false from by simp [h1],
    show (a.totalLength ≤ off) = false from by simp [h2],
    show (a.totalLength < off + d.size) = false from by simp [h3],
    Bool.false_eq_true, reduceIte] at h
  split at h
  · next hb => cases h
  · next hb =>
    -- duplicate: assembler returned unchanged
    cases h
    exact ⟨rfl, rfl⟩
  · next hb =>
    -- fresh slot: record it, copy the bytes
    split at h
    all_goals cases h
    all_goals
      refine ⟨?_, ?_⟩
      · simp
      · exact copyBytes_size _ _ _

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
    (params : Protocol.FragmentParams)
    (hcap : xs.size ≤ Constants.maximumFragmentAssemblers) :
    (absorbFragment xs origin params).1.size ≤ Constants.maximumFragmentAssemblers := by
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
        · simp only [Array.size_push]
          omega
        · exact hcap

/-- `assemblerArrayAfterDeliver` never grows the array. -/
theorem assemblerArrayAfterDeliver_size (xs : Array FragmentAssembler) (origin : FragmentOrigin)
    (params : Protocol.FragmentParams)
    (result : Option (Except CodecError (FragmentAssembler × Option ByteArray))) :
    (assemblerArrayAfterDeliver xs origin params result).size ≤ xs.size := by
  unfold assemblerArrayAfterDeliver
  split
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · rw [Array.size_map]
    exact Nat.le_refl _
  · exact Array.size_filter_le

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
  unfold receiveOnChannel
  split
  · exact pruneAssemblers_size _ _
  · exact Nat.le_refl _

/-- `handleFragment` never grows the assembler array beyond the cap: when the
gate passes, the array is `assemblerArrayAfterDeliver xs …` (then possibly
pruned by the channel delivery), which never exceeds
`xs = (absorbFragment ...).1`, itself capped by `absorbFragment_cap_preserved`;
when the gate fails the peer is returned unchanged. -/
theorem handleFragment_cap_preserved (p : Peer) (channelId : UInt8) (reliableSeq : UInt16)
    (params : Protocol.FragmentParams) (unreliable : Bool)
    (hcap : p.fragmentAssemblers.size ≤ Constants.maximumFragmentAssemblers) :
    (handleFragment p channelId reliableSeq params unreliable).1.fragmentAssemblers.size
      ≤ Constants.maximumFragmentAssemblers := by
  unfold handleFragment
  split
  · exact hcap
  by_cases hg : fragmentGateOk p channelId reliableSeq params unreliable = true
  · rw [if_neg (by simp [hg] : ¬((!fragmentGateOk p channelId reliableSeq params unreliable) = true))]
    -- gate passed: the array is `assemblerArrayAfterDeliver` of the absorbed array
    have hxs := absorbFragment_cap_preserved p.fragmentAssemblers
      (fragmentOrigin channelId reliableSeq unreliable) params hcap
    have hdel := fun result => Nat.le_trans
      (assemblerArrayAfterDeliver_size _ (fragmentOrigin channelId reliableSeq unreliable) params result) hxs
    simp only [] -- zeta the lets, iota-reduce the pair match
    split
    · exact Nat.le_trans (receiveOnChannel_fragmentAssemblers_size _ _ _) (hdel _)
    · exact hdel _
    · exact hdel _
  · rw [if_pos (by simp [hg] : ((!fragmentGateOk p channelId reliableSeq params unreliable) = true))]
    exact hcap

/-! ## Staged reliable packets -/

open Channel

/-- Draining delivers from the staged array; it never adds to it. -/
theorem drainContiguousLoop_size : ∀ (f : Nat) (cur : UInt16) (staged : Array StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat),
    (drainContiguousLoop cur staged del f adv).2.2.1.size ≤ staged.size := by
  intro f
  induction f with
  | zero => intro cur staged del adv; simp [drainContiguousLoop]
  | succ f ih =>
    intro cur staged del adv
    simp only [drainContiguousLoop]
    split
    · next idx _ =>
      split
      · next hidx =>
        have := ih ((cur + 1) + ((staged[idx]).span - 1).toUInt16) (staged.eraseIdx idx hidx)
          (del.push ((staged[idx]).span, (staged[idx]).packet)) (adv + (staged[idx]).span)
        rw [Array.size_eraseIdx] at this
        omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- One reliable receive stages at most one delivery. -/
theorem receiveReliableSpan_staged_le (c : Channel) (seq : UInt16) (span : Nat) (packet : Packet) :
    (receiveReliableSpan c seq span packet).1.stagedReliable.size ≤ c.stagedReliable.size + 1 := by
  unfold receiveReliableSpan
  split
  · simp
  · split
    · simp
    · split
      · have := drainContiguousLoop_size c.stagedReliable.size (seq + (span - 1).toUInt16)
          c.stagedReliable #[] 0
        simp only [drainContiguous]
        generalize drainContiguousLoop _ c.stagedReliable #[] c.stagedReliable.size 0 = r at this ⊢
        obtain ⟨_, _, rest, _⟩ := r
        simp only at this ⊢
        exact Nat.le_trans Array.size_filter_le (by omega)
      · simp only []
        split <;> simp

/-! ## The staging bound -/

/-- A sequence number the receive path admits lies fewer than
`(freeReliableWindows - 1) * reliableWindowSize` numbers past the frontier
(cyclically): the gate admits the frontier's window and the next six. -/
theorem isReliableAhead_offset (c : Channel) (s : UInt16) (h : c.isReliableAhead s = true) :
    (s - c.incomingReliableSequenceNumber).toNat
      < (Constants.freeReliableWindows - 1) * Constants.reliableWindowSize := by
  simp only [isReliableAhead, isIncomingReliableInWindow, Constants.reliableWindowSize,
    Constants.reliableWindows, Constants.freeReliableWindows, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at h ⊢
  obtain ⟨hw, -⟩ := h
  have hs := UInt16.toNat_lt s
  have hf := UInt16.toNat_lt c.incomingReliableSequenceNumber
  rw [UInt16.toNat_sub]
  split at hw
  · next hlt =>
    rw [UInt16.lt_iff_toNat_lt] at hlt
    simp at hw
    omega
  · next hlt =>
    rw [UInt16.lt_iff_toNat_lt] at hlt
    simp at hw
    omega

/-- `isReliableAhead` reads only the dispatch frontier. -/
theorem isReliableAhead_congr {c d : Channel}
    (h : c.incomingReliableSequenceNumber = d.incomingReliableSequenceNumber) (s : UInt16) :
    c.isReliableAhead s = d.isReliableAhead s := by
  simp [isReliableAhead, isIncomingReliableInWindow, h]

/-- The staging invariant: staged sequence numbers are distinct, and each
is still ahead of the frontier inside the receive window. -/
def StagedReliableInv (c : Channel) : Prop :=
  (c.stagedReliable.toList.map (·.seq)).Nodup ∧
    ∀ e ∈ c.stagedReliable, c.isReliableAhead e.seq = true

/-- The staging bound: distinct sequence numbers inside the window span
number at most the span. -/
theorem stagedReliableInv_size {c : Channel} (h : StagedReliableInv c) :
    c.stagedReliable.size ≤ (Constants.freeReliableWindows - 1) * Constants.reliableWindowSize := by
  obtain ⟨hnd, hahead⟩ := h
  let off (e : StagedReliable) : Nat := (e.seq - c.incomingReliableSequenceNumber).toNat
  have hnd' : (c.stagedReliable.toList.map off).Nodup := by
    rw [List.Nodup, List.pairwise_map] at hnd ⊢
    refine hnd.imp fun {a b} hab heq => hab ?_
    have : a.seq - c.incomingReliableSequenceNumber = b.seq - c.incomingReliableSequenceNumber :=
      UInt16.toNat_inj.mp heq
    rw [← UInt16.sub_add_cancel a.seq c.incomingReliableSequenceNumber, this,
      UInt16.sub_add_cancel]
  have hsub : c.stagedReliable.toList.map off
      ⊆ List.range ((Constants.freeReliableWindows - 1) * Constants.reliableWindowSize) := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
    exact List.mem_range.mpr (isReliableAhead_offset c e.seq (hahead e (Array.mem_toList_iff.mp he)))
  have := hnd'.length_le_of_subset hsub
  simpa using this

/-- What the drain leaves staged is a sublist of what was staged. -/
theorem drainContiguousLoop_sublist : ∀ (f : Nat) (cur : UInt16) (staged : Array StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat),
    (drainContiguousLoop cur staged del f adv).2.2.1.toList.Sublist staged.toList := by
  intro f
  induction f with
  | zero => intro cur staged del adv; simp [drainContiguousLoop]
  | succ f ih =>
    intro cur staged del adv
    simp only [drainContiguousLoop]
    split
    · next idx _ =>
      split
      · next hidx =>
        refine (ih _ _ _ _).trans ?_
        rw [Array.toList_eraseIdx]
        exact List.eraseIdx_sublist _ _
      · exact List.Sublist.refl _
    · exact List.Sublist.refl _

/-- Every reliable receive keeps the staging invariant: staging adds only an
admitted, new sequence number, and an in-order delivery keeps only the
entries still ahead of the new frontier. -/
theorem receiveReliableSpan_stagedReliableInv {c : Channel} (h : StagedReliableInv c)
    (seq : UInt16) (span : Nat) (packet : Packet) : StagedReliableInv (receiveReliableSpan c seq span packet).1 := by
  obtain ⟨hnd, hahead⟩ := h
  unfold receiveReliableSpan
  split
  · exact ⟨hnd, hahead⟩
  · next hwin =>
    split
    · exact ⟨hnd, hahead⟩
    · next hdup =>
      split
      · simp only [drainContiguous]
        have hsub := drainContiguousLoop_sublist c.stagedReliable.size (seq + (span - 1).toUInt16)
          c.stagedReliable #[] 0
        generalize drainContiguousLoop _ c.stagedReliable #[] c.stagedReliable.size 0 = r at hsub ⊢
        obtain ⟨newSeq, _, rest, _⟩ := r
        simp only at hsub ⊢
        refine ⟨?_, ?_⟩
        · rw [Array.toList_filter]
          exact hnd.sublist ((List.filter_sublist).map _ |>.trans (hsub.map _))
        · intro e he
          exact (Array.mem_filter.mp he).2
      · simp only []
        split
        · exact ⟨hnd, hahead⟩
        · next hany =>
          refine ⟨?_, ?_⟩
          · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
            refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
            intro a ha b hb
            simp only [List.mem_singleton] at hb
            subst hb
            intro heq
            subst heq
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
            exact hany (Array.any_eq_true'.mpr ⟨e, Array.mem_toList_iff.mp he, by simp⟩)
          · intro e he
            simp only [Array.mem_push] at he
            rcases he with he | rfl
            · exact hahead e he
            · show c.isReliableAhead seq = true
              simp only [Bool.not_eq_true'] at hwin
              simp only [beq_iff_eq] at hdup
              simp [isReliableAhead, hdup]
              simpa using hwin

/-- Releasing staged unreliable packets leaves reliable staging and the
frontier alone. -/
theorem releaseStagedUnreliable_reliable (c : Channel) :
    (releaseStagedUnreliable c).1.stagedReliable = c.stagedReliable ∧
      (releaseStagedUnreliable c).1.incomingReliableSequenceNumber = c.incomingReliableSequenceNumber := by
  unfold releaseStagedUnreliable
  split
  · exact ⟨rfl, rfl⟩
  · simp only []
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

/-- The channel's reliable receive path keeps the staging invariant. -/
theorem receiveReliableAndRelease_stagedReliableInv {c : Channel} (h : StagedReliableInv c)
    (seq : UInt16) (span : Nat) (packet : Packet) : StagedReliableInv (receiveReliableAndRelease c seq span packet).1 := by
  have h' := receiveReliableSpan_stagedReliableInv h seq span packet
  unfold receiveReliableAndRelease
  generalize receiveReliableSpan c seq span packet = r at h' ⊢
  obtain ⟨c', dels⟩ := r
  simp only [] at h' ⊢
  split
  · exact h'
  · obtain ⟨hs, hf⟩ := releaseStagedUnreliable_reliable c'
    obtain ⟨hnd, hahead⟩ := h'
    refine ⟨by simpa [hs] using hnd, fun e he => ?_⟩
    rw [isReliableAhead_congr hf]
    exact hahead e (hs ▸ he)

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

/-- The staging invariant reads only the staged array and the frontier. -/
theorem stagedReliableInv_of_same {c d : Channel} (hs : d.stagedReliable = c.stagedReliable)
    (hf : d.incomingReliableSequenceNumber = c.incomingReliableSequenceNumber)
    (h : StagedReliableInv c) : StagedReliableInv d := by
  obtain ⟨hnd, hahead⟩ := h
  refine ⟨hs ▸ hnd, fun e he => ?_⟩
  rw [isReliableAhead_congr hf]
  exact hahead e (hs ▸ he)

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
  unfold Peer.receiveOnChannel
  split
  · next hlt =>
    intro ch hch
    simp only [pruneAssemblers_channels] at hch
    rcases mem_set_or hch with hch | rfl
    · exact h ch hch
    · exact hr _ (h _ (Array.getElem_mem hlt))
  · exact h

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
  unfold Peer.handleFragment
  split
  · exact h
  split
  · exact h
  · dsimp only
    split
    · dsimp only
      refine receiveOnChannel_peerStagedInv ?_ _ _ fun c hc => ?_
      · exact h
      split
      · exact receiveUnreliable_stagedReliableInv hc _ _ _
      · exact receiveReliableAndRelease_stagedReliableInv hc _ _ _
    · exact peerStagedInv_of_channels rfl h
    · exact peerStagedInv_of_channels rfl h

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
        | exact fragmentCommands_stagedReliableInv (h _ hmem) ..
        | exact packetCommand_stagedReliableInv _ (h _ hmem) ..

theorem send_peerStagedInv {p p' : Peer} (h : PeerStagedInv p) {channelId : UInt8} {packet : Packet}
    {hasChecksum : Bool} (hs : p.send channelId packet hasChecksum = .ok p') : PeerStagedInv p' := by
  unfold Peer.send at hs
  split at hs
  · cases hs
  · cases hs
    exact enqueue_peerStagedInv h _ _ _

theorem packAck_channels (mtu : UInt32) (st : Host.PackState) (ack : Acknowledgement) :
    (Host.PackState.packAck mtu st ack).channels = st.channels := by
  unfold Host.PackState.packAck
  dsimp only
  split <;> rfl

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
  repeat' split
  all_goals first
    | exact h
    | (rw [packUnreliable_channels]; exact h)
    | (intro ch hch
       simp only at hch
       rcases mem_modify_or hch with hch | ⟨c, hc, rfl⟩
       · exact h ch hch
       · exact acquireReliableWindow_stagedReliableInv (h c hc) _)

/-- Packing a datagram only occupies sender-side windows. -/
theorem packOutgoingCommands_peerStagedInv {p : Peer} (h : PeerStagedInv p) (now : UInt32) :
    PeerStagedInv (Host.packOutgoingCommands p now).1 := by
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
`Peer.receiveOnChannel` (pruning); `Peer.reset` clears it. -/

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

/-- Absorbing a fragment keeps every assembler well formed, and hands back a
well-formed one to deliver to. -/
theorem absorbFragment_ok {xs : Array FragmentAssembler} (hxs : ∀ a ∈ xs, AssemblerOk a)
    (origin : FragmentOrigin) (params : Protocol.FragmentParams) :
    (∀ a ∈ (absorbFragment xs origin params).1, AssemblerOk a) ∧
      ∀ a, (absorbFragment xs origin params).2 = some a → AssemblerOk a := by
  unfold absorbFragment
  split
  · next asm hfind => exact ⟨hxs, fun a ha => by cases ha; exact hxs _ (Array.mem_of_find?_eq_some hfind)⟩
  · split
    · exact ⟨hxs, fun a ha => by cases ha⟩
    · next hcount =>
      split
      · exact ⟨hxs, fun a ha => by cases ha⟩
      · next room hroom =>
        split
        · exact ⟨hxs, fun a ha => by cases ha⟩
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
          refine ⟨fun a ha => ?_, fun a ha => by cases ha; exact hnew⟩
          rcases Array.mem_push.mp ha with ha | rfl
          · exact hxs a (assemblerRoom_sub hroom a ha)
          · exact hnew
        · exact ⟨hxs, fun a ha => by cases ha⟩

theorem assemblerArrayAfterDeliver_ok {xs : Array FragmentAssembler} (hxs : ∀ a ∈ xs, AssemblerOk a)
    (origin : FragmentOrigin) (params : Protocol.FragmentParams)
    {result : Option (Except CodecError (FragmentAssembler × Option ByteArray))}
    (hres : ∀ a' r, result = some (.ok (a', r)) → AssemblerOk a') :
    ∀ a ∈ assemblerArrayAfterDeliver xs origin params result, AssemblerOk a := by
  unfold assemblerArrayAfterDeliver
  split
  · exact hxs
  · exact hxs
  · next a' =>
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Array.mem_map.mp ha
    split
    · exact hres _ _ rfl
    · exact hxs b hb
  · intro a ha
    exact hxs a (Array.mem_filter.mp ha).1

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
  unfold receiveOnChannel
  split
  · split
    refine pruneAssemblers_ok ?_ _
    exact h
  · exact h

theorem handleFragment_ok {p : Peer} (h : ∀ a ∈ p.fragmentAssemblers, AssemblerOk a) (channelId : UInt8)
    (reliableSeq : UInt16) (params : Protocol.FragmentParams) (unreliable : Bool) :
    ∀ a ∈ (handleFragment p channelId reliableSeq params unreliable).1.fragmentAssemblers, AssemblerOk a := by
  unfold handleFragment
  split
  · exact h
  split
  · exact h
  · dsimp only
    obtain ⟨hxs, hasm⟩ := absorbFragment_ok h (fragmentOrigin channelId reliableSeq unreliable) params
    have hdel := assemblerArrayAfterDeliver_ok hxs (fragmentOrigin channelId reliableSeq unreliable) params
      (result := (absorbFragment p.fragmentAssemblers (fragmentOrigin channelId reliableSeq unreliable) params).2.bind
        fun asm =>
          if asm.totalLength != params.totalLength.toNat || asm.fragmentCount != params.fragmentCount.toNat then
            some (.error (.custom "fragment does not match its set"))
          else some (asm.addFragment params.fragmentNumber.toNat params.fragmentOffset.toNat params.data))
      (fun a' r hr => by
        cases hopt : (absorbFragment p.fragmentAssemblers (fragmentOrigin channelId reliableSeq unreliable) params).2 with
        | none => rw [hopt] at hr; cases hr
        | some asm =>
          rw [hopt] at hr
          simp only [Option.bind_some] at hr
          split at hr
          · cases hr
          · exact addFragment_ok (hasm asm hopt) (Option.some.inj hr))
    split
    · exact receiveOnChannel_ok hdel _ _
    · exact hdel
    · exact hdel

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

/-- Each assembler's memory: at most `maximumPacketSize` buffer bytes and
`maximumReceivedFragmentCount` bitset slots. -/
theorem assemblerOk_footprint {a : FragmentAssembler} (h : AssemblerOk a) :
    a.buffer.size ≤ Constants.maximumPacketSize ∧
      a.received.size ≤ Constants.maximumReceivedFragmentCount := by
  obtain ⟨⟨hr, hb, -⟩, htl, hfc⟩ := h
  exact ⟨hb ▸ htl, hr ▸ hfc⟩

end Lenet.Proofs
