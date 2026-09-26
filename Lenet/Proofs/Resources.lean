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
   (`addFragment_size_preserved`). Worst-case attacker-triggered footprint
   per peer: `cap × (maximumMtu * 1024 + maximumReceivedFragmentCount)` -
   a constant, not a function of attack duration. (An array-level
   all-elements-`Inv` preservation theorem is deferred; it is a mem-map
   composition of the elementwise lemmas proven here and in
   `Proofs/Reassembly.lean`.)
2. **Staged reliable packets** (`Channel.stagedReliable`): at most
   `(freeReliableWindows - 1) * reliableWindowSize` per channel
   (`stagedReliableInv_size`), whatever the sender does. The receive-window
   gate drops out-of-window seqs, the duplicate check keeps keys distinct,
   and an in-order delivery drops the entries its span jumped over, so
   staged keys stay distinct and inside the window
   (`StagedReliableInv`, kept by every receive:
   `receiveReliableAndRelease_stagedReliableInv`,
   `receiveUnreliable_stagedReliableInv`). The replay corpus asserts the
   bound too.
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

end Lenet.Proofs
