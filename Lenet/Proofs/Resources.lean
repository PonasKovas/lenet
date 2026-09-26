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
2. **Staged reliable packets** (`Channel.stagedReliable`): the receive-window
   gate drops out-of-window seqs, the duplicate check keeps keys distinct,
   draining only shrinks the staged array (`drainContiguousLoop_size`), and
   one receive stages at most one entry (`receiveReliableSpan_staged_le`).
   The full window-span bound is asserted by the replay corpus
   (test/Replay.lean); proving it needs the sender-side window invariant
   (TODO.md).
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
        omega
      · simp only []
        split <;> simp

end Lenet.Proofs
