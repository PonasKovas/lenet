import Lenet.Constants
import Lenet.Host
import Lenet.Channel
import Lenet.Proofs.Reassembly
import Lenet.Proofs.Channel

/-!
# Resource-safety proofs

Robustness against hostile input (DESIGN.md 1.5 - deliberately stricter than
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
   delivery only shrinks the staged array (`drainContiguousLoop_size`), and
   a non-delivery call adds at most one entry
   (`receiveReliable_staged_mono`). The full window-span bound is asserted
   in the replay corpus (test/Replay.lean) alongside the deferred Peer-skew
   formal proof.
3. **Acknowledgement queue**: production is coupled to the driver's pump
   rate (≤ 32 acks per received datagram) and the packing loop drains up to
   `maximumPacketCommands` per tick; growth beyond a well-behaved pump is
   the same exposure as ENet's - documented, not capped (capping drops ACKs
   and forces retransmissions for no robustness gain).

The mutator of `fragmentAssemblers` is `Peer.handleFragment` (via
`absorbFragment` + `assemblerArrayAfterDeliver`; `Peer.reset` clears the
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

/-- `absorbFragment` never grows the array beyond the cap. -/
theorem absorbFragment_cap_preserved (xs : Array FragmentAssembler)
    (params : Protocol.FragmentParams)
    (hcap : xs.size ≤ Constants.maximumFragmentAssemblers) :
    (absorbFragment xs params).1.size ≤ Constants.maximumFragmentAssemblers := by
  unfold absorbFragment
  split
  · next _ => exact hcap
  · next =>
    by_cases hguard : xs.size ≥ Constants.maximumFragmentAssemblers ∨
        params.fragmentCount.toNat > Constants.maximumReceivedFragmentCount
    · simp only [hguard, reduceIte]
      exact hcap
    · have hlt : xs.size < Constants.maximumFragmentAssemblers := by
        simp at hguard
        omega
      simp only [hguard, reduceIte]
      split
      · next newAsm _ =>
        have hproj : (xs.push newAsm, some newAsm).1.size = (xs.push newAsm).size := rfl
        have hpush : (xs.push newAsm).size = xs.size + 1 := Array.size_push newAsm
        omega
      · next _ => exact hcap

/-- `assemblerArrayAfterDeliver` never grows the array. -/
theorem assemblerArrayAfterDeliver_size (xs : Array FragmentAssembler)
    (params : Protocol.FragmentParams)
    (result : Option (Except CodecError (FragmentAssembler × Option ByteArray))) :
    (assemblerArrayAfterDeliver xs params result).size ≤ xs.size := by
  unfold assemblerArrayAfterDeliver
  split
  · next => exact Nat.le_refl _
  · next _ => exact Nat.le_refl _
  · next updatedAsm _ =>
    rw [Array.size_map]
    exact Nat.le_refl _
  · next _ _ =>
    exact Nat.le_trans (Array.size_filter_le
      (p := fun a : FragmentAssembler =>
        a.startSequenceNumber ≠ params.startSequenceNumber)) (Nat.le_refl _)

/-- `handleFragment` never grows the assembler array beyond the cap: both
match arms set `fragmentAssemblers := assemblerArrayAfterDeliver xs params
result`, which never exceeds `xs = (absorbFragment ...).1`, itself capped by
`absorbFragment_cap_preserved`. -/
theorem handleFragment_cap_preserved (p : Peer) (channelId : UInt8)
    (params : Protocol.FragmentParams) (unreliable : Bool)
    (hcap : p.fragmentAssemblers.size ≤ Constants.maximumFragmentAssemblers) :
    (handleFragment p channelId params unreliable).1.fragmentAssemblers.size
      ≤ Constants.maximumFragmentAssemblers := by
  unfold handleFragment
  split
  · next xs asm heq =>
    have hfst : (absorbFragment p.fragmentAssemblers params).1 = xs :=
      congrArg Prod.fst heq
    have hxs := absorbFragment_cap_preserved p.fragmentAssemblers params hcap
    rw [hfst] at hxs
    simp only [] -- zeta-reduce the lets
    -- both match arms set fragmentAssemblers := assemblerArrayAfterDeliver …
    split
    · next fullData _ =>
      -- completion arm: the delivery path's channel-if keeps `p'`'s array
      split
      · next _ _ =>
        show (assemblerArrayAfterDeliver xs params
          (Option.bind asm fun asm => asm.addFragment params.fragmentNumber.toNat
            params.fragmentOffset.toNat params.data)).size ≤ _
        have hd := assemblerArrayAfterDeliver_size xs params
          (Option.bind asm fun asm => asm.addFragment params.fragmentNumber.toNat
            params.fragmentOffset.toNat params.data)
        omega
      · next =>
        show (assemblerArrayAfterDeliver xs params
          (Option.bind asm fun asm => asm.addFragment params.fragmentNumber.toNat
            params.fragmentOffset.toNat params.data)).size ≤ _
        have hd := assemblerArrayAfterDeliver_size xs params
          (Option.bind asm fun asm => asm.addFragment params.fragmentNumber.toNat
            params.fragmentOffset.toNat params.data)
        omega
    · next =>
      show (assemblerArrayAfterDeliver xs params
        (Option.bind asm fun asm => asm.addFragment params.fragmentNumber.toNat
          params.fragmentOffset.toNat params.data)).size ≤ _
      have hd := assemblerArrayAfterDeliver_size xs params
        (Option.bind asm fun asm => asm.addFragment params.fragmentNumber.toNat
          params.fragmentOffset.toNat params.data)
      omega
end Lenet.Proofs
