import Lenet.Constants
import Lenet.Reassembly
import Lenet.Proofs.Basic

/-!
# Reassembly safety proofs

The non-obvious content (see TODO.md Phase 2): the fragment assembler's
received-bitset and fragmentsRemaining counter must stay in correspondence -
`fragmentsRemaining + received.count = fragmentCount` - which is what makes
completion sound: the assembled buffer is dispatched only after every
validated fragment slot was written, and the `fragmentsRemaining - 1`
decrement never depends on Nat-saturation.
-/

namespace Lenet.Proofs

open FragmentAssembler

/-! ## Counting helpers -/

/-- A `false` slot bounds the true-count strictly below the size. -/
theorem countP_true_lt_of_false {xs : Array Bool} {i : Nat} (hi : i < xs.size)
    (hf : xs[i] = false) : xs.countP (fun b => b) < xs.size := by
  have hset : (xs.set i true hi).countP (fun b => b) = xs.countP (fun b => b) + 1 := by
    rw [Array.countP_set (p := fun b => b) hi]
    simp [hf]
  have hle : xs.countP (fun b => b) + 1 ≤ xs.size := by
    have hcl := Array.countP_le_size (p := (fun b => b)) (xs := xs.set i true hi)
    rw [hset] at hcl
    rw [Array.size_set (h := hi)] at hcl
    omega
  omega

/-- If every slot counts, every slot is `true`. -/
theorem countP_true_all {xs : Array Bool} (h : xs.countP (fun b => b) = xs.size) :
    ∀ (i : Nat) (hi : i < xs.size), xs[i]'hi = true := by
  intro i hi
  match hb : xs[i]'hi with
  | true => rfl
  | false =>
    have hf : xs[i] = false := hb
    have hlt := countP_true_lt_of_false hi hf
    rw [h] at hlt
    omega

/-! ## The assembler invariant -/

/-- Reachable-assembler invariant: one received-bit per fragment, a
totalLength-sized buffer, and `fragmentsRemaining` equal to the number of
not-yet-received fragments. -/
def Inv (a : FragmentAssembler) : Prop :=
  a.received.size = a.fragmentCount ∧
  a.buffer.size = a.totalLength ∧
  a.fragmentsRemaining + a.received.countP (fun b => b) = a.fragmentCount

/-- A successfully initialized assembler satisfies the invariant. -/
theorem init_inv {ssn : UInt16} {tl fc : Nat} {a : FragmentAssembler}
    (h : FragmentAssembler.init ssn tl fc = .ok a) : Inv a := by
  unfold FragmentAssembler.init at h
  by_cases h1 : fc = 0
  · simp [h1, Except.throw_eq', Except.bind_error'] at h
  by_cases h2 : fc > Constants.maximumFragmentCount
  · simp [h1, h2, Except.throw_eq', Except.bind_error'] at h
  by_cases h3 : tl > Constants.maximumMtu * 1024
  · simp [h1, h2, h3, Except.throw_eq', Except.bind_error'] at h
  by_cases h4 : tl < fc
  · simp [h1, h2, h3, h4, Except.throw_eq', Except.map_error'] at h
  have h1' : (fc == 0) = false := by simp [h1]
  have h2' : (fc > Constants.maximumFragmentCount) = false := by simp [h2]
  have h3' : (tl > Constants.maximumMtu * 1024) = false := by simp [h3]
  have h4' : (tl < fc) = false := by simp [h4]
  simp only [h1', h2', h3', h4'] at h
  simp only [Bool.false_eq_true, reduceIte, Except.throw_eq', Except.pure_eq'] at h
  simp at h
  subst h
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp [ByteArray.size]
  · simp [Array.countP_replicate]

/-- `copyBytes` preserves the destination size: a fragment write stays
within the buffer, so no clamping occurs. -/
theorem copyBytes_size (dst : ByteArray) (dstOffset : Nat) (src : ByteArray) :
    (FragmentAssembler.copyBytes dst dstOffset src).size = dst.size := by
  unfold FragmentAssembler.copyBytes
  split
  · rfl
  · next h =>
    have hoff : dstOffset ≤ dst.size := by omega
    have hsrc : dstOffset + src.size ≤ dst.size := by omega
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

/-- Fragment writes are in-bounds: whatever `addFragment` accepts satisfies
`offset + data.size ≤ totalLength` (ENet's identical validation). -/
theorem addFragment_write_bounded {a : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {a' : FragmentAssembler} {r : Option ByteArray}
    (h : a.addFragment n off d = .ok (a', r)) : off + d.size ≤ a.totalLength := by
  by_cases h1 : a.fragmentCount ≤ n
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = true from by simp [h1],
      reduceIte, Except.throw_eq', Except.bind_error'] at h
    cases h
  by_cases h2 : a.totalLength ≤ off
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = true from by simp [h2],
      reduceIte, Except.throw_eq', Except.bind_error'] at h
    cases h
  by_cases h3 : a.totalLength < off + d.size
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = false from by simp [h2],
      show (a.totalLength < off + d.size) = true from by simp [h3],
      reduceIte, Except.throw_eq', Except.bind_error'] at h
    cases h
  omega

/-- `addFragment` preserves the invariant. -/
theorem addFragment_inv {a : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {a' : FragmentAssembler} {r : Option ByteArray}
    (hinv : Inv a) (h : a.addFragment n off d = .ok (a', r)) : Inv a' := by
  obtain ⟨hsize, hbuf, hcount⟩ := hinv
  by_cases h1 : a.fragmentCount ≤ n
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = true from by simp [h1],
      reduceIte, Except.throw_eq', Except.bind_error'] at h
    cases h
  by_cases h2 : a.totalLength ≤ off
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = true from by simp [h2],
      reduceIte, Except.throw_eq', Except.bind_error'] at h
    cases h
  by_cases h3 : a.totalLength < off + d.size
  · simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = false from by simp [h2],
      show (a.totalLength < off + d.size) = true from by simp [h3],
      reduceIte, Except.throw_eq', Except.bind_error'] at h
    cases h
  have hlt : n < a.fragmentCount := by omega
  -- all range checks passed: reduce them in h, then case on the bitset slot
  simp only [FragmentAssembler.addFragment,
    show (a.fragmentCount ≤ n) = false from by simp [h1],
    show (a.totalLength ≤ off) = false from by simp [h2],
    show (a.totalLength < off + d.size) = false from by simp [h3],
    Bool.false_eq_true, reduceIte] at h
  split at h
  · next hb => cases h
  · next hb =>
    cases h
    exact ⟨hsize, hbuf, hcount⟩
  · next hb =>
    -- fresh slot: record it, copy the bytes, decrement the counter
    obtain ⟨hlt'', hbv⟩ := Array.getElem?_eq_some_iff.mp hb
    have hbfalse : a.received[n] = false := hbv
    have hlt' : n < a.received.size := hlt''
    split at h
    all_goals cases h
    all_goals
      show Inv { a with
        received           := a.received.setIfInBounds n true
        buffer             := FragmentAssembler.copyBytes a.buffer off d
        fragmentsRemaining := a.fragmentsRemaining - 1 }
      simp only [Inv, Array.setIfInBounds, dif_pos hlt', Array.size_set (h := hlt')]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsize]
      · exact (copyBytes_size _ _ _).trans hbuf
      -- count: the fresh slot raises the true-count by one, so the decrement
      -- is a true subtraction (fragmentsRemaining ≥ 1), not saturation
      · have hcset : (a.received.set n true hlt').countP (fun b => b)
          = a.received.countP (fun b => b) + 1 := by
          rw [Array.countP_set (p := fun b => b) hlt']
          simp [hbfalse]
        have hle : a.received.countP (fun b => b) + 1 ≤ a.fragmentCount := by
          have hcl := Array.countP_le_size (p := (fun b => b))
            (xs := a.received.set n true hlt')
          rw [hcset, Array.size_set (h := hlt'), hsize] at hcl
          exact hcl
        omega

/-- Completion soundness: when `addFragment` reports the assembled packet,
every fragment slot was received (so the buffer is the product of exactly
`fragmentCount` validated, in-bounds writes over a zero-filled buffer). -/
theorem addFragment_completion_sound {a a' : FragmentAssembler} {n off : Nat}
    {d data : ByteArray} (hinv : Inv a)
    (h : a.addFragment n off d = .ok (a', some data)) :
    a'.buffer.size = a'.totalLength ∧ ∀ (i : Nat) (hi : i < a'.received.size), a'.received[i]'hi = true := by
  have hinv' := addFragment_inv hinv h
  -- the result is `some`, so the completing branch ran: remaining = 0
  have hrem : a'.fragmentsRemaining = 0 := by
    by_cases h1 : a.fragmentCount ≤ n
    · simp only [FragmentAssembler.addFragment,
        show (a.fragmentCount ≤ n) = true from by simp [h1],
        reduceIte, Except.throw_eq', Except.bind_error'] at h
      cases h
    by_cases h2 : a.totalLength ≤ off
    · simp only [FragmentAssembler.addFragment,
        show (a.fragmentCount ≤ n) = false from by simp [h1],
        show (a.totalLength ≤ off) = true from by simp [h2],
        reduceIte, Except.throw_eq', Except.bind_error'] at h
      cases h
    by_cases h3 : a.totalLength < off + d.size
    · simp only [FragmentAssembler.addFragment,
        show (a.fragmentCount ≤ n) = false from by simp [h1],
        show (a.totalLength ≤ off) = false from by simp [h2],
        show (a.totalLength < off + d.size) = true from by simp [h3],
        reduceIte, Except.throw_eq', Except.bind_error'] at h
      cases h
    simp only [FragmentAssembler.addFragment,
      show (a.fragmentCount ≤ n) = false from by simp [h1],
      show (a.totalLength ≤ off) = false from by simp [h2],
      show (a.totalLength < off + d.size) = false from by simp [h3],
      Bool.false_eq_true, reduceIte] at h
    split at h
    · next hb =>
      simp only [Except.throw_eq'] at h
      cases h
    · next hb =>
      simp only [Except.pure_eq'] at h
      cases h
    · next hb =>
      split at h
      · next hz =>
        simp only [Except.pure_eq'] at h
        cases h
        simp only [beq_iff_eq] at hz
        omega
      · next hz =>
        simp only [Except.pure_eq'] at h
        cases h
  obtain ⟨hsz', hbuf', hcnt'⟩ := hinv'
  have hcountrz : a'.received.countP (fun b => b) = a'.received.size := by omega
  refine ⟨hbuf', countP_true_all hcountrz⟩

end Lenet.Proofs
