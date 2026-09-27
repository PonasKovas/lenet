import Lenet.Constants
import Lenet.Reassembly
import Lenet.Proofs.Basic

/-!
# Reassembly safety proofs

The fragment assembler keeps only what arrived. Its received-bitset,
`fragmentsRemaining` counter, stored fragments and byte count must stay in
step: `fragmentsRemaining + marked = fragmentCount`, one stored fragment per
marked slot, and the stored bytes add up to `receivedBytes`. That makes
completion sound: the packet is built only after every fragment slot was
written once and the fragments carried exactly `totalLength` bytes, and the
`fragmentsRemaining - 1` decrement never depends on Nat saturation.
-/

namespace Lenet.Proofs

open FragmentAssembler

/-- The fragments a received-bitset marks. -/
def marked (b : ByteArray) : Nat := b.data.countP (· != 0)

theorem addFragment_ok_cases {a a' : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {r : Option ByteArray} (h : a.addFragment n off d = .ok (a', r)) :
    n < a.fragmentCount ∧ off < a.totalLength ∧ off + d.size ≤ a.totalLength ∧
    ∃ hn : n < a.received.size,
      (a.received[n] ≠ 0 ∧ a' = a ∧ r = none) ∨
      (a.received[n] = 0 ∧ a.bytesFit d.size = true ∧
        a' = { a with received := a.received.set n 1 hn, receivedBytes := a.receivedBytes + d.size,
                      fragments := a.fragments.push (off, d),
                      fragmentsRemaining := a.fragmentsRemaining - 1 } ∧
        r = if a.fragmentsRemaining - 1 == 0 then some a'.assemble else none) := by
  obtain ⟨origin, ssn, tl, fc, fr, rcv, rb, frags⟩ := a
  unfold addFragment at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  by_cases h1 : fc ≤ n
  · simp [h1] at h
  by_cases h2 : tl ≤ off
  · simp [h1, h2] at h
  by_cases h3 : tl < off + d.size
  · simp [h1, h2, h3] at h
  simp only [ge_iff_le, h1, h2, gt_iff_lt, h3, reduceIte] at h
  dsimp only
  refine ⟨by omega, by omega, by omega, ?_⟩
  split at h
  · next hn =>
    refine ⟨hn, ?_⟩
    split at h
    · next hz =>
      cases h
      exact .inl ⟨by simpa using hz, rfl, rfl⟩
    · next hz =>
      split at h
      · cases h
      · next hb =>
        simp only [Bool.not_eq_true'] at hb
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hz
        split at h <;> cases h <;> simp_all
  · cases h

/-! ## The assembler invariant -/

/-- Reachable-assembler invariant: one received byte per fragment, the
counter and the stored fragments in step with the marked slots, the stored
bytes counted exactly and within `totalLength`, and every stored fragment
inside the packet. -/
def Inv (a : FragmentAssembler) : Prop :=
  a.received.size = a.fragmentCount ∧
  a.fragmentsRemaining + marked a.received = a.fragmentCount ∧
  a.fragments.size = marked a.received ∧
  (a.fragments.toList.map (·.2.size)).sum = a.receivedBytes ∧
  a.receivedBytes ≤ a.totalLength ∧
  ∀ f ∈ a.fragments, f.1 + f.2.size ≤ a.totalLength

theorem mem_of_mem_extract {xs : Array UInt8} {a b : Nat} {x : UInt8} (h : x ∈ xs.extract a b) : x ∈ xs := by
  rw [Array.mem_iff_getElem] at h ⊢
  obtain ⟨i, hi, rfl⟩ := h
  simp only [Array.size_extract] at hi
  exact ⟨a + i, by omega, by simp [Array.getElem_extract]⟩

theorem byteArray_size_set (b : ByteArray) (i : Nat) (v : UInt8) (h : i < b.size) :
    (b.set i v h).size = b.size := by
  show (b.data.set i v h).size = b.data.size
  exact Array.size_set h

theorem zeros_seed : ∀ x ∈ (ByteArray.empty.push 0).data, x = 0 := by
  intro x hx
  simp [ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity] at hx
  rcases hx with hx | hx
  · exact absurd hx (Array.not_mem_empty x)
  · exact hx

theorem zeros_grow_spec (n : Nat) (b : ByteArray) (hb : 0 < b.size) (hz : ∀ x ∈ b.data, x = 0) :
    (FragmentAssembler.zeros.grow n b).size = n ∧ ∀ x ∈ (FragmentAssembler.zeros.grow n b).data, x = 0 := by
  induction b using FragmentAssembler.zeros.grow.induct n with
  | case1 b h ih =>
    rw [FragmentAssembler.zeros.grow, dif_pos h]
    refine ih (by simp only [ByteArray.size_append]; omega) ?_
    intro x hx
    rw [ByteArray.data_append, Array.mem_append] at hx
    rcases hx with hx | hx <;> exact hz x hx
  | case2 b h =>
    rw [FragmentAssembler.zeros.grow, dif_neg h]
    refine ⟨by rw [ByteArray.size_extract]; omega, ?_⟩
    intro x hx
    rw [ByteArray.data_extract] at hx
    exact hz x (mem_of_mem_extract hx)

theorem zeros_size (n : Nat) : (FragmentAssembler.zeros n).size = n :=
  (zeros_grow_spec n _ (by simp) zeros_seed).1

theorem marked_zeros (n : Nat) : marked (FragmentAssembler.zeros n) = 0 := by
  have := (zeros_grow_spec n (ByteArray.empty.push 0) (by simp) zeros_seed).2
  unfold marked
  rw [Array.countP_eq_zero]
  intro x hx
  simp [this x hx]

/-- A successfully initialized assembler satisfies the invariant. -/
theorem init_inv {ssn : UInt16} {tl fc maxPacketSize : Nat} {a : FragmentAssembler}
    (h : FragmentAssembler.init ssn tl fc maxPacketSize = Except.ok a) : Inv a := by
  unfold FragmentAssembler.init at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals cases h
  refine ⟨zeros_size fc, by simp [marked_zeros], by simp [marked_zeros], rfl, Nat.zero_le _, ?_⟩
  intro f hf
  simp at hf

/-- `copyBytes` preserves the destination size: a fragment write stays
within the buffer, so no clamping occurs. -/
theorem copyBytes_size (dst : ByteArray) (dstOffset : Nat) (src : ByteArray) :
    (FragmentAssembler.copyBytes dst dstOffset src).size = dst.size := by
  unfold FragmentAssembler.copyBytes
  split
  · rfl
  · next h =>
    simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract]
    simp only [ByteArray.size] at h
    omega

/-- The assembled packet is `totalLength` bytes. -/
theorem assemble_size (a : FragmentAssembler) : a.assemble.size = a.totalLength := by
  suffices h : (FragmentAssembler.assemble.placed a).size = a.totalLength by
    unfold FragmentAssembler.assemble
    split
    · split
      · next hs => simpa using hs
      · exact h
    · exact h
  unfold FragmentAssembler.assemble.placed
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (Nat × ByteArray)) (b : ByteArray),
      (l.foldl (fun buf (x : Nat × ByteArray) => copyBytes buf x.1 x.2) b).size = b.size by
    rw [this]; exact zeros_size _
  intro l
  induction l with
  | nil => intro b; rfl
  | cons x l ih => intro b; simp only [List.foldl_cons]; rw [ih, copyBytes_size]

/-- Fragment writes are in-bounds: whatever `addFragment` accepts satisfies
`offset + data.size ≤ totalLength` (ENet's identical validation). -/
theorem addFragment_write_bounded {a : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {a' : FragmentAssembler} {r : Option ByteArray}
    (h : a.addFragment n off d = .ok (a', r)) : off + d.size ≤ a.totalLength :=
  (addFragment_ok_cases h).2.2.1

/-- `addFragment` preserves the invariant. -/
theorem addFragment_inv {a : FragmentAssembler} {n off : Nat} {d : ByteArray}
    {a' : FragmentAssembler} {r : Option ByteArray}
    (hinv : Inv a) (h : a.addFragment n off d = .ok (a', r)) : Inv a' := by
  obtain ⟨hsize, hcount, hfrags, hsum, hbytes, hin⟩ := hinv
  obtain ⟨-, -, hw, hn, hc⟩ := addFragment_ok_cases h
  rcases hc with ⟨-, rfl, -⟩ | ⟨hz, hfit, rfl, -⟩
  · exact ⟨hsize, hcount, hfrags, hsum, hbytes, hin⟩
  -- a fresh slot: it raises the marked count by one, so the decrement is a
  -- true subtraction (fragmentsRemaining ≥ 1), not saturation
  have hmark : marked (a.received.set n 1 hn) = marked a.received + 1 := by
    unfold marked
    show (a.received.data.set n 1 hn).countP _ = _
    rw [Array.countP_set (p := (· != 0)) hn]
    have : a.received.data[n] = 0 := hz
    simp [this]
  have hle : marked a.received + 1 ≤ a.fragmentCount := by
    have hcl : marked (a.received.set n 1 hn) ≤ (a.received.set n 1 hn).size := Array.countP_le_size
    rw [byteArray_size_set, hsize] at hcl
    omega
  unfold FragmentAssembler.bytesFit at hfit
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (a.received.set n 1 hn).size = _
    rw [byteArray_size_set, hsize]
  · show a.fragmentsRemaining - 1 + marked (a.received.set n 1 hn) = a.fragmentCount
    omega
  · show (a.fragments.push (off, d)).size = marked (a.received.set n 1 hn)
    simp [hfrags, hmark]
  · show ((a.fragments.push (off, d)).toList.map (·.2.size)).sum = a.receivedBytes + d.size
    simp [hsum]
  · show a.receivedBytes + d.size ≤ a.totalLength
    exact hfit.1
  · intro f hf
    rcases Array.mem_push.mp hf with hf | rfl
    · exact hin f hf
    · exact hw

/-- Completion soundness: when `addFragment` reports the assembled packet,
it is the assembler's fragments copied to their offsets (`assemble`), it is
`totalLength` bytes, every fragment slot was received, and the fragments
received carried exactly `totalLength` bytes between them. -/
theorem addFragment_completion_sound {a a' : FragmentAssembler} {n off : Nat}
    {d data : ByteArray} (hinv : Inv a)
    (h : a.addFragment n off d = .ok (a', some data)) :
    data = a'.assemble ∧ data.size = a'.totalLength ∧
      (a'.fragments.toList.map (·.2.size)).sum = a'.totalLength ∧
      ∀ (i : Nat) (hi : i < a'.received.size), a'.received[i]'hi ≠ 0 := by
  have hinv' := addFragment_inv hinv h
  obtain ⟨hsize, hcount, -, -, -, -⟩ := hinv
  obtain ⟨hsz', hcnt', -, hsum', -, -⟩ := hinv'
  obtain ⟨-, -, -, hn, hc⟩ := addFragment_ok_cases h
  rcases hc with ⟨-, -, hr⟩ | ⟨hz, hfit, rfl, hr⟩
  · cases hr
  -- the result is `some`, so the completing branch ran: the fresh slot was
  -- the last one missing, and `bytesFit` made its bytes the rest
  have hlast : a.fragmentsRemaining - 1 = 0 := by
    split at hr
    · next he => simpa using he
    · cases hr
  have hdata : data = FragmentAssembler.assemble
      { a with
        received := a.received.set n 1 hn
        receivedBytes := a.receivedBytes + d.size
        fragments := a.fragments.push (off, d)
        fragmentsRemaining := a.fragmentsRemaining - 1 } := by
    rw [if_pos (by simpa using hlast)] at hr
    cases hr; rfl
  have hone : a.fragmentsRemaining = 1 := by
    have : marked a.received < a.fragmentCount := by
      have hlt : marked a.received < a.received.size := by
        unfold marked
        have hne : ¬ (a.received.data[n]'hn != 0) = true := by
          have : a.received.data[n] = 0 := hz
          simp [this]
        exact Nat.lt_of_le_of_ne (Array.countP_le_size) fun heq =>
          hne (Array.countP_eq_size.mp heq _ (Array.getElem_mem hn))
      omega
    omega
  unfold FragmentAssembler.bytesFit at hfit
  simp only [hone, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hfit
  refine ⟨hdata, hdata ▸ assemble_size _, ?_, ?_⟩
  · rw [hsum']; exact hfit.2
  · intro i hi
    have hall : marked (a.received.set n 1 hn) = (a.received.set n 1 hn).size := by
      have h1 : a.fragmentsRemaining - 1 + marked (a.received.set n 1 hn) = a.fragmentCount := hcnt'
      have h2 : (a.received.set n 1 hn).size = a.fragmentCount := hsz'
      omega
    unfold marked at hall
    have hmem := Array.countP_eq_size.mp hall _ (Array.getElem_mem hi)
    simp only [bne_iff_ne, ne_eq] at hmem
    exact hmem

end Lenet.Proofs
