namespace Lenet

/-- Takes element `i` out of `xs`, leaving `v` in its slot, so the caller
holds the only reference to the element and can update it in place.

Out of line on purpose: inlined, the compiler may sink the write after the
element's last use (it does so in `Array.modifyM`), and the element is then
still shared while it changes, which copies it. -/
@[noinline] def takeAt (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) : α × Array α :=
  xs.swapAt i v h

theorem takeAt_eq (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) :
    takeAt xs i v h = (xs[i], xs.set i v) := rfl

end Lenet

namespace Lenet

/-- Putting a new element back where `takeAt` took one. -/
theorem set_setIfInBounds_same (xs : Array α) (i : Nat) (v w : α) (h : i < xs.size) :
    (xs.set i v h).setIfInBounds i w = xs.set i w h := by
  rw [Array.setIfInBounds_def, dif_pos (by simpa using h), Array.set_set]

/-- Removing the slot `takeAt` emptied. -/
theorem set_eraseIdxIfInBounds_same (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set i v h).eraseIdxIfInBounds i = xs.eraseIdx i h := by
  rw [Array.eraseIdxIfInBounds_eq, dif_pos (by simpa using h)]
  exact Array.eraseIdx_set_eq

end Lenet
