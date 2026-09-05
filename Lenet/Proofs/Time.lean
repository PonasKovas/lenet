import Std.Tactic.BVDecide
import Lenet.Time

/-!
# Wrap-aware time arithmetic proofs

`Time.difference` / `less` / `greater` interpret 32-bit millisecond timestamps
with ENet's 24-hour disambiguation window. The non-obvious property:

* Translation invariance: `difference (a + k) (b + k) = difference a b` - the
  load-bearing property for the driver-facing `Host.nextDeadline` API, whose
  deadline comparisons must be insensitive to when the driver's clock
  started. Reduces to cyclic subtraction invariance, a fixed-width fact.
-/

namespace Lenet.Proofs

open Time

/-- Cyclic subtraction is translation-invariant. -/
theorem sub_add_add (a b k : UInt32) : a + k - (b + k) = a - b := by bv_decide

theorem sub_add_add' (a b k : UInt32) : b + k - (a + k) = b - a := by bv_decide

/-- Clock translation leaves elapsed differences unchanged. -/
theorem difference_translation (a b k : UInt32) :
    Time.difference (a + k) (b + k) = Time.difference a b := by
  unfold Time.difference
  rw [sub_add_add, sub_add_add']

/-- Clock translation preserves the strict order. -/
theorem less_translation (a b k : UInt32) :
    Time.less (a + k) (b + k) = Time.less a b := by
  unfold Time.less
  rw [sub_add_add]

end Lenet.Proofs
