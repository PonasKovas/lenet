import Std.Tactic.BVDecide
import Lenet.Time

/-!
# Wrap-aware time arithmetic proofs

`Time.difference` / `less` interpret 32-bit millisecond timestamps
with ENet's 24-hour disambiguation window. The non-obvious property:

* Translation invariance: `difference (a + k) (b + k) = difference a b` - the
  load-bearing property for the driver-facing `Host.nextDeadline` API, whose
  deadline comparisons must be insensitive to when the driver's clock
  started. Reduces to cyclic subtraction invariance, a fixed-width fact.
* `Time.fromWire` recovers a timestamp from its low 16 bits whenever it lies
  less than half a 16-bit cycle (32.8 s) in the past - which is what makes RTT
  samples from echoed 16-bit sent times correct at any uptime.
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

/-- A timestamp less than half a 16-bit cycle old is recovered exactly from
its wire form. -/
theorem fromWire_recovers (t age : UInt32) (h : age < 0x8000) :
    Time.fromWire (t + age) t.toUInt16 = t := by
  unfold Time.fromWire
  have : t.toUInt16.toUInt32 = t &&& 0xFFFF := by bv_decide
  rw [this]
  bv_decide

end Lenet.Proofs
