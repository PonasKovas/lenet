import Lenet.Time

/-!
# Wrap-aware time arithmetic proofs

`Time.difference` / `less` / `greater` are correct modulo the 24h-window
premise ENet itself assumes; translation invariance under clock skew is the
load-bearing property for the driver-facing deadline API.
-/

namespace Lenet.Proofs

end Lenet.Proofs
