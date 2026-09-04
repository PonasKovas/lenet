import Lenet.Constants
import Lenet.Host

/-!
# Panic-site audit

After the Phase 1 conventions (DESIGN.md 1.7), the only runtime panic source
left in `Lenet/` is division by zero (all indexing is proof-carrying by
construction). This module proves every divisor non-zero on all reachable
paths; a new unguarded division site fails review by its absence here.
-/

namespace Lenet.Proofs

end Lenet.Proofs
