import Lenet.Constants
import Lenet.Reassembly

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

end Lenet.Proofs
