import Lenet.Proofs.Codec
import Lenet.Proofs.Roundtrip
import Lenet.Proofs.Reassembly
import Lenet.Proofs.Channel
import Lenet.Proofs.Time
import Lenet.Proofs.Deadline
import Lenet.Proofs.Unsequenced
import Lenet.Proofs.Panic
import Lenet.Proofs.Resources
import Lenet.Proofs.Events
import Lenet.Proofs.HostEvents
import Lenet.Proofs.Window

/-!
# LenetProofs

Machine-checked properties of the Lenet core; DESIGN.md summarizes what is
proven. A separate library, so the C distribution never compiles proofs.
-/
