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
import Lenet.Proofs.Delivery
import Lenet.Proofs.Connection
import Lenet.Proofs.ResourcesRun
import Lenet.Proofs.Idle

/-!
# LenetProofs

Machine-checked properties of the Lenet core, one file per topic; each
file's header says what it proves. A separate library, so the C
distribution never compiles proofs.

Most results rest on Lean's kernel and its three standard axioms. The
bit-level lemmas proved with `bv_decide` add one axiom each: the SAT
solver's certificate is checked by Lean's compiled LRAT checker, not by the
kernel. `#print axioms` shows which results depend on them.
-/
