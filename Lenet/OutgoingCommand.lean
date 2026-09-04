import Lenet.Protocol.Command
import Lenet.Packet

namespace Lenet

/--
An outgoing protocol command queued for transmission or in-flight waiting for acknowledgment.
-/
structure OutgoingCommand where
  command          : Protocol.Command
  sendAttempts     : Nat := 0
  sentTime         : UInt32 := 0
  roundTripTimeout : UInt32 := 0
  fragmentOffset   : Nat := 0
  fragmentLength   : Nat := 0
deriving BEq, Inhabited

end Lenet