import Lenet.Protocol.Command

namespace Lenet

/-- A protocol command queued for transmission, or in flight awaiting its
acknowledgement. -/
structure OutgoingCommand where
  command          : Protocol.Command
  sendAttempts     : Nat := 0
  sentTime         : UInt32 := 0
  roundTripTimeout : UInt32 := 0
  /-- Packet payload bytes the command carries; they count towards the
  peer's reliable data in transit while it is in flight. -/
  fragmentLength   : Nat := 0
deriving BEq, Inhabited

end Lenet