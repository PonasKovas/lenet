import Lenet.Address
import Lenet.Packet

namespace Lenet

/--
High-level protocol events dispatched to the application.
-/
inductive Event where
  /-- A remote peer has successfully connected. -/
  | connect (peerId : UInt16) (data : UInt32)
  /-- A remote peer has disconnected or timed out. -/
  | disconnect (peerId : UInt16) (data : UInt32)
  /-- A data packet has been received on a channel. -/
  | receive (peerId : UInt16) (channelId : UInt8) (packet : Packet)
deriving BEq, Inhabited

end Lenet