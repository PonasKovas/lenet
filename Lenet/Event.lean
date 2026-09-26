import Lenet.Packet

namespace Lenet

/-- Application events produced by `Host.handleDatagram` and `Host.service`. -/
inductive Event where
  /-- A connection completed; `data` is the connect data the client sent. -/
  | connect (peerId : UInt16) (data : UInt32)
  /-- A connection ended: gracefully (with the remote's data) or by timeout
  (data 0). The peer slot is free again. -/
  | disconnect (peerId : UInt16) (data : UInt32)
  /-- A data packet has been received on a channel. -/
  | receive (peerId : UInt16) (channelId : UInt8) (packet : Packet)
deriving BEq, Inhabited

end Lenet