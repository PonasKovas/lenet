import Lenet.Constants

namespace Lenet

/--
Delivery reliability and sequencing mode for a user packet.
In ENet:
- `reliable`: Guaranteed in-order delivery. If packet exceeds MTU, sent as reliable fragments.
- `unreliable`: Sequenced, dropped if out of order. If packet exceeds MTU, sent as reliable fragments by default.
- `unsequenced`: No ordering, no reliability.
- `unreliableFragment`: Unreliable packet that explicitly permits unreliable fragmentation if larger than MTU.
-/
inductive DeliveryMode where
  | reliable
  | unreliable
  | unsequenced
  | unreliableFragment
deriving Repr, BEq, Inhabited

namespace DeliveryMode

/-- Converts a `DeliveryMode` to ENet packet flag bits. -/
def toFlags : DeliveryMode → UInt32
  | .reliable           => Constants.packetFlagReliable
  | .unsequenced        => Constants.packetFlagUnsequenced
  | .unreliable         => 0
  | .unreliableFragment => Constants.packetFlagUnreliableFragment

/-- Parses ENet packet flag bits into a strongly-typed `DeliveryMode`. -/
def fromFlags (flags : UInt32) : DeliveryMode :=
  if (flags &&& Constants.packetFlagReliable) != 0 then
    .reliable
  else if (flags &&& Constants.packetFlagUnsequenced) != 0 then
    .unsequenced
  else if (flags &&& Constants.packetFlagUnreliableFragment) != 0 then
    .unreliableFragment
  else
    .unreliable

/-- True if the packet requires reliable acknowledgment and retransmission. -/
@[inline]
def isReliable : DeliveryMode → Bool
  | .reliable => true
  | _         => false

/-- True if the packet is unsequenced. -/
@[inline]
def isUnsequenced : DeliveryMode → Bool
  | .unsequenced => true
  | _            => false

end DeliveryMode

/--
A user data packet to be sent or received over an ENet channel.
-/
structure Packet where
  data     : ByteArray
  delivery : DeliveryMode := .reliable
deriving BEq, Inhabited

namespace Packet

/-- Creates a reliable packet. -/
@[inline]
def reliable (data : ByteArray) : Packet :=
  { data, delivery := .reliable }

/-- Creates an unreliable sequenced packet. -/
@[inline]
def unreliable (data : ByteArray) : Packet :=
  { data, delivery := .unreliable }

/-- Creates an unsequenced packet. -/
@[inline]
def unsequenced (data : ByteArray) : Packet :=
  { data, delivery := .unsequenced }

/-- Creates an unreliable fragmentable packet. -/
@[inline]
def unreliableFragment (data : ByteArray) : Packet :=
  { data, delivery := .unreliableFragment }

/-- The size in bytes of the packet's payload. -/
@[inline]
def size (p : Packet) : Nat :=
  p.data.size

end Packet

end Lenet
