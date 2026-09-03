namespace Lenet

/--
Delivery reliability and sequencing mode for a user packet.
In ENet, reliable packets are always sequenced, while unreliable packets may be sequenced,
unsequenced, or fragmented.
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
  | .reliable           => (1 : UInt32) <<< 0 -- ENET_PACKET_FLAG_RELIABLE
  | .unsequenced        => (1 : UInt32) <<< 1 -- ENET_PACKET_FLAG_UNSEQUENCED
  | .unreliable         => 0
  | .unreliableFragment => (1 : UInt32) <<< 3 -- ENET_PACKET_FLAG_UNRELIABLE_FRAGMENT

/-- Parses ENet packet flag bits into a strongly-typed `DeliveryMode`. -/
def fromFlags (flags : UInt32) : DeliveryMode :=
  if (flags &&& ((1 : UInt32) <<< 0)) != 0 then
    .reliable
  else if (flags &&& ((1 : UInt32) <<< 1)) != 0 then
    .unsequenced
  else if (flags &&& ((1 : UInt32) <<< 3)) != 0 then
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
