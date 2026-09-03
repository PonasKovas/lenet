namespace Lenet

/--
Portable Internet address structure representing an IPv4 endpoint.
`host` is stored as a 32-bit integer in network byte order (little-endian octet layout in memory),
and `port` is in host byte order.
-/
structure Address where
  host : UInt32 := 0
  port : UInt16 := 0
deriving Repr, BEq, Inhabited

namespace Address

def any : UInt32 := 0
def broadcast : UInt32 := 0xFFFFFFFF

/-- Constructs a 32-bit network-order IPv4 address from 4 octets (`b0.b1.b2.b3`). -/
@[inline]
def fromOctets (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- Deconstructs a 32-bit IPv4 address into its 4 octets (`b0.b1.b2.b3`). -/
@[inline]
def toOctets (host : UInt32) : UInt8 × UInt8 × UInt8 × UInt8 :=
  (host.toUInt8, (host >>> 8).toUInt8, (host >>> 16).toUInt8, (host >>> 24).toUInt8)

/-- Formats a 32-bit host into standard "a.b.c.d" IPv4 notation. -/
def formatIPv4 (host : UInt32) : String :=
  let (b0, b1, b2, b3) := toOctets host
  s!"{b0}.{b1}.{b2}.{b3}"

/-- Constructs an `Address` from 4 octets (`b0.b1.b2.b3`) and a port. -/
@[inline]
def ipv4 (b0 b1 b2 b3 : UInt8) (port : UInt16 := 0) : Address :=
  { host := fromOctets b0 b1 b2 b3, port }

instance : ToString Address where
  toString a := s!"{formatIPv4 a.host}:{a.port}"

end Address

end Lenet