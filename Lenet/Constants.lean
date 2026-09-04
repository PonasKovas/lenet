namespace Lenet.Constants

/-! ### Protocol Limits and Sizes -/

def minimumMtu : Nat := 576
def maximumMtu : Nat := 4096
/-- ENet's `ENET_HOST_DEFAULT_MTU` — the default MTU a host is created with. -/
def defaultMtu : Nat := 1392
def maximumPacketCommands : Nat := 32
def minimumWindowSize : Nat := 4096
def maximumWindowSize : Nat := 65536
def minimumChannelCount : Nat := 1
def maximumChannelCount : Nat := 255
def maximumPeerId : UInt16 := 0x0FFF
def maximumFragmentCount : Nat := 1024 * 1024

/-! ### Sliding Window Parameters -/

def reliableWindows : Nat := 16
def reliableWindowSize : Nat := 0x1000 -- 4096 sequence numbers per window
def freeReliableWindows : Nat := 8

def unsequencedWindows : Nat := 64
def unsequencedWindowSize : Nat := 1024
def freeUnsequencedWindows : Nat := 32

/-! ### Protocol Header Bitmasks & Flags -/

def headerFlagCompressed : UInt16 := (1 : UInt16) <<< 14
def headerFlagSentTime   : UInt16 := (1 : UInt16) <<< 15
def headerFlagMask       : UInt16 := headerFlagCompressed ||| headerFlagSentTime

def headerSessionShift   : Nat    := 12
def headerSessionMask    : UInt16 := (3 : UInt16) <<< 12

/-! ### Protocol Command Bitmasks & Flags -/

def commandFlagAcknowledge : UInt8 := (1 : UInt8) <<< 7
def commandFlagUnsequenced : UInt8 := (1 : UInt8) <<< 6
def commandMask            : UInt8 := 0x0F

/-! ### Protocol Command Numbers -/

def commandNone                   : UInt8 := 0
def commandAcknowledge            : UInt8 := 1
def commandConnect                : UInt8 := 2
def commandVerifyConnect          : UInt8 := 3
def commandDisconnect             : UInt8 := 4
def commandPing                   : UInt8 := 5
def commandSendReliable           : UInt8 := 6
def commandSendUnreliable         : UInt8 := 7
def commandSendFragment           : UInt8 := 8
def commandSendUnsequenced        : UInt8 := 9
def commandBandwidthLimit         : UInt8 := 10
def commandThrottleConfigure      : UInt8 := 11
def commandSendUnreliableFragment : UInt8 := 12
def commandCount                  : Nat   := 13

/-! ### Packet Flags -/

def packetFlagReliable           : UInt32 := (1 : UInt32) <<< 0
def packetFlagUnsequenced        : UInt32 := (1 : UInt32) <<< 1
def packetFlagNoAllocate         : UInt32 := (1 : UInt32) <<< 2
def packetFlagUnreliableFragment : UInt32 := (1 : UInt32) <<< 3
def packetFlagSent               : UInt32 := (1 : UInt32) <<< 8

/-! ### Peer Defaults & Throttle Constants -/

def defaultRoundTripTime              : UInt32 := 500
def defaultPacketThrottle             : UInt32 := 32
def packetThrottleScale               : UInt32 := 32
def packetThrottleCounter             : UInt32 := 7
def defaultPacketThrottleAcceleration : UInt32 := 2
def defaultPacketThrottleDeceleration : UInt32 := 2
def defaultPacketThrottleInterval     : UInt32 := 5000
def defaultPingInterval               : UInt32 := 500
def defaultTimeoutLimit               : UInt32 := 32
def defaultTimeoutMinimum             : UInt32 := 5000
def defaultTimeoutMaximum           : UInt32 := 30000
def windowSizeScale                 : UInt32 := 64 * 1024
def bandwidthThrottleInterval       : UInt32 := 1000

end Lenet.Constants
