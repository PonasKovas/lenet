import Lenet.Constants
import Lenet.Codec

namespace Lenet.Protocol

open Lenet
open Lenet.ReaderM
open Lenet.WriterM

/--
Negotiation parameters shared between `Connect` and `VerifyConnect` commands.
Total serialized size: 40 bytes.
-/
structure ConnectParams where
  outgoingPeerId             : UInt16
  incomingSessionId          : UInt8
  outgoingSessionId          : UInt8
  mtu                        : UInt32
  windowSize                 : UInt32
  channelCount               : UInt32
  incomingBandwidth          : UInt32
  outgoingBandwidth          : UInt32
  packetThrottleInterval     : UInt32
  packetThrottleAcceleration : UInt32
  packetThrottleDeceleration : UInt32
  connectId                  : UInt32
deriving Repr, BEq, Inhabited

namespace ConnectParams

def decode : ReaderM ConnectParams := do
  let outgoingPeerId             ← readUInt16BE
  let incomingSessionId          ← readUInt8
  let outgoingSessionId          ← readUInt8
  let mtu                        ← readUInt32BE
  let windowSize                 ← readUInt32BE
  let channelCount               ← readUInt32BE
  let incomingBandwidth          ← readUInt32BE
  let outgoingBandwidth          ← readUInt32BE
  let packetThrottleInterval     ← readUInt32BE
  let packetThrottleAcceleration ← readUInt32BE
  let packetThrottleDeceleration ← readUInt32BE
  let connectId                  ← readUInt32BE
  return {
    outgoingPeerId, incomingSessionId, outgoingSessionId,
    mtu, windowSize, channelCount, incomingBandwidth, outgoingBandwidth,
    packetThrottleInterval, packetThrottleAcceleration, packetThrottleDeceleration,
    connectId
  }

def encode (p : ConnectParams) : WriterM Unit := do
  writeUInt16BE p.outgoingPeerId
  writeUInt8    p.incomingSessionId
  writeUInt8    p.outgoingSessionId
  writeUInt32BE p.mtu
  writeUInt32BE p.windowSize
  writeUInt32BE p.channelCount
  writeUInt32BE p.incomingBandwidth
  writeUInt32BE p.outgoingBandwidth
  writeUInt32BE p.packetThrottleInterval
  writeUInt32BE p.packetThrottleAcceleration
  writeUInt32BE p.packetThrottleDeceleration
  writeUInt32BE p.connectId

end ConnectParams

instance : Decode ConnectParams where decode := ConnectParams.decode
instance : Encode ConnectParams where encode := ConnectParams.encode

/--
Parameters for fragmented packet transmission commands (`SendFragment` and `SendUnreliableFragment`).
Total fixed header size: 24 bytes (followed immediately by `data.size` bytes of payload).
-/
structure FragmentParams where
  startSequenceNumber : UInt16
  fragmentCount       : UInt32
  fragmentNumber      : UInt32
  totalLength         : UInt32
  fragmentOffset      : UInt32
  data                : ByteArray
deriving BEq, Inhabited

namespace FragmentParams

def decode : ReaderM FragmentParams := do
  let startSequenceNumber ← readUInt16BE
  let dataLength          ← readUInt16BE
  let fragmentCount       ← readUInt32BE
  let fragmentNumber      ← readUInt32BE
  let totalLength         ← readUInt32BE
  let fragmentOffset      ← readUInt32BE
  let data                ← readBytes dataLength.toNat
  return {
    startSequenceNumber,
    fragmentCount,
    fragmentNumber,
    totalLength,
    fragmentOffset,
    data
  }

def encode (p : FragmentParams) : WriterM Unit := do
  writeUInt16BE p.startSequenceNumber
  writeUInt16BE p.data.size.toUInt16
  writeUInt32BE p.fragmentCount
  writeUInt32BE p.fragmentNumber
  writeUInt32BE p.totalLength
  writeUInt32BE p.fragmentOffset
  writeBytes    p.data

end FragmentParams

instance : Decode FragmentParams where decode := FragmentParams.decode
instance : Encode FragmentParams where encode := FragmentParams.encode

/--
Payload variants for all 12 ENet protocol commands.
-/
inductive CommandBody where
  | acknowledge (receivedReliableSequenceNumber : UInt16) (receivedSentTime : UInt16)
  | connect (params : ConnectParams) (data : UInt32)
  | verifyConnect (params : ConnectParams)
  | disconnect (data : UInt32)
  | ping
  | sendReliable (data : ByteArray)
  | sendUnreliable (unreliableSequenceNumber : UInt16) (data : ByteArray)
  | sendFragment (params : FragmentParams)
  | sendUnsequenced (unsequencedGroup : UInt16) (data : ByteArray)
  | bandwidthLimit (incomingBandwidth : UInt32) (outgoingBandwidth : UInt32)
  | throttleConfigure (packetThrottleInterval : UInt32) (packetThrottleAcceleration : UInt32) (packetThrottleDeceleration : UInt32)
  | sendUnreliableFragment (params : FragmentParams)
deriving  BEq, Inhabited

namespace CommandBody

def commandNumber : CommandBody → UInt8
  | .acknowledge ..            => Constants.commandAcknowledge
  | .connect ..                => Constants.commandConnect
  | .verifyConnect ..          => Constants.commandVerifyConnect
  | .disconnect ..             => Constants.commandDisconnect
  | .ping                      => Constants.commandPing
  | .sendReliable ..           => Constants.commandSendReliable
  | .sendUnreliable ..         => Constants.commandSendUnreliable
  | .sendFragment ..           => Constants.commandSendFragment
  | .sendUnsequenced ..        => Constants.commandSendUnsequenced
  | .bandwidthLimit ..         => Constants.commandBandwidthLimit
  | .throttleConfigure ..      => Constants.commandThrottleConfigure
  | .sendUnreliableFragment .. => Constants.commandSendUnreliableFragment

def encode (body : CommandBody) : WriterM Unit := do
  match body with
  | .acknowledge receivedSeq receivedTime =>
    writeUInt16BE receivedSeq
    writeUInt16BE receivedTime
  | .connect params data =>
    params.encode
    writeUInt32BE data
  | .verifyConnect params =>
    params.encode
  | .disconnect data =>
    writeUInt32BE data
  | .ping =>
    pure ()
  | .sendReliable data =>
    writeUInt16BE data.size.toUInt16
    writeBytes data
  | .sendUnreliable unseq data =>
    writeUInt16BE unseq
    writeUInt16BE data.size.toUInt16
    writeBytes data
  | .sendFragment params =>
    params.encode
  | .sendUnsequenced unseqGroup data =>
    writeUInt16BE unseqGroup
    writeUInt16BE data.size.toUInt16
    writeBytes data
  | .bandwidthLimit inBw outBw =>
    writeUInt32BE inBw
    writeUInt32BE outBw
  | .throttleConfigure interval accel decel =>
    writeUInt32BE interval
    writeUInt32BE accel
    writeUInt32BE decel
  | .sendUnreliableFragment params =>
    params.encode

end CommandBody

/--
Complete ENet protocol command containing routing metadata and the command payload.
-/
structure Command where
  channelId              : UInt8
  reliableSequenceNumber : UInt16
  acknowledge            : Bool := false
  unsequenced            : Bool := false
  body                   : CommandBody
deriving BEq, Inhabited

namespace Command

def decode : ReaderM Command := do
  let rawCommand ← readUInt8
  let channelId  ← readUInt8
  let reliableSequenceNumber ← readUInt16BE

  let acknowledge := (rawCommand &&& Constants.commandFlagAcknowledge) != 0
  let unsequenced := (rawCommand &&& Constants.commandFlagUnsequenced) != 0
  let cmdNumber   := rawCommand &&& Constants.commandMask

  let body ← match cmdNumber with
  | 1 => do
    let recvSeq ← readUInt16BE
    let recvTime ← readUInt16BE
    pure (.acknowledge recvSeq recvTime)
  | 2 => do
    let params ← ConnectParams.decode
    let data ← readUInt32BE
    pure (.connect params data)
  | 3 => do
    let params ← ConnectParams.decode
    pure (.verifyConnect params)
  | 4 => do
    let data ← readUInt32BE
    pure (.disconnect data)
  | 5 => do
    pure .ping
  | 6 => do
    let dataLen ← readUInt16BE
    let data ← readBytes dataLen.toNat
    pure (.sendReliable data)
  | 7 => do
    let unseq ← readUInt16BE
    let dataLen ← readUInt16BE
    let data ← readBytes dataLen.toNat
    pure (.sendUnreliable unseq data)
  | 8 => do
    let params ← FragmentParams.decode
    pure (.sendFragment params)
  | 9 => do
    let unseqGroup ← readUInt16BE
    let dataLen ← readUInt16BE
    let data ← readBytes dataLen.toNat
    pure (.sendUnsequenced unseqGroup data)
  | 10 => do
    let inBw ← readUInt32BE
    let outBw ← readUInt32BE
    pure (.bandwidthLimit inBw outBw)
  | 11 => do
    let interval ← readUInt32BE
    let accel ← readUInt32BE
    let decel ← readUInt32BE
    pure (.throttleConfigure interval accel decel)
  | 12 => do
    let params ← FragmentParams.decode
    pure (.sendUnreliableFragment params)
  | n =>
    throw (CodecError.invalidEnumValue "ENetProtocolCommand" n.toNat)

  return {
    channelId
    reliableSequenceNumber
    acknowledge
    unsequenced
    body
  }

def encode (cmd : Command) : WriterM Unit := do
  let flags : UInt8 :=
    (if cmd.acknowledge then Constants.commandFlagAcknowledge else 0) |||
    (if cmd.unsequenced then Constants.commandFlagUnsequenced else 0)
  let rawCommand := (cmd.body.commandNumber &&& Constants.commandMask) ||| flags

  writeUInt8 rawCommand
  writeUInt8 cmd.channelId
  writeUInt16BE cmd.reliableSequenceNumber
  cmd.body.encode

end Command

instance : Decode Command where decode := Command.decode
instance : Encode Command where encode := Command.encode

end Lenet.Protocol
