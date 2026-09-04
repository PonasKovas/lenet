import Lenet.Constants
import Lenet.Time
import Lenet.Address
import Lenet.Channel
import Lenet.Unsequenced
import Lenet.Packet
import Lenet.OutgoingCommand

namespace Lenet

/--
Lifecycle state machine of an ENet peer connection.
-/
inductive PeerState where
  | disconnected
  | connecting
  | acknowledgingConnect
  | connectionPending
  | connectionSucceeded
  | connected
  | disconnectLater
  | disconnecting
  | acknowledgingDisconnect
  | zombie
deriving Repr, BEq, DecidableEq, Inhabited

/--
A peer endpoint representing a remote connected host.
Manages channels, sequence numbers, congestion throttling, and RTT estimation.
-/
structure Peer where
  peerId                         : UInt16 := 0
  outgoingPeerId                 : UInt16 := Constants.maximumPeerId
  incomingSessionId              : UInt8 := 0xFF
  outgoingSessionId              : UInt8 := 0xFF
  connectId                      : UInt32 := 0
  address                        : Address := {}
  state                          : PeerState := .disconnected
  channels                       : Array Channel := #[]
  unsequencedWindow              : UnsequencedWindow := {}
  mtu                            : UInt32 := Constants.minimumMtu.toUInt32
  windowSize                     : UInt32 := Constants.maximumWindowSize.toUInt32
  incomingBandwidth              : UInt32 := 0
  outgoingBandwidth              : UInt32 := 0
  roundTripTime                  : UInt32 := Constants.defaultRoundTripTime
  roundTripTimeVariance          : UInt32 := 0
  lowestRoundTripTime            : UInt32 := Constants.defaultRoundTripTime
  highestRoundTripTimeVariance   : UInt32 := 0
  lastRoundTripTime              : UInt32 := Constants.defaultRoundTripTime
  lastRoundTripTimeVariance      : UInt32 := 0
  lastReceiveTime                : UInt32 := 0
  lastSendTime                   : UInt32 := 0
  nextTimeout                    : UInt32 := 0
  earliestTimeout                : UInt32 := 0
  pingInterval                   : UInt32 := Constants.defaultPingInterval
  timeoutLimit                   : UInt32 := Constants.defaultTimeoutLimit
  timeoutMinimum                 : UInt32 := Constants.defaultTimeoutMinimum
  timeoutMaximum                 : UInt32 := Constants.defaultTimeoutMaximum
  packetThrottle                 : UInt32 := Constants.defaultPacketThrottle
  packetThrottleLimit            : UInt32 := Constants.packetThrottleScale
  packetThrottleCounter          : UInt32 := 0
  packetThrottleEpoch            : UInt32 := 0
  packetThrottleAcceleration     : UInt32 := Constants.defaultPacketThrottleAcceleration
  packetThrottleDeceleration     : UInt32 := Constants.defaultPacketThrottleDeceleration
  packetThrottleInterval         : UInt32 := Constants.defaultPacketThrottleInterval
  eventData                      : UInt32 := 0
  reliableDataInTransit          : Nat := 0
  outgoingCommands               : Array OutgoingCommand := #[]
  sentReliableCommands           : Array OutgoingCommand := #[]
  acknowledgements               : Array (UInt8 × UInt16 × UInt16) := #[]
deriving BEq, Inhabited

namespace Peer

/-- Creates an initialized peer allocated with `channelCount` channels. -/
def create (peerId : UInt16) (channelCount : Nat := 1) (address : Address := {}) : Peer :=
  let channels := Array.replicate channelCount Channel.init
  {
    peerId
    address
    channels
    mtu := Constants.minimumMtu.toUInt32
  }

/-- Resets the peer back to disconnected state, clearing channels and sequence numbers. -/
def reset (p : Peer) : Peer :=
  { p with
    outgoingPeerId               := Constants.maximumPeerId
    incomingSessionId            := 0xFF
    outgoingSessionId            := 0xFF
    connectId                    := 0
    state                        := .disconnected
    channels                     := Array.replicate p.channels.size Channel.init
    unsequencedWindow            := UnsequencedWindow.init
    roundTripTime                := Constants.defaultRoundTripTime
    roundTripTimeVariance        := 0
    lowestRoundTripTime          := Constants.defaultRoundTripTime
    highestRoundTripTimeVariance := 0
    lastReceiveTime              := 0
    lastSendTime                 := 0
    nextTimeout                  := 0
    earliestTimeout              := 0
    packetThrottle               := Constants.defaultPacketThrottle
    packetThrottleLimit          := Constants.packetThrottleScale
    packetThrottleCounter        := 0
    packetThrottleEpoch          := 0
    reliableDataInTransit        := 0
    eventData                    := 0
    outgoingCommands             := #[]
    sentReliableCommands         := #[]
    acknowledgements             := #[]
  }

/-- Queues an outgoing command for transmission. -/
def queueOutgoingCommand (p : Peer) (cmd : OutgoingCommand) : Peer :=
  { p with outgoingCommands := p.outgoingCommands.push cmd }

/-- Queues an acknowledgment (channelId, reliableSequenceNumber, sentTime) to be sent to this peer. -/
def queueAck (p : Peer) (channelId : UInt8) (seq : UInt16) (sentTime : UInt16) : Peer :=
  { p with acknowledgements := p.acknowledgements.push (channelId, seq, sentTime) }

/--
Removes an in-flight reliable command upon receiving its acknowledgment.
Releases the channel's sliding window slot and decrements `reliableDataInTransit`.
-/
def removeSentReliableCommand (p : Peer) (channelId : UInt8) (seq : UInt16) : Peer × Option Protocol.Command :=
  let idx? := p.sentReliableCommands.findIdx? fun outCmd =>
    outCmd.command.channelId == channelId && outCmd.command.reliableSequenceNumber == seq

  match idx? with
  | some idx =>
    let outCmd := p.sentReliableCommands[idx]?.getD default
    let remainingCommands :=
      if h : idx < p.sentReliableCommands.size then
        p.sentReliableCommands.eraseIdx idx
      else
        p.sentReliableCommands

    -- Release window slot on the channel:
    let chIdx := channelId.toNat
    let newChannels :=
      if h : chIdx < p.channels.size then
        let ch := p.channels[chIdx]
        p.channels.set chIdx (ch.releaseReliableWindow seq) h
      else
        p.channels

    let inTransit :=
      if p.reliableDataInTransit ≥ outCmd.fragmentLength then
        p.reliableDataInTransit - outCmd.fragmentLength
      else
        0

    let updatedPeer := { p with
      sentReliableCommands  := remainingCommands
      channels              := newChannels
      reliableDataInTransit := inTransit
    }
    (updatedPeer, some outCmd.command)
  | none =>
    (p, none)

/--
Queues a user packet to be sent on the specified channel of this peer.
Automatically fragments packets exceeding the channel MTU into individual fragment commands.
-/
def send (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) : Except String Peer := do
  if p.state ≠ .connected then
    throw "Cannot send packet: peer is not connected"
  if channelId.toNat ≥ p.channels.size then
    throw s!"Invalid channel ID {channelId} (peer has {p.channels.size} channels)"

  let channel := p.channels[channelId.toNat]?.getD Channel.init
  let headerOverhead : Nat := 4 + (if hasChecksum then 4 else 0)
  let fragmentOverhead : Nat := headerOverhead + 28
  let maxPayload : Nat := if p.mtu.toNat > fragmentOverhead then p.mtu.toNat - fragmentOverhead else 500

  if packet.data.size > maxPayload then
    -- Fragmented packet send
    let fragmentLength := maxPayload
    let fragmentCount := (packet.data.size + fragmentLength - 1) / fragmentLength

    if fragmentCount > Constants.maximumFragmentCount then
      throw "Packet exceeds maximum allowable fragment count"

    let isUnreliableFrag := packet.delivery == .unreliableFragment
    let (ch', startSeq) :=
      if isUnreliableFrag then
        channel.nextUnreliableSequenceNumber
      else
        channel.nextReliableSequenceNumber

    let newChannels :=
      if h : channelId.toNat < p.channels.size then
        p.channels.set channelId.toNat ch' h
      else
        p.channels

    let mut updatedPeer := { p with channels := newChannels }

    for i in [0:fragmentCount] do
      let offset := i * fragmentLength
      let len := Nat.min fragmentLength (packet.data.size - offset)
      let chunk := packet.data.extract offset (offset + len)

      let fragParams : Protocol.FragmentParams := {
        startSequenceNumber := startSeq
        fragmentCount       := fragmentCount.toUInt32
        fragmentNumber      := i.toUInt32
        totalLength         := packet.data.size.toUInt32
        fragmentOffset      := offset.toUInt32
        data                := chunk
      }

      let cmdBody : Protocol.CommandBody :=
        if isUnreliableFrag then
          .sendUnreliableFragment fragParams
        else
          .sendFragment fragParams

      let cmd : Protocol.Command := {
        channelId
        reliableSequenceNumber := if isUnreliableFrag then 0 else startSeq
        acknowledge            := !isUnreliableFrag
        unsequenced            := false
        body                   := cmdBody
      }

      let outCmd : OutgoingCommand := {
        command        := cmd
        fragmentOffset := offset
        fragmentLength := len
      }
      updatedPeer := updatedPeer.queueOutgoingCommand outCmd

    return updatedPeer
  else
    -- Unfragmented single command send
    let (ch', cmd) := match packet.delivery with
      | .reliable =>
        let (ch, seq) := channel.nextReliableSequenceNumber
        (ch, {
          channelId
          reliableSequenceNumber := seq
          acknowledge            := true
          unsequenced            := false
          body                   := .sendReliable packet.data
        })
      | .unreliable =>
        let (ch, unseq) := channel.nextUnreliableSequenceNumber
        (ch, {
          channelId
          reliableSequenceNumber := ch.outgoingReliableSequenceNumber
          acknowledge            := false
          unsequenced            := false
          body                   := .sendUnreliable unseq packet.data
        })
      | .unsequenced =>
        (channel, {
          channelId
          reliableSequenceNumber := 0
          acknowledge            := false
          unsequenced            := true
          body                   := .sendUnsequenced 0 packet.data
        })
      | .unreliableFragment =>
        let (ch, unseq) := channel.nextUnreliableSequenceNumber
        (ch, {
          channelId
          reliableSequenceNumber := ch.outgoingReliableSequenceNumber
          acknowledge            := false
          unsequenced            := false
          body                   := .sendUnreliable unseq packet.data
        })

    let newChannels :=
      if h : channelId.toNat < p.channels.size then
        p.channels.set channelId.toNat ch' h
      else
        p.channels

    let outCmd : OutgoingCommand := {
      command        := cmd
      fragmentOffset := 0
      fragmentLength := packet.data.size
    }
    return ({ p with channels := newChannels }).queueOutgoingCommand outCmd

/--
Dynamically updates the packet throttle based on current round trip time.
-/
def throttle (p : Peer) (rtt : UInt32) : Peer :=
  if p.lastRoundTripTime ≤ p.lastRoundTripTimeVariance then
    { p with packetThrottle := p.packetThrottleLimit }
  else if rtt ≤ p.lastRoundTripTime then
    let newThrottle := p.packetThrottle + p.packetThrottleAcceleration
    let clamped := if newThrottle > p.packetThrottleLimit then p.packetThrottleLimit else newThrottle
    { p with packetThrottle := clamped }
  else if rtt > p.lastRoundTripTime + 2 * p.lastRoundTripTimeVariance then
    let clamped :=
      if p.packetThrottle > p.packetThrottleDeceleration then
        p.packetThrottle - p.packetThrottleDeceleration
      else
        0
    { p with packetThrottle := clamped }
  else
    p

/--
Updates smoothed round trip time and variance calculations upon receiving an acknowledgment.
-/
def updateRtt (p : Peer) (now : UInt32) (rtt : UInt32) : Peer :=
  let sampleRtt := if rtt == 0 then (1 : UInt32) else rtt
  let pThrottled := if p.lastReceiveTime > 0 then p.throttle sampleRtt else p

  let (newRtt, newVar) :=
    if p.lastReceiveTime > 0 then
      let curVar := pThrottled.roundTripTimeVariance - (pThrottled.roundTripTimeVariance / 4)
      if sampleRtt ≥ pThrottled.roundTripTime then
        let diff := sampleRtt - pThrottled.roundTripTime
        (pThrottled.roundTripTime + diff / 8, curVar + diff / 4)
      else
        let diff := pThrottled.roundTripTime - sampleRtt
        (pThrottled.roundTripTime - diff / 8, curVar + diff / 4)
    else
      (sampleRtt, (sampleRtt + 1) / 2)

  let lowestRtt := if newRtt < pThrottled.lowestRoundTripTime then newRtt else pThrottled.lowestRoundTripTime
  let highestVar := if newVar > pThrottled.highestRoundTripTimeVariance then newVar else pThrottled.highestRoundTripTimeVariance

  let pEpoch :=
    if pThrottled.packetThrottleEpoch == 0 ∨ Time.difference now pThrottled.packetThrottleEpoch ≥ pThrottled.packetThrottleInterval then
      { pThrottled with
        lastRoundTripTime            := lowestRtt
        lastRoundTripTimeVariance    := if highestVar == 0 then (1 : UInt32) else highestVar
        lowestRoundTripTime          := newRtt
        highestRoundTripTimeVariance := newVar
        packetThrottleEpoch          := now
      }
    else
      pThrottled

  { pEpoch with
    roundTripTime                := newRtt
    roundTripTimeVariance        := newVar
    lowestRoundTripTime          := lowestRtt
    highestRoundTripTimeVariance := highestVar
    lastReceiveTime              := if now == 0 then (1 : UInt32) else now
    earliestTimeout              := 0
  }

/--
Checks whether a peer has exceeded timeout limits on unacknowledged reliable commands.
-/
def isTimedOut (p : Peer) (now : UInt32) (sendAttempts : Nat) : Bool :=
  if p.earliestTimeout == 0 then
    false
  else
    let elapsed := Time.difference now p.earliestTimeout
    let attemptThreshold := (1 : UInt32) <<< (if sendAttempts == 0 then 0 else (sendAttempts - 1).toUInt32)
    elapsed ≥ p.timeoutMaximum ∨ (attemptThreshold ≥ p.timeoutLimit ∧ elapsed ≥ p.timeoutMinimum)

end Peer

end Lenet