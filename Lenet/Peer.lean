import Lenet.Constants
import Lenet.Time
import Lenet.Address
import Lenet.Channel
import Lenet.Unsequenced
import Lenet.Reassembly
import Lenet.Packet
import Lenet.OutgoingCommand
import Lenet.Event

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
  /-- ENet: marks peers already bandwidth-adjusted within the current
  bandwidth-throttle epoch (incomingBandwidthThrottleEpoch). -/
  incomingBandwidthThrottleEpoch : UInt32 := 0
  eventData                      : UInt32 := 0
  reliableDataInTransit          : Nat := 0
  /-- Sequence counter for reliable control commands sent on channel 0xFF
  (connect/verifyConnect/disconnect/ping). ENet uses `channels[0xFF]`, which is
  out of bounds but in practice acts as a persistent counter starting at 0. -/
  outgoingControlSeq             : UInt16 := 0
  /-- Group number assigned to outgoing unsequenced packets (pre-incremented,
  so the first unsequenced packet is group 1, matching ENet). -/
  outgoingUnsequencedGroup       : UInt16 := 0
  outgoingCommands               : Array OutgoingCommand := #[]
  sentReliableCommands           : Array OutgoingCommand := #[]
  acknowledgements               : Array (UInt8 × UInt16 × UInt16) := #[]
  fragmentAssemblers             : Array FragmentAssembler := #[]
deriving BEq, Inhabited

namespace Peer

/-- Creates an initialized peer allocated with `channelCount` channels. -/
def create (peerId : UInt16) (channelCount : Nat := 1) (address : Address := {}) : Peer :=
  let channels := Array.replicate channelCount Channel.init
  {
    peerId
    address
    channels
    mtu := Constants.defaultMtu.toUInt32
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
    incomingBandwidthThrottleEpoch := 0
    reliableDataInTransit        := 0
    outgoingControlSeq           := 0
    outgoingUnsequencedGroup     := 0
    eventData                    := 0
    outgoingCommands             := #[]
    sentReliableCommands         := #[]
    acknowledgements             := #[]
    fragmentAssemblers           := #[]
  }

/-- Queues an outgoing command for transmission. -/
def queueOutgoingCommand (p : Peer) (cmd : OutgoingCommand) : Peer :=
  { p with outgoingCommands := p.outgoingCommands.push cmd }

/-- Pre-increments and returns the control-command sequence number (channel 0xFF). -/
def nextControlSeq (p : Peer) : Peer × UInt16 :=
  let next := p.outgoingControlSeq + 1
  ({ p with outgoingControlSeq := next }, next)

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
  -- ENet: mtu - sizeof(ENetProtocolHeader) - sizeof(ENetProtocolSendFragment)
  -- (4-byte protocol header + 24-byte fragment command incl. its 4-byte header)
  let fragmentOverhead : Nat := headerOverhead + 24
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

    -- ENet queues every fragment through setup_outgoing_command, which
    -- increments the channel's reliable counter per fragment: fragment i
    -- carries reliableSequenceNumber = startSeq + i (reliable fragments),
    -- while unreliable fragments all share the channel's current reliable
    -- sequence number.
    let endChannel : Channel :=
      if isUnreliableFrag then
        ch' -- unreliable counter already advanced once
      else
        { ch' with
          outgoingReliableSequenceNumber :=
            startSeq + (fragmentCount - 1).toUInt16
          outgoingUnreliableSequenceNumber := 0 }

    let newChannels :=
      if h : channelId.toNat < p.channels.size then
        p.channels.set channelId.toNat endChannel h
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
        reliableSequenceNumber :=
          if isUnreliableFrag then channel.outgoingReliableSequenceNumber
          else startSeq + i.toUInt16
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
    let (p2, ch', cmd) := match packet.delivery with
      | .reliable =>
        let (ch, seq) := channel.nextReliableSequenceNumber
        (p, ch, ({
          channelId
          reliableSequenceNumber := seq
          acknowledge            := true
          unsequenced            := false
          body                   := .sendReliable packet.data
        } : Protocol.Command))
      | .unreliable =>
        let (ch, unseq) := channel.nextUnreliableSequenceNumber
        (p, ch, ({
          channelId
          reliableSequenceNumber := ch.outgoingReliableSequenceNumber
          acknowledge            := false
          unsequenced            := false
          body                   := .sendUnreliable unseq packet.data
        } : Protocol.Command))
      | .unsequenced =>
        -- ENet pre-increments the peer-level unsequenced group (first = 1).
        let group := p.outgoingUnsequencedGroup + 1
        ({ p with outgoingUnsequencedGroup := group },
          channel,
          ({
            channelId
            reliableSequenceNumber := 0
            acknowledge            := false
            unsequenced            := true
            body                   := .sendUnsequenced group packet.data
          } : Protocol.Command))
      | .unreliableFragment =>
        let (ch, unseq) := channel.nextUnreliableSequenceNumber
        (p, ch, ({
          channelId
          reliableSequenceNumber := ch.outgoingReliableSequenceNumber
          acknowledge            := false
          unsequenced            := false
          body                   := .sendUnreliable unseq packet.data
        } : Protocol.Command))

    let newChannels :=
      if h : channelId.toNat < p2.channels.size then
        p2.channels.set channelId.toNat ch' h
      else
        p2.channels

    let outCmd : OutgoingCommand := {
      command        := cmd
      fragmentOffset := 0
      fragmentLength := packet.data.size
    }
    return ({ p2 with channels := newChannels }).queueOutgoingCommand outCmd

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

/--
Processes a single incoming protocol command received from this peer.
- Automatically queues an ACK if the command requested acknowledgment.
- Updates RTT, sliding window state, and fragment assembly.
- Returns the updated `Peer` and any high-level `Event`s produced.
-/
def handleCommand (p : Peer) (now : UInt32) (cmd : Protocol.Command) (sentTime : Option UInt16) : Peer × Array Event :=
  -- 1. Queue ACK if required:
  let pAck :=
    if cmd.acknowledge then
      if let some st := sentTime then
        p.queueAck cmd.channelId cmd.reliableSequenceNumber st
      else
        p
    else
      p

  -- 2. Process command body:
  match cmd.body with
  | .acknowledge recvSeq recvTime =>
    let sampleRtt := Time.difference now recvTime.toUInt32
    let pRtt := pAck.updateRtt now sampleRtt
    let (pRemoved, removedCmd?) := pRtt.removeSentReliableCommand cmd.channelId recvSeq

    match pRemoved.state, removedCmd? with
    | .acknowledgingConnect, some removedCmd =>
      if removedCmd.body.commandNumber == Constants.commandVerifyConnect then
        ({ pRemoved with state := .connected }, #[Event.connect pRemoved.peerId pRemoved.eventData])
      else
        (pRemoved, #[])
    | .disconnecting, some removedCmd =>
      if removedCmd.body.commandNumber == Constants.commandDisconnect then
        -- ENet's notify_disconnect always reports data = 0 here.
        ({ pRemoved with state := .zombie }, #[Event.disconnect pRemoved.peerId 0])
      else
        (pRemoved, #[])
    | .disconnectLater, _ =>
      if pRemoved.outgoingCommands.isEmpty ∧ pRemoved.sentReliableCommands.isEmpty then
        ({ pRemoved with state := .disconnecting }, #[])
      else
        (pRemoved, #[])
    | _, _ =>
      (pRemoved, #[])

  | .ping =>
    (pAck, #[])

  | .sendReliable data =>
    if pAck.state ≠ .connected ∧ pAck.state ≠ .disconnectLater then
      (pAck, #[])
    else
      let chIdx := cmd.channelId.toNat
      if h : chIdx < pAck.channels.size then
        let ch := pAck.channels[chIdx]
        let (ch', delivered) := ch.receiveReliable cmd.reliableSequenceNumber (Packet.reliable data)
        let newChannels := pAck.channels.set chIdx ch' h
        let events := delivered.map (fun pkt => Event.receive pAck.peerId cmd.channelId pkt)
        ({ pAck with channels := newChannels }, events)
      else
        (pAck, #[])

  | .sendUnreliable unseq data =>
    if pAck.state ≠ .connected ∧ pAck.state ≠ .disconnectLater then
      (pAck, #[])
    else
      let chIdx := cmd.channelId.toNat
      if h : chIdx < pAck.channels.size then
        let ch := pAck.channels[chIdx]
        let (ch', deliveredOpt) := ch.receiveUnreliable unseq (Packet.unreliable data)
        let newChannels := pAck.channels.set chIdx ch' h
        let events := match deliveredOpt with
          | some pkt => #[Event.receive pAck.peerId cmd.channelId pkt]
          | none     => #[]
        ({ pAck with channels := newChannels }, events)
      else
        (pAck, #[])

  | .sendUnsequenced group data =>
    if pAck.state ≠ .connected ∧ pAck.state ≠ .disconnectLater then
      (pAck, #[])
    else
      match pAck.unsequencedWindow.checkAndAdd group with
      | some newWin =>
        let updatedPeer := { pAck with unsequencedWindow := newWin }
        (updatedPeer, #[Event.receive pAck.peerId cmd.channelId (Packet.unsequenced data)])
      | none =>
        (pAck, #[])

  | .sendFragment params =>
    if pAck.state ≠ .connected ∧ pAck.state ≠ .disconnectLater then
      (pAck, #[])
    else
      let startSeq := params.startSequenceNumber
      let existingIdx? := pAck.fragmentAssemblers.findIdx? fun a => a.startSequenceNumber == startSeq

      let (assemblers, assembler) := match existingIdx? with
        | some idx =>
          (pAck.fragmentAssemblers, pAck.fragmentAssemblers[idx]?.getD default)
        | none =>
          match FragmentAssembler.init startSeq params.totalLength.toNat params.fragmentCount.toNat with
          | .ok newAsm => (pAck.fragmentAssemblers.push newAsm, newAsm)
          | .error _   => (pAck.fragmentAssemblers, default)

      match assembler.addFragment params.fragmentNumber.toNat params.fragmentOffset.toNat params.data with
      | .ok (updatedAsm, some fullData) =>
        let cleanAssemblers := assemblers.filter (fun a => a.startSequenceNumber ≠ startSeq)
        let pClean := { pAck with fragmentAssemblers := cleanAssemblers }
        let chIdx := cmd.channelId.toNat
        if h : chIdx < pClean.channels.size then
          let ch := pClean.channels[chIdx]
          let (ch', delivered) := ch.receiveReliable startSeq (Packet.reliable fullData)
          let newChannels := pClean.channels.set chIdx ch' h
          let events := delivered.map (fun pkt => Event.receive pClean.peerId cmd.channelId pkt)
          ({ pClean with channels := newChannels }, events)
        else
          (pClean, #[])
      | .ok (updatedAsm, none) =>
        let updatedList := assemblers.map (fun a => if a.startSequenceNumber == startSeq then updatedAsm else a)
        ({ pAck with fragmentAssemblers := updatedList }, #[])
      | .error _ =>
        (pAck, #[])

  | .sendUnreliableFragment params =>
    if pAck.state ≠ .connected ∧ pAck.state ≠ .disconnectLater then
      (pAck, #[])
    else
      let startSeq := params.startSequenceNumber
      let existingIdx? := pAck.fragmentAssemblers.findIdx? fun a => a.startSequenceNumber == startSeq

      let (assemblers, assembler) := match existingIdx? with
        | some idx =>
          (pAck.fragmentAssemblers, pAck.fragmentAssemblers[idx]?.getD default)
        | none =>
          match FragmentAssembler.init startSeq params.totalLength.toNat params.fragmentCount.toNat with
          | .ok newAsm => (pAck.fragmentAssemblers.push newAsm, newAsm)
          | .error _   => (pAck.fragmentAssemblers, default)

      match assembler.addFragment params.fragmentNumber.toNat params.fragmentOffset.toNat params.data with
      | .ok (updatedAsm, some fullData) =>
        let cleanAssemblers := assemblers.filter (fun a => a.startSequenceNumber ≠ startSeq)
        let pClean := { pAck with fragmentAssemblers := cleanAssemblers }
        let chIdx := cmd.channelId.toNat
        if h : chIdx < pClean.channels.size then
          let ch := pClean.channels[chIdx]
          let (ch', deliveredOpt) := ch.receiveUnreliable startSeq (Packet.unreliableFragment fullData)
          let newChannels := pClean.channels.set chIdx ch' h
          let events := match deliveredOpt with
            | some pkt => #[Event.receive pClean.peerId cmd.channelId pkt]
            | none     => #[]
          ({ pClean with channels := newChannels }, events)
        else
          (pClean, #[])
      | .ok (updatedAsm, none) =>
        let updatedList := assemblers.map (fun a => if a.startSequenceNumber == startSeq then updatedAsm else a)
        ({ pAck with fragmentAssemblers := updatedList }, #[])
      | .error _ =>
        (pAck, #[])

  | .disconnect data =>
    ({ pAck with state := .zombie, eventData := data }, #[Event.disconnect pAck.peerId data])

  | .bandwidthLimit inBw outBw =>
    -- ENet recomputes the peer's windowSize here too (handle_bandwidth_limit),
    -- but that needs the *host's* outgoing bandwidth, so the recompute happens
    -- at host level after the command fold (see Host.handleDatagram).
    ({ pAck with incomingBandwidth := inBw, outgoingBandwidth := outBw }, #[])

  | .throttleConfigure interval accel decel =>
    ({ pAck with
       packetThrottleInterval     := interval
       packetThrottleAcceleration := accel
       packetThrottleDeceleration := decel
    }, #[])

  | .verifyConnect params =>
    -- Client side: the server's VERIFY_CONNECT completes the handshake
    -- (ENet: enet_protocol_handle_verify_connect).
    if pAck.state == .connecting then
      -- ENet removes the client's CONNECT from the sent-reliable list here
      -- (nothing ever ACKs it - the VERIFY_CONNECT replaces it).
      let (pRm, _) := pAck.removeSentReliableCommand 0xFF 1
      -- ENet clamps the received windowSize to [min, max] and only shrinks
      -- the peer's own (bandwidth-derived) window to match.
      let ws := Nat.min Constants.maximumWindowSize (Nat.max Constants.minimumWindowSize params.windowSize.toNat)
      let p' := { pRm with
        outgoingPeerId      := params.outgoingPeerId
        incomingSessionId   := params.incomingSessionId
        outgoingSessionId   := params.outgoingSessionId
        connectId           := params.connectId
        mtu                 := params.mtu
        windowSize          := Nat.min pRm.windowSize.toNat ws |>.toUInt32
        incomingBandwidth   := params.incomingBandwidth
        outgoingBandwidth   := params.outgoingBandwidth
        state               := .connected
      }
      (p', #[Event.connect p'.peerId p'.eventData])
    else
      (pAck, #[])

  | .connect .. =>
    -- A CONNECT for an existing peer is invalid; ignore (ENet does the same).
    (pAck, #[])

end Peer

end Lenet