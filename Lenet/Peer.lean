import Lenet.Constants
import Lenet.Time
import Lenet.Address
import Lenet.Error
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

/-- Resets the peer back to disconnected state, clearing channels and sequence numbers.
ENet's enet_peer_reset does NOT reset the session IDs: a reused slot keeps the
previously negotiated sessions (fresh slots start at 0xFF from host creation). -/
def reset (p : Peer) : Peer :=
  { p with
    outgoingPeerId               := Constants.maximumPeerId
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

/-- Queues the graceful-disconnect DISCONNECT command (control channel 0xFF)
and enters the `disconnecting` state (ENet's enet_peer_disconnect). -/
def queueDisconnect (p : Peer) (data : UInt32) : Peer :=
  let (p, controlSeq) := p.nextControlSeq
  let cmd : Protocol.Command := {
    channelId              := 0xFF
    reliableSequenceNumber := controlSeq
    acknowledge            := true
    unsequenced            := false
    body                   := .disconnect data
  }
  { p with state := .disconnecting, eventData := data }
    |>.queueOutgoingCommand { command := cmd }

/-- Queues an acknowledgment (channelId, reliableSequenceNumber, sentTime) to be sent to this peer. -/
def queueAck (p : Peer) (channelId : UInt8) (seq : UInt16) (sentTime : UInt16) : Peer :=
  { p with acknowledgements := p.acknowledgements.push (channelId, seq, sentTime) }

/--
Removes an in-flight reliable command upon receiving its acknowledgment.
Releases the channel's sliding window slot and decrements `reliableDataInTransit`.
-/
def removeSentReliableCommand (p : Peer) (channelId : UInt8) (seq : UInt16) : Peer × Option Protocol.Command :=
  match p.sentReliableCommands.find? fun outCmd =>
      outCmd.command.channelId == channelId && outCmd.command.reliableSequenceNumber == seq with
  | none =>
    (p, none)
  | some outCmd =>
    -- Release window slot on the channel:
    let newChannels :=
      if h : channelId.toNat < p.channels.size then
        let ch := p.channels[channelId.toNat]
        p.channels.set channelId.toNat (ch.releaseReliableWindow seq) h
      else
        p.channels

    let inTransit :=
      if p.reliableDataInTransit ≥ outCmd.fragmentLength then
        p.reliableDataInTransit - outCmd.fragmentLength
      else
        0

    let updatedPeer := { p with
      sentReliableCommands  := p.sentReliableCommands.erase outCmd
      channels              := newChannels
      reliableDataInTransit := inTransit
    }
    (updatedPeer, some outCmd.command)

/--
Queues a user packet to be sent on the specified channel of this peer.
Automatically fragments packets exceeding the channel MTU into individual fragment commands.
-/
def send (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) : Except LenetError Peer := do
  if p.state ≠ .connected then
    throw (.peerNotConnected p.peerId)
  if h : channelId.toNat < p.channels.size then
    let channel := p.channels[channelId.toNat]
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
        throw (.tooManyFragments packet.data.size)

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

      let newChannels := p.channels.set channelId.toNat endChannel h

      let fragments : List OutgoingCommand :=
        (List.range fragmentCount).map fun i =>
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

          { command := {
              channelId
              reliableSequenceNumber :=
                if isUnreliableFrag then channel.outgoingReliableSequenceNumber
                else startSeq + i.toUInt16
              acknowledge            := !isUnreliableFrag
              unsequenced            := false
              body                   := cmdBody
            }
            fragmentOffset := offset
            fragmentLength := len }

      let updatedPeer :=
        fragments.foldl (init := { p with channels := newChannels })
          fun peer outCmd => peer.queueOutgoingCommand outCmd
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

      -- `ch'` is the channel's post-send state (unchanged for unsequenced).
      let newChannels := p.channels.set channelId.toNat ch' h

      let outCmd : OutgoingCommand := {
        command        := cmd
        fragmentOffset := 0
        fragmentLength := packet.data.size
      }
      return ({ p2 with channels := newChannels }).queueOutgoingCommand outCmd
  else
    throw (.invalidChannelId p.peerId channelId p.channels.size)

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
`earliestTimeout` is the *updated* earliest timeout (ENet updates
`peer->earliestTimeout` within the same check_timeouts iteration and then
evaluates the condition against the fresh value).
-/
def isTimedOut (p : Peer) (now : UInt32) (earliestTimeout : UInt32) (sendAttempts : Nat) : Bool :=
  if earliestTimeout == 0 then
    false
  else
    let elapsed := Time.difference now earliestTimeout
    let attemptThreshold := (1 : UInt32) <<< (if sendAttempts == 0 then 0 else (sendAttempts - 1).toUInt32)
    elapsed ≥ p.timeoutMaximum ∨ (attemptThreshold ≥ p.timeoutLimit ∧ elapsed ≥ p.timeoutMinimum)

/-- ENet processes incoming data commands only in these states
(protocol.c `handle_command`: CONNECTED or DISCONNECT_LATER). -/
def acceptsTraffic (p : Peer) : Bool :=
  p.state == .connected ∨ p.state == .disconnectLater

/-- Absorbs a fragment into the assembler array: finds the assembler for
`params.startSequenceNumber` (creating one when below the concurrency cap
`maximumFragmentAssemblers` and the fragment count is within
`maximumReceivedFragmentCount` - robustness guards, DESIGN.md 1.5,
deliberately stricter than ENet whose pending-assembler growth is bounded
only by its window span). Returns the (possibly grown) array and the
assembler to deliver to. -/
def absorbFragment (xs : Array FragmentAssembler) (params : Protocol.FragmentParams) :
    Array FragmentAssembler × Option FragmentAssembler :=
  match xs.find? (fun a => a.startSequenceNumber == params.startSequenceNumber) with
  | some asm => (xs, some asm)
  | none =>
    if xs.size ≥ Constants.maximumFragmentAssemblers ∨
        params.fragmentCount.toNat > Constants.maximumReceivedFragmentCount then
      (xs, none)
    else
      match FragmentAssembler.init params.startSequenceNumber params.totalLength.toNat
          params.fragmentCount.toNat with
      | .ok newAsm => (xs.push newAsm, some newAsm)
      | .error _ => (xs, none)

/-- The assembler array after delivering a fragment result: the matching
assembler is updated in place while the assembly is partial, and filtered
out when it completes. `none` (no assembler, e.g. cap-rejected or invalid
parameters) leaves the array unchanged. -/
def assemblerArrayAfterDeliver (xs : Array FragmentAssembler)
    (params : Protocol.FragmentParams)
    (result : Option (Except CodecError (FragmentAssembler × Option ByteArray))) :
    Array FragmentAssembler :=
  match result with
  | none => xs
  | some (.error _) => xs
  | some (.ok (updatedAsm, none)) =>
    xs.map (fun a => if a.startSequenceNumber == params.startSequenceNumber then updatedAsm else a)
  | some (.ok (_, some _)) =>
    xs.filter (fun a => a.startSequenceNumber ≠ params.startSequenceNumber)

/-- Delivers a fragment to the (possibly newly created) assembler for
`params.startSequenceNumber` and returns the updated peer with any receive
event fired on assembly completion. Fragments with invalid parameters (which
ENet validates identically on receipt) are dropped. -/
def handleFragment (p : Peer) (channelId : UInt8) (params : Protocol.FragmentParams)
    (unreliable : Bool) : Peer × Array Event :=
  let (xs, assembler?) := absorbFragment p.fragmentAssemblers params
  let result : Option (Except CodecError (FragmentAssembler × Option ByteArray)) :=
    assembler?.bind
      (fun asm => asm.addFragment params.fragmentNumber.toNat params.fragmentOffset.toNat params.data)
  let p' := { p with fragmentAssemblers := assemblerArrayAfterDeliver xs params result }
  match result with
  | some (.ok (_, some fullData)) =>
    -- Assembly complete: the assembler is consumed and the reassembled
    -- payload goes through the channel's reliable/unreliable receive path.
    let chIdx := channelId.toNat
    if h : chIdx < p'.channels.size then
      let ch := p'.channels[chIdx]
      let (ch', events) :=
        if unreliable then
          let (ch', deliveredOpt) := ch.receiveUnreliable params.startSequenceNumber (Packet.unreliableFragment fullData)
          (ch', deliveredOpt.map (fun pkt => Event.receive p'.peerId channelId pkt) |>.toArray)
        else
          let (ch', delivered) := ch.receiveReliable params.startSequenceNumber (Packet.reliable fullData)
          (ch', delivered.map (fun pkt => Event.receive p'.peerId channelId pkt))
      ({ p' with channels := p'.channels.set chIdx ch' h }, events)
    else
      (p', #[])
  | _ => (p', #[])

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
        -- ENet's notify_disconnect: event (data = 0) + enet_peer_reset, so
        -- the slot is immediately reusable for a new connection.
        (Peer.reset pRemoved, #[Event.disconnect pRemoved.peerId 0])
      else
        (pRemoved, #[])
    | .disconnectLater, _ =>
      -- ENet (handle_acknowledge): once the acks have drained, queue the
      -- actual DISCONNECT (en_peer_disconnect) carrying the deferred data.
      if pRemoved.outgoingCommands.isEmpty ∧ pRemoved.sentReliableCommands.isEmpty then
        (pRemoved.queueDisconnect pRemoved.eventData, #[])
      else
        (pRemoved, #[])
    | _, _ =>
      (pRemoved, #[])

  | .ping =>
    (pAck, #[])

  | .sendReliable data =>
    if pAck.acceptsTraffic then
      let chIdx := cmd.channelId.toNat
      if h : chIdx < pAck.channels.size then
        let ch := pAck.channels[chIdx]
        let (ch', delivered) := ch.receiveReliable cmd.reliableSequenceNumber (Packet.reliable data)
        let newChannels := pAck.channels.set chIdx ch' h
        let events := delivered.map (fun pkt => Event.receive pAck.peerId cmd.channelId pkt)
        ({ pAck with channels := newChannels }, events)
      else
        (pAck, #[])
    else
      (pAck, #[])

  | .sendUnreliable unseq data =>
    if pAck.acceptsTraffic then
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
    else
      (pAck, #[])

  | .sendUnsequenced group data =>
    if pAck.acceptsTraffic then
      match pAck.unsequencedWindow.checkAndAdd group with
      | some newWin =>
        let updatedPeer := { pAck with unsequencedWindow := newWin }
        (updatedPeer, #[Event.receive pAck.peerId cmd.channelId (Packet.unsequenced data)])
      | none =>
        (pAck, #[])
    else
      (pAck, #[])

  | .sendFragment params =>
    if pAck.acceptsTraffic then
      handleFragment pAck cmd.channelId params (unreliable := false)
    else
      (pAck, #[])

  | .sendUnreliableFragment params =>
    if pAck.acceptsTraffic then
      handleFragment pAck cmd.channelId params (unreliable := true)
    else
      (pAck, #[])

  | .disconnect data =>
    -- ENet enet_protocol_handle_disconnect:
    -- - already disconnecting/zombie/acknowledgingDisconnect: ignore
    -- - connected/disconnectLater + ack-flagged: ACKNOWLEDGING_DISCONNECT;
    --   the ACK goes out at the next pack and the peer resets once the acks
    --   have drained (Host.pollPeer - ENet dispatches ZOMBIE in
    --   send_acknowledgements and resets when the event is dispatched).
    -- - other states: ZOMBIE-equivalent immediately (event + reset).
    if pAck.state == .disconnected ∨ pAck.state == .zombie ∨ pAck.state == .acknowledgingDisconnect then
      (pAck, #[])
    else if pAck.state == .connected ∨ pAck.state == .disconnectLater then
      ({ pAck with state := .acknowledgingDisconnect, eventData := data }, #[])
    else
      (Peer.reset { pAck with eventData := data }, #[Event.disconnect pAck.peerId data])

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