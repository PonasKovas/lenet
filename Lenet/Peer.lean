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

/-- Lifecycle of an ENet peer connection (ENet's `ENetPeerState`, minus the
two states that only exist for ENet's deferred event dispatch). -/
inductive PeerState where
  | disconnected
  /-- Client: CONNECT sent, waiting for the VERIFY_CONNECT. -/
  | connecting
  /-- Server: VERIFY_CONNECT sent, waiting for its ACK. -/
  | acknowledgingConnect
  | connected
  | disconnectLater
  | disconnecting
  | acknowledgingDisconnect
  | zombie
deriving Repr, BEq, DecidableEq, Inhabited

/-- An acknowledgement owed to the remote peer: echoes the acknowledged
command's channel and reliable sequence number, and the sent time from the
datagram header it arrived in. -/
structure Acknowledgement where
  channelId              : UInt8
  reliableSequenceNumber : UInt16
  sentTime               : UInt16
deriving BEq, Inhabited

/-- One peer slot of a host: connection state, channels, RTT estimate,
packet throttle and the command queues. -/
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
  mtu                            : UInt32 := Constants.defaultMtu.toUInt32
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
  earliestTimeout                : UInt32 := 0
  pingInterval                   : UInt32 := Constants.defaultPingInterval
  timeoutLimit                   : UInt32 := Constants.defaultTimeoutLimit
  timeoutMinimum                 : UInt32 := Constants.defaultTimeoutMinimum
  timeoutMaximum                 : UInt32 := Constants.defaultTimeoutMaximum
  packetThrottle                 : UInt32 := Constants.defaultPacketThrottle
  packetThrottleLimit            : UInt32 := Constants.packetThrottleScale
  packetThrottleEpoch            : UInt32 := 0
  packetThrottleAcceleration     : UInt32 := Constants.defaultPacketThrottleAcceleration
  packetThrottleDeceleration     : UInt32 := Constants.defaultPacketThrottleDeceleration
  packetThrottleInterval         : UInt32 := Constants.defaultPacketThrottleInterval
  eventData                      : UInt32 := 0
  reliableDataInTransit          : Nat := 0
  /-- Sequence counter of the reliable control commands on channel 0xFF
  (connect, verify, disconnect, ping, bandwidth/throttle configuration);
  ENet's `peer->outgoingReliableSequenceNumber`. -/
  outgoingControlSeq             : UInt16 := 0
  /-- Group number assigned to outgoing unsequenced packets (pre-incremented,
  so the first unsequenced packet is group 1, matching ENet). -/
  outgoingUnsequencedGroup       : UInt16 := 0
  outgoingCommands               : Array OutgoingCommand := #[]
  sentReliableCommands           : Array OutgoingCommand := #[]
  acknowledgements               : Array Acknowledgement := #[]
  fragmentAssemblers             : Array FragmentAssembler := #[]
deriving BEq, Inhabited

namespace Peer

/-- ENet's enet_peer_reset: back to a fresh disconnected slot. Only the
session IDs survive, so a reused slot keeps the previously negotiated
sessions (fresh slots start at 0xFF). -/
def reset (p : Peer) : Peer :=
  { peerId            := p.peerId
    incomingSessionId := p.incomingSessionId
    outgoingSessionId := p.outgoingSessionId }

/-- ENet counts CONNECTED and DISCONNECT_LATER peers as connected: they share
the host's bandwidth, and only they process data commands (protocol.c
handle_incoming_commands). -/
def isConnected (p : Peer) : Bool :=
  p.state == .connected ∨ p.state == .disconnectLater

/-! ## Outgoing commands -/

/-- Queues an outgoing command for transmission. -/
def queueOutgoingCommand (p : Peer) (cmd : OutgoingCommand) : Peer :=
  { p with outgoingCommands := p.outgoingCommands.push cmd }

/-- Queues a reliable control command on channel 0xFF, numbered by the
peer-level control sequence (pre-incremented: the first one is 1). -/
def queueControlCommand (p : Peer) (body : Protocol.CommandBody) : Peer :=
  let seq := p.outgoingControlSeq + 1
  { p with outgoingControlSeq := seq }.queueOutgoingCommand
    { command := { channelId := 0xFF, reliableSequenceNumber := seq, acknowledge := true, body } }

/-- Queues the graceful-disconnect DISCONNECT command and enters the
`disconnecting` state (ENet's enet_peer_disconnect). -/
def queueDisconnect (p : Peer) (data : UInt32) : Peer :=
  { p with state := .disconnecting, eventData := data }.queueControlCommand (.disconnect data)

/-- Queues an acknowledgement for the remote peer. -/
def queueAck (p : Peer) (ack : Acknowledgement) : Peer :=
  { p with acknowledgements := p.acknowledgements.push ack }

/-- Removes the in-flight reliable command `(channelId, seq)` once it is
acknowledged: releases its channel window slot and its in-transit bytes.
Returns the removed command, if there was one. -/
def removeSentReliableCommand (p : Peer) (channelId : UInt8) (seq : UInt16) : Peer × Option Protocol.Command :=
  match p.sentReliableCommands.find? fun outCmd =>
      outCmd.command.channelId == channelId && outCmd.command.reliableSequenceNumber == seq with
  | none => (p, none)
  | some outCmd =>
    ({ p with
      sentReliableCommands  := p.sentReliableCommands.erase outCmd
      channels              := p.channels.modify channelId.toNat (·.releaseReliableWindow seq)
      -- no underflow: these bytes were added when the command was sent
      reliableDataInTransit := p.reliableDataInTransit - outCmd.fragmentLength
    }, some outCmd.command)

/-- Largest payload a single command may carry at this peer's MTU before
the packet is fragmented (ENet enet_peer_send: MTU minus the protocol header,
the SEND_FRAGMENT command and the checksum). The fallback only matters for an
MTU below the protocol minimum, which negotiation never produces. -/
def maxFragmentPayload (p : Peer) (hasChecksum : Bool) : Nat :=
  let overhead := 4 + 24 + (if hasChecksum then 4 else 0)
  if p.mtu.toNat > overhead then p.mtu.toNat - overhead else 500

/-- The fragment commands of `packet` (`fragmentCount` pieces of
`fragmentLength` bytes) and `channel` after numbering them. ENet numbers
every fragment through setup_outgoing_command: reliable fragments take
consecutive reliable sequence numbers starting at the set's start sequence
number, unreliable fragments share one unreliable sequence number and carry
the channel's current reliable sequence number. -/
def fragmentCommands (channel : Channel) (channelId : UInt8) (packet : Packet)
    (fragmentLength fragmentCount : Nat) : Channel × Array OutgoingCommand :=
  let unreliable := packet.delivery == .unreliableFragment
  let (next, startSeq) :=
    if unreliable then channel.nextUnreliableSequenceNumber
    else channel.nextReliableSequenceNumber
  let next :=
    if unreliable then next
    else { next with outgoingReliableSequenceNumber := startSeq + (fragmentCount - 1).toUInt16 }
  let commands := (Array.range fragmentCount).map fun i =>
    let offset := i * fragmentLength
    let chunk := packet.data.extract offset (offset + fragmentLength)
    let params : Protocol.FragmentParams := {
      startSequenceNumber := startSeq
      fragmentCount       := fragmentCount.toUInt32
      fragmentNumber      := i.toUInt32
      totalLength         := packet.data.size.toUInt32
      fragmentOffset      := offset.toUInt32
      data                := chunk
    }
    { command := {
        channelId
        reliableSequenceNumber :=
          if unreliable then channel.outgoingReliableSequenceNumber else startSeq + i.toUInt16
        acknowledge := !unreliable
        body := if unreliable then .sendUnreliableFragment params else .sendFragment params }
      fragmentLength := chunk.size }
  (next, commands)

/-- The single command carrying an unfragmented `packet`, with the peer and
`channel` after numbering it. -/
def packetCommand (p : Peer) (channel : Channel) (channelId : UInt8) (packet : Packet) :
    Peer × Channel × Protocol.Command :=
  match packet.delivery with
  | .reliable =>
    let (channel, seq) := channel.nextReliableSequenceNumber
    (p, channel, { channelId, reliableSequenceNumber := seq, acknowledge := true,
                   body := .sendReliable packet.data })
  | .unreliable | .unreliableFragment =>
    let (channel, seq) := channel.nextUnreliableSequenceNumber
    (p, channel, { channelId, reliableSequenceNumber := channel.outgoingReliableSequenceNumber,
                   body := .sendUnreliable seq packet.data })
  | .unsequenced =>
    -- the unsequenced group is peer-level and pre-incremented (first = 1)
    let group := p.outgoingUnsequencedGroup + 1
    ({ p with outgoingUnsequencedGroup := group }, channel,
      { channelId, reliableSequenceNumber := 0, unsequenced := true,
        body := .sendUnsequenced group packet.data })

/-- Queues `packet` on `channelId` (ENet enet_peer_send). Packets larger
than `maxFragmentPayload` are split into fragments: reliable ones unless the
packet explicitly allows unreliable fragmentation. -/
def send (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) :
    Except LenetError Peer := do
  if p.state ≠ .connected then
    throw (.peerNotConnected p.peerId)
  let some channel := p.channels[channelId.toNat]?
    | throw (.invalidChannelId p.peerId channelId p.channels.size)
  let fragmentLength := p.maxFragmentPayload hasChecksum
  if packet.data.size > fragmentLength then
    let fragmentCount := (packet.data.size + fragmentLength - 1) / fragmentLength
    if fragmentCount > Constants.maximumFragmentCount then
      throw (.tooManyFragments packet.data.size)
    let (channel, fragments) := fragmentCommands channel channelId packet fragmentLength fragmentCount
    return fragments.foldl queueOutgoingCommand
      { p with channels := p.channels.setIfInBounds channelId.toNat channel }
  else
    let (p, channel, cmd) := p.packetCommand channel channelId packet
    return { p with channels := p.channels.setIfInBounds channelId.toNat channel }
      |>.queueOutgoingCommand { command := cmd, fragmentLength := packet.data.size }

/-! ## Round-trip time and throttle -/

/-- ENet enet_peer_throttle: adapts the packet throttle to an RTT sample. -/
def throttle (p : Peer) (rtt : UInt32) : Peer :=
  if p.lastRoundTripTime ≤ p.lastRoundTripTimeVariance then
    { p with packetThrottle := p.packetThrottleLimit }
  else if rtt ≤ p.lastRoundTripTime then
    { p with packetThrottle := min (p.packetThrottle + p.packetThrottleAcceleration) p.packetThrottleLimit }
  else if rtt > p.lastRoundTripTime + 2 * p.lastRoundTripTimeVariance then
    { p with packetThrottle :=
        if p.packetThrottle > p.packetThrottleDeceleration then p.packetThrottle - p.packetThrottleDeceleration
        else 0 }
  else
    p

/-- Folds an RTT sample into the smoothed RTT and variance, the per-epoch
extremes and the throttle (ENet handle_acknowledge). -/
def updateRtt (p : Peer) (now : UInt32) (rtt : UInt32) : Peer :=
  let sample := max rtt 1
  let (p, rtt, var) :=
    if p.lastReceiveTime > 0 then
      let p := p.throttle sample
      let var := p.roundTripTimeVariance - p.roundTripTimeVariance / 4
      if sample ≥ p.roundTripTime then
        let diff := sample - p.roundTripTime
        (p, p.roundTripTime + diff / 8, var + diff / 4)
      else
        let diff := p.roundTripTime - sample
        (p, p.roundTripTime - diff / 8, var + diff / 4)
    else
      (p, sample, (sample + 1) / 2)
  let lowest := min rtt p.lowestRoundTripTime
  let highestVar := max var p.highestRoundTripTimeVariance
  -- at each throttle epoch the epoch's extremes become the reference values
  -- the throttle compares against, and the next epoch's extremes start over
  -- from the current estimate
  let newEpoch := p.packetThrottleEpoch == 0 ∨
    Time.difference now p.packetThrottleEpoch ≥ p.packetThrottleInterval
  let p :=
    if newEpoch then
      { p with
        lastRoundTripTime         := lowest
        lastRoundTripTimeVariance := max highestVar 1
        packetThrottleEpoch       := now }
    else p
  { p with
    roundTripTime                := rtt
    roundTripTimeVariance        := var
    lowestRoundTripTime          := if newEpoch then rtt else lowest
    highestRoundTripTimeVariance := if newEpoch then var else highestVar
    lastReceiveTime              := max now 1
    earliestTimeout              := 0 }

/-- Whether the peer has exceeded its timeout limits (ENet check_timeouts).
`earliestTimeout` is the *updated* earliest timeout: ENet updates
`peer->earliestTimeout` within the same iteration and evaluates the
condition against the fresh value. -/
def isTimedOut (p : Peer) (now : UInt32) (earliestTimeout : UInt32) (sendAttempts : Nat) : Bool :=
  if earliestTimeout == 0 then
    false
  else
    let elapsed := Time.difference now earliestTimeout
    let attemptThreshold := (1 : UInt32) <<< (sendAttempts - 1).toUInt32
    elapsed ≥ p.timeoutMaximum ∨ (attemptThreshold ≥ p.timeoutLimit ∧ elapsed ≥ p.timeoutMinimum)

/-! ## Incoming commands -/

/-- Runs a channel's receive step on channel `channelId` and turns what it
delivers into receive events. Commands for a channel the peer does not have
are dropped. -/
def receiveOnChannel (p : Peer) (channelId : UInt8) (receive : Channel → Channel × Array Packet) :
    Peer × Array Event :=
  if h : channelId.toNat < p.channels.size then
    let (ch, delivered) := receive p.channels[channelId.toNat]
    ({ p with channels := p.channels.set channelId.toNat ch h },
      delivered.map (Event.receive p.peerId channelId))
  else
    (p, #[])

/-- Absorbs a fragment into the assembler array: finds the assembler for
`params.startSequenceNumber` (creating one when below the concurrency cap
`maximumFragmentAssemblers` and the fragment count is within
`maximumReceivedFragmentCount` - robustness guards, DESIGN.md,
deliberately stricter than ENet whose pending-assembler growth is bounded
only by its window span). Returns the (possibly grown) array and the
assembler to deliver to. -/
def absorbFragment (xs : Array FragmentAssembler) (params : Protocol.FragmentParams) :
    Array FragmentAssembler × Option FragmentAssembler :=
  match xs.find? (fun a => a.startSequenceNumber == params.startSequenceNumber) with
  | some asm => (xs, some asm)
  | none =>
    if xs.size ≥ Constants.maximumFragmentAssemblers ∨
        params.fragmentCount.toNat = 0 ∨
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

/-- The reliable-fragment receive gate: unreliable fragments always pass;
reliable fragments must be inside the receive window and not duplicate the
dispatch frontier (protocol.c handle_send_fragment's cyclic window check plus
peer.c queue_incoming_command's duplicate check) - anything else is a stale or
duplicate fragment set and is dropped. -/
def fragmentGateOk (p : Peer) (channelId : UInt8) (params : Protocol.FragmentParams)
    (unreliable : Bool) : Bool :=
  if unreliable then true
  else
    match p.channels[channelId.toNat]? with
    | none => false
    | some ch =>
      ch.isIncomingReliableInWindow params.startSequenceNumber ∧
        params.startSequenceNumber ≠ ch.incomingReliableSequenceNumber

/-- Delivers a fragment to the (possibly newly created) assembler for
`params.startSequenceNumber`. When the fragment completes the packet, the
assembler is consumed and the packet goes through the channel's receive
path; a reliable set occupies `fragmentCount` sequence numbers (ENet
advances the dispatch frontier by the whole span). Fragments with invalid
parameters (which ENet validates identically) are dropped. -/
def handleFragment (p : Peer) (channelId : UInt8) (params : Protocol.FragmentParams)
    (unreliable : Bool) : Peer × Array Event :=
  if !fragmentGateOk p channelId params unreliable then
    (p, #[])
  else
    let (xs, assembler?) := absorbFragment p.fragmentAssemblers params
    let result : Option (Except CodecError (FragmentAssembler × Option ByteArray)) :=
      assembler?.bind fun asm =>
        asm.addFragment params.fragmentNumber.toNat params.fragmentOffset.toNat params.data
    let p := { p with fragmentAssemblers := assemblerArrayAfterDeliver xs params result }
    match result with
    | some (.ok (_, some data)) =>
      p.receiveOnChannel channelId fun ch =>
        if unreliable then
          let (ch, delivered) := ch.receiveUnreliable params.startSequenceNumber (.unreliableFragment data)
          (ch, delivered.toArray)
        else
          let (ch, delivered) :=
            ch.receiveReliableSpan params.startSequenceNumber params.fragmentCount.toNat (.reliable data)
          (ch, delivered.map (·.2))
    | _ => (p, #[])

/-- Handles a data command (send reliable/unreliable/unsequenced/fragment);
other commands are ignored. -/
def handleData (p : Peer) (cmd : Protocol.Command) : Peer × Array Event :=
  match cmd.body with
  | .sendReliable data =>
    p.receiveOnChannel cmd.channelId fun ch =>
      let (ch, delivered) := ch.receiveReliable cmd.reliableSequenceNumber (.reliable data)
      (ch, delivered.map (·.2))
  | .sendUnreliable seq data =>
    p.receiveOnChannel cmd.channelId fun ch =>
      let (ch, delivered) := ch.receiveUnreliable seq (.unreliable data)
      (ch, delivered.toArray)
  | .sendUnsequenced group data =>
    match p.unsequencedWindow.checkAndAdd group with
    | some window =>
      ({ p with unsequencedWindow := window }, #[.receive p.peerId cmd.channelId (.unsequenced data)])
    | none => (p, #[])
  | .sendFragment params => p.handleFragment cmd.channelId params (unreliable := false)
  | .sendUnreliableFragment params => p.handleFragment cmd.channelId params (unreliable := true)
  | _ => (p, #[])

/-- Handles an ACK (ENet handle_acknowledge): updates the RTT, retires the
acknowledged command, and completes a pending handshake or disconnect. -/
def handleAcknowledge (p : Peer) (now : UInt32) (channelId : UInt8) (seq sentTime : UInt16) :
    Peer × Array Event :=
  -- the echoed sent time is the low 16 bits of our clock
  let sent := Time.fromWire now sentTime
  if Time.less now sent then
    (p, #[]) -- acknowledges a send from the future: ignored (ENet)
  else
    let (p, acked?) := (p.updateRtt now (Time.difference now sent)).removeSentReliableCommand channelId seq
    let ackedNumber := acked?.map (·.body.commandNumber)
    match p.state with
    | .acknowledgingConnect =>
      if ackedNumber == some Constants.commandVerifyConnect then
        ({ p with state := .connected }, #[.connect p.peerId p.eventData])
      else (p, #[])
    | .disconnecting =>
      if ackedNumber == some Constants.commandDisconnect then
        -- ENet's notify_disconnect: event (data = 0) + reset, so the slot is
        -- immediately reusable
        (p.reset, #[.disconnect p.peerId 0])
      else (p, #[])
    | .disconnectLater =>
      -- once everything is acknowledged, the deferred DISCONNECT goes out
      if p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty then
        (p.queueDisconnect p.eventData, #[])
      else (p, #[])
    | _ => (p, #[])

/-- Handles a DISCONNECT (ENet handle_disconnect). A connected peer
acknowledges it and resets once that ACK is out (`Host.pollPeer`); a peer
still handshaking resets immediately. -/
def handleDisconnect (p : Peer) (data : UInt32) : Peer × Array Event :=
  match p.state with
  | .disconnected | .zombie | .acknowledgingDisconnect => (p, #[])
  | .connected | .disconnectLater => ({ p with state := .acknowledgingDisconnect, eventData := data }, #[])
  | _ => (p.reset, #[.disconnect p.peerId data])

/-- Handles the server's VERIFY_CONNECT, completing the client's handshake
(ENet handle_verify_connect). -/
def handleVerifyConnect (p : Peer) (params : Protocol.ConnectParams) : Peer × Array Event :=
  if p.state != .connecting then
    (p, #[])
  else if params.channelCount.toNat < Constants.minimumChannelCount ∨
      params.channelCount.toNat > Constants.maximumChannelCount ∨
      params.packetThrottleInterval != p.packetThrottleInterval ∨
      params.packetThrottleAcceleration != p.packetThrottleAcceleration ∨
      params.packetThrottleDeceleration != p.packetThrottleDeceleration ∨
      params.connectId != p.connectId then
    -- not an answer to our CONNECT: ENet dispatches ZOMBIE (event + reset)
    (p.reset, #[.disconnect p.peerId 0])
  else
    -- the VERIFY_CONNECT stands in for the ACK of our CONNECT
    let (p, _) := p.removeSentReliableCommand 0xFF 1
    -- the server's MTU and window are clamped to the protocol range and can
    -- only shrink the client's own values
    let clamp (lo hi : Nat) (v : UInt32) : Nat := Nat.min hi (Nat.max lo v.toNat)
    let mtu := clamp Constants.minimumMtu Constants.maximumMtu params.mtu
    let windowSize := clamp Constants.minimumWindowSize Constants.maximumWindowSize params.windowSize
    let p := { p with
      outgoingPeerId    := params.outgoingPeerId
      incomingSessionId := params.incomingSessionId
      outgoingSessionId := params.outgoingSessionId
      channels          := p.channels.take params.channelCount.toNat
      mtu               := Nat.min p.mtu.toNat mtu |>.toUInt32
      windowSize        := Nat.min p.windowSize.toNat windowSize |>.toUInt32
      incomingBandwidth := params.incomingBandwidth
      outgoingBandwidth := params.outgoingBandwidth
      state             := .connected }
    (p, #[.connect p.peerId p.eventData])

/-- Processes one incoming command from this peer: queues the ACK it asks
for, then applies it. Returns the updated peer and the events produced. -/
def handleCommand (p : Peer) (now : UInt32) (cmd : Protocol.Command) (sentTime : Option UInt16) :
    Peer × Array Event :=
  let p := match cmd.acknowledge, sentTime with
    | true, some sentTime =>
      p.queueAck { channelId := cmd.channelId, reliableSequenceNumber := cmd.reliableSequenceNumber, sentTime }
    | _, _ => p
  match cmd.body with
  | .acknowledge seq sentTime => p.handleAcknowledge now cmd.channelId seq sentTime
  | .disconnect data => p.handleDisconnect data
  | .verifyConnect params => p.handleVerifyConnect params
  | .bandwidthLimit inBw outBw =>
    -- ENet also recomputes the window size here, which needs the host's
    -- outgoing bandwidth: `Host.handleDatagram` does that
    ({ p with incomingBandwidth := inBw, outgoingBandwidth := outBw }, #[])
  | .throttleConfigure interval accel decel =>
    ({ p with
      packetThrottleInterval     := interval
      packetThrottleAcceleration := accel
      packetThrottleDeceleration := decel }, #[])
  | .ping => (p, #[])
  -- a CONNECT for an existing peer is ignored (ENet same)
  | .connect .. => (p, #[])
  | .sendReliable .. | .sendUnreliable .. | .sendUnsequenced ..
  | .sendFragment .. | .sendUnreliableFragment .. =>
    if p.isConnected then p.handleData cmd else (p, #[])

end Peer

end Lenet
