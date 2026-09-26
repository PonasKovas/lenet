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
  /-- Cycles through `0 ..< packetThrottleScale`; an unreliable packet is
  dropped when it lands above `packetThrottle` (ENet `packetThrottleCounter`). -/
  packetThrottleCounter          : UInt32 := 0
  packetThrottleEpoch            : UInt32 := 0
  packetThrottleAcceleration     : UInt32 := Constants.defaultPacketThrottleAcceleration
  packetThrottleDeceleration     : UInt32 := Constants.defaultPacketThrottleDeceleration
  packetThrottleInterval         : UInt32 := Constants.defaultPacketThrottleInterval
  eventData                      : UInt32 := 0
  reliableDataInTransit          : Nat := 0
  /-- Bytes of commands and ACKs queued for this peer since the last
  bandwidth-throttle epoch; retransmissions do not count (ENet
  `outgoingDataTotal`). -/
  outgoingDataTotal              : Nat := 0
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
  { p with
    outgoingCommands  := p.outgoingCommands.push cmd
    outgoingDataTotal := p.outgoingDataTotal + cmd.command.wireSize }

/-- Queues a reliable control command on channel 0xFF, numbered by the
peer-level control sequence (pre-incremented: the first one is 1). -/
def queueControlCommand (p : Peer) (body : Protocol.CommandBody) : Peer :=
  let seq := p.outgoingControlSeq + 1
  { p with outgoingControlSeq := seq }.queueOutgoingCommand
    { command := { channelId := 0xFF, reliableSequenceNumber := seq, acknowledge := true, body } }

/-- Starts a disconnect (ENet enet_peer_disconnect). Nothing happens when
one is already under way or the slot is free. Otherwise everything queued
or in flight is dropped (ENet enet_peer_reset_queues) and DISCONNECT is
queued: a connected peer sends it reliably and waits for its ACK in
`disconnecting`; a peer still handshaking sends it once, unacknowledged,
and is then reset without an event (ENet flushes and resets at once; here
the peer waits as `zombie` until `Host.pollPeer` has sent it). -/
def queueDisconnect (p : Peer) (data : UInt32) : Peer :=
  match p.state with
  | .disconnecting | .disconnected | .acknowledgingDisconnect | .zombie => p
  | state =>
    let p : Peer := { p with
      outgoingCommands      := #[]
      sentReliableCommands  := #[]
      acknowledgements      := #[]
      reliableDataInTransit := 0 }
    if state == .connected || state == .disconnectLater then
      { p with state := .disconnecting }.queueControlCommand (.disconnect data)
    else
      -- numbered like every command on channel 0xFF (ENet setup_outgoing_command)
      let seq : UInt16 := p.outgoingControlSeq + 1
      { p with outgoingControlSeq := seq, state := .zombie }.queueOutgoingCommand
        { command := { channelId := 0xFF, reliableSequenceNumber := seq, unsequenced := true
                       body := .disconnect data } }

/-- Queues an acknowledgement for the remote peer. -/
def queueAck (p : Peer) (ack : Acknowledgement) : Peer :=
  { p with
    acknowledgements  := p.acknowledgements.push ack
    outgoingDataTotal := p.outgoingDataTotal + 8 } -- an ACK command's wire size

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

/-- Why `send` refuses `packet` on `channelId`, if it does: the peer is not
connected, has no such channel, or the packet needs more than
`maximumFragmentCount` fragments. Only reads the peer. -/
def sendError? (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) :
    Option LenetError :=
  let fragmentLength := p.maxFragmentPayload hasChecksum
  if p.state ≠ .connected then some (.peerNotConnected p.peerId)
  else if p.channels.size ≤ channelId.toNat then
    some (.invalidChannelId p.peerId channelId p.channels.size)
  else if packet.data.size > fragmentLength ∧
      (packet.data.size + fragmentLength - 1) / fragmentLength > Constants.maximumFragmentCount then
    some (.tooManyFragments packet.data.size)
  else none

/-- Queues `packet` on `channelId` (ENet enet_peer_send), once `sendError?`
has accepted it; a channel the peer does not have leaves it unchanged.
Packets larger than `maxFragmentPayload` are split into fragments: reliable
ones unless the packet explicitly allows unreliable fragmentation. -/
def enqueue (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) : Peer :=
  match p.channels[channelId.toNat]? with
  | none => p
  | some channel =>
    let fragmentLength := p.maxFragmentPayload hasChecksum
    if packet.data.size > fragmentLength then
      let fragmentCount := (packet.data.size + fragmentLength - 1) / fragmentLength
      let (channel, fragments) := fragmentCommands channel channelId packet fragmentLength fragmentCount
      fragments.foldl queueOutgoingCommand
        { p with channels := p.channels.setIfInBounds channelId.toNat channel }
    else
      let (p, channel, cmd) := p.packetCommand channel channelId packet
      { p with channels := p.channels.setIfInBounds channelId.toNat channel }
        |>.queueOutgoingCommand { command := cmd, fragmentLength := packet.data.size }

/-- Queues `packet` on `channelId` (`enqueue`), or says why not
(`sendError?`). -/
def send (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) :
    Except LenetError Peer :=
  match p.sendError? channelId packet hasChecksum with
  | some e => .error e
  | none => .ok (p.enqueue channelId packet hasChecksum)

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

/-- The origin of the fragment set a fragment command on `channelId`
belongs to; `reliableSeq` is the command's reliable sequence number. -/
def fragmentOrigin (channelId : UInt8) (reliableSeq : UInt16) (unreliable : Bool) : FragmentOrigin :=
  { channelId, unreliable, reliableSeq := if unreliable then reliableSeq else 0 }

/-- Whether the fragment set (`origin`, `startSeq`) can still be delivered on
channel `ch`. Anything else is stale or a duplicate: its fragments are
dropped before reassembly, and an assembler for it is discarded.
- Reliable sets: the start sequence number must be inside the receive window
  and not duplicate the dispatch frontier (protocol.c handle_send_fragment's
  cyclic window check plus peer.c queue_incoming_command's duplicate check),
  and the set must not be complete already and staged (ENet finds the staged
  command and ignores the fragment).
- Unreliable sets: the reliable command they were sent after must be inside
  the receive window, and a set sent after the frontier must be newer than
  the last unreliable delivery (protocol.c handle_send_unreliable_fragment)
  and not complete already and staged. -/
def fragmentSetLive (ch : Channel) (origin : FragmentOrigin) (startSeq : UInt16) : Bool :=
  if origin.unreliable then
    ch.isIncomingReliableInWindow origin.reliableSeq &&
      !(origin.reliableSeq == ch.incomingReliableSequenceNumber &&
        startSeq ≤ ch.incomingUnreliableSequenceNumber) &&
      !ch.stagedUnreliable.any fun e => e.reliableSeq == origin.reliableSeq && e.unreliableSeq == startSeq
  else
    ch.isReliableAhead startSeq && !ch.stagedReliable.any (·.seq == startSeq)

/-- Discards the assemblers of channel `channelId` whose set can no longer be
delivered: the dispatch frontier or the last unreliable delivery moved past
it. Without this, an unreliable set that lost a fragment would hold its
assembler forever. -/
def pruneAssemblers (p : Peer) (channelId : UInt8) : Peer :=
  match p.channels[channelId.toNat]? with
  | some ch =>
    if p.fragmentAssemblers.isEmpty then p
    else
      { p with
        fragmentAssemblers := p.fragmentAssemblers.filter fun a =>
          a.origin.channelId != channelId || fragmentSetLive ch a.origin a.startSequenceNumber }
  | none => p

/-- Runs a channel's receive step on channel `channelId`, discards the
assemblers that step made stale, and turns what it delivers into receive
events. Commands for a channel the peer does not have are dropped. -/
def receiveOnChannel (p : Peer) (channelId : UInt8) (receive : Channel → Channel × Array Packet) :
    Peer × Array Event :=
  if h : channelId.toNat < p.channels.size then
    let (ch, delivered) := receive p.channels[channelId.toNat]
    (({ p with channels := p.channels.set channelId.toNat ch h } : Peer).pruneAssemblers channelId,
      delivered.map (Event.receive p.peerId channelId))
  else
    (p, #[])

/-- Room for one more assembler in `xs`: `xs` itself below the cap
`maximumFragmentAssemblers`, otherwise `xs` without its oldest unreliable
assembler (an unreliable packet may be lost anyway). `none` when every slot
holds a reliable set. -/
def assemblerRoom (xs : Array FragmentAssembler) : Option (Array FragmentAssembler) :=
  if xs.size < Constants.maximumFragmentAssemblers then some xs
  else
    match xs.findFinIdx? (·.origin.unreliable) with
    | some i => some (xs.eraseIdx i)
    | none => none

/-- Absorbs a fragment into the assembler array: finds the assembler for the
set (`origin`, `params.startSequenceNumber`), or creates one when there is
room (`assemblerRoom`) and the fragment count is within
`maximumReceivedFragmentCount` - robustness guards, DESIGN.md, deliberately
stricter than ENet whose pending-assembler growth is bounded only by its
window span. Returns the (possibly changed) array and the assembler to
deliver to. -/
def absorbFragment (xs : Array FragmentAssembler) (origin : FragmentOrigin)
    (params : Protocol.FragmentParams) : Array FragmentAssembler × Option FragmentAssembler :=
  match xs.find? (fun a => a.origin == origin && a.startSequenceNumber == params.startSequenceNumber) with
  | some asm => (xs, some asm)
  | none =>
    if params.fragmentCount.toNat = 0 ∨
        params.fragmentCount.toNat > Constants.maximumReceivedFragmentCount then
      (xs, none)
    else
      match assemblerRoom xs with
      | none => (xs, none)
      | some room =>
        match FragmentAssembler.init params.startSequenceNumber params.totalLength.toNat
            params.fragmentCount.toNat with
        | .ok newAsm =>
          let newAsm := { newAsm with origin }
          (room.push newAsm, some newAsm)
        | .error _ => (xs, none)

/-- The assembler array after delivering a fragment result: the matching
assembler is updated in place while the assembly is partial, and filtered
out when it completes. `none` (no assembler, e.g. no room or invalid
parameters) leaves the array unchanged. -/
def assemblerArrayAfterDeliver (xs : Array FragmentAssembler) (origin : FragmentOrigin)
    (params : Protocol.FragmentParams)
    (result : Option (Except CodecError (FragmentAssembler × Option ByteArray))) :
    Array FragmentAssembler :=
  let isSet (a : FragmentAssembler) :=
    a.origin == origin && a.startSequenceNumber == params.startSequenceNumber
  match result with
  | none => xs
  | some (.error _) => xs
  | some (.ok (updatedAsm, none)) => xs.map fun a => if isSet a then updatedAsm else a
  | some (.ok (_, some _)) => xs.filter fun a => !isSet a

/-- The fragment receive gate (`fragmentSetLive` on the command's channel). -/
def fragmentGateOk (p : Peer) (channelId : UInt8) (reliableSeq : UInt16)
    (params : Protocol.FragmentParams) (unreliable : Bool) : Bool :=
  match p.channels[channelId.toNat]? with
  | none => false
  | some ch => fragmentSetLive ch (fragmentOrigin channelId reliableSeq unreliable) params.startSequenceNumber

/-- Delivers a fragment to the (possibly newly created) assembler for its
set. When the fragment completes the packet, the assembler is consumed and
the packet goes through the channel's receive path; a reliable set occupies
`fragmentCount` sequence numbers (ENet advances the dispatch frontier by the
whole span). The flag is false when the fragment passed the gate but found
no assembler (no room, or invalid parameters, which ENet validates
identically): such a reliable fragment must not be acknowledged, so the
sender retransmits it (ENet skips the acknowledgement of a command it
failed to handle). -/
def handleFragment (p : Peer) (channelId : UInt8) (reliableSeq : UInt16)
    (params : Protocol.FragmentParams) (unreliable : Bool) : Peer × Array Event × Bool :=
  if !fragmentGateOk p channelId reliableSeq params unreliable then
    (p, #[], true)
  else
    let origin := fragmentOrigin channelId reliableSeq unreliable
    let (xs, assembler?) := absorbFragment p.fragmentAssemblers origin params
    let result : Option (Except CodecError (FragmentAssembler × Option ByteArray)) :=
      assembler?.bind fun asm =>
        asm.addFragment params.fragmentNumber.toNat params.fragmentOffset.toNat params.data
    let p := { p with fragmentAssemblers := assemblerArrayAfterDeliver xs origin params result }
    match result with
    | some (.ok (_, some data)) =>
      let (p, events) := p.receiveOnChannel channelId fun ch =>
        if unreliable then
          let (ch, delivered) :=
            ch.receiveUnreliable reliableSeq params.startSequenceNumber (.unreliableFragment data)
          (ch, delivered.toArray)
        else
          ch.receiveReliableAndRelease params.startSequenceNumber params.fragmentCount.toNat (.reliable data)
      (p, events, true)
    | _ => (p, #[], assembler?.isSome)

/-- Handles an unfragmented data command (send reliable/unreliable/
unsequenced); other commands are ignored. -/
def handleData (p : Peer) (cmd : Protocol.Command) : Peer × Array Event :=
  match cmd.body with
  | .sendReliable data =>
    p.receiveOnChannel cmd.channelId fun ch =>
      ch.receiveReliableAndRelease cmd.reliableSequenceNumber 1 (.reliable data)
  | .sendUnreliable seq data =>
    p.receiveOnChannel cmd.channelId fun ch =>
      let (ch, delivered) := ch.receiveUnreliable cmd.reliableSequenceNumber seq (.unreliable data)
      (ch, delivered.toArray)
  | .sendUnsequenced group data =>
    match p.unsequencedWindow.checkAndAdd group with
    | some window =>
      ({ p with unsequencedWindow := window }, #[.receive p.peerId cmd.channelId (.unsequenced data)])
    | none => (p, #[])
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
acknowledges it and resets once that ACK is out (`Host.pollPeer`). A server
peer still handshaking resets without an event: the application never saw
it connect. A client still connecting, or a peer disconnecting itself,
resets and reports the disconnect. -/
def handleDisconnect (p : Peer) (data : UInt32) : Peer × Array Event :=
  match p.state with
  | .disconnected | .zombie | .acknowledgingDisconnect => (p, #[])
  | .connected | .disconnectLater => ({ p with state := .acknowledgingDisconnect, eventData := data }, #[])
  | .acknowledgingConnect => (p.reset, #[])
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
for, then applies it. Returns the updated peer and the events produced. A
reliable fragment that found no assembler is not acknowledged
(`handleFragment`). -/
def handleCommand (p : Peer) (now : UInt32) (cmd : Protocol.Command) (sentTime : Option UInt16) :
    Peer × Array Event :=
  let ack (p : Peer) : Peer := match cmd.acknowledge, sentTime with
    | true, some sentTime =>
      p.queueAck { channelId := cmd.channelId, reliableSequenceNumber := cmd.reliableSequenceNumber, sentTime }
    | _, _ => p
  let fragment (params : Protocol.FragmentParams) (unreliable : Bool) : Peer × Array Event :=
    if p.isConnected then
      let (p, events, accepted) := p.handleFragment cmd.channelId cmd.reliableSequenceNumber params unreliable
      (if accepted then ack p else p, events)
    else (ack p, #[])
  match cmd.body with
  | .sendFragment params => fragment params (unreliable := false)
  | .sendUnreliableFragment params => fragment params (unreliable := true)
  | body =>
    let p := ack p
    match body with
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
    | .sendReliable .. | .sendUnreliable .. | .sendUnsequenced .. =>
      if p.isConnected then p.handleData cmd else (p, #[])
    | .sendFragment .. | .sendUnreliableFragment .. => (p, #[])

end Peer

end Lenet
