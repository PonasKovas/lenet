import Lenet.Constants
import Lenet.Time
import Lenet.Address
import Lenet.Error
import Lenet.Channel
import Lenet.Unsequenced
import Lenet.Take
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
  /-- ACKs owed. Not capped: a datagram adds at most 32 and every service
  sends them all, and a cap would only force retransmissions (as in ENet). -/
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

/-- ENet enet_peer_reset_queues: drops everything queued, in flight or
waiting for delivery, and the channels with it (ENet frees them). -/
def resetQueues (p : Peer) : Peer :=
  { p with
    outgoingCommands      := #[]
    sentReliableCommands  := #[]
    acknowledgements      := #[]
    reliableDataInTransit := 0
    channels              := #[]
    fragmentAssemblers    := #[] }

/-- Queues one unacknowledged DISCONNECT and leaves the peer `zombie`:
`Host.pollPeer` resets it without an event once the DISCONNECT is out (ENet
sends it and resets at once; there is no socket to flush here). -/
def sendLastDisconnect (p : Peer) (data : UInt32) : Peer :=
  -- numbered like every command on channel 0xFF (ENet setup_outgoing_command)
  let seq : UInt16 := p.outgoingControlSeq + 1
  { p with outgoingControlSeq := seq, state := .zombie }.queueOutgoingCommand
    { command := { channelId := 0xFF, reliableSequenceNumber := seq, unsequenced := true
                   body := .disconnect data } }

/-- Starts a disconnect (ENet enet_peer_disconnect). Nothing happens when
one is already under way or the slot is free. Otherwise everything queued
or in flight is dropped (`resetQueues`) and DISCONNECT is
queued: a connected peer sends it reliably and waits for its ACK in
`disconnecting`; a peer still handshaking sends it once, unacknowledged,
and is then reset without an event (ENet flushes and resets at once; here
the peer waits as `zombie` until `Host.pollPeer` has sent it). -/
def queueDisconnect (p : Peer) (data : UInt32) : Peer :=
  match p.state with
  | .disconnecting | .disconnected | .acknowledgingDisconnect | .zombie => p
  | state =>
    let p := p.resetQueues
    if state == .connected || state == .disconnectLater then
      { p with state := .disconnecting }.queueControlCommand (.disconnect data)
    else p.sendLastDisconnect data

/-- ENet enet_peer_disconnect_now: ends the connection without waiting and
without an event (the application asked for it). A connection still up
drops its queues and sends one unacknowledged DISCONNECT (`sendLastDisconnect`);
a peer already disconnecting just resets. -/
def disconnectNow (p : Peer) (data : UInt32) : Peer :=
  match p.state with
  | .disconnected | .zombie => p
  | .disconnecting => p.reset
  | _ => p.resetQueues.sendLastDisconnect data

/-- Queues an acknowledgement for the remote peer. -/
def queueAck (p : Peer) (ack : Acknowledgement) : Peer :=
  { p with
    acknowledgements  := p.acknowledgements.push ack
    outgoingDataTotal := p.outgoingDataTotal + 8 } -- an ACK command's wire size

/-- Removes the in-flight reliable command `(channelId, seq)` once it is
acknowledged: releases its channel window slot and its in-transit bytes.
A command queued again for retransmission (`Host.checkPeerTimeouts`) is
still found, as ENet's remove_sent_reliable_command finds it: among the
queue's reliable commands up to the first one never sent. Its bytes left
the in-transit count when it was queued again. Returns the removed
command, if there was one. -/
def removeSentReliableCommand (p : Peer) (channelId : UInt8) (seq : UInt16) : Peer × Option Protocol.Command :=
  let isIt (outCmd : OutgoingCommand) : Bool :=
    outCmd.command.channelId == channelId && outCmd.command.reliableSequenceNumber == seq
  match p.sentReliableCommands.findFinIdx? isIt with
  | some i =>
    ({ p with
      sentReliableCommands  := p.sentReliableCommands.eraseIdx i
      channels              := p.channels.modify channelId.toNat (·.releaseReliableWindow seq)
      -- no underflow: these bytes were added when the command was sent
      reliableDataInTransit := p.reliableDataInTransit - p.sentReliableCommands[i].fragmentLength
    }, some p.sentReliableCommands[i].command)
  | none =>
    -- the first reliable command that is either it or never sent
    match p.outgoingCommands.findFinIdx? fun outCmd =>
        outCmd.command.acknowledge && (outCmd.sendAttempts == 0 || isIt outCmd) with
    | some i =>
      if p.outgoingCommands[i].sendAttempts == 0 then (p, none)
      else
        ({ p with
          outgoingCommands := p.outgoingCommands.eraseIdx i
          channels         := p.channels.modify channelId.toNat (·.releaseReliableWindow seq)
        }, some p.outgoingCommands[i].command)
    | none => (p, none)

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
the channel's current reliable sequence number. Once the channel's
unreliable sequence number is used up (0xFFFF), the set goes reliable, which
starts the unreliable numbering again (ENet enet_peer_send). -/
def fragmentCommands (channel : Channel) (channelId : UInt8) (packet : Packet)
    (fragmentLength fragmentCount : Nat) : Channel × Array OutgoingCommand :=
  let unreliable := packet.delivery == .unreliableFragment && channel.outgoingUnreliableSequenceNumber < 0xFFFF
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
`channel` after numbering it. An unreliable packet goes reliable once the
channel's unreliable sequence number is used up (0xFFFF), which starts the
unreliable numbering again: wrapping it to 0 would make the receiver drop
every later unreliable packet as old (ENet enet_peer_send). -/
def packetCommand (p : Peer) (channel : Channel) (channelId : UInt8) (packet : Packet) :
    Peer × Channel × Protocol.Command :=
  let reliable (channel : Channel) : Peer × Channel × Protocol.Command :=
    let (channel, seq) := channel.nextReliableSequenceNumber
    (p, channel, { channelId, reliableSequenceNumber := seq, acknowledge := true,
                   body := .sendReliable packet.data })
  match packet.delivery with
  | .reliable => reliable channel
  | .unreliable | .unreliableFragment =>
    if channel.outgoingUnreliableSequenceNumber ≥ 0xFFFF then reliable channel
    else
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
connected, has no such channel, the packet is larger than
`maximumPacketSize` or needs more than `maximumFragmentCount` fragments
(ENet enet_peer_send). Only reads the peer. -/
def sendError? (p : Peer) (channelId : UInt8) (packet : Packet) (hasChecksum : Bool := false) :
    Option LenetError :=
  let fragmentLength := p.maxFragmentPayload hasChecksum
  if p.state ≠ .connected then some (.peerNotConnected p.peerId)
  else if p.channels.size ≤ channelId.toNat then
    some (.invalidChannelId p.peerId channelId p.channels.size)
  else if packet.data.size > Constants.maximumPacketSize then some (.packetTooLarge packet.data.size)
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
      !(ch.stagedUnreliable[origin.reliableSeq]?).any (·.contains startSeq)
  else
    ch.isReliableAhead startSeq && !ch.stagedReliable.contains startSeq

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
    -- the channel leaves the peer (`takeAt`), so `receive` holds it once and
    -- its staged maps change in place: a shared one would be copied whole
    let peerId := p.peerId
    let channels := p.channels
    let p := { p with channels := #[] }
    let (ch, channels) := takeAt channels channelId.toNat default h
    let (ch, delivered) := receive ch
    (({ p with channels := channels.setIfInBounds channelId.toNat ch } : Peer).pruneAssemblers channelId,
      delivered.map (Event.receive peerId channelId))
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

/-- The bytes the assemblers in `xs` hold back for their packets: a set's
whole `totalLength` from the moment it starts, as ENet charges it, so a set
once started never waits on the budget. -/
def waitingBytes (xs : Array FragmentAssembler) : Nat :=
  xs.foldl (fun n a => n + a.totalLength) 0

/-- The fragments the sets in `xs` claim. -/
def waitingFragments (xs : Array FragmentAssembler) : Nat :=
  xs.foldl (fun n a => n + a.fragmentCount) 0

/-- The bytes of the packets `channels` hold back. -/
def channelsStagedBytes (channels : Array Channel) : Nat :=
  channels.foldl (fun n ch => n + ch.stagedBytes) 0

/-- The bytes of the packets the peer's channels hold back. -/
def stagedBytes (p : Peer) : Nat := channelsStagedBytes p.channels

/-- Whether a fragment set starting at `startSeq` is the next thing channel
`channelId` delivers: a reliable set right after the frontier. -/
def deliversNext (channels : Array Channel) (channelId : UInt8) (startSeq : UInt16) (unreliable : Bool) : Bool :=
  !unreliable && channels[channelId.toNat]?.any (·.incomingReliableSequenceNumber + 1 == startSeq)

/-- What the peer holds back from the application: its fragment sets under
way and the packets its channels staged. ENet's `totalWaitingData`, which
also counts packets delivered but not yet read by the application; here
those are events, which the application drains. -/
def heldBytes (p : Peer) : Nat :=
  waitingBytes p.fragmentAssemblers + p.stagedBytes

/-- Absorbs a fragment into the assembler array: finds the assembler for the
set (`origin`, `params.startSequenceNumber`), or creates one when
- there is room (`assemblerRoom`) and the fragment count is within
  `maximumReceivedFragmentCount`,
- the assemblers hold less than `maximumWaitingData` bytes and claim fewer
  than `maximumReceivedFragmentCount` fragments, and
- the peer holds back less than `maximumWaitingData` bytes in all (`held`,
  what its channels staged, is added), unless the set is the next thing
  its channel delivers (`next`): refusing that one would stall the channel,
  since what it staged waits for it.

The byte budget is ENet's (queue_incoming_command refuses a new packet once
`totalWaitingData` reaches `maximumWaitingData`, the next one too); the
rest are robustness guards, stricter than ENet. Returns the
(possibly changed) array and the index of the set's assembler in it. -/
def absorbFragment (xs : Array FragmentAssembler) (origin : FragmentOrigin)
    (params : Protocol.FragmentParams) (held : Unit → Nat) (next : Bool) :
    Array FragmentAssembler × Option Nat :=
  match xs.findFinIdx? (fun a => a.origin == origin && a.startSequenceNumber == params.startSequenceNumber) with
  | some i => (xs, some i.val)
  | none =>
    if params.fragmentCount.toNat = 0 ∨
        params.fragmentCount.toNat > Constants.maximumReceivedFragmentCount then
      (xs, none)
    else
      match assemblerRoom xs with
      | none => (xs, none)
      | some room =>
        if waitingBytes room ≥ Constants.maximumWaitingData then (xs, none)
        else if waitingFragments room ≥ Constants.maximumReceivedFragmentCount then (xs, none)
        else if !next && waitingBytes room + held () ≥ Constants.maximumWaitingData then (xs, none)
        else
        match FragmentAssembler.init params.startSequenceNumber params.totalLength.toNat
            params.fragmentCount.toNat with
        | .ok newAsm => (room.push { newAsm with origin }, some room.size)
        | .error _ => (xs, none)

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
no assembler (no room, over budget, or invalid parameters) or does not fit it, which
ENet validates identically: ENet refuses such a command (`applyCommand`),
so it is not acknowledged and the sender retransmits it. -/
def handleFragment (p : Peer) (channelId : UInt8) (reliableSeq : UInt16)
    (params : Protocol.FragmentParams) (unreliable : Bool) : Peer × Array Event × Bool :=
  -- ENet refuses an empty fragment before anything else
  if params.data.size == 0 then (p, #[], false)
  else if !fragmentGateOk p channelId reliableSeq params unreliable then
    (p, #[], true)
  else
    let origin := fragmentOrigin channelId reliableSeq unreliable
    -- the assemblers leave the peer and the set's assembler leaves the array
    -- (`takeAt`), so its buffer is held once and each fragment is copied in
    -- place: a shared buffer would be copied whole for every fragment
    let xs := p.fragmentAssemblers
    let p := { p with fragmentAssemblers := #[] }
    match absorbFragment xs origin params (fun _ => channelsStagedBytes p.channels)
        (deliversNext p.channels channelId params.startSequenceNumber unreliable) with
    | (xs, none) => ({ p with fragmentAssemblers := xs }, #[], false)
    | (xs, some i) =>
      if hi : i < xs.size then
        let (asm, xs) := takeAt xs i default hi
        let number := params.fragmentNumber.toNat
        let offset := params.fragmentOffset.toNat
        -- a fragment that does not describe the set under way, or does not
        -- fit it, is refused (ENet), and so is one whose bytes do not fit
        -- what the set is missing (`bytesFit`, stricter than ENet)
        if asm.totalLength != params.totalLength.toNat || asm.fragmentCount != params.fragmentCount.toNat ||
            !asm.takes number offset params.data then
          -- a set this fragment would have started is not kept
          if asm.fragments.isEmpty then ({ p with fragmentAssemblers := xs.eraseIdxIfInBounds i }, #[], false)
          else ({ p with fragmentAssemblers := xs.setIfInBounds i asm }, #[], false)
        else
          match asm.addFragment number offset params.data with
          | .ok (asm, none) => ({ p with fragmentAssemblers := xs.setIfInBounds i asm }, #[], true)
          | .ok (_, some data) =>
            let p := { p with fragmentAssemblers := xs.eraseIdxIfInBounds i }
            let (p, events) := p.receiveOnChannel channelId fun ch =>
              if unreliable then
                let (ch, delivered) :=
                  ch.receiveUnreliable reliableSeq params.startSequenceNumber (.unreliableFragment data)
                (ch, delivered.toArray)
              else
                ch.receiveReliableAndRelease params.startSequenceNumber params.fragmentCount.toNat (.reliable data)
            (p, events, true)
          -- unreachable: `takes` covers every refusal of `addFragment`
          | .error _ => ({ p with fragmentAssemblers := xs.eraseIdxIfInBounds i }, #[], false)
      else ({ p with fragmentAssemblers := xs }, #[], false)

/-- Handles an unfragmented data command (send reliable/unreliable/
unsequenced); other commands are ignored.

An unsequenced packet is delivered when it arrives. ENet appends it to the
channel's unreliable queue, where it waits behind any staged unreliable
packet (forever, if that one's reliable frontier never comes). -/
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
    if p.unsequencedWindow.accepts group then
      -- the window leaves the peer first, so it is marked in place
      let window := p.unsequencedWindow
      let p := { p with unsequencedWindow := {} }
      ({ p with unsequencedWindow := window.add group }, #[.receive p.peerId cmd.channelId (.unsequenced data)])
    else (p, #[])
  | _ => (p, #[])

/-- Handles an ACK (ENet handle_acknowledge): updates the RTT, retires the
acknowledged command, and completes a pending handshake or disconnect. The
flag is false where ENet refuses the ACK: one for anything but the
VERIFY_CONNECT while the handshake waits for it, or for anything but the
DISCONNECT while disconnecting (the RTT update and the removal stand). -/
def handleAcknowledge (p : Peer) (now : UInt32) (channelId : UInt8) (seq sentTime : UInt16) :
    Peer × Array Event × Bool :=
  -- the echoed sent time is the low 16 bits of our clock
  let sent := Time.fromWire now sentTime
  -- a peer a DISCONNECT earlier in the datagram reset takes nothing more (ENet)
  if p.state == .disconnected || p.state == .zombie then (p, #[], true)
  else if Time.less now sent then
    (p, #[], true) -- acknowledges a send from the future: ignored (ENet)
  else
    let (p, acked?) := (p.updateRtt now (Time.difference now sent)).removeSentReliableCommand channelId seq
    let ackedNumber := acked?.map (·.body.commandNumber)
    match p.state with
    | .acknowledgingConnect =>
      if ackedNumber == some Constants.commandVerifyConnect then
        ({ p with state := .connected }, #[.connect p.peerId p.eventData], true)
      else (p, #[], false)
    | .disconnecting =>
      if ackedNumber == some Constants.commandDisconnect then
        -- ENet's notify_disconnect: event (data = 0) + reset, so the slot is
        -- immediately reusable
        (p.reset, #[.disconnect p.peerId 0], true)
      else (p, #[], false)
    | .disconnectLater =>
      -- once everything is acknowledged, the deferred DISCONNECT goes out
      if p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty then
        (p.queueDisconnect p.eventData, #[], true)
      else (p, #[], true)
    | _ => (p, #[], true)

/-- Handles a DISCONNECT (ENet handle_disconnect). A connected peer drops
everything queued or in flight (`resetQueues`), acknowledges the
DISCONNECT and resets once that ACK is out (`Host.pollPeer`). A server
peer still handshaking resets without an event: the application never saw
it connect. A client still connecting, or a peer disconnecting itself,
resets and reports the disconnect. -/
def handleDisconnect (p : Peer) (data : UInt32) : Peer × Array Event :=
  match p.state with
  | .disconnected | .zombie | .acknowledgingDisconnect => (p, #[])
  | .connected | .disconnectLater =>
    ({ p.resetQueues with state := .acknowledgingDisconnect, eventData := data }, #[])
  | .acknowledgingConnect => (p.reset, #[])
  | _ => (p.reset, #[.disconnect p.peerId data])

/-- Handles the server's VERIFY_CONNECT, completing the client's handshake
(ENet handle_verify_connect). The flag is false for a VERIFY_CONNECT that
does not answer our CONNECT, which ENet refuses. -/
def handleVerifyConnect (p : Peer) (params : Protocol.ConnectParams) : Peer × Array Event × Bool :=
  if p.state != .connecting then
    (p, #[], true)
  else if params.channelCount.toNat < Constants.minimumChannelCount ∨
      params.channelCount.toNat > Constants.maximumChannelCount ∨
      params.packetThrottleInterval != p.packetThrottleInterval ∨
      params.packetThrottleAcceleration != p.packetThrottleAcceleration ∨
      params.packetThrottleDeceleration != p.packetThrottleDeceleration ∨
      params.connectId != p.connectId then
    -- not an answer to our CONNECT: ENet dispatches ZOMBIE (event + reset)
    (p.reset, #[.disconnect p.peerId 0], false)
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
    (p, #[.connect p.peerId p.eventData], true)

/-- Whether channel `channelId` would stage unfragmented packet `cmd`
rather than deliver or drop it: reliable data ahead of the frontier but not
next, or unreliable data sent after such a reliable command. -/
def wouldStage (p : Peer) (cmd : Protocol.Command) : Bool :=
  match p.channels[cmd.channelId.toNat]? with
  | none => false
  | some ch =>
    match cmd.body with
    | .sendReliable .. =>
      ch.isReliableAhead cmd.reliableSequenceNumber &&
        cmd.reliableSequenceNumber != ch.incomingReliableSequenceNumber + 1
    | .sendUnreliable .. => ch.isReliableAhead cmd.reliableSequenceNumber
    | _ => false

/-- An unfragmented reliable or unreliable packet (`handleData`), refused
when it would be staged while the peer already holds back
`maximumWaitingData` bytes (ENet's queue_incoming_command). A packet the
channel delivers at once is always taken: it is what the channel staged
waits for. The test comes first, so `p` is not kept for a refusal and
`handleData` updates it in place. -/
def handleHeldData (p : Peer) (cmd : Protocol.Command) : Peer × Array Event × Bool :=
  if p.wouldStage cmd && p.heldBytes ≥ Constants.maximumWaitingData then (p, #[], false)
  else
    let (q, events) := p.handleData cmd
    (q, events, true)

/-- ENet's handler for one incoming command (protocol.c
handle_incoming_commands and the handle_* functions): the updated peer, the
events, and whether ENet accepts the command. A refused command is not
acknowledged and ENet reads no further in its datagram. Data, PING,
BANDWIDTH_LIMIT and THROTTLE_CONFIGURE need a connected peer, data also an
existing channel; a CONNECT for an existing peer is refused.

A peer in `disconnectLater` accepts data but delivers none of it (ENet
enet_peer_queue_incoming_command discards it): an unsequenced packet still
marks its group, a fragment of a set already under way still completes it,
and a fragment that would start a new set is refused. -/
def applyCommand (p : Peer) (now : UInt32) (cmd : Protocol.Command) : Peer × Array Event × Bool :=
  let takesData := p.isConnected && cmd.channelId.toNat < p.channels.size
  let draining := p.state == .disconnectLater
  -- whether a fragment would start a set while draining
  let startsSet (params : Protocol.FragmentParams) (unreliable : Bool) : Bool :=
    let origin := fragmentOrigin cmd.channelId cmd.reliableSequenceNumber unreliable
    draining && p.fragmentGateOk cmd.channelId cmd.reliableSequenceNumber params unreliable &&
      !p.fragmentAssemblers.any fun a => a.origin == origin && a.startSequenceNumber == params.startSequenceNumber
  match cmd.body with
  | .acknowledge seq sentTime => p.handleAcknowledge now cmd.channelId seq sentTime
  | .connect .. => (p, #[], false)
  | .verifyConnect params => p.handleVerifyConnect params
  | .disconnect data =>
    let (p, events) := p.handleDisconnect data
    (p, events, true)
  | .ping => (p, #[], p.isConnected)
  | .bandwidthLimit inBw outBw =>
    -- ENet also recomputes the window size here, which needs the host's
    -- outgoing bandwidth: `Host.handlePeerDatagram` does that
    if p.isConnected then ({ p with incomingBandwidth := inBw, outgoingBandwidth := outBw }, #[], true)
    else (p, #[], false)
  | .throttleConfigure interval accel decel =>
    if p.isConnected then
      ({ p with
        packetThrottleInterval     := interval
        packetThrottleAcceleration := accel
        packetThrottleDeceleration := decel }, #[], true)
    else (p, #[], false)
  | .sendReliable .. | .sendUnreliable .. =>
    if !takesData then (p, #[], false)
    else if draining then (p, #[], true)
    else p.handleHeldData cmd
  | .sendUnsequenced .. =>
    if !takesData then (p, #[], false)
    else
      let (p, events) := p.handleData cmd
      (p, if draining then #[] else events, true)
  | .sendFragment params =>
    if !takesData || startsSet params false then (p, #[], false)
    else p.handleFragment cmd.channelId cmd.reliableSequenceNumber params false
  | .sendUnreliableFragment params =>
    if !takesData || startsSet params true then (p, #[], false)
    else p.handleFragment cmd.channelId cmd.reliableSequenceNumber params true

/-- Whether ENet acknowledges `cmd` for a peer that is in state `s` after
handling it (handle_incoming_commands): not while disconnecting, still
handshaking as the server, or gone, and only the DISCONNECT itself while
acknowledging one. -/
def acksIn (s : PeerState) (cmd : Protocol.Command) : Bool :=
  match s with
  | .disconnecting | .acknowledgingConnect | .disconnected | .zombie => false
  | .acknowledgingDisconnect => (cmd.body matches .disconnect _)
  | _ => true

/-- Whether `cmd` is reliable data just past its channel's receive window
(`Channel.isReliableTooFarAhead`, by the set's start for a fragment): it is
dropped, and not acknowledged, so the sender sends it again. -/
def tooFarAhead (p : Peer) (cmd : Protocol.Command) : Bool :=
  let ahead (seq : UInt16) := p.channels[cmd.channelId.toNat]?.any (·.isReliableTooFarAhead seq)
  match cmd.body with
  | .sendReliable .. => ahead cmd.reliableSequenceNumber
  | .sendFragment params => ahead params.startSequenceNumber
  | _ => false

/-- Processes one incoming command from this peer (`applyCommand`), then
queues the ACK it asks for when ENet would, echoing the datagram's
`sentTime`, except for reliable data too far ahead (`tooFarAhead`). The
flag says whether to read on in the datagram: not after a refused command,
nor after one asking for an ACK in a datagram without a sent time (ENet
same). -/
def handleCommand (p : Peer) (now : UInt32) (cmd : Protocol.Command) (sentTime : Option UInt16) :
    Peer × Array Event × Bool :=
  let withhold := p.tooFarAhead cmd
  let (p, events, accepted) := p.applyCommand now cmd
  if !accepted then (p, events, false)
  else if !cmd.acknowledge then (p, events, true)
  else
    match sentTime with
    | none => (p, events, false)
    | some sentTime =>
      let p := if acksIn p.state cmd && !withhold then
        p.queueAck { channelId := cmd.channelId, reliableSequenceNumber := cmd.reliableSequenceNumber, sentTime }
      else p
      (p, events, true)

end Peer

end Lenet
