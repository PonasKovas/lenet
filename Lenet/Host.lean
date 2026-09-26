import Lenet.Constants
import Lenet.Time
import Lenet.Address
import Lenet.Error
import Lenet.Packet
import Lenet.Channel
import Lenet.OutgoingCommand
import Lenet.Event
import Lenet.Peer
import Lenet.Protocol.Datagram

/-!
# The host

`Host` is the whole sans-I/O protocol engine: a fixed array of peer slots
plus host-wide settings. The driver feeds it received datagrams
(`handleDatagram`), calls `service` on its timer (`nextDeadline` says when),
and transmits the datagrams `service` returns.
-/

namespace Lenet

structure Host where
  /-- The address the driver's socket is bound to (informational). -/
  address                : Address := {}
  peers                  : Array Peer := #[]
  /-- Maximum channels per connection. -/
  channelLimit           : Nat := Constants.maximumChannelCount
  /-- Bandwidths in bytes/second; 0 means unlimited. -/
  incomingBandwidth      : UInt32 := 0
  outgoingBandwidth      : UInt32 := 0
  bandwidthThrottleEpoch : UInt32 := 0
  /-- Set by connects and disconnects: the next bandwidth-throttle epoch sends
  every connected peer a fresh BANDWIDTH_LIMIT. -/
  recalculateBandwidthLimits : Bool := false
  mtu                    : UInt32 := Constants.defaultMtu.toUInt32
  /-- PRNG state for connect IDs. -/
  randomSeed             : UInt32 := 0x12345678
  /-- CRC32 checksums on every datagram (ENet: `host->checksum = enet_crc32`);
  must match the remote side. -/
  checksumEnabled        : Bool := false
deriving Inhabited

namespace Host

/-- Clamps a window size to the protocol's `[minimumWindowSize,
maximumWindowSize]`. -/
def clampWindowSize (n : Nat) : UInt32 :=
  Nat.min Constants.maximumWindowSize (Nat.max Constants.minimumWindowSize n) |>.toUInt32

/-- ENet's bandwidth-derived receive window size (protocol.c: same formula at
connect, handle_connect, handle_verify_connect and handle_bandwidth_limit):
- both bandwidths 0 → maximum window
- exactly one set → `max(hostOutBw, peerInBw) / 64k * 4096`
- both set → `min(hostOutBw, peerInBw) / 64k * 4096`
clamped to the protocol range. -/
def windowSizeFor (hostOutBw : UInt32) (peerInBw : UInt32) : UInt32 :=
  let scale := Constants.windowSizeScale.toNat
  clampWindowSize <|
    if peerInBw.toNat == 0 ∧ hostOutBw.toNat == 0 then
      Constants.maximumWindowSize
    else if peerInBw.toNat == 0 ∨ hostOutBw.toNat == 0 then
      Nat.max peerInBw.toNat hostOutBw.toNat / scale * Constants.minimumWindowSize
    else
      Nat.min peerInBw.toNat hostOutBw.toNat / scale * Constants.minimumWindowSize

/-- Creates a host with `peerCount` peer slots, at most `maximumPeerId`
(4095): peer ID 0xFFF addresses CONNECTs, so a slot with that ID could never
be reached (ENet's enet_host_create refuses such counts). `channelLimit` 0
means the protocol maximum; `mtu` is clamped to [576, 4096] (ENet silently
corrects out-of-range MTUs too). -/
def create (address : Address := {}) (peerCount : Nat := 32)
    (channelLimit : Nat := Constants.maximumChannelCount) (inBw : UInt32 := 0) (outBw : UInt32 := 0)
    (seed : UInt32 := 0x12345678) (mtu : UInt32 := Constants.defaultMtu.toUInt32) : Host :=
  { address
    peers             :=
      (Array.range (Nat.min peerCount Constants.maximumPeerId.toNat)).map fun idx => { peerId := idx.toUInt16 }
    channelLimit      :=
      if channelLimit == 0 ∨ channelLimit > Constants.maximumChannelCount then Constants.maximumChannelCount
      else channelLimit
    incomingBandwidth := inBw
    outgoingBandwidth := outBw
    mtu               := Nat.min Constants.maximumMtu (Nat.max Constants.minimumMtu mtu.toNat) |>.toUInt32
    randomSeed        := seed }

/-- Mulberry32 PRNG step, for connect IDs. -/
def random (h : Host) : Host × UInt32 :=
  let seed := h.randomSeed + 0x6D2B79F5
  let n1 := (seed ^^^ (seed >>> 15)) * (seed ||| 1)
  let n2 := n1 ^^^ (n1 + (n1 ^^^ (n1 >>> 7)) * (n1 ||| 61))
  ({ h with randomSeed := seed }, n2 ^^^ (n2 >>> 14))

/-- Applies `f` to peer `peerId`; unknown peer IDs leave the host unchanged. -/
def modifyPeer (h : Host) (peerId : UInt16) (f : Peer → Peer) : Host :=
  { h with peers := h.peers.modify peerId.toNat f }

/-- The host with its peer array taken out, so the caller holds the only
reference to it; put it back with `{ h with peers }`. Reading a peer out of
an array the host still holds shares it, and then every change to the peer
copies the peer and its arrays. -/
@[inline] def takePeers (h : Host) : Host × Array Peer :=
  ({ h with peers := #[] }, h.peers)

/-- Runs `f` on peer slot `i` and puts the result back. Returns `dflt` when
there is no such slot.

The peer is taken out of the array first (`takeAt`), so `f` holds its only
reference: a fragment's bytes then go into the assembler's buffer in place
instead of copying it. (`Array.modifyM` is meant to do this, but once it is
specialized to `StateM` the compiler moves the slot-emptying step after the
call.) `mapPeers` has no such problem. -/
@[inline] def withPeer (h : Host) (i : Nat) (dflt : α) (f : Peer → Peer × α) : Host × α :=
  let (h, peers) := h.takePeers
  if hi : i < peers.size then
    let (p, peers) := takeAt peers i default hi
    let (p, a) := f p
    ({ h with peers := peers.setIfInBounds i p }, a)
  else ({ h with peers }, dflt)

/-- Runs `f` on every peer in order, each one unshared (`Array.mapM`),
threading `init` through. -/
@[inline] def mapPeers (h : Host) (init : σ) (f : Peer → σ → Peer × σ) : Host × σ :=
  let (h, peers) := h.takePeers
  let (peers, s) := (peers.mapM (m := StateM σ) fun p => modifyGet (f p)).run init
  ({ h with peers }, s)

/-- The first disconnected (reusable) peer slot. -/
def freeSlot? (h : Host) : Option (Fin h.peers.size) :=
  h.peers.findFinIdx? (·.state == .disconnected)

/-! ## Application API -/

/-- Starts connecting to `remoteAddress` with `channelCount` channels
(clamped to [1, 255]; the host's channel limit only caps incoming
connections, as in ENet enet_host_connect), sending `data` with the CONNECT.
Returns the updated host and the peer ID of the new connection. -/
def connect (h : Host) (remoteAddress : Address) (channelCount : Nat := 2) (data : UInt32 := 0) :
    Except LenetError (Host × UInt16) := do
  let some slot := h.freeSlot? | throw .noFreePeerSlots
  let p := h.peers[slot]
  let (h, connectId) := h.random
  let channels := Nat.max Constants.minimumChannelCount (Nat.min channelCount Constants.maximumChannelCount)
  -- ENet (enet_host_connect): the client's window derives from its own
  -- outgoing bandwidth (a fresh slot has incomingBandwidth = 0)
  let windowSize := windowSizeFor h.outgoingBandwidth 0
  let params : Protocol.ConnectParams := {
    outgoingPeerId             := p.peerId
    -- the slot's current sessions: 0xFF/0xFF for a fresh slot, the
    -- previously negotiated values for a reused one (ENet same)
    incomingSessionId          := p.incomingSessionId
    outgoingSessionId          := p.outgoingSessionId
    mtu                        := h.mtu
    windowSize
    channelCount               := channels.toUInt32
    incomingBandwidth          := h.incomingBandwidth
    outgoingBandwidth          := h.outgoingBandwidth
    packetThrottleInterval     := p.packetThrottleInterval
    packetThrottleAcceleration := p.packetThrottleAcceleration
    packetThrottleDeceleration := p.packetThrottleDeceleration
    connectId
  }
  let p := { p with
    address   := remoteAddress
    state     := .connecting
    connectId
    channels  := Array.replicate channels {}
    -- the client's own connect event reports 0: ENet's enet_host_connect
    -- leaves eventData at its reset value, the data goes in the CONNECT
    eventData := 0
    mtu       := h.mtu
    windowSize
  }.queueControlCommand (.connect params data)
  return (h.modifyPeer p.peerId fun _ => p, p.peerId)

/-- Queues `packet` for peer `peerId` on `channelId`, or says why not; the
host comes back either way (unchanged on error), so a caller never needs to
keep the old one and the update stays in place. -/
def trySend (h : Host) (peerId : UInt16) (channelId : UInt8) (packet : Packet) :
    Host × Except LenetError Unit :=
  let checksumEnabled := h.checksumEnabled
  h.withPeer peerId.toNat (.error (.invalidPeerId peerId)) fun p =>
    match p.sendError? channelId packet checksumEnabled with
    | some e => (p, .error e)
    | none => (p.enqueue channelId packet checksumEnabled, .ok ())

/-- Queues `packet` for peer `peerId` on `channelId` (`trySend`). -/
def send (h : Host) (peerId : UInt16) (channelId : UInt8) (packet : Packet) : Except LenetError Host :=
  let (h, result) := h.trySend peerId channelId packet
  result.map fun () => h

/-- Queues `packet` for every connected peer. Peers whose send fails (e.g. a
channel they do not have) are skipped, as ENet's enet_host_broadcast does. -/
def broadcast (h : Host) (channelId : UInt8) (packet : Packet) : Host :=
  let checksumEnabled := h.checksumEnabled
  (h.mapPeers () fun p () =>
    if p.state == .connected && (p.sendError? channelId packet checksumEnabled).isNone then
      (p.enqueue channelId packet checksumEnabled, ())
    else (p, ())).1

/-- Starts a graceful disconnect of `peerId`, sending `data` with it. -/
def disconnect (h : Host) (peerId : UInt16) (data : UInt32 := 0) : Host :=
  h.modifyPeer peerId (·.queueDisconnect data)

/-- ENet's enet_peer_disconnect_later: a peer that still has commands queued
or in flight enters `disconnectLater` and disconnects once they are all
acknowledged; otherwise it disconnects now. -/
def disconnectLater (h : Host) (peerId : UInt16) (data : UInt32 := 0) : Host :=
  h.modifyPeer peerId fun p =>
    if p.isConnected ∧ (!p.outgoingCommands.isEmpty ∨ !p.sentReliableCommands.isEmpty) then
      { p with state := .disconnectLater, eventData := data }
    else
      p.queueDisconnect data

/-- ENet's enet_peer_throttle_configure: sets the local throttle parameters
and sends them to the remote peer. -/
def throttleConfigure (h : Host) (peerId : UInt16) (interval accel decel : UInt32) : Host :=
  h.modifyPeer peerId fun p =>
    { p with
      packetThrottleInterval     := interval
      packetThrottleAcceleration := accel
      packetThrottleDeceleration := decel
    }.queueControlCommand (.throttleConfigure interval accel decel)

/-- ENet's enet_peer_timeout: sets the peer's timeout parameters (see
`Peer.isTimedOut`); 0 means the default, as in ENet. -/
def setPeerTimeout (h : Host) (peerId : UInt16) (limit minimum maximum : UInt32) : Host :=
  let orDefault (v dflt : UInt32) := if v == 0 then dflt else v
  h.modifyPeer peerId fun p =>
    { p with
      timeoutLimit   := orDefault limit Constants.defaultTimeoutLimit
      timeoutMinimum := orDefault minimum Constants.defaultTimeoutMinimum
      timeoutMaximum := orDefault maximum Constants.defaultTimeoutMaximum }

/-! ## Receiving -/

/-- ENet session negotiation (handle_connect): the next session ID after the
one the client offered (`0xFF`: none, continue from the slot's `current`),
skipping `current` so a reused slot never repeats its previous session.
Forwarding 0xFF verbatim would set the header's compressed-flag bit in every
later datagram. -/
def nextSession (offered current : UInt8) : UInt8 :=
  let base := if offered == 0xFF then current else offered
  let s := (base + 1) &&& 3
  if s == current then (s + 1) &&& 3 else s

/-- ENet handle_connect: an incoming CONNECT (addressed to peer ID 0xFFF)
takes a free slot, which negotiates sessions, MTU and window and answers
with a VERIFY_CONNECT. The connect event fires once the client acknowledges
the VERIFY_CONNECT. CONNECTs with a channel count outside [1, 255], or with
no slot free, are ignored, and so is a retransmitted one: a peer (other
than a client still connecting) already has its address and connect ID.
ENet also caps the peers per remote IP (`host->duplicatePeers`), but its
default, 4095, is more than a host has slots. -/
def handleIncomingConnect (h : Host) (fromAddr : Address) (params : Protocol.ConnectParams)
    (data : UInt32) : Host :=
  let duplicate := h.peers.any fun p =>
    p.state != .disconnected && p.state != .connecting && p.address == fromAddr &&
      p.connectId == params.connectId
  if params.channelCount.toNat < Constants.minimumChannelCount ∨
      params.channelCount.toNat > Constants.maximumChannelCount ∨ duplicate then
    h
  else
    match h.freeSlot? with
    | none => h
    | some slot =>
      let p := h.peers[slot]
      let channels := Nat.min params.channelCount.toNat h.channelLimit
      let outSession := nextSession params.incomingSessionId p.outgoingSessionId
      let inSession := nextSession params.outgoingSessionId p.incomingSessionId
      -- the offered MTU is clamped to the protocol range *before* the min
      -- with the host's: a hostile mtu = 0 must not collapse the peer's MTU
      let mtu := Nat.min h.mtu.toNat (Nat.min Constants.maximumMtu (Nat.max Constants.minimumMtu params.mtu.toNat))
      -- the VERIFY_CONNECT advertises the host's incoming-bandwidth-derived
      -- window, shrunk to the client's offer
      let hostWindow :=
        if h.incomingBandwidth == 0 then Constants.maximumWindowSize
        else h.incomingBandwidth.toNat / Constants.windowSizeScale.toNat * Constants.minimumWindowSize
      let verifyParams : Protocol.ConnectParams := {
        outgoingPeerId             := p.peerId
        incomingSessionId          := outSession
        outgoingSessionId          := inSession
        mtu                        := mtu.toUInt32
        windowSize                 := clampWindowSize (Nat.min hostWindow params.windowSize.toNat)
        channelCount               := channels.toUInt32
        incomingBandwidth          := h.incomingBandwidth
        outgoingBandwidth          := h.outgoingBandwidth
        -- the client's throttle parameters, which the peer takes over: the
        -- client refuses a VERIFY_CONNECT that does not echo them (ENet)
        packetThrottleInterval     := params.packetThrottleInterval
        packetThrottleAcceleration := params.packetThrottleAcceleration
        packetThrottleDeceleration := params.packetThrottleDeceleration
        connectId                  := params.connectId
      }
      let p := { p with
        address           := fromAddr
        outgoingPeerId    := params.outgoingPeerId
        connectId         := params.connectId
        state             := .acknowledgingConnect
        channels          := Array.replicate channels {}
        eventData         := data
        mtu               := mtu.toUInt32
        windowSize        := windowSizeFor h.outgoingBandwidth params.incomingBandwidth
        incomingBandwidth := params.incomingBandwidth
        outgoingBandwidth := params.outgoingBandwidth
        packetThrottleInterval     := params.packetThrottleInterval
        packetThrottleAcceleration := params.packetThrottleAcceleration
        packetThrottleDeceleration := params.packetThrottleDeceleration
        incomingSessionId := inSession
        outgoingSessionId := outSession
      }.queueControlCommand (.verifyConnect verifyParams)
      h.modifyPeer p.peerId fun _ => p

/-- ENet's peer lookup (protocol.c enet_protocol_handle_incoming_commands):
whether peer `p` takes a datagram from `fromAddr` whose header carries
`session`. The datagram must come from the peer's address (unless that is
the broadcast address), and once the connection is negotiated (the remote
peer ID is known) carry the peer's session; disconnected and zombie peers
take nothing. -/
def acceptsDatagram (p : Peer) (fromAddr : Address) (session : UInt8) : Bool :=
  let negotiated := p.outgoingPeerId < Constants.maximumPeerId
  let wrongAddress := p.address.host != Address.broadcast && fromAddr != p.address
  !(p.state == .disconnected || p.state == .zombie || wrongAddress ||
    (negotiated && session != p.incomingSessionId))

/-- One step of `handlePeerDatagram`'s command loop. The state is the peer,
the events so far, whether to read on (ENet drops the rest of a datagram
after a command it refuses, `Peer.handleCommand`), and whether a
BANDWIDTH_LIMIT was applied (only a connected peer takes one). -/
def readCommand (now : UInt32) (sentTime : Option UInt16) (st : Peer × Array Event × Bool × Bool)
    (cmd : Protocol.Command) : Peer × Array Event × Bool × Bool :=
  let (p, events, reading, bandwidthChanged) := st
  if !reading then st
  else
    let bandwidthChanged := bandwidthChanged || (p.isConnected && cmd.body matches .bandwidthLimit ..)
    let (p, newEvents, reading) := p.handleCommand now cmd sentTime
    (p, events ++ newEvents, reading, bandwidthChanged)

/-- Applies an accepted datagram's commands to its peer `p`, in order
(`readCommand`), and returns the events they produce. `outgoingBandwidth`
is the host's. -/
def handlePeerDatagram (p : Peer) (now : UInt32) (fromAddr : Address) (datagram : Protocol.Datagram)
    (outgoingBandwidth : UInt32) : Peer × Array Event :=
  -- a peer connected to the broadcast address learns the real one
  let p := { p with address := fromAddr }
  let (p, events, _, bandwidthChanged) :=
    datagram.commands.foldl (readCommand now datagram.header.sentTime) (p, #[], true, false)
  -- ENet (handle_bandwidth_limit) also recomputes the receive window from the
  -- peer's new incoming bandwidth, which needs the host's outgoing bandwidth:
  -- done here, after the command loop (the last BANDWIDTH_LIMIT wins either way)
  let p :=
    if bandwidthChanged then { p with windowSize := windowSizeFor outgoingBandwidth p.incomingBandwidth }
    else p
  (p, events)

/-- Processes one received UDP datagram from `fromAddr`: CONNECTs to the
broadcast peer ID open a connection, everything else goes to its peer.
Returns the updated host and the application events produced; undecodable
or unacceptable datagrams are dropped. -/
def handleDatagram (h : Host) (now : UInt32) (fromAddr : Address) (bytes : ByteArray) :
    Host × Array Event :=
  -- the checksum key is the target peer's connectID (0 for the broadcast
  -- peer ID; ENet enet_protocol_receive)
  let connectIdOf (peerId : UInt16) : UInt32 :=
    if peerId == Constants.maximumPeerId then 0
    else h.peers[peerId.toNat]?.map (·.connectId) |>.getD 0
  match ReaderM.run (Protocol.Datagram.decode h.checksumEnabled (some connectIdOf)) bytes with
  | .error _ => (h, #[])
  | .ok datagram =>
    let peerId := datagram.header.peerId
    if peerId == Constants.maximumPeerId then
      match datagram.commands[0]?.map (·.body) with
      | some (Protocol.CommandBody.connect params data) => (h.handleIncomingConnect fromAddr params data, #[])
      | _ => (h, #[])
    else
      match h.peers[peerId.toNat]? with
      | none => (h, #[])
      | some p =>
        if !acceptsDatagram p fromAddr datagram.header.session then
          (h, #[])
        else
          let outgoingBandwidth := h.outgoingBandwidth
          let (h, events) := h.withPeer peerId.toNat #[]
            (handlePeerDatagram · now fromAddr datagram outgoingBandwidth)
          -- connects and disconnects trigger a bandwidth recalculation (ENet)
          let connectionChanged := events.any fun
            | .receive .. => false
            | _ => true
          ({ h with recalculateBandwidthLimits := h.recalculateBandwidthLimits || connectionChanged }, events)

/-! ## Sending -/

/-- State of `packOutgoingCommands` while it fills one datagram. -/
structure PackState where
  packedAcks        : Nat := 0
  commandsToPack    : Array Protocol.Command := #[]
  remainingOutgoing : Array OutgoingCommand := #[]
  sentReliables     : Array OutgoingCommand
  channels          : Array Channel
  inTransitAdd      : Nat := 0
  packetSize        : Nat := 0
  /-- The datagram is full: every later command waits for the next one. -/
  full              : Bool := false
  /-- A reliable command hit a still-occupied sequence window: later reliable
  channel commands wait too, so none overtakes it (ENet's `windowWrap`). -/
  windowWrap        : Bool := false
  /-- A reliable data command was held back (window or congestion): every
  later one waits too. ENet keeps them in their own list and stops reading
  it for the pass (`currentSendReliableCommand = end`). -/
  reliableHeld      : Bool := false
  /-- The peer's `packetThrottleCounter`, advanced per unreliable packet. -/
  throttleCounter   : UInt32
  /-- Channel and start sequence number of the unreliable fragment set whose
  first fragment the throttle dropped: its other fragments go too. -/
  droppedSet        : Option (UInt8 × UInt16) := none

namespace PackState

/-- Whether `cmd` still fits the datagram for a peer with MTU `mtu`. -/
@[inline] def fits (st : PackState) (mtu : UInt32) (cmd : Protocol.Command) : Bool :=
  st.commandsToPack.size < Constants.maximumPacketCommands ∧
    st.packetSize + cmd.wireSize ≤ mtu.toNat

/-- Adds `cmd` to the datagram. -/
@[inline] def pack (st : PackState) (cmd : Protocol.Command) : PackState :=
  { st with commandsToPack := st.commandsToPack.push cmd, packetSize := st.packetSize + cmd.wireSize }

/-- Leaves `outCmd` queued for a later datagram. -/
@[inline] def defer (st : PackState) (outCmd : OutgoingCommand) : PackState :=
  { st with remainingOutgoing := st.remainingOutgoing.push outCmd }

/-- Whether `cmd` is the first (or only) command of an unreliable packet,
the unit the packet throttle drops. -/
def startsUnreliablePacket (cmd : Protocol.Command) : Bool :=
  match cmd.body with
  | .sendUnreliable .. | .sendUnsequenced .. => true
  | .sendUnreliableFragment f => f.fragmentOffset == 0
  | _ => false

/-- Whether `cmd` is a later fragment of the set the throttle dropped. -/
def continuesDroppedSet (st : PackState) (cmd : Protocol.Command) : Bool :=
  match st.droppedSet, cmd.body with
  | some (channelId, startSeq), .sendUnreliableFragment f =>
    f.fragmentOffset != 0 && channelId == cmd.channelId && startSeq == f.startSequenceNumber
  | _, _ => false

/-- Packs an unreliable command for peer `p`, or drops it: the counter steps
through `0 ..< packetThrottleScale` and a packet whose step lands above the
throttle is dropped, whole (ENet check_outgoing_commands). At the full
throttle nothing is dropped.

ENet drops a packet together with every directly following command that has
the same sequence numbers. Unsequenced packets all have (0, 0), so ENet also
drops every unsequenced packet queued right behind a dropped one; Lenet only
drops the packet itself (see test/README.md, divergence triage). -/
def packUnreliable (p : Peer) (st : PackState) (cmd : Protocol.Command) : PackState :=
  if !startsUnreliablePacket cmd then st.pack cmd
  else
    let counter := (st.throttleCounter + Constants.packetThrottleCounter) % Constants.packetThrottleScale
    if counter > p.packetThrottle then
      { st with
        throttleCounter := counter
        droppedSet := match cmd.body with
          | .sendUnreliableFragment f => some (cmd.channelId, f.startSequenceNumber)
          | _ => none }
    else { st.pack cmd with throttleCounter := counter }

/-- Packs one queued ACK (ENet send_acknowledgements). -/
def packAck (mtu : UInt32) (st : PackState) (ack : Acknowledgement) : PackState :=
  let cmd : Protocol.Command := {
    channelId              := ack.channelId
    reliableSequenceNumber := ack.reliableSequenceNumber
    body                   := .acknowledge ack.reliableSequenceNumber ack.sentTime }
  if st.full ∨ !st.fits mtu cmd then { st with full := true }
  else { st.pack cmd with packedAcks := st.packedAcks + 1 }

/-- Whether `cmd` carries application data (ENet: `packet != NULL`), as
opposed to a control command. -/
def carriesPacket (cmd : Protocol.Command) : Bool :=
  match cmd.body with
  | .sendReliable .. | .sendUnreliable .. | .sendUnsequenced .. | .sendFragment ..
  | .sendUnreliableFragment .. => true
  | _ => false

/-- Packs one queued command for peer `p` (ENet check_outgoing_commands). A
reliable command stays queued while its sequence window is not free or while
the congestion window is exhausted; an unreliable one may be dropped by
the packet throttle (`packUnreliable`). -/
def packCommand (p : Peer) (now : UInt32) (st : PackState) (outCmd : OutgoingCommand) : PackState :=
  let cmd := outCmd.command
  -- the command's data channel; control commands (channel 0xFF) have none
  let channel? := if cmd.acknowledge then st.channels[cmd.channelId.toNat]? else none
  let firstSend := outCmd.sendAttempts == 0
  let reliableData := cmd.acknowledge && carriesPacket cmd
  if st.continuesDroppedSet cmd then st
  else if st.full then st.defer outCmd
  else if reliableData && st.reliableHeld then st.defer outCmd
  else if channel?.isSome && st.windowWrap then st.defer outCmd
  else if channel?.any (fun ch => firstSend && !ch.canSendReliable cmd.reliableSequenceNumber) then
    { st with windowWrap := true, reliableHeld := true }.defer outCmd
  -- congestion: reliable payload in flight may not exceed the throttle-scaled
  -- receive window (but always admits one MTU). ENet checks every command
  -- with a packet, so an empty one waits too while too much is in flight.
  else if reliableData &&
      p.reliableDataInTransit + st.inTransitAdd + outCmd.fragmentLength >
        Nat.max ((p.packetThrottle * p.windowSize) / Constants.packetThrottleScale).toNat p.mtu.toNat then
    { st with reliableHeld := true }.defer outCmd
  else if !st.fits p.mtu cmd then { st with full := true }.defer outCmd
  else if !cmd.acknowledge then st.packUnreliable p cmd -- fire-and-forget
  else
    -- reliable: occupy its sequence window on first send, and track it for
    -- acknowledgement and retransmission. The arrays are taken out of `st`
    -- first so each has one reference and updates in place.
    let channels := st.channels
    let sentReliables := st.sentReliables
    let inTransitAdd := st.inTransitAdd + outCmd.fragmentLength
    let st := { st with channels := #[], sentReliables := #[] }
    let channels :=
      if firstSend then
        channels.modify cmd.channelId.toNat (·.acquireReliableWindow cmd.reliableSequenceNumber)
      else channels
    let inFlight := { outCmd with
      sendAttempts     := outCmd.sendAttempts + 1
      sentTime         := now
      roundTripTimeout :=
        if outCmd.roundTripTimeout == 0 then p.roundTripTime + 4 * p.roundTripTimeVariance
        else outCmd.roundTripTimeout }
    { st.pack cmd with channels, sentReliables := sentReliables.push inFlight, inTransitAdd }

end PackState

/-- Packs pending ACKs and outgoing commands for a peer into one datagram,
following ENet's rules: ACKs first, then queued commands in order, at most
`maximumPacketCommands` within the peer MTU. Returns the updated peer and
the commands to send. -/
def packOutgoingCommands (p : Peer) (now : UInt32) : Peer × Array Protocol.Command :=
  let initial : PackState := {
    packetSize      := 4 -- ENetProtocolHeader (peer ID + sent time)
    sentReliables   := p.sentReliableCommands
    channels        := p.channels
    throttleCounter := p.packetThrottleCounter
  }
  -- the pack state holds the only reference to the arrays it grows, so they
  -- update in place instead of being copied
  let p := { p with sentReliableCommands := #[], channels := #[] }
  let withAcks := p.acknowledgements.foldl (PackState.packAck p.mtu) initial
  -- read before the command fold, which then holds the only reference
  let packedAcks := withAcks.packedAcks
  let final := p.outgoingCommands.foldl (PackState.packCommand p now) withAcks
  let updatedPeer := { p with
    acknowledgements      := p.acknowledgements.drop packedAcks
    outgoingCommands      := final.remainingOutgoing
    sentReliableCommands  := final.sentReliables
    channels              := final.channels
    reliableDataInTransit := p.reliableDataInTransit + final.inTransitAdd
    packetThrottleCounter := final.throttleCounter
  }
  (updatedPeer, final.commandsToPack)

/-- The datagram carrying `commands` to peer `p`, encoded. -/
def encodeDatagram (p : Peer) (now : UInt32) (checksumEnabled : Bool)
    (commands : Array Protocol.Command) : ByteArray :=
  let negotiated := p.outgoingPeerId < Constants.maximumPeerId
  let datagram : Protocol.Datagram := {
    -- as ENet: the sent time only when a command asks for an ACK (ACKs echo
    -- it), the session only once the remote peer ID is known
    header   := { peerId := p.outgoingPeerId, session := if negotiated then p.outgoingSessionId else 0
                  compressed := false
                  sentTime := if commands.any (·.acknowledge) then some now.toUInt16 else none }
    checksum := if checksumEnabled then some 0 else none
    commands
  }
  -- the checksum key is the peer's connectID, 0 while the remote peer ID is
  -- still unset (the client's CONNECT; ENet same)
  datagram.encode (if p.outgoingPeerId < Constants.maximumPeerId then p.connectId else 0)

/-- Everything peer `p` has to send, as MTU-bounded datagrams (ENet repeats
check_outgoing_commands while CONTINUE_SENDING is set). Also completes three
deferred transitions:
- a `disconnectLater` peer with nothing left queued or in flight sends its
  DISCONNECT;
- an `acknowledgingDisconnect` peer whose ACKs are all out resets and reports
  the disconnect (ENet dispatches ZOMBIE once the ACK of the DISCONNECT is
  sent);
- a `zombie` peer, one that was disconnected while handshaking, resets
  without an event once its DISCONNECT is out. -/
def pollPeer (p : Peer) (now : UInt32) (checksumEnabled : Bool) :
    Peer × Array (Address × ByteArray) × Array Event :=
  if p.state == .disconnected then (p, #[], #[])
  -- every datagram but the last sends at least one queued command or ACK
  else go (p.outgoingCommands.size + p.acknowledgements.size + 1) p #[]
where
  go : Nat → Peer → Array (Address × ByteArray) → Peer × Array (Address × ByteArray) × Array Event
    | 0, p, datagrams => (p, datagrams, #[])
    | fuel + 1, p, datagrams =>
      let p :=
        if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty then
          p.queueDisconnect p.eventData
        else p
      let (p, commands) := packOutgoingCommands p now
      if !commands.isEmpty then
        go fuel p (datagrams.push (p.address, encodeDatagram p now checksumEnabled commands))
      else if p.state == .acknowledgingDisconnect ∧ p.acknowledgements.isEmpty then
        (p.reset, datagrams, #[.disconnect p.peerId p.eventData])
      else if p.state == .zombie then
        -- the DISCONNECT of a peer that never connected is out (`Peer.queueDisconnect`)
        (p.reset, datagrams, #[])
      else
        (p, datagrams, #[])

/-- Every peer's outgoing datagrams, as `(destination, bytes)`, plus the
disconnect events completed on the way (see `pollPeer`). -/
def pollOutgoing (h : Host) (now : UInt32) : Host × Array (Address × ByteArray) × Array Event :=
  let checksumEnabled := h.checksumEnabled
  let (h, datagrams, events) := h.mapPeers (#[], #[]) fun p (datagrams, events) =>
    let (p, newDatagrams, newEvents) := pollPeer p now checksumEnabled
    (p, datagrams ++ newDatagrams, events ++ newEvents)
  (h, datagrams, events)

/-! ## Timers -/

/-- Result of scanning a peer's in-flight commands for timeouts. -/
structure TimeoutScan where
  stillInFlight   : Array OutgoingCommand := #[]
  retransmits     : Array OutgoingCommand := #[]
  timedOut        : Bool := false
  earliestTimeout : UInt32

/-- ENet check_timeouts: in-flight commands past their retransmit timeout go
back to the front of the queue with the timeout doubled, unless the peer has
exceeded its timeout limits, which disconnects it (event with data 0, slot
reset). -/
def checkPeerTimeouts (p : Peer) (now : UInt32) : Peer × Option Event :=
  let scan := p.sentReliableCommands.foldl (init := ({ earliestTimeout := p.earliestTimeout } : TimeoutScan))
    fun scan outCmd =>
      if scan.timedOut then scan
      else if Time.difference now outCmd.sentTime < outCmd.roundTripTimeout then
        { scan with stillInFlight := scan.stillInFlight.push outCmd }
      else
        let earliest :=
          if scan.earliestTimeout == 0 ∨ Time.less outCmd.sentTime scan.earliestTimeout then outCmd.sentTime
          else scan.earliestTimeout
        -- ENet evaluates the timeout against the just-updated earliest timeout
        if p.isTimedOut now earliest outCmd.sendAttempts then
          { scan with timedOut := true }
        else
          { scan with
            earliestTimeout := earliest
            retransmits := scan.retransmits.push { outCmd with roundTripTimeout := outCmd.roundTripTimeout * 2 } }
  if scan.timedOut then
    -- a server peer still handshaking was never reported as connected, so
    -- it goes without an event (ENet enet_protocol_notify_disconnect)
    (p.reset, if p.state == .acknowledgingConnect then none else some (.disconnect p.peerId 0))
  else
    -- a command queued for retransmission is no longer in transit
    let retransmitted := scan.retransmits.foldl (init := 0) (· + ·.fragmentLength)
    ({ p with
      sentReliableCommands  := scan.stillInFlight
      outgoingCommands      := scan.retransmits ++ p.outgoingCommands
      earliestTimeout       := scan.earliestTimeout
      reliableDataInTransit := p.reliableDataInTransit - retransmitted }, none)

/-- Whether a connected peer may ping: nothing reliable queued or in flight
(ENet send_outgoing_commands pings when a pass packed no reliable command
and none is in flight; queued unreliable data does not stop it, and a
queued reliable command always goes out when nothing is in flight). -/
def pingEligible (p : Peer) : Bool :=
  p.state == .connected && p.sentReliableCommands.isEmpty && p.outgoingCommands.all (!·.command.acknowledge)

/-- Queues a keepalive PING when a peer that may ping (`pingEligible`) has
received nothing for its ping interval. -/
def checkPeerPing (p : Peer) (now : UInt32) : Peer :=
  if pingEligible p ∧ Time.difference now p.lastReceiveTime ≥ p.pingInterval then
    p.queueControlCommand .ping
  else p

/-- Runs every live peer's retransmit/timeout check and keepalive ping.
Returns the disconnect events of peers that timed out. -/
def checkTimeoutsAndPings (h : Host) (now : UInt32) : Host × Array Event :=
  h.mapPeers #[] fun p events =>
    if p.state == .disconnected ∨ p.state == .zombie then (p, events)
    else
      match checkPeerTimeouts p now with
      | (p, some event) => (p, events.push event)
      | (p, none) => (checkPeerPing p now, events)

/-- ENet's iterative split of the host's incoming bandwidth among `peers`
(enet_host_bandwidth_throttle): a peer whose own outgoing bandwidth is below
the current per-peer share is capped at that rate ("marked"), its rate leaves
the pool, and the share is recomputed until no more peers get marked.
Returns the final share and the marked peers. -/
def incomingBandwidthShare (bandwidth : UInt32) (peers : Array Peer) : UInt32 × Array UInt16 :=
  -- every round but the last marks at least one more peer
  go bandwidth peers.size 0 #[] (peers.size + 1)
where
  go (bandwidth : UInt32) (remaining : Nat) (share : UInt32) (marked : Array UInt16) :
      Nat → UInt32 × Array UInt16
    | 0 => (share, marked)
    | fuel + 1 =>
      if remaining == 0 then (share, marked)
      else
        let share := bandwidth / remaining.toUInt32
        let (bandwidth', remaining', marked') :=
          peers.foldl (init := (bandwidth, remaining, marked)) fun (bw, rem, m) p =>
            if m.contains p.peerId ∨ (p.outgoingBandwidth > 0 ∧ p.outgoingBandwidth ≥ share) then (bw, rem, m)
            else (bw - p.outgoingBandwidth, rem - 1, m.push p.peerId)
        if marked'.size > marked.size then go bandwidth' remaining' share marked' fuel
        else (share, marked')

/-- What is left of the host's outgoing budget for one bandwidth-throttle
epoch: the bytes it may send and the bytes its peers queued. `none` when the
host's outgoing bandwidth is unlimited. -/
abbrev OutgoingBudget := Option (Nat × Nat)

/-- The packet throttle limit that spreads `budget` over the queued bytes. -/
def OutgoingBudget.throttle : OutgoingBudget → Nat
  | some (bandwidth, dataTotal) =>
    if dataTotal ≤ bandwidth then Constants.packetThrottleScale.toNat
    else bandwidth * Constants.packetThrottleScale.toNat / dataTotal
  | none => Constants.packetThrottleScale.toNat

/-- Sets peer `p`'s packet throttle limit, lowers its throttle to it, and
starts its next epoch's byte count. -/
def limitPeerThrottle (p : Peer) (limit : Nat) : Peer :=
  let limit := limit.toUInt32
  { p with
    packetThrottleLimit := limit
    packetThrottle      := min p.packetThrottle limit
    outgoingDataTotal   := 0 }

/-- ENet's outgoing half of enet_host_bandwidth_throttle, over an epoch of
`elapsed` ms. First, every connected peer that was queued more bytes than
its own incoming bandwidth takes (at the current host-wide throttle) is
limited to that bandwidth, and its share leaves the host's budget; this
repeats until no more peers are limited. Then every other connected peer
gets the throttle that spreads the rest of the budget over the bytes queued.

The arithmetic is on `Nat`. ENet computes `bandwidth * elapsed` in 32 bits,
which overflows from about 4.3 MB/s up, and subtracts a limited peer's
bandwidth from a host budget that may be smaller, which wraps to "no limit"
(see test/README.md, divergence triage). -/
def outgoingThrottleLimits (h : Host) (elapsed : Nat) : Array Peer :=
  let budget : OutgoingBudget :=
    if h.outgoingBandwidth == 0 then none
    else
      some (h.outgoingBandwidth.toNat * elapsed / 1000,
        h.peers.foldl (init := 0) fun total p => if p.isConnected then total + p.outgoingDataTotal else total)
  let connected := h.peers.filter (·.isConnected) |>.size
  let needsAdjustment := h.peers.any fun p => p.isConnected ∧ p.incomingBandwidth != 0
  let (peers, budget, limited) := limitPeers budget #[] needsAdjustment h.peers (connected + 1)
  if limited.size ≥ connected then peers
  else
    let throttle := budget.throttle
    peers.map fun p =>
      if p.isConnected ∧ !limited.contains p.peerId then limitPeerThrottle p throttle else p
where
  /-- The rounds of limiting peers to their own bandwidth; every round but
  the last limits at least one more peer. -/
  limitPeers (budget : OutgoingBudget) (limited : Array UInt16) (needsAdjustment : Bool) (peers : Array Peer) :
      Nat → Array Peer × OutgoingBudget × Array UInt16
    | 0 => (peers, budget, limited)
    | fuel + 1 =>
      if !needsAdjustment ∨ limited.size ≥ connectedCount peers then (peers, budget, limited)
      else
        let throttle := budget.throttle
        let (peers', budget', limited') :=
          peers.foldl (init := (#[], budget, limited)) fun (acc, budget, limited) p =>
            let peerBandwidth := p.incomingBandwidth.toNat * elapsed / 1000
            if !p.isConnected ∨ p.incomingBandwidth == 0 ∨ limited.contains p.peerId ∨
                throttle * p.outgoingDataTotal / Constants.packetThrottleScale.toNat ≤ peerBandwidth then
              (acc.push p, budget, limited)
            else
              -- `outgoingDataTotal > peerBandwidth` here, so the division is
              -- by a positive total and `dataTotal` does not underflow
              let limit := max 1 (peerBandwidth * Constants.packetThrottleScale.toNat / p.outgoingDataTotal)
              (acc.push (limitPeerThrottle p limit),
                budget.map fun (bandwidth, dataTotal) => (bandwidth - peerBandwidth, dataTotal - peerBandwidth),
                limited.push p.peerId)
        limitPeers budget' limited' (limited'.size > limited.size) peers' fuel
  connectedCount (peers : Array Peer) : Nat := peers.filter (·.isConnected) |>.size

/-- The bandwidth-throttle epoch (every `bandwidthThrottleInterval` ms,
ENet enet_host_bandwidth_throttle): recomputes each connected peer's packet
throttle limit from the host's outgoing bandwidth and, after connects or
disconnects, sends every connected peer its BANDWIDTH_LIMIT. -/
def bandwidthThrottle (h : Host) (now : UInt32) : Host :=
  if Time.difference now h.bandwidthThrottleEpoch < Constants.bandwidthThrottleInterval then h
  else
    let connected := h.peers.filter (·.isConnected)
    if connected.isEmpty then { h with bandwidthThrottleEpoch := now }
    else
      let peers := h.outgoingThrottleLimits (Time.difference now h.bandwidthThrottleEpoch).toNat
      let peers :=
        if !h.recalculateBandwidthLimits then peers
        else
          let (share, marked) :=
            if h.incomingBandwidth == 0 then (0, #[]) else incomingBandwidthShare h.incomingBandwidth connected
          peers.map fun p =>
            if p.isConnected then
              let incoming := if marked.contains p.peerId then p.outgoingBandwidth else share
              p.queueControlCommand (.bandwidthLimit incoming h.outgoingBandwidth)
            else p
      { h with peers, bandwidthThrottleEpoch := now, recalculateBandwidthLimits := false }

/-- The host's periodic step at time `now` (ENet enet_host_service without
the socket): the bandwidth throttle, retransmissions, timeouts and pings,
then packing everything queued into datagrams. Returns the updated host, the
datagrams to transmit and the application events.

Disconnects trigger a bandwidth recalculation (ENet: notify_disconnect and
the ZOMBIE dispatch), except the timeout of a client still connecting. -/
def service (h : Host) (now : UInt32) : Host × Array (Address × ByteArray) × Array Event :=
  let before := h
  let (h, timeoutEvents) := (h.bandwidthThrottle now).checkTimeoutsAndPings now
  let (h, datagrams, disconnectEvents) := h.pollOutgoing now
  -- a timed-out peer is reset by now: its state before the timeout decides
  let connectionChanged := !disconnectEvents.isEmpty || timeoutEvents.any fun
    | .disconnect peerId _ => before.peers[peerId.toNat]?.any (·.state != .connecting)
    | _ => false
  ({ h with recalculateBandwidthLimits := h.recalculateBandwidthLimits || connectionChanged },
    datagrams, timeoutEvents ++ disconnectEvents)

/--
The next time at which this host's state can change, so a driver can sleep
until then instead of busy-polling: between datagram arrivals, calling
`service` at the returned deadline is sufficient. The candidates are
- the retransmit/timeout boundary of every in-flight reliable command
  (`sentTime + roundTripTimeout`),
- the keepalive boundary of every peer that may ping (`pingEligible`,
  `lastReceiveTime + pingInterval`),
- the bandwidth-throttle epoch boundary (always scheduled, so the result is
  never `none` in practice).

The result is the wrap-aware earliest of these (`Time.earliest`, not
numeric `min`; `Proofs/Deadline.lean`). Timestamps are UInt32 milliseconds
and wrap: drivers must compare them with `Lenet.Time`'s arithmetic.
-/
def nextDeadline (h : Host) : Option UInt32 :=
  let peerDeadline := h.peers.foldl (init := none) fun (acc : Option UInt32) p =>
    -- retransmit boundaries of in-flight reliable commands
    let inFlight := p.sentReliableCommands.foldl (init := acc) fun a outCmd =>
      Time.earliestSome a (outCmd.sentTime + outCmd.roundTripTimeout)
    -- keepalive boundary: only peers that could actually ping right now
    if pingEligible p then
      Time.earliestSome inFlight (p.lastReceiveTime + p.pingInterval)
    else
      inFlight
  Time.earliestSome peerDeadline (h.bandwidthThrottleEpoch + Constants.bandwidthThrottleInterval)

end Host

end Lenet
