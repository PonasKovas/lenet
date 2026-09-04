import Lenet.Constants
import Lenet.Time
import Lenet.Checksum
import Lenet.Address
import Lenet.Packet
import Lenet.Channel
import Lenet.OutgoingCommand
import Lenet.Event
import Lenet.Peer
import Lenet.Protocol.Header
import Lenet.Protocol.Command
import Lenet.Protocol.Datagram

namespace Lenet

/--
Top-level sans-I/O ENet host coordinator.
Manages an array of peer connection slots, connection negotiation,
datagram packaging, and bandwidth limits.
-/
structure Host where
  address                : Address := {}
  peers                  : Array Peer := #[]
  channelLimit           : Nat := Constants.maximumChannelCount
  incomingBandwidth      : UInt32 := 0
  outgoingBandwidth      : UInt32 := 0
  bandwidthThrottleEpoch : UInt32 := 0
  /-- ENet: set when a connect/disconnect event should cause BANDWIDTH_LIMIT
  commands to be queued at the next bandwidth throttle epoch. -/
  recalculateBandwidthLimits : Bool := false
  mtu                    : UInt32 := Constants.defaultMtu.toUInt32
  randomSeed             : UInt32 := 0x12345678
  compressor             : Option Compressor := none
  checksumEnabled        : Bool := false
  maximumPacketSize      : Nat := 32 * 1024 * 1024
deriving Inhabited

namespace Host

/-- ENet's bandwidth-derived receive window size (protocol.c: same formula at
connect, handle_connect, handle_verify_connect and handle_bandwidth_limit):
- both bandwidths 0 → maximum window
- exactly one set → `max(hostOutBw, peerInBw) / 64k * 4096`
- both set → `min(hostOutBw, peerInBw) / 64k * 4096`
clamped to `[minimumWindowSize, maximumWindowSize]`. -/
def windowSizeFor (hostOutBw : UInt32) (peerInBw : UInt32) : UInt32 :=
  let scale := Constants.windowSizeScale.toNat
  let raw : Nat :=
    if peerInBw.toNat == 0 ∧ hostOutBw.toNat == 0 then
      Constants.maximumWindowSize
    else if peerInBw.toNat == 0 ∨ hostOutBw.toNat == 0 then
      Nat.max peerInBw.toNat hostOutBw.toNat / scale * Constants.minimumWindowSize
    else
      Nat.min peerInBw.toNat hostOutBw.toNat / scale * Constants.minimumWindowSize
  Nat.min Constants.maximumWindowSize (Nat.max Constants.minimumWindowSize raw) |>.toUInt32

/-- Creates an initialized host with `peerCount` allocated peer slots. -/
def create (address : Address := {}) (peerCount : Nat := 32) (channelLimit : Nat := Constants.maximumChannelCount) (inBw : UInt32 := 0) (outBw : UInt32 := 0) (seed : UInt32 := 0x87654321) : Host :=
  let cl := if channelLimit == 0 ∨ channelLimit > Constants.maximumChannelCount then Constants.maximumChannelCount else channelLimit
  let peers := (List.range peerCount).toArray.map fun idx =>
    Peer.create idx.toUInt16 1 address
  {
    address
    peers
    channelLimit      := cl
    incomingBandwidth := inBw
    outgoingBandwidth := outBw
    randomSeed        := seed
  }

/-- Mulberry32 deterministic PRNG step for generating connect IDs. -/
def random (h : Host) : Host × UInt32 :=
  let seed := h.randomSeed + 0x6D2B79F5
  let n0 := seed
  let n1 := (n0 ^^^ (n0 >>> 15)) * (n0 ||| 1)
  let n2 := n1 ^^^ (n1 + (n1 ^^^ (n1 >>> 7)) * (n1 ||| 61))
  let result := n2 ^^^ (n2 >>> 14)
  ({ h with randomSeed := seed }, result)

/--
Initiates an outgoing connection to `remoteAddress` with `channelCount` channels.
Returns the updated host and the allocated `peerId`.
-/
def connect (h : Host) (remoteAddress : Address) (channelCount : Nat := 2) (data : UInt32 := 0) : Except String (Host × UInt16) := do
  let freeIdx? := h.peers.findIdx? fun p => p.state == .disconnected
  match freeIdx? with
  | none =>
    throw "No available peer slots for initiating connection"
  | some idx =>
    let (hRand, connectId) := h.random
    let channels := if channelCount == 0 then 1 else Nat.min channelCount hRand.channelLimit
    let p := hRand.peers[idx]?.getD default
    let peerChannels := Array.replicate channels Channel.init
    -- Control commands on channel 0xFF share a pre-incremented counter;
    -- the CONNECT is the first reliable control command (seq 1).
    let (p, controlSeq) := p.nextControlSeq

    let connectParams : Protocol.ConnectParams := {
      outgoingPeerId             := p.peerId
      incomingSessionId          := 0xFF
      outgoingSessionId          := 0xFF
      mtu                        := hRand.mtu
      -- ENet: the client's window derives from its own outgoing bandwidth
      -- (enet_host_connect); a fresh peer slot has incomingBandwidth = 0.
      windowSize                 := windowSizeFor hRand.outgoingBandwidth 0
      channelCount               := channels.toUInt32
      incomingBandwidth          := hRand.incomingBandwidth
      outgoingBandwidth          := hRand.outgoingBandwidth
      packetThrottleInterval     := p.packetThrottleInterval
      packetThrottleAcceleration := p.packetThrottleAcceleration
      packetThrottleDeceleration := p.packetThrottleDeceleration
      connectId                  := connectId
    }

    let cmd : Protocol.Command := {
      channelId              := 0xFF
      reliableSequenceNumber := controlSeq
      acknowledge            := true
      unsequenced            := false
      body                   := .connect connectParams data
    }

    let outCmd : OutgoingCommand := {
      command        := cmd
      fragmentOffset := 0
      fragmentLength := 0
    }

    let updatedPeer := { p with
      address   := remoteAddress
      state     := .connecting
      connectId := connectId
      channels  := peerChannels
      eventData := data
    }.queueOutgoingCommand outCmd

    let newPeers :=
      if hIdx : idx < hRand.peers.size then
        hRand.peers.set idx updatedPeer hIdx
      else
        hRand.peers

    -- ENet: notify_connect flags a bandwidth recalculation.
    return ({ hRand with peers := newPeers, recalculateBandwidthLimits := true }, p.peerId)

/-- Sends a packet to a specific connected peer. -/
def send (h : Host) (peerId : UInt16) (channelId : UInt8) (packet : Packet) : Except String Host := do
  let idx := peerId.toNat
  if hIdx : idx < h.peers.size then
    let p := h.peers[idx]
    let updatedPeer ← p.send channelId packet h.checksumEnabled
    return { h with peers := h.peers.set idx updatedPeer hIdx }
  else
    throw s!"Invalid peerId {peerId}"

/-- Broadcasts a packet across all connected peers. -/
def broadcast (h : Host) (channelId : UInt8) (packet : Packet) : Host :=
  let newPeers := h.peers.map fun p =>
    if p.state == .connected then
      (p.send channelId packet h.checksumEnabled).toOption.getD p
    else
      p
  { h with peers := newPeers }

/-- Initiates graceful disconnection of a peer. -/
def disconnect (h : Host) (peerId : UInt16) (data : UInt32 := 0) : Host :=
  let idx := peerId.toNat
  if hIdx : idx < h.peers.size then
    let p := h.peers[idx]
    -- Control commands on channel 0xFF share a pre-incremented counter.
    let (p, controlSeq) := p.nextControlSeq
    let cmd : Protocol.Command := {
      channelId              := 0xFF
      reliableSequenceNumber := controlSeq
      acknowledge            := true
      unsequenced            := false
      body                   := .disconnect data
    }
    let outCmd : OutgoingCommand := { command := cmd }
    let updatedPeer := { p with state := .disconnecting, eventData := data }.queueOutgoingCommand outCmd
    { h with peers := h.peers.set idx updatedPeer hIdx }
  else
    h

/-- ENet's deferred disconnect (enet_peer_disconnect_later): if the peer
still has commands queued or in flight, enter `disconnectLater` and defer
the DISCONNECT until everything is flushed; otherwise disconnect now. -/
def disconnectLater (h : Host) (peerId : UInt16) (data : UInt32 := 0) : Host :=
  let idx := peerId.toNat
  if hIdx : idx < h.peers.size then
    let p := h.peers[idx]
    if (p.state == .connected ∨ p.state == .disconnectLater) ∧
       (!p.outgoingCommands.isEmpty ∨ !p.sentReliableCommands.isEmpty) then
      { h with peers := h.peers.set idx { p with state := .disconnectLater, eventData := data } hIdx }
    else
      h.disconnect peerId data
  else
    h

/-- ENet's disconnectLater drain transition (protocol.c:1593): once a
`disconnectLater` peer has no queued or in-flight commands left, the queued
DISCONNECT (carrying the deferred data) goes out. -/
def flushDisconnectLater (p : Peer) : Peer :=
  if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty then
    let (p, controlSeq) := p.nextControlSeq
    let cmd : Protocol.Command := {
      channelId              := 0xFF
      reliableSequenceNumber := controlSeq
      acknowledge            := true
      unsequenced            := false
      body                   := .disconnect p.eventData
    }
    { p with state := .disconnecting }.queueOutgoingCommand { command := cmd }
  else
    p

/--
Consumes an incoming raw UDP datagram received from `fromAddr`.
Updates host/peer states, processes commands, and emits high-level `Event`s.
-/
def handleDatagram (h : Host) (now : UInt32) (fromAddr : Address) (bytes : ByteArray) : Host × Array Event :=
  -- 1. Decode datagram. When checksums are enabled, the verification key is
  -- the target peer's connectID (ENet enet_protocol_receive): 0 for the
  -- broadcast peer 0xFFF, the slot's stored connectID otherwise.
  let connectIdOf : UInt16 → UInt32 := fun peerId =>
    if peerId == Constants.maximumPeerId then 0
    else match h.peers[peerId.toNat]? with
      | some p => p.connectId
      | none => 0
  let decodeResult :=
    ReaderM.run (Protocol.Datagram.decodeWith h.checksumEnabled (some connectIdOf) h.compressor) bytes
  match decodeResult with
  | .error _ =>
    (h, #[])
  | .ok datagram =>
    let peerId := datagram.header.peerId

    -- Case A: Incoming connection request to server:
    if peerId == Constants.maximumPeerId then
      if let some cmd := datagram.commands[0]? then
        match cmd.body with
        | .connect params data =>
          -- ENet (handle_connect) rejects channel counts outside [1, 255]
          -- outright; anything else would corrupt the channel allocation.
          if params.channelCount.toNat < Constants.minimumChannelCount ∨
             params.channelCount.toNat > Constants.maximumChannelCount then
            (h, #[])
          else
            let freeIdx? := h.peers.findIdx? fun p => p.state == .disconnected
            match freeIdx? with
            | some idx =>
              let p := h.peers[idx]?.getD default
              let channels := Nat.min params.channelCount.toNat h.channelLimit
              let peerChannels := Array.replicate channels Channel.init

              -- ENet session negotiation (enet_protocol_handle_connect): each
              -- side's `outgoing` session ID = (peer's `incoming` + 1) mod 4,
              -- with 0xFF meaning "unset". Forwarding 0xFF verbatim would set
              -- the header's compressed-flag bit in every later datagram.
              let outSession :=
                let base := if params.incomingSessionId == 0xFF then p.outgoingSessionId else params.incomingSessionId
                let inc := (base + 1) &&& 3
                if inc == p.outgoingSessionId then (inc + 1) &&& 3 else inc
              let inSession :=
                let base := if params.outgoingSessionId == 0xFF then p.incomingSessionId else params.outgoingSessionId
                let inc := (base + 1) &&& 3
                if inc == p.incomingSessionId then (inc + 1) &&& 3 else inc
              -- ENet: the peer's receive window derives from the host's outgoing
              -- bandwidth and the peer's offered incoming bandwidth
              -- (enet_protocol_handle_connect).
              let peerWindowSize := windowSizeFor h.outgoingBandwidth params.incomingBandwidth
              -- ENet: the VERIFY_CONNECT advertises the server's incoming-
              -- bandwidth-derived window, shrunk to the client's offer.
              let hostInWindow : UInt32 :=
                if h.incomingBandwidth == 0 then Constants.maximumWindowSize.toUInt32
                else (h.incomingBandwidth.toNat / Constants.windowSizeScale.toNat * Constants.minimumWindowSize).toUInt32
              let verifyWindow := Nat.min Constants.maximumWindowSize (Nat.max Constants.minimumWindowSize
                (Nat.min hostInWindow.toNat params.windowSize.toNat)) |>.toUInt32
              -- ENet (handle_connect): the offered MTU is clamped to
              -- [minimumMtu, maximumMtu] *before* the min with the host's MTU;
              -- a hostile mtu=0 must not collapse the peer's MTU.
              let peerMtu :=
                Nat.min h.mtu.toNat
                  (Nat.min Constants.maximumMtu
                    (Nat.max Constants.minimumMtu params.mtu.toNat))
              let verifyParams : Protocol.ConnectParams := {
                outgoingPeerId             := p.peerId
                incomingSessionId          := outSession
                outgoingSessionId          := inSession
                mtu                        := peerMtu.toUInt32
                windowSize                 := verifyWindow
                channelCount               := channels.toUInt32
                incomingBandwidth          := h.incomingBandwidth
                outgoingBandwidth          := h.outgoingBandwidth
                packetThrottleInterval     := p.packetThrottleInterval
                packetThrottleAcceleration := p.packetThrottleAcceleration
                packetThrottleDeceleration := p.packetThrottleDeceleration
                connectId                  := params.connectId
              }

              let verifyCmd : Protocol.Command := {
                channelId              := 0xFF
                reliableSequenceNumber := 1
                acknowledge            := true
                unsequenced            := false
                body                   := .verifyConnect verifyParams
              }

              let outCmd : OutgoingCommand := { command := verifyCmd }
              -- Control commands on channel 0xFF share a pre-incremented counter;
              -- the VERIFY_CONNECT is the server's first control command (seq 1).
              let (updatedPeer, controlSeq) := p.nextControlSeq
              let verifyCmd := { verifyCmd with reliableSequenceNumber := controlSeq }
              let outCmd := { outCmd with command := verifyCmd }
              let updatedPeer := { updatedPeer with
                address              := fromAddr
                outgoingPeerId       := params.outgoingPeerId
                connectId            := params.connectId
                state                := .acknowledgingConnect
                channels             := peerChannels
                eventData            := data
                mtu                  := peerMtu.toUInt32
                windowSize           := peerWindowSize
                incomingBandwidth    := params.incomingBandwidth
                outgoingBandwidth    := params.outgoingBandwidth
                incomingSessionId    := inSession
                outgoingSessionId    := outSession
              }.queueOutgoingCommand outCmd

              let newPeers := if hIdx : idx < h.peers.size then h.peers.set idx updatedPeer hIdx else h.peers
              ({ h with peers := newPeers }, #[])
            | none =>
              (h, #[])
        | _ =>
          (h, #[])
      else
        (h, #[])

    -- Case B: Traffic for an existing peer:
    else
      let idx := peerId.toNat
      if hIdx : idx < h.peers.size then
        let p := h.peers[idx]
        -- ENet peer lookup (protocol.c): datagrams for a negotiated peer must
        -- come from the peer's address (broadcast targets exempt). This drops
        -- datagrams whose header peerId collides with a different host's peer.
        if p.outgoingPeerId < Constants.maximumPeerId ∧
           (!(p.address == {}) && p.address.host != Address.broadcast &&
              fromAddr != p.address) then
          (h, #[])
        -- ENet (protocol.c peer lookup): datagrams for disconnected or zombie
        -- peers are dropped outright - no ACKs, no state changes.
        else if p.state == .disconnected ∨ p.state == .zombie then
          (h, #[])
        else
          -- ENet drops datagrams whose header session doesn't match the peer's
          -- negotiated incoming session ID (protocol.c peer lookup). The check
          -- only applies once the remote peer ID is known (post-negotiation);
          -- while `outgoingPeerId` is unset (0xFFF) any session is tolerated.
          if p.outgoingPeerId < Constants.maximumPeerId ∧
             datagram.header.session ≠ p.incomingSessionId then
            (h, #[])
          else
            let (curPeer, events) := datagram.commands.foldl (init := (p, #[])) fun (cur, evs) cmd =>
              let (nextPeer, newEvs) := cur.handleCommand now cmd datagram.header.sentTime
              (nextPeer, evs ++ newEvs)
            -- ENet (handle_bandwidth_limit): a BANDWIDTH_LIMIT command also
            -- recomputes the peer's receive window from the (just-updated) peer
            -- incoming bandwidth and the host's outgoing bandwidth. The recompute
            -- happens here because the formula needs host-level state; with the
            -- fold's last-write-wins semantics this matches ENet's per-command
            -- recompute.
            let bwChanged := datagram.commands.any fun c =>
              match c.body with | .bandwidthLimit _ _ => true | _ => false
            let curPeer :=
              if bwChanged then
                { curPeer with windowSize := windowSizeFor h.outgoingBandwidth curPeer.incomingBandwidth }
              else curPeer
            let newPeers := h.peers.set idx curPeer hIdx
            -- ENet: connect/disconnect notifications flag a bandwidth recalculation.
            let recalc := events.any fun
              | .connect _ _ => true
              | .disconnect _ _ => true
              | .receive _ _ _ => false
            ({ h with peers := newPeers, recalculateBandwidthLimits := h.recalculateBandwidthLimits || recalc }, events)
      else
        (h, #[])

/-- Formats queued pending ACKs into outgoing acknowledge commands. -/
def formatAcks (acks : Array (UInt8 × UInt16 × UInt16)) : Array Protocol.Command :=
  acks.map fun (chId, seq, st) => {
    channelId              := chId
    reliableSequenceNumber := seq
    acknowledge            := false
    unsequenced            := false
    body                   := .acknowledge seq st
  }

structure PackState where
  packedAcks        : Array (UInt8 × UInt16 × UInt16) := #[]
  commandsToPack    : Array Protocol.Command := #[]
  remainingOutgoing : Array OutgoingCommand := #[]
  sentReliables     : Array OutgoingCommand
  inTransitAdd      : Nat := 0
  packetSize        : Nat := 0
  commandCount      : Nat := 0

/-- Size of a serialized command's fixed part (4-byte command header +
body fields, excluding any packet payload). The payload is accounted for
separately via `fragmentLength`, matching ENet's packetSize arithmetic. -/
def commandWireSize (body : Protocol.CommandBody) : Nat :=
  4 + match body with
    | .acknowledge ..             => 4
    | .connect ..                 => 44
    | .verifyConnect ..           => 40
    | .disconnect ..              => 4
    | .ping                       => 0
    | .sendReliable _             => 2
    | .sendUnreliable _ _         => 4
    | .sendFragment _             => 20
    | .sendUnsequenced _ _        => 4
    | .bandwidthLimit ..          => 8
    | .throttleConfigure ..       => 12
    | .sendUnreliableFragment _   => 20

/-- Packs pending ACKs and outgoing commands for a peer, honoring the
32-command cap and the peer MTU (ENet's packing rules: ACKs first, then
queued commands; window-blocked and over-budget commands stay queued).
Returns the updated peer and the commands to place in one datagram. -/
def packOutgoingCommands (p : Peer) (now : UInt32) : Peer × Array Protocol.Command :=
  let ackSize := commandWireSize (.acknowledge 0 0)
  let initial : PackState := {
    packetSize    := 4 -- ENetProtocolHeader, always budgeted first
    sentReliables := p.sentReliableCommands
  }
  -- 1. ACKs first (ENet: enet_protocol_send_acknowledgements).
  let withAcks := p.acknowledgements.foldl (init := initial) fun acc ack =>
    if acc.commandCount ≥ Constants.maximumPacketCommands ∨
       acc.packetSize + ackSize > p.mtu.toNat then
      acc -- over budget; ENet flags CONTINUE_SENDING and stops
    else
      { acc with
        packedAcks   := acc.packedAcks.push ack
        packetSize   := acc.packetSize + ackSize
        commandCount := acc.commandCount + 1 }
  -- 2. Outgoing commands (ENet: enet_protocol_check_outgoing_commands).
  let finalState := p.outgoingCommands.foldl (init := withAcks) fun acc outCmd =>
    let cmdSize := commandWireSize outCmd.command.body
    if acc.commandCount ≥ Constants.maximumPacketCommands ∨
       acc.packetSize + cmdSize + outCmd.fragmentLength > p.mtu.toNat then
      { acc with remainingOutgoing := acc.remainingOutgoing.push outCmd }
    else
      let isWindowAvail :=
        if outCmd.command.acknowledge then
          if outCmd.command.channelId == 0xFF then
            true
          else
            let chIdx := outCmd.command.channelId.toNat
            if chH : chIdx < p.channels.size then
              p.channels[chIdx].canSendReliable outCmd.command.reliableSequenceNumber
            else
              true
        else
          true
      if outCmd.command.acknowledge && !isWindowAvail then
        { acc with remainingOutgoing := acc.remainingOutgoing.push outCmd }
      else
        -- ENet (check_outgoing_commands): reliable commands carrying a packet
        -- are blocked while the reliable data in flight exceeds the
        -- throttle-scaled receive window (`reliableDataInTransit +
        -- fragmentLength > max(throttle * windowSize, mtu)`). Blocked
        -- commands stay queued; they don't add to in-transit, so every
        -- further payload command is blocked the same way within the pass.
        let isCongested :=
          outCmd.command.acknowledge ∧ outCmd.fragmentLength > 0 ∧
            p.reliableDataInTransit + acc.inTransitAdd + outCmd.fragmentLength >
              Nat.max ((p.packetThrottle * p.windowSize) / Constants.packetThrottleScale).toNat p.mtu.toNat
        if isCongested then
          { acc with remainingOutgoing := acc.remainingOutgoing.push outCmd }
        else
          let inFlightCmd := { outCmd with
            sendAttempts := outCmd.sendAttempts + 1
            sentTime     := now
            roundTripTimeout :=
              -- ENet: initialize on first send from the peer's RTT estimate.
              if outCmd.roundTripTimeout == 0 then
                p.roundTripTime + 4 * p.roundTripTimeVariance
              else
                outCmd.roundTripTimeout
          }
          -- Only reliable (ack-flagged) commands are tracked in-flight for
          -- retransmission; others are fire-and-forget (ENet semantics).
          let acc :=
            if outCmd.command.acknowledge then
              { acc with
                sentReliables := acc.sentReliables.push inFlightCmd
                inTransitAdd  := acc.inTransitAdd + outCmd.fragmentLength }
            else acc
          { acc with
            commandsToPack := acc.commandsToPack.push outCmd.command
            packetSize     := acc.packetSize + cmdSize + outCmd.fragmentLength
            commandCount   := acc.commandCount + 1 }

  let updatedPeer := { p with
    acknowledgements      := p.acknowledgements.drop withAcks.packedAcks.size
    outgoingCommands      := finalState.remainingOutgoing
    sentReliableCommands  := finalState.sentReliables
    reliableDataInTransit := p.reliableDataInTransit + finalState.inTransitAdd
  }
  (updatedPeer, formatAcks withAcks.packedAcks ++ finalState.commandsToPack)

/-- Polls a single peer for outgoing datagrams. Loops until no further
progress is possible, mirroring ENet's CONTINUE_SENDING multi-pass packing:
each pass produces one MTU-bounded datagram. -/
def pollPeer (p : Peer) (now : UInt32) (checksumEnabled : Bool) (compressor : Option Compressor) : Peer × Array (Address × ByteArray) :=
  if p.state == .disconnected then
    (p, #[])
  else
    let rec loop (p : Peer) (fuel : Nat) (acc : Array (Address × ByteArray)) : Peer × Array (Address × ByteArray) :=
      match fuel with
      | 0 => (p, acc)
      | fuel' + 1 =>
        let p := flushDisconnectLater p
        let (updatedPeer, commandsToPack) := packOutgoingCommands p now
        if commandsToPack.isEmpty then
          (updatedPeer, acc)
        else
          let header : Protocol.Header := {
            peerId     := updatedPeer.outgoingPeerId
            session    := updatedPeer.outgoingSessionId
            compressed := false
            sentTime   := some (now.toUInt16)
          }
          let datagram : Protocol.Datagram := {
            header
            checksum := if checksumEnabled then some 0 else none
            commands := commandsToPack
          }
          -- ENet: the checksum field holds the peer's connectID during
          -- computation, 0 while the peer's outgoing ID is still unset
          -- (pre-negotiation, e.g. the client's CONNECT).
          let connectId :=
            if updatedPeer.outgoingPeerId < Constants.maximumPeerId then
              updatedPeer.connectId
            else
              0
          let datagramBytes := datagram.encodeWith compressor connectId
          loop updatedPeer fuel' (acc.push (updatedPeer.address, datagramBytes))
    -- fuel bounds the number of datagrams per poll (one per queued command is
    -- more than enough)
    loop p (p.outgoingCommands.size + 1) #[]

/--
Packages pending ACKs and outgoing commands across all peers into datagrams.
Returns the updated host and the array of outgoing `(destinationAddress, datagramBytes)`.
-/
def pollOutgoing (h : Host) (now : UInt32) : Host × Array (Address × ByteArray) :=
  let (updatedPeers, packets) := h.peers.foldl (init := (#[], #[])) fun (peersAcc, pktsAcc) p =>
    let (p', pkts) := pollPeer p now h.checksumEnabled h.compressor
    (peersAcc.push p', pktsAcc ++ pkts)
  ({ h with peers := updatedPeers }, packets)

structure TimeoutCheckResult where
  stillInFlight   : Array OutgoingCommand := #[]
  retransmits     : Array OutgoingCommand := #[]
  isTimedOut      : Bool := false
  earliestTimeout : UInt32 := 0

/-- Evaluates in-flight reliable commands for timeouts and retransmissions. -/
def checkPeerTimeouts (p : Peer) (now : UInt32) : Peer × Option Event :=
  let initial : TimeoutCheckResult := { earliestTimeout := p.earliestTimeout }
  let result := p.sentReliableCommands.foldl (init := initial) fun acc outCmd =>
    if acc.isTimedOut then
      acc
    else
      let elapsed := Time.difference now outCmd.sentTime
      if elapsed ≥ outCmd.roundTripTimeout then
        -- ENet: track the earliest timed-out command's sentTime.
        let earliest :=
          if acc.earliestTimeout == 0 ∨ Time.less outCmd.sentTime acc.earliestTimeout then
            outCmd.sentTime
          else
            acc.earliestTimeout
        let acc := { acc with earliestTimeout := earliest }
        if p.isTimedOut now outCmd.sendAttempts then
          { acc with isTimedOut := true }
        else
          let retryCmd := { outCmd with
            roundTripTimeout := outCmd.roundTripTimeout * 2
          }
          { acc with retransmits := acc.retransmits.push retryCmd }
      else
        { acc with stillInFlight := acc.stillInFlight.push outCmd }

  if result.isTimedOut then
    let deadPeer := { p with state := .zombie, earliestTimeout := result.earliestTimeout }
    -- ENet's notify_disconnect always reports data = 0 on this path.
    (deadPeer, some (Event.disconnect p.peerId 0))
  else
    let newOutgoing := result.retransmits ++ p.outgoingCommands
    let pUpdated := { p with
      sentReliableCommands := result.stillInFlight
      outgoingCommands     := newOutgoing
      earliestTimeout      := result.earliestTimeout
    }
    (pUpdated, none)

/-- Sends a ping if the peer is connected and has been idle longer than `pingInterval`. -/
def checkPeerPing (p : Peer) (now : UInt32) : Peer :=
  if p.state == .connected ∧
     p.sentReliableCommands.isEmpty ∧
     p.outgoingCommands.isEmpty ∧
     (Time.difference now p.lastReceiveTime ≥ p.pingInterval) then
    -- Pings are reliable control commands on channel 0xFF (share the counter).
    let (p, controlSeq) := p.nextControlSeq
    let pingCmd : Protocol.Command := {
      channelId              := 0xFF
      reliableSequenceNumber := controlSeq
      acknowledge            := true
      unsequenced            := false
      body                   := .ping
    }
    p.queueOutgoingCommand { command := pingCmd }
  else
    p

/--
Sweeps all active peers to check for timeouts on in-flight reliable commands,
retransmissions, and periodic ping keepalives.
Returns the updated `Host` and any disconnect `Event`s triggered by timeouts.
-/
def checkTimeoutsAndPings (h : Host) (now : UInt32) : Host × Array Event :=
  let (updatedPeers, events) := h.peers.foldl (init := (#[], #[])) fun (peersAcc, evsAcc) p =>
    if p.state == .disconnected ∨ p.state == .zombie then
      (peersAcc.push p, evsAcc)
    else
      let (pAfterTimeout, timeoutEvOpt) := checkPeerTimeouts p now
      match timeoutEvOpt with
      | some ev =>
        (peersAcc.push pAfterTimeout, evsAcc.push ev)
      | none =>
        let pAfterPing := checkPeerPing pAfterTimeout now
        (peersAcc.push pAfterPing, evsAcc)

  ({ h with peers := updatedPeers }, events)

/--
Dynamically recalculates peer bandwidth allocations and packet throttle limits
over each 1000ms epoch.
-/
def bandwidthThrottle (h : Host) (now : UInt32) : Host :=
  let elapsed := Time.difference now h.bandwidthThrottleEpoch
  if elapsed < Constants.bandwidthThrottleInterval then
    h
  else
    let connectedPeers := h.peers.filter (fun p => p.state == .connected ∨ p.state == .disconnectLater)
    if connectedPeers.isEmpty then
      { h with bandwidthThrottleEpoch := now }
    else
      let updatedPeers := h.peers.map fun p =>
        if p.state == .connected ∨ p.state == .disconnectLater then
          let pThrottled :=
            if h.outgoingBandwidth > 0 then
              let totalData := p.reliableDataInTransit.toUInt32
              let peerShare := h.outgoingBandwidth / connectedPeers.size.toUInt32
              let throttle :=
                if totalData ≤ peerShare then
                  Constants.packetThrottleScale
                else
                  (peerShare * Constants.packetThrottleScale) / (if totalData == 0 then 1 else totalData)
              { p with packetThrottleLimit := Nat.max 1 throttle.toNat |>.toUInt32 }
            else
              { p with packetThrottleLimit := Constants.packetThrottleScale }
          pThrottled
        else
          p
      -- ENet: when recalculateBandwidthLimits is set, queue a BANDWIDTH_LIMIT
      -- command for every connected peer at the epoch boundary
      -- (enet_host_bandwidth_throttle, recalculateBandwidthLimits block).
      -- ENet iteratively shares the host's incoming bandwidth out: a peer
      -- whose own outgoing bandwidth is below the current per-peer share gets
      -- marked and its rate is removed from the pool; marked peers are told
      -- to limit their incoming to their own outgoing rate, unmarked peers
      -- get the final share.
      let (updatedPeers, recalc) :=
        if h.recalculateBandwidthLimits then
          let connected := connectedPeers
          let rec loop (bandwidth : UInt32) (peersRemaining : Nat) (bandwidthLimit : UInt32)
              (marked : Array UInt16) (fuel : Nat) : UInt32 × UInt32 × Array UInt16 :=
            match fuel with
            | 0 => (bandwidth, bandwidthLimit, marked)
            | fuel' + 1 =>
              if peersRemaining == 0 then
                (bandwidth, bandwidthLimit, marked)
              else
                let bandwidthLimit := bandwidth / peersRemaining.toUInt32
                let (bandwidth', peersRemaining', marked') :=
                  connected.foldl (init := (bandwidth, peersRemaining, marked)) fun acc p =>
                    let (bw, remaining, markedIds) := acc
                    if markedIds.contains p.peerId ∨
                       (p.outgoingBandwidth > 0 ∧ p.outgoingBandwidth >= bandwidthLimit) then
                      (bw, remaining, markedIds)
                    else
                      (bw - p.outgoingBandwidth, remaining - 1, markedIds.push p.peerId)
                if marked'.size > marked.size then
                  loop bandwidth' peersRemaining' bandwidthLimit marked' fuel'
                else
                  (bandwidth', bandwidthLimit, marked')
          let (bandwidthLimit, marked) :=
            if h.incomingBandwidth == 0 then
              ((0 : UInt32), (#[] : Array UInt16))
            else
              let (bw, bl, markedIds) := loop h.incomingBandwidth connected.size 0 #[] (connected.size + 2)
              (bl, markedIds)
          let updatedPeers := updatedPeers.map fun p =>
            if p.state == .connected ∨ p.state == .disconnectLater then
              let (p, controlSeq) := p.nextControlSeq
              let incoming : UInt32 :=
                if marked.contains p.peerId then p.outgoingBandwidth else bandwidthLimit
              let cmd : Protocol.Command := {
                channelId              := 0xFF
                reliableSequenceNumber := controlSeq
                acknowledge            := true
                unsequenced            := false
                body                   := .bandwidthLimit incoming h.outgoingBandwidth
              }
              let p := { p with incomingBandwidthThrottleEpoch := now }
              p.queueOutgoingCommand { command := cmd }
            else p
          (updatedPeers, false)
        else (updatedPeers, h.recalculateBandwidthLimits)
      { h with
        peers                       := updatedPeers
        bandwidthThrottleEpoch      := now
        recalculateBandwidthLimits  := recalc
      }

/--
Master sans-I/O service step for the host:
1. Recalculates bandwidth limits and throttling.
2. Checks timeouts, retransmissions, and pings across all peers.
3. Packages pending ACKs and outgoing commands into MTU-bounded datagrams.
Returns the updated `Host`, outgoing datagrams to transmit, and any application `Event`s.
-/
def service (h : Host) (now : UInt32) : Host × Array (Address × ByteArray) × Array Event :=
  let hThrottled := h.bandwidthThrottle now
  let (hTimedOut, timeoutEvents) := hThrottled.checkTimeoutsAndPings now
  let (hPolled, outgoingPackets) := hTimedOut.pollOutgoing now
  (hPolled, outgoingPackets, timeoutEvents)

end Host

end Lenet