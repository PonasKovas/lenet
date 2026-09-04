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
  address           : Address := {}
  peers             : Array Peer := #[]
  channelLimit      : Nat := Constants.maximumChannelCount
  incomingBandwidth : UInt32 := 0
  outgoingBandwidth : UInt32 := 0
  mtu               : UInt32 := Constants.minimumMtu.toUInt32
  randomSeed        : UInt32 := 0x12345678
  compressor        : Option Compressor := none
  checksumEnabled   : Bool := false
  maximumPacketSize : Nat := 32 * 1024 * 1024
deriving Inhabited

namespace Host

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

    let connectParams : Protocol.ConnectParams := {
      outgoingPeerId             := p.peerId
      incomingSessionId          := 0xFF
      outgoingSessionId          := 0xFF
      mtu                        := hRand.mtu
      windowSize                 := Constants.maximumWindowSize.toUInt32
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
      reliableSequenceNumber := 1
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
      mtu       := hRand.mtu
    }.queueOutgoingCommand outCmd

    let newPeers :=
      if hIdx : idx < hRand.peers.size then
        hRand.peers.set idx updatedPeer hIdx
      else
        hRand.peers

    return ({ hRand with peers := newPeers }, p.peerId)

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
    let cmd : Protocol.Command := {
      channelId              := 0xFF
      reliableSequenceNumber := 0
      acknowledge            := true
      unsequenced            := false
      body                   := .disconnect data
    }
    let outCmd : OutgoingCommand := { command := cmd }
    let updatedPeer := { p with state := .disconnecting, eventData := data }.queueOutgoingCommand outCmd
    { h with peers := h.peers.set idx updatedPeer hIdx }
  else
    h

/--
Consumes an incoming raw UDP datagram received from `fromAddr`.
Updates host/peer states, processes commands, and emits high-level `Event`s.
-/
def handleDatagram (h : Host) (now : UInt32) (fromAddr : Address) (bytes : ByteArray) : Host × Array Event :=
  -- 1. Decode datagram:
  let decodeResult := ReaderM.run (Protocol.Datagram.decodeWith h.checksumEnabled h.compressor) bytes
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
          let freeIdx? := h.peers.findIdx? fun p => p.state == .disconnected
          match freeIdx? with
          | some idx =>
            let p := h.peers[idx]?.getD default
            let channels := Nat.min params.channelCount.toNat h.channelLimit
            let peerChannels := Array.replicate channels Channel.init

            let verifyParams : Protocol.ConnectParams := {
              outgoingPeerId             := p.peerId
              incomingSessionId          := params.outgoingSessionId
              outgoingSessionId          := params.incomingSessionId
              mtu                        := Nat.min h.mtu.toNat params.mtu.toNat |>.toUInt32
              windowSize                 := Constants.maximumWindowSize.toUInt32
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
            let updatedPeer := { p with
              address        := fromAddr
              outgoingPeerId := params.outgoingPeerId
              connectId      := params.connectId
              state          := .acknowledgingConnect
              channels       := peerChannels
              eventData      := data
              mtu            := verifyParams.mtu
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
        let (curPeer, events) := datagram.commands.foldl (init := (p, #[])) fun (cur, evs) cmd =>
          let (nextPeer, newEvs) := cur.handleCommand now cmd datagram.header.sentTime
          (nextPeer, evs ++ newEvs)
        let newPeers := h.peers.set idx curPeer hIdx
        ({ h with peers := newPeers }, events)
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
  commandsToPack    : Array Protocol.Command := #[]
  remainingOutgoing : Array OutgoingCommand := #[]
  sentReliables     : Array OutgoingCommand
  inTransitAdd      : Nat := 0

/-- Packs pending ACKs and outgoing commands for a peer, honoring channel window limits. -/
def packOutgoingCommands (p : Peer) (now : UInt32) : Peer × Array Protocol.Command :=
  let ackCommands := formatAcks p.acknowledgements
  let initial : PackState := {
    commandsToPack := ackCommands
    sentReliables  := p.sentReliableCommands
  }
  let finalState := p.outgoingCommands.foldl (init := initial) fun acc outCmd =>
    if outCmd.command.acknowledge then
      let isWindowAvail :=
        if outCmd.command.channelId == 0xFF then
          true
        else
          let chIdx := outCmd.command.channelId.toNat
          if chH : chIdx < p.channels.size then
            p.channels[chIdx].canSendReliable outCmd.command.reliableSequenceNumber
          else
            true
      if isWindowAvail then
        let inFlightCmd := { outCmd with
          sendAttempts := outCmd.sendAttempts + 1
          sentTime     := now
        }
        { acc with
          commandsToPack := acc.commandsToPack.push outCmd.command
          sentReliables  := acc.sentReliables.push inFlightCmd
          inTransitAdd   := acc.inTransitAdd + outCmd.fragmentLength
        }
      else
        { acc with remainingOutgoing := acc.remainingOutgoing.push outCmd }
    else
      { acc with commandsToPack := acc.commandsToPack.push outCmd.command }

  let updatedPeer := { p with
    acknowledgements      := #[]
    outgoingCommands      := finalState.remainingOutgoing
    sentReliableCommands  := finalState.sentReliables
    reliableDataInTransit := p.reliableDataInTransit + finalState.inTransitAdd
  }
  (updatedPeer, finalState.commandsToPack)

/-- Polls a single peer for outgoing datagrams. -/
def pollPeer (p : Peer) (now : UInt32) (checksumEnabled : Bool) (compressor : Option Compressor) : Peer × Option (Address × ByteArray) :=
  if p.state == .disconnected then
    (p, none)
  else
    let (updatedPeer, commandsToPack) := packOutgoingCommands p now
    if commandsToPack.isEmpty then
      (updatedPeer, none)
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
      let datagramBytes := datagram.encodeWith compressor
      (updatedPeer, some (updatedPeer.address, datagramBytes))

/--
Packages pending ACKs and outgoing commands across all peers into datagrams.
Returns the updated host and the array of outgoing `(destinationAddress, datagramBytes)`.
-/
def pollOutgoing (h : Host) (now : UInt32) : Host × Array (Address × ByteArray) :=
  let (updatedPeers, packets) := h.peers.foldl (init := (#[], #[])) fun (peersAcc, pktsAcc) p =>
    let (p', pktOpt) := pollPeer p now h.checksumEnabled h.compressor
    let nextPeers := peersAcc.push p'
    let nextPkts := match pktOpt with
      | some pkt => pktsAcc.push pkt
      | none     => pktsAcc
    (nextPeers, nextPkts)
  ({ h with peers := updatedPeers }, packets)

end Host

end Lenet