/-
Unit tests: small, targeted checks of behavior the golden traces cannot
reach (they are short and loss-free, and ENet decides what they contain).

Each test is a pure function returning `Except String Unit`; a failure
names what it expected. Peer-level tests drive `Peer.handleCommand` with
hand-built commands on the server side of a connected in-process pair;
host-level tests run the pair and drop datagrams on purpose.

Exit code 0 iff every test passes.

Run: lake build unit && ./.lake/build/bin/unit
-/
import Lenet

open Lenet

namespace Unit

abbrev Check := Except String Unit

def expect (ok : Bool) (msg : String) : Check :=
  if ok then pure () else throw msg

structure Test where
  name : String
  run : Unit → Check

/-! ## A connected pair -/

def clientAddr : Address := Address.ipv4 10 0 0 1 10001
def serverAddr : Address := Address.ipv4 10 0 0 2 10002

structure Pair where
  client : Host
  server : Host
  clientPeer : UInt16 := 0
  serverPeer : UInt16 := 0
  now : UInt32
  /-- Events of both sides so far, client's first in each round. -/
  clientEvents : Array Event := #[]
  serverEvents : Array Event := #[]

/-- One round at `p.now`: service both hosts and route what they emit to
the other side, unless `drop` says to lose it (`true` for client-to-server
datagrams, `false` for the other way). The clock then moves 1 ms. -/
def Pair.round (p : Pair) (drop : Bool → Bool := fun _ => false) : Pair :=
  let (c, couts, cevs) := p.client.service p.now
  let (s, souts, sevs) := p.server.service p.now
  let (s, sevs) := if drop true then (s, sevs) else
    couts.foldl (init := (s, sevs)) fun (s, evs) d =>
      let (s, e) := s.handleDatagram p.now clientAddr d.2
      (s, evs ++ e)
  let (c, cevs) := if drop false then (c, cevs) else
    souts.foldl (init := (c, cevs)) fun (c, evs) d =>
      let (c, e) := c.handleDatagram p.now serverAddr d.2
      (c, evs ++ e)
  { p with client := c, server := s, now := p.now + 1
           clientEvents := p.clientEvents ++ cevs, serverEvents := p.serverEvents ++ sevs }

def Pair.rounds (p : Pair) (n : Nat) (drop : Bool → Bool := fun _ => false) : Pair :=
  (List.range n).foldl (init := p) fun p _ => p.round drop

def Pair.clientP (p : Pair) : Peer := p.client.peers[p.clientPeer.toNat]!
def Pair.serverP (p : Pair) : Peer := p.server.peers[p.serverPeer.toNat]!

/-- A pair connected with two channels, its event logs cleared. -/
def connected : Except String Pair := do
  let (client, clientPeer) ← (Host.create clientAddr 4).connect serverAddr 2 |>.mapError toString
  let p := ({ client, server := Host.create serverAddr 4, clientPeer, now := 1000 } : Pair).rounds 10
  let some sp := p.server.peers.findIdx? (·.state == .connected) | throw "handshake: server not connected"
  let p := { p with serverPeer := sp.toUInt16 }
  expect (p.clientP.state == .connected) "handshake: client not connected"
  return { p with clientEvents := #[], serverEvents := #[] }

def bytes (n : Nat) (tag : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => (i * 7 + tag).toUInt8⟩

def received (evs : Array Event) : Array (UInt8 × ByteArray) :=
  evs.filterMap fun | .receive _ ch pkt => some (ch, pkt.data) | _ => none

/-! ## Fragment assemblers

Fragments of 4 bytes each; `whole tag count` is the packet a set of `count`
fragments with that tag reassembles to. -/

def whole (tag count : Nat) : ByteArray := bytes (4 * count) tag

def fragParams (start : UInt16) (tag count num : Nat) : Protocol.FragmentParams :=
  { startSequenceNumber := start, fragmentCount := count.toUInt32
    fragmentNumber := num.toUInt32, totalLength := (4 * count).toUInt32
    fragmentOffset := (4 * num).toUInt32
    data := (whole tag count).extract (4 * num) (4 * num + 4) }

/-- Fragment `num` of a reliable set starting at `start` on `ch`. -/
def relFrag (ch : UInt8) (start : UInt16) (tag count num : Nat) : Protocol.Command :=
  { channelId := ch, reliableSequenceNumber := start + num.toUInt16, acknowledge := true
    body := .sendFragment (fragParams start tag count num) }

/-- Fragment `num` of an unreliable set with unreliable sequence number
`start`, sent after reliable command `relSeq` on `ch`. -/
def unrelFrag (ch : UInt8) (relSeq start : UInt16) (tag count num : Nat) : Protocol.Command :=
  { channelId := ch, reliableSequenceNumber := relSeq
    body := .sendUnreliableFragment (fragParams start tag count num) }

def reliableCmd (ch : UInt8) (seq : UInt16) (data : ByteArray) : Protocol.Command :=
  { channelId := ch, reliableSequenceNumber := seq, acknowledge := true, body := .sendReliable data }

def unreliableCmd (ch : UInt8) (relSeq seq : UInt16) (data : ByteArray) : Protocol.Command :=
  { channelId := ch, reliableSequenceNumber := relSeq, body := .sendUnreliable seq data }

def unsequencedCmd (ch : UInt8) (group : UInt16) (data : ByteArray) : Protocol.Command :=
  { channelId := ch, reliableSequenceNumber := 0, unsequenced := true, body := .sendUnsequenced group data }

/-- Feeds `cmds` to peer `p` in order, each as if in a datagram of its own,
collecting the events. -/
def feed (p : Peer) (cmds : List Protocol.Command) : Peer × Array Event :=
  cmds.foldl (init := (p, #[])) fun (p, evs) cmd =>
    let (p, e, _) := p.handleCommand 2000 cmd (some 0)
    (p, evs ++ e)

def serverPeer : Except String Peer := return (← connected).serverP

def fragmentTests : List Test := [
  { name := "fragment sets on two channels with the same start stay apart"
    run := fun _ => do
      let (p, evs) := feed (← serverPeer)
        [relFrag 0 1 10 2 0, relFrag 1 1 20 2 1, relFrag 0 1 10 2 1, relFrag 1 1 20 2 0]
      expect (received evs == #[(0, whole 10 2), (1, whole 20 2)]) "expected each channel's own packet"
      expect p.fragmentAssemblers.isEmpty "assemblers left over" },
  { name := "a reliable and an unreliable set with the same start stay apart"
    run := fun _ => do
      let (_, evs) := feed (← serverPeer)
        [relFrag 0 1 10 2 0, unrelFrag 0 0 1 20 2 1, unrelFrag 0 0 1 20 2 0, relFrag 0 1 10 2 1]
      expect (received evs == #[(0, whole 20 2), (0, whole 10 2)]) "expected both packets, intact" },
  { name := "a resent fragment of a complete, staged set opens no assembler and is acked"
    run := fun _ => do
      -- seq 1 is missing, so the set at 2..3 completes but stays staged
      let (p, evs) := feed (← serverPeer) [relFrag 0 2 10 2 0, relFrag 0 2 10 2 1]
      expect evs.isEmpty "delivered past a gap"
      let acks := p.acknowledgements.size
      let (p, evs) := feed p [relFrag 0 2 10 2 0]
      expect evs.isEmpty "delivered a duplicate"
      expect p.fragmentAssemblers.isEmpty "the duplicate opened an assembler"
      expect (p.acknowledgements.size == acks + 1) "the duplicate was not acked"
      let (_, evs) := feed p [reliableCmd 0 1 (bytes 3 1)]
      expect (received evs == #[(0, bytes 3 1), (0, whole 10 2)]) "expected the gap, then the set" },
  { name := "a reliable packet staged inside a delivered set's span is dropped"
    run := fun _ => do
      -- seq 2 stages, then the set at 1..2 jumps the frontier over it
      let (p, evs) := feed (← serverPeer) [reliableCmd 0 2 (bytes 3 1), relFrag 0 1 10 2 0, relFrag 0 1 10 2 1]
      expect (received evs == #[(0, whole 10 2)]) "expected only the set"
      expect (p.channels.all (·.stagedReliable.isEmpty)) "stale staged packet kept" },
  { name := "an incomplete unreliable set is discarded once a newer packet is delivered"
    run := fun _ => do
      let (p, _) := feed (← serverPeer) [unrelFrag 0 0 1 10 2 0]
      expect (p.fragmentAssemblers.size == 1) "expected one assembler"
      let (p, evs) := feed p [unreliableCmd 0 0 2 (bytes 3 1)]
      expect (received evs == #[(0, bytes 3 1)]) "expected the newer packet"
      expect p.fragmentAssemblers.isEmpty "stale assembler kept" },
  { name := "an incomplete unreliable set is discarded once the reliable frontier passes it"
    run := fun _ => do
      let (p, _) := feed (← serverPeer) [unrelFrag 0 0 1 10 2 0, unrelFrag 1 0 1 10 2 0]
      let (p, _) := feed p [reliableCmd 0 1 (bytes 3 1)]
      expect (p.fragmentAssemblers.size == 1) "expected only channel 1's assembler left"
      expect (p.fragmentAssemblers.all (·.origin.channelId == 1)) "pruned the wrong channel" },
  { name := "a full cap evicts the oldest unreliable assembler"
    run := fun _ => do
      let fill := (List.range Constants.maximumFragmentAssemblers).map fun k =>
        unrelFrag 0 0 (k + 1).toUInt16 10 2 0
      let (p, _) := feed (← serverPeer) fill
      expect (p.fragmentAssemblers.size == Constants.maximumFragmentAssemblers) "cap not filled"
      let acks := p.acknowledgements.size
      let (p, _) := feed p [relFrag 0 1 20 2 0]
      expect (p.fragmentAssemblers.size == Constants.maximumFragmentAssemblers) "cap exceeded"
      expect (p.acknowledgements.size == acks + 1) "reliable fragment not acked"
      expect (!p.fragmentAssemblers.any fun a => a.origin.unreliable && a.startSequenceNumber == 1)
        "oldest unreliable assembler kept"
      expect (p.fragmentAssemblers.any (!·.origin.unreliable)) "reliable assembler missing" },
  { name := "with the cap full of reliable sets, a new set is refused and not acked"
    run := fun _ => do
      let starts := (List.range Constants.maximumFragmentAssemblers).map fun k => (1 + 2 * k).toUInt16
      let (p, _) := feed (← serverPeer) (starts.map fun s => relFrag 0 s 10 2 0)
      let acks := p.acknowledgements.size
      let (p, _) := feed p [relFrag 0 65 10 2 0]
      expect (p.acknowledgements.size == acks) "refused fragment was acked"
      expect (p.fragmentAssemblers.size == Constants.maximumFragmentAssemblers) "cap exceeded"
      -- a fragment of a set already being assembled still gets in
      let (p, evs) := feed p [relFrag 0 1 10 2 1]
      expect (p.acknowledgements.size == acks + 1) "fragment of a known set not acked"
      expect (received evs == #[(0, whole 10 2)]) "known set not delivered" } ]

/-! ## Unsequenced window

Lenet slides a 1024-group window behind the highest group seen; ENet keeps
aligned blocks of 1024 and drops everything below the current block (see
test/README.md, "Unsequenced window"). -/

/-- The groups of `groups` that `feed` delivers, one packet per group. -/
def fragmentValidationTests : List Test := [
  { name := "an empty fragment is refused"
    run := fun _ => do
      let peer ← serverPeer
      let cmd := relFrag 0 1 5 2 0
      let cmd := { cmd with body := .sendFragment { fragParams 1 5 2 0 with data := .empty } }
      let (q, _, reading) := peer.handleCommand 2000 cmd (some 0)
      -- ENet handle_send_fragment: fragmentLength <= 0 returns -1
      expect (!reading && q.acknowledgements.isEmpty) "empty fragment taken" },
  { name := "a fragment that does not match its set is refused"
    run := fun _ => do
      let peer ← serverPeer
      let (peer, _) := feed peer [relFrag 0 1 5 2 0]
      -- fragment 1, claiming a set of 3 (another total length)
      let (q, evs, reading) := peer.handleCommand 2000 (relFrag 0 1 5 3 1) (some 0)
      expect (!reading && evs.isEmpty) "mismatched fragment taken"
      expect (q.acknowledgements.size == peer.acknowledgements.size) "mismatched fragment acknowledged"
      -- the refused fragment left the set as it was: the real fragment 1
      -- completes it with the right bytes
      let (_, evs) := feed q [relFrag 0 1 5 2 1]
      expect (received evs == #[(0, whole 5 2)]) "the set did not complete intact" },
  { name := "a receiver assembles packets up to ENet's 32 MB"
    run := fun _ => do
      let peer ← serverPeer
      let set (total : Nat) : Protocol.Command :=
        let cmd := relFrag 0 1 5 2 0
        { cmd with body := .sendFragment { fragParams 1 5 2 0 with totalLength := total.toUInt32 } }
      let (q, _, reading) := peer.handleCommand 2000 (set (5 * 1024 * 1024)) (some 0)
      expect (reading && q.fragmentAssemblers.size == 1) "a 5 MB set was refused"
      let (q, _, reading) := peer.handleCommand 2000 (set (Constants.maximumPacketSize + 1)) (some 0)
      expect (!reading && q.fragmentAssemblers.isEmpty) "a set over 32 MB was taken" },
  { name := "no new fragmented packet once the assemblers hold 32 MB"
    run := fun _ => do
      let peer ← serverPeer
      let set (start : UInt16) (total : Nat) : Protocol.Command :=
        let cmd := relFrag 0 start 5 2 0
        { cmd with body := .sendFragment { fragParams start 5 2 0 with totalLength := total.toUInt32 } }
      let half := Constants.maximumWaitingData / 2
      let (peer, _) := feed peer [set 1 half, set 3 half]
      expect (peer.fragmentAssemblers.size == 2) "the first two sets were refused"
      -- ENet queue_incoming_command: totalWaitingData >= maximumWaitingData
      -- refuses a new packet (notifyError)
      let (q, _, reading) := peer.handleCommand 2000 (set 5 100) (some 0)
      expect (!reading && q.fragmentAssemblers.size == 2) "a set over the budget was taken" } ]

def deliveredGroups (p : Peer) (groups : List UInt16) : List UInt16 :=
  let (_, delivered) := groups.foldl (init := (p, [])) fun (p, acc) g =>
    let (p, evs) := feed p [unsequencedCmd 0 g (bytes 3 g.toNat)]
    (p, if evs.isEmpty then acc else acc ++ [g])
  delivered

def unsequencedTests : List Test := [
  { name := "unsequenced: duplicates are dropped, unseen groups within 1024 delivered"
    run := fun _ => do
      let got := deliveredGroups (← serverPeer) [1024, 1023, 1023, 1024, 1030, 1025]
      expect (got == [1024, 1023, 1030, 1025]) s!"delivered {got}" },
  { name := "unsequenced: a group 1024 or more behind the highest is dropped"
    run := fun _ => do
      let got := deliveredGroups (← serverPeer) [1024, 3000, 1500, 1976, 1977, 1977]
      expect (got == [1024, 3000, 1977]) s!"delivered {got}" },
  { name := "unsequenced: the window follows the groups across the 16-bit wrap"
    run := fun _ => do
      let got := deliveredGroups (← serverPeer) [65530, 3, 65534, 3, 65534]
      expect (got == [65530, 3, 65534]) s!"delivered {got}" } ]

/-! ## Host behavior under loss -/

def pkt (n : Nat) (mode : DeliveryMode := .reliable) : Packet := { data := bytes n 3, delivery := mode }

def send (p : Pair) (packet : Packet) (ch : UInt8 := 0) : Except String Pair := do
  let client ← p.client.send p.clientPeer ch packet |>.mapError toString
  return { p with client }

def dropAll : Bool → Bool := fun _ => true

/-- A datagram carrying `cmds`, header fields as a peer accepts them. -/
def dgram (cmds : List Protocol.Command) : Protocol.Datagram :=
  { header := { peerId := 0, session := 0, compressed := false, sentTime := some 0 }, commands := cmds.toArray }

/-- An ACK of `(ch, seq)` echoing sent time `t`. -/
def ackOf (ch : UInt8) (seq t : UInt16) : Protocol.Command :=
  { channelId := ch, reliableSequenceNumber := seq, body := .acknowledge seq t }

/-- A connected pair whose client has started a disconnect and sent its
DISCONNECT (lost), with the DISCONNECT's sequence number. -/
def disconnecting : Except String (Pair × UInt16) := do
  let p ← connected
  let p := { p with client := p.client.disconnect p.clientPeer }
  let p := p.round dropAll
  expect (p.clientP.state == .disconnecting) "client not disconnecting"
  let some d := p.clientP.sentReliableCommands[0]? | throw "no DISCONNECT in flight"
  return (p, d.command.reliableSequenceNumber)

def hostTests : List Test := [
  { name := "send rejects a bad peer, a bad channel, an unconnected peer and an oversized packet"
    run := fun _ => do
      let p ← connected
      expect (p.client.send 99 0 (pkt 10) matches .error (.invalidPeerId 99)) "bad peer accepted"
      expect (p.client.send p.clientPeer 2 (pkt 10) matches .error (.invalidChannelId ..))
        "bad channel accepted"
      expect (p.client.send 1 0 (pkt 10) matches .error (.peerNotConnected 1)) "free slot accepted"
      -- ENet enet_peer_send refuses packets over host->maximumPacketSize (32 MB)
      let big : Packet := { data := ByteArray.mk (Array.replicate (Constants.maximumPacketSize + 1) 0) }
      expect (p.client.send p.clientPeer 0 big matches .error (.packetTooLarge ..)) "oversized packet accepted" },
  { name := "a host has at most 4095 peer slots, none with the CONNECT peer ID"
    run := fun _ => do
      let h := Host.create clientAddr 5000
      expect (h.peers.size == 4095) s!"{h.peers.size} slots"
      expect (h.peers.all (·.peerId < Constants.maximumPeerId)) "a slot has peer ID 0xFFF" },
  { name := "connect fails when every slot is taken"
    run := fun _ => do
      let h := Host.create clientAddr 1
      let .ok (h, _) := h.connect serverAddr | throw "first connect failed"
      expect (h.connect serverAddr matches .error .noFreePeerSlots) "second connect accepted" },
  { name := "a lost reliable packet is resent after its timeout, counted in transit once"
    run := fun _ => do
      let p ← send (← connected) (pkt 100)
      let p := p.round dropAll
      let sent := p.clientP.sentReliableCommands
      expect (sent.size == 1) "expected one command in flight"
      expect (p.clientP.reliableDataInTransit == 100) "in-transit bytes not counted"
      let rto := sent[0]!.roundTripTimeout
      -- nothing is resent before the timeout
      let p := (p.rounds (rto.toNat - 2) dropAll)
      expect (p.clientP.sentReliableCommands[0]!.sendAttempts == 1) "resent early"
      let p := p.rounds 2 dropAll
      let cmd := p.clientP.sentReliableCommands[0]!
      expect (cmd.sendAttempts == 2) "not resent after the timeout"
      expect (cmd.roundTripTimeout == 2 * rto) "timeout not doubled"
      expect (p.clientP.reliableDataInTransit == 100) "resend counted twice"
      let p := p.rounds (2 * rto.toNat + 10)
      expect (received p.serverEvents == #[(0, bytes 100 3)]) "not delivered exactly once"
      expect (p.clientP.reliableDataInTransit == 0) "in-transit bytes left after the ack"
      expect (p.clientP.channels.all (·.reliableWindows.all (· == 0))) "window slot left after the ack" },
  { name := "an empty reliable packet waits while the bytes in flight exceed the window"
    run := fun _ => do
      let p ← send (← send (← send (← connected) (pkt 1000)) (pkt 1000)) (pkt 1000)
      let p := p.round dropAll
      expect (p.clientP.reliableDataInTransit == 3000) "the three packets are not in flight"
      -- the window shrinks below what is in flight (ENet: the throttle falls on an RTT spike)
      let p := { p with client := p.client.modifyPeer p.clientPeer ({ · with packetThrottle := 0 }) }
      let p ← send p (pkt 0)
      let (q, cmds) := Host.packOutgoingCommands p.clientP p.now
      -- ENet checks every command with a packet, empty or not (check_outgoing_commands)
      expect (!cmds.any (·.body matches .sendReliable ..)) "empty packet sent past the congestion window"
      expect (q.outgoingCommands.size == 1) "empty packet not left queued" },
  { name := "a reliable packet held back by congestion holds back every later one"
    run := fun _ => do
      let p := (← send (← connected) (pkt 1000)).round dropAll
      -- the window shrinks to one MTU (1392): 1000 in flight + 500 is over, + 100 is not
      let p := { p with client := p.client.modifyPeer p.clientPeer ({ · with packetThrottle := 0 }) }
      let p ← send (← send p (pkt 500)) (pkt 100) (ch := 1)
      let (q, cmds) := Host.packOutgoingCommands p.clientP p.now
      -- ENet stops taking from its reliable send list for the pass
      -- (check_outgoing_commands: currentSendReliableCommand = end)
      expect (!cmds.any (·.body matches .sendReliable ..)) "a later reliable packet overtook the held one"
      expect (q.outgoingCommands.size == 2) "both packets not left queued" },
  { name := "a command ENet refuses ends its datagram: a stray ACK hides the DISCONNECT's"
    run := fun _ => do
      let (p, seq) ← disconnecting
      let t := p.now.toUInt16
      -- an ACK for something the disconnect dropped, then the real one
      let (q, evs) := Host.handlePeerDatagram p.clientP p.now serverAddr (dgram [ackOf 0 1 t, ackOf 0xFF seq t]) 0
      expect evs.isEmpty "the DISCONNECT's ACK counted after a refused command"
      expect (q.state == .disconnecting) "disconnect completed"
      let (_, evs) := Host.handlePeerDatagram p.clientP p.now serverAddr (dgram [ackOf 0xFF seq t]) 0
      expect (evs == #[.disconnect p.clientPeer 0]) "the ACK alone did not complete the disconnect" },
  { name := "a slot reset by a DISCONNECT takes no later ACK of the same datagram"
    run := fun _ => do
      let p ← connected
      let peer := p.clientP
      -- a DISCONNECT from a client still connecting resets the slot; an ACK
      -- after it in the datagram must not touch the free slot (ENet returns
      -- early from handle_acknowledge)
      let peer := { peer with state := .connecting }
      let disc : Protocol.Command :=
        { channelId := 0xFF, reliableSequenceNumber := 9, acknowledge := true, body := .disconnect 0 }
      let (q, _) := Host.handlePeerDatagram peer (p.now + 100) serverAddr (dgram [disc, ackOf 0 1 p.now.toUInt16]) 0
      expect (q.state == .disconnected) "slot not reset"
      expect (q.lastReceiveTime == (Peer.reset peer).lastReceiveTime) "the ACK updated the free slot" },
  { name := "a disconnecting peer neither takes nor acknowledges data"
    run := fun _ => do
      let (p, _) ← disconnecting
      let (q, evs, reading) := p.clientP.handleCommand p.now (reliableCmd 0 1 (bytes 10 1)) (some 0)
      expect (evs.isEmpty && !reading) "data taken"
      expect q.acknowledgements.isEmpty "data acknowledged" },
  { name := "a remote DISCONNECT drops what is queued: only its ACK goes out"
    run := fun _ => do
      let p ← send (← connected) (pkt 100)
      let (q, _, _) := p.clientP.handleCommand p.now
        { channelId := 0xFF, reliableSequenceNumber := 5, acknowledge := true, body := .disconnect 3 } (some 0)
      expect (q.state == .acknowledgingDisconnect) "not acknowledging the disconnect"
      expect q.outgoingCommands.isEmpty "queued packet kept"
      expect (q.acknowledgements.size == 1) s!"{q.acknowledgements.size} ACKs queued" },
  { name := "a peer still handshaking refuses a BANDWIDTH_LIMIT"
    run := fun _ => do
      let .ok (client, _) := (Host.create clientAddr 1).connect serverAddr 2 | throw "connect failed"
      let p := ({ client, server := Host.create serverAddr 1, now := 1000 } : Pair).round (fun c2s => !c2s)
      let peer := p.server.peers[0]!
      expect (peer.state == .acknowledgingConnect) "server peer not handshaking"
      let (q, _, reading) := peer.handleCommand 1001
        { channelId := 0xFF, reliableSequenceNumber := 2, acknowledge := true, body := .bandwidthLimit 1000 2000 } (some 0)
      expect (!reading && q.incomingBandwidth == peer.incomingBandwidth) "BANDWIDTH_LIMIT taken" },
  { name := "an unreliable packet goes reliable once the unreliable numbers are used up"
    run := fun _ => do
      let p ← connected
      let used := fun (c : Channel) => { c with outgoingUnreliableSequenceNumber := 0xFFFF }
      let p := { p with client := p.client.modifyPeer p.clientPeer fun q =>
        { q with channels := q.channels.modify 0 used } }
      -- ENet enet_peer_send: at 0xFFFF the packet is sent reliably, which
      -- restarts the unreliable numbering
      let p ← send p (pkt 10 .unreliable)
      let q := p.clientP
      expect (q.outgoingCommands.any (·.command.body matches .sendReliable ..)) "not sent reliably"
      expect (q.channels[0]!.outgoingUnreliableSequenceNumber == 0) "unreliable numbering not restarted"
      let p ← send p (pkt 10 .unreliable)
      expect (p.clientP.outgoingCommands.any (·.command.body matches .sendUnreliable 1 _)) "next one not unreliable 1"
      -- a fragmented set too
      let p := { p with client := p.client.modifyPeer p.clientPeer fun q =>
        { q with channels := q.channels.modify 0 used } }
      let p ← send p (pkt 3000 .unreliableFragment)
      expect (p.clientP.outgoingCommands.any (·.command.body matches .sendFragment ..)) "fragments not reliable" },
  { name := "queued unreliable data does not stop the keepalive PING"
    run := fun _ => do
      let p ← connected
      let p ← send p (pkt 10 .unreliable)
      -- idle for longer than the ping interval (ENet pings once a pass packs
      -- nothing reliable and nothing is in flight)
      let now := p.now + Constants.defaultPingInterval + 10
      let (_, outs, _) := p.client.service now
      let cmds := outs.toList.flatMap fun (_, d) =>
        match ReaderM.run Protocol.Datagram.decode d with | .ok d => d.commands.toList | .error _ => []
      expect (cmds.any (·.body matches .sendUnreliable ..)) "unreliable packet not sent"
      expect (cmds.any (·.body matches .ping)) "no PING"
      expect (p.client.nextDeadline.any (Time.less · now)) "no keepalive deadline" },
  { name := "a zero timeout parameter means its default"
    run := fun _ => do
      let p ← connected
      let q := (p.client.setPeerTimeout p.clientPeer 0 0 5000).peers[p.clientPeer.toNat]!
      -- ENet enet_peer_timeout: each 0 is replaced by its default
      expect (q.timeoutLimit == Constants.defaultTimeoutLimit && q.timeoutMinimum == Constants.defaultTimeoutMinimum
        && q.timeoutMaximum == 5000) s!"{q.timeoutLimit}/{q.timeoutMinimum}/{q.timeoutMaximum}" },
  { name := "the server takes over and echoes the client's throttle parameters"
    run := fun _ => do
      -- a client whose throttle parameters are not the defaults
      let client := (Host.create clientAddr 1).modifyPeer 0 fun q =>
        { q with packetThrottleInterval := 2000, packetThrottleAcceleration := 3, packetThrottleDeceleration := 4 }
      let .ok (client, _) := client.connect serverAddr 2 | throw "connect failed"
      let p := ({ client, server := Host.create serverAddr 1, now := 1000 } : Pair).rounds 10
      let some sp := p.server.peers[0]? | throw "no server peer"
      expect (sp.packetThrottleInterval == 2000 && sp.packetThrottleAcceleration == 3 &&
        sp.packetThrottleDeceleration == 4) "server peer kept its own throttle parameters"
      -- the client checks the echo (ENet handle_verify_connect)
      expect (p.clientP.state == .connected) "client refused the VERIFY_CONNECT" },
  { name := "connect asks for its channel count whatever the host's channel limit"
    run := fun _ => do
      -- ENet enet_host_connect clamps to [1, 255] only; the limit caps incoming CONNECTs
      let .ok (h, id) := (Host.create clientAddr 1 (channelLimit := 1)).connect serverAddr 4
        | throw "connect failed"
      expect (h.peers[id.toNat]!.channels.size == 4) s!"{h.peers[id.toNat]!.channels.size} channels"
      let .ok (h, id) := (Host.create clientAddr 1).connect serverAddr 0 | throw "connect failed"
      expect (h.peers[id.toNat]!.channels.size == 1) "0 channels not raised to 1"
      let .ok (h, id) := (Host.create clientAddr 1).connect serverAddr 300 | throw "connect failed"
      expect (h.peers[id.toNat]!.channels.size == 255) "300 channels not capped at 255" },
  { name := "a retransmitted CONNECT does not take a second slot"
    run := fun _ => do
      let .ok (client, _) := (Host.create clientAddr 1).connect serverAddr 2 | throw "connect failed"
      let (_, outs, _) := client.service 1000
      let some (_, connect) := outs[0]? | throw "no CONNECT sent"
      let server := Host.create serverAddr 4
      let (server, _) := server.handleDatagram 1000 clientAddr connect
      -- the same CONNECT again, as the client resends it when the VERIFY_CONNECT is late
      let (server, _) := server.handleDatagram 1600 clientAddr connect
      let taken := server.peers.filter (·.state != .disconnected) |>.size
      expect (taken == 1) s!"{taken} slots taken" },
  { name := "a disconnect reported by service triggers a bandwidth recalculation"
    run := fun _ => do
      -- past the first throttle epoch, which clears the connect's recalculation
      let p := (← connected).rounds (Constants.bandwidthThrottleInterval.toNat + 10)
      expect (!p.server.recalculateBandwidthLimits) "recalculation still pending"
      let p := { p with client := p.client.disconnect p.clientPeer }
      let p := p.rounds 5
      expect (p.serverEvents.any (· matches .disconnect ..)) "server saw no disconnect"
      -- ENet dispatches the ZOMBIE peer, which sets recalculateBandwidthLimits
      expect p.server.recalculateBandwidthLimits "no recalculation after the disconnect" },
  { name := "a peer waiting to disconnect later takes data but delivers none"
    run := fun _ => do
      let p ← send (← connected) (pkt 100)
      let p := { p with client := p.client.disconnectLater p.clientPeer }
      let peer := p.clientP
      expect (peer.state == .disconnectLater) "not waiting"
      -- ENet enet_peer_queue_incoming_command discards data in this state:
      -- acknowledged, never delivered
      let (q, evs, reading) := peer.handleCommand p.now (reliableCmd 0 1 (bytes 10 1)) (some 0)
      expect (evs.isEmpty && reading) "reliable packet delivered or refused"
      expect (q.acknowledgements.size == peer.acknowledgements.size + 1) "reliable packet not acknowledged"
      expect (q.channels[0]!.incomingReliableSequenceNumber == 0) "frontier moved"
      let (_, evs, _) := peer.handleCommand p.now (unsequencedCmd 0 1 (bytes 10 2)) (some 0)
      expect evs.isEmpty "unsequenced packet delivered"
      -- a fragment that would start a set is refused (discarded with a
      -- fragment count: notifyError)
      let (q, evs, reading) := peer.handleCommand p.now (relFrag 0 1 5 2 0) (some 0)
      expect (evs.isEmpty && !reading) "new fragment set taken"
      expect (q.acknowledgements.size == peer.acknowledgements.size) "new fragment set acknowledged"
      -- a set already under way still completes
      let started := { (feed { peer with state := .connected } [relFrag 0 1 5 2 0]).1 with state := .disconnectLater }
      let (_, evs, _) := started.handleCommand p.now (relFrag 0 1 5 2 1) (some 0)
      expect (evs.size == 1) "a set under way did not complete" },
  { name := "an ACK for a command queued for resend retires it"
    run := fun _ => do
      let p := (← send (← connected) (pkt 100)).round dropAll
      let some cmd := p.clientP.sentReliableCommands[0]? | throw "nothing in flight"
      let now := p.now + cmd.roundTripTimeout + 1
      let (peer, _) := Host.checkPeerTimeouts p.clientP now
      expect (peer.sentReliableCommands.isEmpty && peer.outgoingCommands.size == 1) "not queued for resend"
      -- the late ACK of the first send arrives before the resend goes out:
      -- ENet's remove_sent_reliable_command also looks in the queue
      let (q, _, _) := peer.handleCommand now
        (ackOf 0 cmd.command.reliableSequenceNumber cmd.sentTime.toUInt16) (some 0)
      expect q.outgoingCommands.isEmpty "acknowledged command still queued"
      expect (q.channels[0]!.reliableWindows.all (· == 0)) "window slot kept"
      expect (q.reliableDataInTransit == 0) "in-transit bytes wrong" },
  { name := "the header carries a sent time only for reliable commands, a session only once negotiated"
    run := fun _ => do
      let headers (outs : Array (Address × ByteArray)) : List Protocol.Header :=
        outs.toList.filterMap fun (_, d) =>
          match ReaderM.run Protocol.Datagram.decode d with | .ok d => some d.header | .error _ => none
      -- a fresh client's CONNECT: no session bits yet (ENet adds them once
      -- the remote peer ID is known)
      let .ok (client, _) := (Host.create clientAddr 1).connect serverAddr 2 | throw "connect failed"
      let (_, outs, _) := client.service 1000
      expect ((headers outs).all fun h => h.session == 0 && h.sentTime.isSome) "CONNECT header"
      -- unreliable data alone: no sent time (ENet sets SENT_TIME only for a reliable command)
      let p ← send (← connected) (pkt 10 .unreliable)
      let (_, outs, _) := p.client.service p.now
      expect (!(headers outs).isEmpty && (headers outs).all (·.sentTime.isNone)) "unreliable-only header has a sent time"
      let p ← send p (pkt 10)
      let (_, outs, _) := p.client.service p.now
      expect ((headers outs).any (·.sentTime.isSome)) "reliable datagram without a sent time" },
  { name := "a peer that never answers times out between the minimum and maximum"
    run := fun _ => do
      let p ← send (← connected) (pkt 100)
      let start := p.now
      -- jump from deadline to deadline, losing everything
      let rec go : Nat → Host → UInt32 → Option (UInt32 × Host)
        | 0, _, _ => none
        | fuel + 1, h, now =>
          let (h, _, evs) := h.service now
          if evs.any (· matches .disconnect ..) then some (now, h)
          else
            let next := h.nextDeadline.getD (now + 1)
            go fuel h (if Time.less now next then next else now + 1)
      let some (at_, h) := go 1000 p.client start | throw "never timed out"
      let elapsed := (at_ - start).toNat
      expect (elapsed ≥ Constants.defaultTimeoutMinimum.toNat) s!"timed out after only {elapsed} ms"
      expect (elapsed ≤ Constants.defaultTimeoutMaximum.toNat + 1000) s!"timed out after {elapsed} ms"
      expect (h.peers[p.clientPeer.toNat]!.state == .disconnected) "slot not freed"
      expect (h.connect serverAddr matches .ok _) "freed slot not reusable" },
  { name := "disconnectLater waits for the queue to drain, then both sides disconnect"
    run := fun _ => do
      let p ← send (← connected) (pkt 100)
      let p := { p with client := p.client.disconnectLater p.clientPeer 7 }
      expect (p.clientP.state == .disconnectLater) "did not wait"
      let p := p.rounds 20
      expect (received p.serverEvents == #[(0, bytes 100 3)]) "queued packet not delivered first"
      expect (p.serverEvents.back? == some (.disconnect p.serverPeer 7)) "server saw no disconnect"
      expect (p.clientEvents.any (· matches .disconnect ..)) "client saw no disconnect" },
  { name := "a server peer whose handshake times out goes without an event"
    run := fun _ => do
      let .ok (client, _) := (Host.create clientAddr 1).connect serverAddr 2
        | throw "connect failed"
      -- the server gets the CONNECT; nothing it sends back arrives
      let p := ({ client, server := Host.create serverAddr 1, now := 1000 } : Pair).round (fun c2s => !c2s)
      expect (p.server.peers[0]!.state == .acknowledgingConnect) "server not handshaking"
      let rec settle : Nat → Host → UInt32 → Array Event → Option (Array Event)
        | 0, _, _, _ => none
        | fuel + 1, h, now, evs =>
          let (h, _, new) := h.service now
          if h.peers[0]!.state == .disconnected then some (evs ++ new)
          else
            let next := h.nextDeadline.getD (now + 1)
            settle fuel h (if Time.less now next then next else now + 1) (evs ++ new)
      let some evs := settle 1000 p.server p.now #[] | throw "handshake never timed out"
      expect evs.isEmpty s!"events for a peer never reported: {evs.size}" },
  { name := "a DISCONNECT during the server's handshake resets without an event"
    run := fun _ => do
      let .ok (client, _) := (Host.create clientAddr 1).connect serverAddr 2
        | throw "connect failed"
      let p := ({ client, server := Host.create serverAddr 1, now := 1000 } : Pair).round (fun c2s => !c2s)
      let peer := p.server.peers[0]!
      let (peer, evs, _) := peer.handleCommand 1001
        { channelId := 0xFF, reliableSequenceNumber := 2, acknowledge := true, body := .disconnect 5 } (some 0)
      expect evs.isEmpty "reported a disconnect for a peer never reported connected"
      expect (peer.state == .disconnected) "slot not freed" },
  { name := "disconnect does nothing on a free slot or a second time"
    run := fun _ => do
      let p ← connected
      let h := p.client.disconnect 3
      expect (h.peers == p.client.peers) "a free slot was touched"
      let h := (p.client.disconnect p.clientPeer 1).disconnect p.clientPeer 2
      let queued := h.peers[p.clientPeer.toNat]!.outgoingCommands
      expect (queued.size == 1 && queued.all (·.command.body matches .disconnect 1))
        s!"queued {queued.size} commands" },
  { name := "disconnect drops what is still queued, then both sides disconnect"
    run := fun _ => do
      let p ← connected
      let p ← (List.range 3).foldlM (init := p) fun p _ => send p (pkt 100)
      let p := { p with client := p.client.disconnect p.clientPeer 7 }
      let p := p.rounds 20
      expect (received p.serverEvents).isEmpty "a packet queued before the disconnect was sent"
      expect (p.serverEvents == #[.disconnect p.serverPeer 7]) "server saw no disconnect"
      expect (p.clientEvents == #[.disconnect p.clientPeer 0]) "client saw no disconnect" },
  { name := "disconnecting a client still connecting sends one DISCONNECT and frees the slot silently"
    run := fun _ => do
      let .ok (client, id) := (Host.create clientAddr 1).connect serverAddr 2
        | throw "connect failed"
      let client := client.disconnect id
      let (client, outs, evs) := client.service 1000
      expect (outs.size == 1) s!"sent {outs.size} datagrams"
      let cmds := match ReaderM.run Protocol.Datagram.decode outs[0]!.2 with
        | .ok d => d.commands | .error _ => #[]
      expect (cmds.size == 1 && cmds.all fun c =>
          c.body matches .disconnect .. && c.unsequenced && !c.acknowledge)
        "expected one unacknowledged, unsequenced DISCONNECT (and no CONNECT)"
      expect evs.isEmpty "reported a disconnect for a connection never made"
      expect (client.peers[id.toNat]!.state == .disconnected) "slot not freed" },
  { name := "the throttle falls on an RTT spike, climbs back, and stops at its limit"
    run := fun _ => do
      let p : Peer := { (← serverPeer) with
        lastRoundTripTime := 50, lastRoundTripTimeVariance := 5
        packetThrottle := 32, packetThrottleLimit := 32
        packetThrottleAcceleration := 2, packetThrottleDeceleration := 3 }
      let steps : List UInt32 := [100, 100, 58, 40, 40, 40, 40]
      let (_, seen) := steps.foldl (init := (p, (#[] : Array UInt32))) fun (p, seen) rtt =>
        let p := p.throttle rtt
        (p, seen.push p.packetThrottle)
      -- above 50 + 2 * 5 falls by 3, within it holds, at or below 50 climbs by 2
      expect (seen == #[29, 26, 26, 28, 30, 32, 32]) s!"throttle went {seen}"
      let p := Peer.throttle { p with packetThrottle := 1 } 100
      expect (p.packetThrottle == 0) "throttle did not floor at 0"
      let p := Peer.throttle { p with lastRoundTripTime := 5, lastRoundTripTimeVariance := 5 } 100
      expect (p.packetThrottle == 32) "a steady link did not reset the throttle to its limit" },
  { name := "at a throttle of 8/32, 9 of 32 unreliable packets go out"
    run := fun _ => do
      let p ← connected
      let p := { p with client := p.client.modifyPeer p.clientPeer fun peer =>
        { peer with packetThrottle := 8, packetThrottleLimit := 8, packetThrottleCounter := 0 } }
      let p ← (List.range 32).foldlM (init := p) fun p _ => send p (pkt 10 .unreliable)
      let p := p.rounds 5
      let got := (received p.serverEvents).size
      expect (got == 9) s!"{got} of 32 delivered" },
  { name := "bandwidth throttle: a slow peer is limited first, the rest share what is left"
    run := fun _ => do
      -- expected values worked out by hand from ENet's enet_host_bandwidth_throttle
      let peer (id : UInt16) (inBw outBw : UInt32) : Peer :=
        { peerId := id, state := .connected, incomingBandwidth := inBw, outgoingBandwidth := outBw
          outgoingDataTotal := 3000 }
      let h : Host := { Host.create serverAddr 4 with
        outgoingBandwidth := 4000, incomingBandwidth := 3000, recalculateBandwidthLimits := true
        peers := #[peer 0 1000 500, peer 1 0 0, peer 2 0 3000, {}] }
      let h := h.bandwidthThrottle 1000
      let limit (i : Nat) := (h.peers[i]!.packetThrottleLimit, h.peers[i]!.packetThrottle)
      -- 4000 for 9000 queued bytes: throttle 14, which leaves A more than
      -- its 1000, so A gets 32 * 1000 / 3000
      expect (limit 0 == (10, 10)) s!"A limit {limit 0}"
      -- the budget loses A's 1000: 32 * 3000 / 8000
      expect (limit 1 == (12, 12) && limit 2 == (12, 12)) s!"B, C limits {limit 1}, {limit 2}"
      expect (h.peers[3]! == {}) "an unconnected slot was touched"
      -- incoming 3000: the share of 1000 marks A (sends at most 500) and B
      -- (unlimited), each told its own outgoing bandwidth; C, sending 3000,
      -- is told the 2500 left
      let limits := h.peers.filterMap fun p => p.outgoingCommands.back?.bind fun c =>
        match c.command.body with
        | .bandwidthLimit incoming outgoing => some (incoming, outgoing)
        | _ => none
      expect (limits == #[(500, 4000), (0, 4000), (2500, 4000)]) s!"BANDWIDTH_LIMITs {limits}"
      expect (!h.recalculateBandwidthLimits && h.bandwidthThrottleEpoch == 1000) "epoch not advanced" },
  { name := "service before nextDeadline does nothing; at it, the resend goes out"
    run := fun _ => do
      let p := (← send (← connected) (pkt 100)).round dropAll
      let h := p.client
      let some d := h.nextDeadline | throw "no deadline with a command in flight"
      expect (Time.less p.now d) "deadline not in the future"
      for t in [p.now, p.now + (d - p.now) / 2, d - 1] do
        let (h', outs, evs) := h.service t
        expect (outs.isEmpty && evs.isEmpty) s!"service at {t} (deadline {d}) sent something"
        expect (h'.peers == h.peers) s!"service at {t} (deadline {d}) changed a peer"
      let (_, outs, _) := h.service d
      expect (!outs.isEmpty) "nothing resent at the deadline" },
  { name := "an idle pair's service before nextDeadline does nothing"
    run := fun _ => do
      let p := (← connected).rounds 50
      for h in [p.client, p.server] do
        let some d := h.nextDeadline | throw "no deadline"
        let (h', outs, evs) := h.service (d - 1)
        expect (outs.isEmpty && evs.isEmpty) "service before the deadline sent something"
        expect (h'.peers == h.peers) "service before the deadline changed a peer" } ]

def tests : List Test := fragmentTests ++ fragmentValidationTests ++ unsequencedTests ++ hostTests

end Unit

def main : IO UInt32 := do
  let mut failed := 0
  for t in Unit.tests do
    match t.run () with
    | .ok () => IO.println s!"  PASS {t.name}"
    | .error msg =>
      IO.println s!"  FAIL {t.name}: {msg}"
      failed := failed + 1
  if failed == 0 then
    IO.println "ALL PASS"
    return 0
  IO.println s!"{failed} of {Unit.tests.length} FAILED"
  return 1
