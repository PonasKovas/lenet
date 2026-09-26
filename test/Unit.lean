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

/-- Feeds `cmds` to peer `p` in order, collecting the events. -/
def feed (p : Peer) (cmds : List Protocol.Command) : Peer × Array Event :=
  cmds.foldl (init := (p, #[])) fun (p, evs) cmd =>
    let (p, e) := p.handleCommand 2000 cmd (some 0)
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

def hostTests : List Test := [
  { name := "send rejects a bad peer, a bad channel and an unconnected peer"
    run := fun _ => do
      let p ← connected
      expect (p.client.send 99 0 (pkt 10) matches .error (.invalidPeerId 99)) "bad peer accepted"
      expect (p.client.send p.clientPeer 2 (pkt 10) matches .error (.invalidChannelId ..))
        "bad channel accepted"
      expect (p.client.send 1 0 (pkt 10) matches .error (.peerNotConnected 1)) "free slot accepted" },
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

def tests : List Test := fragmentTests ++ unsequencedTests ++ hostTests

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
