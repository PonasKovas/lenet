/-
Tests of `Lenet.Net`: two endpoints over real UDP sockets on 127.0.0.1,
driven the way an application would (connect, send, `service` in a loop).
The protocol itself is covered by the traces and unit tests; these check
the driver: datagrams move both ways, timers run, and handles die with
their connection.

Exit code 0 iff every test passes.

Run: lake build net && ./.lake/build/bin/net
-/
import Lenet.Net

open Lenet.Net Std.Net

namespace NetTest

abbrev Check := ExceptT String IO Unit

def expect (ok : Bool) (msg : String) : Check :=
  if ok then pure () else throw msg

def loopback : SocketAddress := .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 }

/-- Services both endpoints, a few milliseconds each, until `done` holds
for the events so far or `ms` milliseconds pass. Returns each side's
events. -/
partial def pump (a b : Endpoint) (ms : Nat) (done : Array Event → Array Event → Bool) :
    IO (Array Event × Array Event) := do
  let deadline := (← IO.monoMsNow) + ms
  let rec loop (ea eb : Array Event) : IO (Array Event × Array Event) := do
    if done ea eb then return (ea, eb)
    if (← IO.monoMsNow) ≥ deadline then return (ea, eb)
    let ea := match ← a.service 2 with | some ev => ea.push ev | none => ea
    let eb := match ← b.service 2 with | some ev => eb.push ev | none => eb
    loop ea eb
  loop #[] #[]

def isConnect : Event → Bool | .connect .. => true | _ => false
def isDisconnect : Event → Bool | .disconnect .. => true | _ => false
def received (es : Array Event) : Array ByteArray :=
  es.filterMap fun | .receive _ _ p => some p.data | _ => none

/-- A connected pair: client, server, and each side's connection. -/
def connected (channels : Nat := 2) (serverConfig : Config := {}) :
    ExceptT String IO (Endpoint × Endpoint × Connection × Connection) := do
  let server ← Endpoint.bind loopback serverConfig
  let client ← Endpoint.bind loopback
  let peer ← match ← client.connect (← server.localAddress) channels 42 with
    | .ok p => pure p
    | .error e => throw s!"connect: {e}"
  let (ec, es) ← pump client server 2000 fun ec es => ec.any isConnect && es.any isConnect
  let some (.connect cp cdata) := ec.find? isConnect | throw "the client never connected"
  let some (.connect sp sdata) := es.find? isConnect | throw "the server never saw the connect"
  expect (cp.peer == peer) "the client's connect event names the handle connect returned"
  expect (cdata == 0 && sdata == 42) s!"connect data: client {cdata}, server {sdata} (want 0, 42)"
  return (client, server, cp, sp)

def bytes (n : Nat) (seed : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => ((i * 31 + seed) % 251).toUInt8⟩

def connectAndExchange : Check := do
  let (client, server, peer, sp) ← connected
  -- reliable packets arrive once and in order, a fragmented one whole
  let payloads := (List.range 50).map (bytes 100 ·) ++ [bytes 100000 7]
  for d in payloads do
    match ← client.send peer peer.first (.reliable d) with
    | .ok () => pure ()
    | .error e => throw s!"send: {e}"
  let (_, es) ← pump client server 3000 fun _ es => (received es).size ≥ payloads.length
  let got := received es
  expect (got.size == payloads.length) s!"{got.size} of {payloads.length} packets arrived"
  expect (got.toList == payloads) "the packets arrived out of order or changed"
  -- and back the other way, on channel 1
  let some ch1 := sp.channel? 1 | throw "the server's connection has no channel 1"
  match ← server.send sp ch1 (.reliable (bytes 10 3)) with
  | .ok () => pure ()
  | .error e => throw s!"server send: {e}"
  let (ec, _) ← pump client server 2000 fun ec _ => !(received ec).isEmpty
  expect (ec.any fun | .receive p ch pk => p == peer && ch.val == 1 && pk.data == bytes 10 3 | _ => false)
    "the client got the server's packet on channel 1"
  -- the RTT estimate came from real ACKs
  let some info ← client.info peer | throw "no info for a live handle"
  expect (info.state == .connected) "the peer is connected"

def disconnectKillsHandles : Check := do
  let (client, server, peer, sp) ← connected
  client.disconnect peer 7
  let (ec, es) ← pump client server 2000 fun ec es => ec.any isDisconnect && es.any isDisconnect
  expect (ec.any fun | .disconnect p _ => p == peer.peer | _ => false) "the client reported its disconnect"
  expect (es.any fun | .disconnect p 7 => p == sp.peer | _ => false) "the server got the disconnect with data 7"
  -- the old handles are dead, even once the slots hold new connections
  match ← client.send peer peer.first (.reliable (bytes 1 0)) with
  | .error (.peerNotConnected _) => pure ()
  | _ => throw "a send on a dead handle did not fail with peerNotConnected"
  let peer2 ← match ← client.connect (← server.localAddress) with
    | .ok p => pure p
    | .error e => throw s!"reconnect: {e}"
  let (_, es) ← pump client server 2000 fun ec es => ec.any isConnect && es.any isConnect
  let some (.connect sp2 _) := es.find? isConnect | throw "the reconnect never arrived"
  expect (peer2.slot == peer.peer.slot && peer2 != peer.peer) "a reused slot gets a new handle"
  expect (sp2.peer != sp.peer) "the server's reused slot gets a new handle"
  expect ((← client.info peer).isNone) "a dead handle has no info"
  match ← server.send sp sp.first (.reliable (bytes 1 0)) with
  | .error (.peerNotConnected _) => pure ()
  | _ => throw "a dead server handle reached the new connection"

def connectTimesOut : Check := do
  -- nothing listens there: the attempt ends with a disconnect event
  let silent ← Endpoint.bind loopback
  let client ← Endpoint.bind loopback
  let peer ← match ← client.connect (← silent.localAddress) with
    | .ok p => pure p
    | .error e => throw s!"connect: {e}"
  client.setTimeout peer 1 100 300
  let events ← client.serviceFor 2000
  expect (events.any fun | .disconnect p 0 => p == peer | _ => false)
    s!"the unanswered connect ended with a disconnect ({events.size} events)"

def serviceWaits : Check := do
  -- an idle endpoint's service returns once the timeout is up, not before
  let e ← Endpoint.bind loopback
  let t0 ← IO.monoMsNow
  let ev ← e.service 100
  let dt := (← IO.monoMsNow) - t0
  expect ev.isNone "an idle endpoint reported an event"
  expect (dt ≥ 90 && dt < 1000) s!"service 100 took {dt} ms"

def pollingOnly : Check := do
  -- a game loop calls service 0 once a frame: it must never block, and
  -- datagrams must still move
  let server ← Endpoint.bind loopback
  let client ← Endpoint.bind loopback
  let peer ← match ← client.connect (← server.localAddress) with
    | .ok p => pure p
    | .error e => throw s!"connect: {e}"
  let deadline := (← IO.monoMsNow) + 2000
  let mut connected := false
  let mut slowest := 0
  while !connected && (← IO.monoMsNow) < deadline do
    let t0 ← IO.monoMsNow
    let ec ← client.service 0
    let _ ← server.service 0
    slowest := max slowest ((← IO.monoMsNow) - t0)
    if ec.any isConnect then connected := true
    IO.sleep 1
  expect connected "polling with service 0 never connected"
  -- a blocking service would sleep to the next timer (hundreds of ms); the
  -- bound leaves room for a busy shared machine
  expect (slowest < 250) s!"a service 0 took {slowest} ms"
  let _ := peer

def wakesOnDatagram : Check := do
  -- a service sleeping on a long timeout returns as soon as a packet lands
  let (client, server, peer, sp) ← connected
  -- let the handshake's ACKs settle, so the next event is the packet
  let _ ← pump client server 200 fun _ _ => false
  match ← server.send sp sp.first (.reliable (bytes 10 1)) with
  | .ok () => pure ()
  | .error e => throw s!"send: {e}"
  -- sent 50 ms into the client's sleep, from another thread
  let t0 ← IO.monoMsNow
  let sender ← IO.asTask (do IO.sleep 50; server.flush)
  let ev ← client.service 2000
  let dt := (← IO.monoMsNow) - t0
  let _ ← IO.wait sender
  expect (ev.any fun | .receive p ch pk => p == peer && ch.val == 0 && pk.data == bytes 10 1 | _ => false)
    "the sleeping client did not get the packet"
  -- a service that slept its whole timeout would take 2000 ms; the bound
  -- leaves room for a busy shared machine
  expect (dt < 1000) s!"a packet sent at 50 ms woke the client at {dt} ms"

def channelsAgreed : Check := do
  -- a server allowing 3 channels grants a client asking for 5 only 3, and
  -- both sides' connections say so
  let (client, server, cp, sp) ← connected 5 { channelLimit := 3 }
  expect (cp.channelCount == 3 && sp.channelCount == 3)
    s!"channel counts: client {cp.channelCount}, server {sp.channelCount} (want 3, 3)"
  expect ((cp.channel? 3).isNone && (cp.channel? 2).isSome) "channel? stops at the count"
  -- a packet on each channel arrives on that channel, and echoing it back
  -- on the channel it came in on needs no check
  for ch in cp.channels do
    let _ ← client.send cp ch (.reliable (bytes 5 ch.val))
  let (_, es) ← pump client server 2000 fun _ es => (received es).size ≥ 3
  for ev in es do
    if let .receive conn ch pk := ev then
      expect (pk.data == bytes 5 ch.val) s!"the packet sent on channel {ch.val} arrived on another"
      let _ ← server.send conn ch pk
  let (ec, _) ← pump client server 2000 fun ec _ => (received ec).size ≥ 3
  expect ((ec.filterMap fun | .receive _ ch _ => some ch.val | _ => none).qsort (· < ·) == #[0, 1, 2])
    "the echoes came back on channels 0, 1 and 2"

/-- A datagram the network refuses (to port 0) is counted and lost; the
endpoint keeps working, and the rest of the batch still goes. -/
def sendFailureSurvives : Check := do
  let (client, server, peer, _) ← connected
  let bad : SocketAddress := .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 }
  let _ ← client.connect bad 2 0
  -- the CONNECT to port 0 and the packet for the server go out together
  match ← client.send peer peer.first (.reliable (bytes 20 1)) with
  | .ok () => pure ()
  | .error e => throw s!"send: {e}"
  let (_, es) ← pump client server 2000 fun _ es => !(received es).isEmpty
  let errs ← client.socketErrors
  expect (errs.sendFailures ≥ 1) "the send to port 0 did not fail"
  expect (received es == #[bytes 20 1]) "the packet sent alongside was lost"

def tests : List (String × Check) := [
  ("connect, then reliable packets both ways arrive once and in order", connectAndExchange),
  ("a disconnect kills the handles, and reused slots get new ones", disconnectKillsHandles),
  ("an unanswered connect times out with a disconnect event", connectTimesOut),
  ("an idle service returns once its timeout is up, not before", serviceWaits),
  ("service 0 alone moves datagrams, without blocking", pollingOnly),
  ("a sleeping service wakes as soon as a datagram lands", wakesOnDatagram),
  ("both sides' connections carry the channel count the server granted", channelsAgreed),
  ("a send the network refuses is counted, and the endpoint goes on", sendFailureSurvives)
]

end NetTest

def main : IO UInt32 := do
  let mut failed := 0
  for (name, t) in NetTest.tests do
    match ← t.run with
    | .ok () => IO.println s!"  PASS {name}"
    | .error msg =>
      IO.println s!"  FAIL {name}: {msg}"
      failed := failed + 1
  if failed == 0 then
    IO.println "ALL PASS"
    return 0
  IO.println s!"{failed} of {NetTest.tests.length} FAILED"
  return 1
