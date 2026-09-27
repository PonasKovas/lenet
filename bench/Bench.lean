/-
Benchmark executable.

Measures, through the pure sans-I/O core only (no sockets, no FFI):

1. Closed-loop throughput per delivery mode. A client and a server host
   are connected in-process (outgoing datagrams of one are fed to the
   other, deadline-ticked like the replay). A batch of packets is sent,
   pumped through both hosts, and the received events counted. Numbers
   are end-to-end: send + service + datagram handling + ack traffic.

2. CPU cost of one driver service tick (one pump round: service both
   hosts + route the emitted datagrams), in the idle connected state and
   under a per-round send load.

3. A lossy link: the same pair with every n-th datagram dropped, so
   retransmission, backoff and the in-transit and window accounting run.
   Reliable packets must all arrive, once and in order; unreliable ones
   may be lost but never duplicated or reordered; and afterwards both
   peers must still be connected with nothing left in transit.

Methodology: wall clock via IO.monoNanosNow around each pure run,
median of 5 runs, one untimed warmup run first. Each timed run gets a
seed derived from the starting clock read (it only offsets the simulated
clock origin) so the optimizer cannot hoist the pure computation out of
the timed region. Payloads are Deterministic (index-derived); no
randomness. The bench FAILs (exit 1) if any scenario loses or corrupts a
packet it must deliver, so the numbers are only printed when they mean
something.

Run: lake build bench && ./.lake/build/bin/bench
-/

import Lenet

open Lenet

namespace Bench

/-! ## Harness: a connected client/server pair in one process -/

private def clientAddr : Address := Address.ipv4 10 0 0 1 10001
private def serverAddr : Address := Address.ipv4 10 0 0 2 10002

/-- Deterministic payload byte `i` (no randomness anywhere in the bench). -/
private def payloadByte (i : Nat) : UInt8 := ((i * 31 + 7) % 256).toUInt8

private def mkPayload (n : Nat) : ByteArray :=
  (List.range n).foldl (init := ByteArray.empty) fun acc i => acc.push (payloadByte i)

structure PumpStats where
  delivered : Nat := 0
  received : Nat := 0
  bad : Nat := 0

private def countEvs (evs : Array Event) (payload : ByteArray) (st : PumpStats) : PumpStats :=
  evs.foldl (init := st) fun acc ev =>
    match ev with
    | .receive _ _ pkt =>
      { acc with
        received := acc.received + 1
        bad := if pkt.data == payload then acc.bad else acc.bad + 1 }
    | _ => acc

structure BenchPair where
  client : Host
  server : Host
  clientPeer : UInt16
  serverPeer : UInt16

/-- Feeds one side's outgoing datagrams to the other host at `now`. -/
private def feed (h : Host) (now : UInt32) (fromAddr : Address)
    (outs : Array (Address × ByteArray)) (payload : ByteArray) (st : PumpStats) :
    Host × PumpStats :=
  outs.foldl (init := (h, st)) fun acc d =>
    let (h', evs) := acc.1.handleDatagram now fromAddr d.2
    (h', countEvs evs payload acc.2)

/-- One pump round: service both hosts, then route each side's emitted
datagrams into the other host. Returns whether anything was emitted
(the quiescence signal for `pump`). -/
private def pumpOnce (p : BenchPair) (now : UInt32) (payload : ByteArray)
    (st : PumpStats) : BenchPair × PumpStats × Bool :=
  -- take the hosts out of the pair so each is held once and updates in
  -- place, as through the C API
  let { client, server, clientPeer, serverPeer } := p
  let (c, couts, cevs) := client.service now
  let (s, souts, _sevs) := server.service now
  let (s2, st1) := feed s now clientAddr couts payload st
  let (c2, st2) := feed c now serverAddr souts payload st1
  ({ client := c2, server := s2, clientPeer, serverPeer }, countEvs cevs payload st2,
    couts.size + souts.size > 0)

/-- Pumps until the pair is quiescent (a round with no emitted datagrams),
bounded by 16 rounds. A settled batch needs ~3 rounds (flush, acks,
ack flush); 16 leaves ample headroom for handshake/disconnect flows. -/
private def pump (p : BenchPair) (now : UInt32) (payload : ByteArray)
    (st : PumpStats) : BenchPair × PumpStats :=
  go 16 p st
where
  go : Nat → BenchPair → PumpStats → BenchPair × PumpStats
    | 0, p, st => (p, st)
    | fuel + 1, p, st =>
      let (p1, st1, active) := pumpOnce p now payload st
      if active then go fuel p1 st1 else (p1, st1)

/-- Connects a client host to a server host in-process. -/
private def handshake : Option BenchPair :=
  let client := Host.create clientAddr 8
  let server := Host.create serverAddr 8
  match client.connect serverAddr 2 42 with
  | .error _ => none
  | .ok (client, clientPeer) =>
    let p : BenchPair := { client, server, clientPeer, serverPeer := 0 }
    let (p, _) := pump p 1000 (mkPayload 0) {}
    match p.server.peers.findIdx? (·.state == .connected) with
    | none => none
    | some spIdx =>
      match p.client.peers[p.clientPeer.toNat]? with
      | some cp =>
        if cp.state == .connected then some { p with serverPeer := spIdx.toUInt16 } else none
      | none => none

/-! ## Throughput scenarios -/

structure RunResult where
  sent : Nat := 0
  received : Nat := 0
  bad : Nat := 0
  sendFailed : Bool := false

/-- Sends `n` packets, returning the host and the count that actually
queued (send can fail only if the harness itself is broken). -/
private def sendBatch (h : Host) (peer : UInt16) (ch : UInt8) (mode : DeliveryMode)
    (payload : ByteArray) (n : Nat) : Host × Nat :=
  (List.range n).foldl (init := (h, 0)) fun (h, sent) _ =>
    match h.trySend peer ch { data := payload, delivery := mode } with
    | (h, .ok ()) => (h, sent + 1)
    | (h, .error _) => (h, sent)

/-- One throughput run: `batches` batches of `batchSize` packets, each
batch fully pumped at 50 ms simulated-clock steps. `seed` offsets the
simulated clock origin; it exists purely so that each timed invocation is a
distinct computation (see `measure`). -/
private def throughputRun (mode : DeliveryMode) (payload : ByteArray)
    (batches : Nat) (batchSize : Nat) (seed : Nat) : RunResult :=
  match handshake with
  | none => { sendFailed := true }
  | some p0 =>
    go batches p0 (1000 + seed % 1000).toUInt32 {} 0 false
where
  go : Nat → BenchPair → UInt32 → PumpStats → Nat → Bool → RunResult
    | 0, _, _, st, sent, failed => { sent, received := st.received, bad := st.bad, sendFailed := failed }
    | b + 1, p, now, st, sent, failed =>
      let { client, server, clientPeer, serverPeer } := p
      let (client, sentNow) := sendBatch client clientPeer 0 mode payload batchSize
      let (p1, st1) := pump { client, server, clientPeer, serverPeer } now payload st
      go b p1 (now + 50) st1 (sent + sentNow)
        (failed ∨ sentNow ≠ batchSize)

structure ThroughputCase where
  label : String
  mode : DeliveryMode
  payloadSize : Nat
  batches : Nat
  batchSize : Nat

/-- 1200 B fits one command inside the 1392 MTU; 4096 B exercises the
fragmentation path. Batch sizes keep concurrent fragment assemblers
(16) under the `maximumFragmentAssemblers` cap of 32. -/
private def throughputCases : List ThroughputCase :=
  [ { label := "reliable 1200B",        mode := .reliable,            payloadSize := 1200, batches := 256, batchSize := 64 }
  , { label := "unreliable 1200B",      mode := .unreliable,          payloadSize := 1200, batches := 256, batchSize := 64 }
  , { label := "unsequenced 1200B",     mode := .unsequenced,         payloadSize := 1200, batches := 256, batchSize := 64 }
  , { label := "reliable 4096B (frag)", mode := .reliable,            payloadSize := 4096, batches := 256, batchSize := 16 }
  , { label := "unrelfrag 4096B (frag)", mode := .unreliableFragment, payloadSize := 4096, batches := 256, batchSize := 16 } ]

/-! ## Large packets -/

/-- One reliable packet of `payload` sent end to end, pumped at 5 ms clock
steps until it arrives (at most `steps` pumps). Exercises reassembly of
thousands of fragments into one buffer. -/
private def largeRun (payload : ByteArray) (steps : Nat) (seed : Nat) : RunResult :=
  match handshake with
  | none => { sendFailed := true }
  | some p0 =>
    let { client, server, clientPeer, serverPeer } := p0
    match client.trySend clientPeer 0 { data := payload, delivery := .reliable } with
    | (_, .error _) => { sendFailed := true }
    | (client, .ok ()) =>
      go steps { client, server, clientPeer, serverPeer } (1000 + seed % 1000).toUInt32 {}
where
  go : Nat → BenchPair → UInt32 → PumpStats → RunResult
    | 0, _, _, st => { sent := 1, received := st.received, bad := st.bad }
    | i + 1, p, now, st =>
      let (p1, st1) := pump p now payload st
      if st1.received > 0 then { sent := 1, received := st1.received, bad := st1.bad }
      else go i p1 (now + 5) st1

/-! ## Service-tick cost scenarios -/

/-- One idle-tick run: `rounds` pump rounds at 50 ms clock steps with no
traffic (keepalive pings are the only work, and they are acked). `seed`
offsets the simulated clock origin; it exists purely so that each timed
invocation is a distinct computation (see `measure`). -/
private def idleTickRun (rounds : Nat) (seed : Nat) : Bool :=
  match handshake with
  | none => false
  | some p0 =>
    let now0 := (1050 + seed % 1000).toUInt32
    let (p0, _) := pump p0 now0 (mkPayload 0) {}
    go rounds p0 now0
where
  go : Nat → BenchPair → UInt32 → Bool
    | 0, _, _ => true
    | i + 1, p, now =>
      let (p1, _) := pump p (now + 50) (mkPayload 0) {}
      go i p1 (now + 50)

/-- One loaded-tick run: `batchSize` reliable 1200 B sends + a full pump
per round. `seed` offsets the simulated clock origin (see `measure`). -/
private def loadedTickRun (rounds : Nat) (batchSize : Nat) (seed : Nat) : RunResult :=
  match handshake with
  | none => { sendFailed := true }
  | some p0 =>
    go rounds p0 (1000 + seed % 1000).toUInt32 {} 0 false
where
  go : Nat → BenchPair → UInt32 → PumpStats → Nat → Bool → RunResult
    | 0, _, _, st, sent, failed => { sent, received := st.received, bad := st.bad, sendFailed := failed }
    | b + 1, p, now, st, sent, failed =>
      let { client, server, clientPeer, serverPeer } := p
      let (client, sentNow) := sendBatch client clientPeer 0 .reliable (mkPayload 1200) batchSize
      let (p1, st1) := pump { client, server, clientPeer, serverPeer } now (mkPayload 1200) st
      go b p1 (now + 50) st1 (sent + sentNow) (failed ∨ sentNow ≠ batchSize)

/-! ## Lossy-link scenarios

The pair above never loses a datagram, so retransmission, backoff and the
in-transit/window accounting never run. Here the link between the hosts
drops every `dropEvery`-th datagram (counted over both directions), which
is deterministic but hits data, acks and pings alike. Each packet carries
its index, so the receiver can check order and duplicates, not just the
count. -/

/-- Packet `k` of a lossy run: its index (big-endian) in the first four
bytes, the deterministic pattern after it. -/
private def taggedPayload (template : ByteArray) (k : Nat) : ByteArray :=
  (template.set! 0 (k >>> 24).toUInt8).set! 1 (k >>> 16).toUInt8
    |>.set! 2 (k >>> 8).toUInt8 |>.set! 3 k.toUInt8

private def payloadTag (data : ByteArray) : Nat :=
  (data.get! 0).toNat <<< 24 ||| (data.get! 1).toNat <<< 16 |||
    (data.get! 2).toNat <<< 8 ||| (data.get! 3).toNat

structure LossyStats where
  /-- Datagrams offered to the link so far, both directions. -/
  offered : Nat := 0
  dropped : Nat := 0
  /-- Indices of the packets the server received, in delivery order. -/
  received : Array Nat := #[]
  bad : Nat := 0
  /-- Disconnect events on either side (a timeout under loss). -/
  disconnects : Nat := 0

private def countLossyEvs (template : ByteArray) (evs : Array Event) (st : LossyStats) : LossyStats :=
  evs.foldl (init := st) fun acc ev =>
    match ev with
    | .receive _ _ pkt =>
      let k := payloadTag pkt.data
      { acc with
        received := acc.received.push k
        bad := if pkt.data == taggedPayload template k then acc.bad else acc.bad + 1 }
    | .disconnect .. => { acc with disconnects := acc.disconnects + 1 }
    | .connect .. => acc

/-- Feeds one side's datagrams through the lossy link into host `h`. -/
private def feedLossy (dropEvery : Nat) (template : ByteArray) (h : Host) (now : UInt32)
    (fromAddr : Address) (outs : Array (Address × ByteArray)) (st : LossyStats) :
    Host × LossyStats :=
  outs.foldl (init := (h, st)) fun (h, st) d =>
    let st := { st with offered := st.offered + 1 }
    if st.offered % dropEvery == 0 then (h, { st with dropped := st.dropped + 1 })
    else
      let (h, evs) := h.handleDatagram now fromAddr d.2
      (h, countLossyEvs template evs st)

/-- Whether nothing is left to (re)send or acknowledge between the pair. -/
private def drained (p : BenchPair) : Bool :=
  let settled (h : Host) (id : UInt16) :=
    match h.peers[id.toNat]? with
    | some peer => peer.outgoingCommands.isEmpty && peer.sentReliableCommands.isEmpty &&
        peer.acknowledgements.isEmpty
    | none => false
  settled p.client p.clientPeer && settled p.server p.serverPeer

/-- Whether a peer is still connected and holds nothing in transit: no
bytes counted in flight and every reliable window slot released. -/
private def clean (h : Host) (id : UInt16) : Bool :=
  match h.peers[id.toNat]? with
  | some peer =>
    peer.state == .connected ∧ peer.reliableDataInTransit == 0 ∧
      peer.channels.all (·.reliableWindows.all (· == 0))
  | none => false

/-- Runs the pair over the lossy link until it drains. A round in which
something was sent advances the clock by 1 ms (the link's latency); a
silent round jumps to the earlier of the two hosts' deadlines, so waiting
for a retransmit timeout costs one round. `fuel` bounds the rounds. -/
private def settleLossy (dropEvery : Nat) (template : ByteArray) :
    Nat → BenchPair → UInt32 → LossyStats → BenchPair × UInt32 × LossyStats
  | 0, p, now, st => (p, now, st)
  | fuel + 1, p, now, st =>
    let { client, server, clientPeer, serverPeer } := p
    let (c, couts, cevs) := client.service now
    let (s, souts, sevs) := server.service now
    let st := countLossyEvs template (cevs ++ sevs) st
    let (s, st) := feedLossy dropEvery template s now clientAddr couts st
    let (c, st) := feedLossy dropEvery template c now serverAddr souts st
    let p := { client := c, server := s, clientPeer, serverPeer }
    if st.disconnects > 0 then (p, now, st)
    else if couts.size + souts.size > 0 then settleLossy dropEvery template fuel p (now + 1) st
    else if drained p then (p, now, st)
    else
      let next := match c.nextDeadline, s.nextDeadline with
        | some a, some b => Time.earliest a b
        | some a, none | none, some a => a
        | none, none => now + 1
      let next := if Time.less now next then next else now + 1
      settleLossy dropEvery template fuel p next st

structure LossyResult where
  sent : Nat := 0
  stats : LossyStats := {}
  /-- Both peers connected with nothing left in transit afterwards. -/
  clean : Bool := false
  /-- Simulated milliseconds the whole run took. -/
  elapsed : Nat := 0

/-- One lossy run: `batches` batches of `batchSize` tagged packets from the
client, each settled over the lossy link before the next is sent. -/
private def lossyRun (mode : DeliveryMode) (template : ByteArray) (batches batchSize dropEvery : Nat)
    (seed : Nat) : LossyResult :=
  match handshake with
  | none => {}
  | some p0 =>
    let now0 := (1000 + seed % 1000).toUInt32
    let (p, now, sent, st) := (List.range batches).foldl (init := (p0, now0, 0, ({} : LossyStats)))
      fun (p, now, sent, st) b =>
        if st.disconnects > 0 then (p, now, sent, st)
        else
          let { client, server, clientPeer, serverPeer } := p
          let (client, sentNow) := (List.range batchSize).foldl (init := (client, 0))
            fun (h, n) i =>
              let pkt := { data := taggedPayload template (b * batchSize + i), delivery := mode }
              match h.trySend clientPeer 0 pkt with
              | (h, .ok ()) => (h, n + 1)
              | (h, .error _) => (h, n)
          let (p, now, st) :=
            settleLossy dropEvery template 100000 { client, server, clientPeer, serverPeer } now st
          (p, now, sent + sentNow, st)
    { sent, stats := st, elapsed := (now - now0).toNat
      clean := drained p ∧ clean p.client p.clientPeer ∧ clean p.server p.serverPeer }

/-- What a lossy run must deliver: reliable modes every packet exactly once
and in order; unreliable modes a strictly increasing subset (sequenced,
so nothing late or duplicated); unsequenced a duplicate-free subset. -/
private def lossyOk (mode : DeliveryMode) (total : Nat) (r : LossyResult) : Bool :=
  let rcv := r.stats.received
  let increasing := (List.range (rcv.size - 1)).all fun i => rcv[i]! < rcv[i + 1]!
  let delivery := match mode with
    | .reliable => rcv == Array.range total
    | .unreliable | .unreliableFragment => increasing ∧ rcv.all (· < total)
    | .unsequenced => (rcv.qsort (· < ·)).toList.eraseDups.length == rcv.size ∧ rcv.all (· < total)
  r.sent == total && r.stats.bad == 0 && r.stats.disconnects == 0 && r.stats.dropped > 0 &&
    r.clean && delivery

structure LossyCase where
  label : String
  mode : DeliveryMode
  payloadSize : Nat
  batches : Nat
  batchSize : Nat
  dropEvery : Nat

/-- Drop rates of 1 in 5 and 1 in 13, one fragmented case each way. The
fragmented reliable case also loses single fragments of a packet. -/
private def lossyCases : List LossyCase :=
  [ { label := "reliable 1200B 1/5",      mode := .reliable,           payloadSize := 1200, batches := 32, batchSize := 64, dropEvery := 5 }
  , { label := "reliable 1200B 1/13",     mode := .reliable,           payloadSize := 1200, batches := 32, batchSize := 64, dropEvery := 13 }
  , { label := "reliable 4096B 1/5",      mode := .reliable,           payloadSize := 4096, batches := 32, batchSize := 16, dropEvery := 5 }
  , { label := "unreliable 1200B 1/5",    mode := .unreliable,         payloadSize := 1200, batches := 32, batchSize := 64, dropEvery := 5 }
  , { label := "unsequenced 1200B 1/5",   mode := .unsequenced,        payloadSize := 1200, batches := 32, batchSize := 64, dropEvery := 5 }
  , { label := "unrelfrag 4096B 1/13",    mode := .unreliableFragment, payloadSize := 4096, batches := 32, batchSize := 16, dropEvery := 13 } ]

/-! ## Timing + reporting -/

private def median (xs : Array Nat) : Nat :=
  let sorted := xs.qsort (· ≤ ·)
  match sorted[sorted.size / 2]? with
  | some v => v
  | none => 0

/-- Median wall time of `runs` invocations of `f`, after one untimed
warmup run; `ok` is the sanity verdict of each run's result. `f` takes a
seed derived from the clock read that starts the timed region: the Lean
optimizer may otherwise float the (pure) timed computation above the first
`monoNanosNow`, since `IO.lazyPure f` is just `pure (f ())`. Depending on a
value obtained from IO makes hoisting impossible. -/
private def measure (runs : Nat) (f : Nat → α) (ok : α → Bool) : IO (Nat × Bool) := do
  let _ ← IO.lazyPure (fun _ => f 0)  -- untimed warmup
  let mut samples := #[]
  let mut sane := true
  for _ in [0:runs] do
    let start ← IO.monoNanosNow
    let r ← IO.lazyPure (fun _ => f (start % 1024))
    let stop ← IO.monoNanosNow
    samples := samples.push (stop - start)
    if ¬ok r then sane := false
  pure (median samples, sane)

private def padRight (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- Microseconds with one decimal. -/
private def fmtUs (nanos : Nat) : String :=
  let t := (nanos + 50) / 100
  s!"{t / 10}.{t % 10}"

def runBench : IO UInt32 := do
  IO.println "Lenet benchmark (pure sans-I/O core, closed loop, median of 5 runs)"
  IO.println ""

  let mut failures := 0

  IO.println "throughput, end-to-end (send + service + datagram handling + acks)"
  IO.println
    (padRight "scenario" 27 ++ padRight "packets" 9 ++ padRight "pkts/s" 10 ++
      padRight "MB/s" 7 ++ padRight "ns/pkt" 8 ++ "sanity")
  for tc in throughputCases do
    let payload := mkPayload tc.payloadSize
    let total := tc.batches * tc.batchSize
    let bytes := total * tc.payloadSize
    let (ns, sane) ← measure 5
      (fun seed => throughputRun tc.mode payload tc.batches tc.batchSize seed)
      (fun r => ¬r.sendFailed ∧ r.sent == total ∧ r.received == total ∧ r.bad == 0)
    unless sane do failures := failures + 1
    unless sane do
      let r := throughputRun tc.mode payload tc.batches tc.batchSize 0
      IO.println s!"  FAIL {tc.label}: sent={r.sent} received={r.received} bad={r.bad} total={total} sendFailed={r.sendFailed}"
    let row :=
      padRight tc.label 27 ++
        padRight (toString total) 9 ++
      padRight (toString (total * 1000000000 / ns)) 10 ++
      padRight (toString (bytes * 10000 / ns / 10)) 7 ++
      padRight (toString (ns / total)) 8 ++
      (if sane then "ok" else "FAIL")
    IO.println row
  IO.println ""

  IO.println "large packets (one reliable packet, end to end)"
  for mb in [1, 4, 16] do
    let payload := ByteArray.mk (Array.replicate (mb * 1024 * 1024) 7)
    let (ns, sane) ← measure 1 (fun seed => largeRun payload 100000 seed)
      (fun r => ¬r.sendFailed ∧ r.received == 1 ∧ r.bad == 0)
    unless sane do failures := failures + 1
    IO.println s!"reliable {mb} MB : {ns / 1000000} ms  {if sane then "ok" else "FAIL"}"
  IO.println ""

  IO.println "service tick cost (one pump round: service both hosts + route datagrams)"
  let (nsIdle, saneIdle) ← measure 5 (fun seed => idleTickRun 400 seed) id
  unless saneIdle do failures := failures + 1
  let okIdle := if saneIdle then "ok" else "FAIL"
  IO.println s!"idle connected pair, 400 rounds @ 50 ms clock steps : {nsIdle / 400} ns/tick  {okIdle}"
  let rounds := 64
  let perRound := 64
  let (nsLoad, saneLoad) ← measure 5
    (fun seed => loadedTickRun rounds perRound seed)
    (fun r => ¬r.sendFailed ∧ r.sent == rounds * perRound ∧ r.received == rounds * perRound ∧ r.bad == 0)
  unless saneLoad do failures := failures + 1
  let okLoad := if saneLoad then "ok" else "FAIL"
  IO.println s!"loaded, {perRound} reliable 1200 B sends + pump per round      : {fmtUs (nsLoad / rounds)} us/tick, {nsLoad / (rounds * perRound)} ns/packet  {okLoad}"
  IO.println ""

  IO.println "lossy link (every n-th datagram dropped; reliable: all delivered once, in order)"
  IO.println
    (padRight "scenario" 27 ++ padRight "packets" 9 ++ padRight "received" 10 ++
      padRight "dropped" 9 ++ padRight "sim ms" 8 ++ padRight "ns/pkt" 8 ++ "sanity")
  for tc in lossyCases do
    let template := mkPayload tc.payloadSize
    let total := tc.batches * tc.batchSize
    let (ns, sane) ← measure 5
      (fun seed => lossyRun tc.mode template tc.batches tc.batchSize tc.dropEvery seed)
      (lossyOk tc.mode total)
    unless sane do failures := failures + 1
    let r := lossyRun tc.mode template tc.batches tc.batchSize tc.dropEvery 0
    unless sane do
      IO.println s!"  FAIL {tc.label}: sent={r.sent} received={r.stats.received.size} bad={r.stats.bad} disconnects={r.stats.disconnects} clean={r.clean}"
    IO.println
      (padRight tc.label 27 ++ padRight (toString total) 9 ++
        padRight (toString r.stats.received.size) 10 ++ padRight (toString r.stats.dropped) 9 ++
        padRight (toString r.elapsed) 8 ++ padRight (toString (ns / total)) 8 ++
        (if sane then "ok" else "FAIL"))
  IO.println ""

  if failures > 0 then
    IO.println s!"{failures} scenario(s) FAILED sanity"
    return 1
  return 0

end Bench

def main : IO UInt32 := Bench.runBench