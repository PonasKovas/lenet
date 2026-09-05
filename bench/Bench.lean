/-
Phase 3 benchmark executable (see TODO.md, "Phase 3 — Performance").

Measures, through the pure sans-I/O core only (no sockets, no FFI):

1. Closed-loop throughput per delivery mode. A client and a server host
   are connected in-process (outgoing datagrams of one are fed to the
   other, deadline-ticked like the replay). A batch of packets is sent,
   pumped through both hosts, and the received events counted. Numbers
   are end-to-end: send + service + datagram handling + ack traffic.

2. CPU cost of one driver service tick (one pump round: service both
   hosts + route the emitted datagrams), in the idle connected state and
   under a per-round send load.

Methodology: wall clock via IO.monoNanosNow around each pure run,
median of 5 runs, one untimed warmup run first. Each timed run gets a
seed derived from the starting clock read (it only offsets the simulated
clock origin) so the optimizer cannot hoist the pure computation out of
the timed region. Payloads are Deterministic (index-derived); no
randomness. The bench FAILs (exit 1) if any scenario loses or corrupts a
packet, so the numbers are only printed when they mean something.

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
  let (c, couts, cevs) := p.client.service now
  let (s, souts, _sevs) := p.server.service now
  let (s2, st1) := feed s now clientAddr couts payload st
  let (c2, st2) := feed c now serverAddr souts payload st1
  ({ p with client := c2, server := s2 }, countEvs cevs payload st2,
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
  (List.range n).foldl (init := (h, 0)) fun acc _ =>
    match acc.1.send peer ch { data := payload, delivery := mode } with
    | .ok h' => (h', acc.2 + 1)
    | .error _ => (acc.1, acc.2)

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
      let (client, sentNow) := sendBatch p.client p.clientPeer 0 mode payload batchSize
      let (p1, st1) := pump { p with client } now payload st
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
      let (client, sentNow) := sendBatch p.client p.clientPeer 0 .reliable (mkPayload 1200) batchSize
      let (p1, st1) := pump { p with client } now (mkPayload 1200) st
      go b p1 (now + 50) st1 (sent + sentNow) (failed ∨ sentNow ≠ batchSize)

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

  if failures > 0 then
    IO.println s!"{failures} scenario(s) FAILED sanity"
    return 1
  return 0

end Bench

def main : IO UInt32 := Bench.runBench