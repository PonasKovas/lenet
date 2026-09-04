/-
Replay recorded ENet traces through the Lenet sans-I/O core and diff
the results against what real ENet did.

For each trace file `<dir>/<scenario>.trace`:
  - replay the client role and the server role through `Lenet.Host`,
    feeding recorded datagrams at recorded timestamps and applying the
    recorded API calls,
  - compare the emitted event stream against ENet's recorded events,
  - compare the merged outgoing command stream (decoded from emitted
    datagrams, packet-boundary tolerant) against ENet's, masking fields
    that are inherently non-deterministic (see maskCmd),
  - sanity-check every emitted datagram (decodes cleanly, <= 4096 bytes).

Exit code 0 iff every scenario/role comparison passes.
-/
import Lenet
import Lenet.Protocol.Datagram

open Lenet

namespace Replay

/-! ## Trace model -/

inductive Role where
  | client
  | server
  deriving BEq, Inhabited

def Role.label : Role → String
  | .client => "client"
  | .server => "server"

/-- Wire direction: client→server or server→client. -/
inductive Dir where
  | c2s
  | s2c
  deriving BEq, Inhabited

/-- Does a datagram travelling in `d` arrive at `r`? -/
def Dir.targets : Dir → Role → Bool
  | .c2s, .server => true
  | .s2c, .client => true
  | _, _ => false

/-- `Dir` of datagrams emitted by role `r`. -/
def Role.outDir : Role → Dir
  | .client => .c2s
  | .server => .s2c

inductive ApiCall where
  | connect (channels : Nat) (data : UInt32)
  | send (ch : UInt8) (flags : UInt32) (payload : ByteArray)
  | disconnect (peer : UInt16) (data : UInt32)
  | peertimeout (limit mn mx : UInt32)
  | stop

inductive ExpEvent where
  | eConnect (peer : UInt16) (data : UInt32)
  | eReceive (peer : UInt16) (ch : UInt8) (flags : UInt32) (payload : ByteArray)
  | eDisconnect (peer : UInt16) (data : UInt32)

inductive Line where
  | api (ms : UInt32) (role : Role) (call : ApiCall)
  | ev (ms : UInt32) (role : Role) (e : ExpEvent)
  | dat (ms : UInt32) (dir : Dir) (bytes : ByteArray)

/-! ## Parsing -/

private def tokens (s : String) : Array String :=
  (s.splitOn " ").filter (· ≠ "") |>.toArray

private def kvVal (key : String) (ts : Array String) : Option String :=
  (ts.find? (·.startsWith (key ++ "="))).map fun t =>
    (t.drop (key.length + 1)).toString

private def hexVal (c : Char) : Nat :=
  let n := c.toNat
  if c.isDigit then n - 48 else if n ≥ 97 then n - 87 else n - 55

private def parseHex (s : String) : ByteArray :=
  let cs := s.data
  let n := cs.length / 2
  (List.range n).foldl (init := ByteArray.empty) fun acc i =>
    acc.push (UInt8.ofNat (hexVal cs[2*i]! * 16 + hexVal cs[2*i+1]!))

private def parseU16 (s : String) : UInt16 := (s.toNat? |>.getD 0).toUInt16
private def parseU32 (s : String) : UInt32 := (s.toNat? |>.getD 0).toUInt32
private def parseU8 (s : String) : UInt8 := (s.toNat? |>.getD 0).toUInt8

private def parseRole (s : String) : Option Role :=
  if s == "C" then some .client else if s == "S" then some .server else none

private def parseDir (s : String) : Option Dir :=
  if s == "C2S" then some .c2s else if s == "S2C" then some .s2c else none

private def parseApiCall (kind : String) (ts : Array String) : Option ApiCall :=
  match kind with
  | "CONNECT" => do
      let ch ← kvVal "channels" ts
      let d ← kvVal "data" ts
      some (.connect (ch.toNat? |>.getD 0) (parseU32 d))
  | "SEND" => do
      let ch ← kvVal "ch" ts
      let fl ← kvVal "flags" ts
      let hx ← kvVal "hex" ts
      some (.send (parseU8 ch) (parseU32 fl) (parseHex hx))
  | "DISCONNECT" => do
      let d ← kvVal "data" ts
      some (.disconnect ((kvVal "peer" ts).map parseU16 |>.getD 0) (parseU32 d))
  | "PEERTIMEOUT" => do
      let a ← kvVal "limit" ts
      let b ← kvVal "min" ts
      let c ← kvVal "max" ts
      some (.peertimeout (parseU32 a) (parseU32 b) (parseU32 c))
  | "STOP" => some .stop
  | _ => none

private def parseEvent (kind : String) (ts : Array String) : Option ExpEvent :=
  match kind with
  | "CONNECT" => do
      let d ← kvVal "data" ts
      some (.eConnect ((kvVal "peer" ts).map parseU16 |>.getD 0) (parseU32 d))
  | "RECEIVE" => do
      let fl ← kvVal "flags" ts
      let hx ← kvVal "hex" ts
      some (.eReceive ((kvVal "peer" ts).map parseU16 |>.getD 0)
        ((kvVal "ch" ts).map parseU8 |>.getD 0) (parseU32 fl) (parseHex hx))
  | "DISCONNECT" => do
      let d ← kvVal "data" ts
      some (.eDisconnect ((kvVal "peer" ts).map parseU16 |>.getD 0) (parseU32 d))
  | _ => none

def parseLine (s : String) : Option Line := do
  let ts := tokens s
  if ts.isEmpty then failure
  match ts[0]! with
  | "A" => do
      let msNat ← (ts[1]? >>= (·.toNat?))
      let role ← (ts[2]? >>= parseRole)
      let kind ← ts[3]?
      let call ← parseApiCall kind ts
      some (.api msNat.toUInt32 role call)
  | "E" => do
      let msNat ← (ts[1]? >>= (·.toNat?))
      let role ← (ts[2]? >>= parseRole)
      let kind ← ts[3]?
      let e ← parseEvent kind ts
      some (.ev msNat.toUInt32 role e)
  | "N" => do
      let msNat ← (ts[1]? >>= (·.toNat?))
      let dir ← (ts[2]? >>= parseDir)
      let hx ← kvVal "hex" ts
      some (.dat msNat.toUInt32 dir (parseHex hx))
  | _ => none

def parseTrace (text : String) : Array Line :=
  (text.splitOn "\n").filterMap parseLine |>.toArray

/-! ## Masked command comparison -/

private def hexOf (b : ByteArray) : String :=
  let digits := "0123456789abcdef".data
  let nib (v : Nat) : Char := digits.getD (v &&& 15) 'x'
  b.foldl (init := "") fun acc x =>
    acc.push (nib (x.toNat >>> 4)) |>.push (nib x.toNat)

/-- Render a byte array for comparison: full hex for small payloads, a
bounded prefix for huge ones (fragment payloads). -/
private def cmpBytes (b : ByteArray) : String :=
  if b.size ≤ 64 then s!"{b.size}:{hexOf b}" else s!"{b.size}:{hexOf (b.extract 0 64)}…"

/-- Canonical, mask-aware representation of a protocol command.
Masked fields (inherently non-deterministic, documented in TESTING.md):
  - connect/verifyConnect: `connectId`, session IDs
Everything else must match exactly. -/
def maskCmd (c : Protocol.Command) : String :=
  let fl := (if c.acknowledge then "A" else "-") ++ (if c.unsequenced then "U" else "-")
  let body :=
    match c.body with
    | .acknowledge rseq rtime => s!"ack(rseq={rseq},rtime={rtime})"
    | .connect p _ =>
      s!"connect(outPid={p.outgoingPeerId},mtu={p.mtu},win={p.windowSize},ch={p.channelCount}," ++
      s!"inBw={p.incomingBandwidth},outBw={p.outgoingBandwidth},pti={p.packetThrottleInterval}," ++
      s!"acc={p.packetThrottleAcceleration},dec={p.packetThrottleDeceleration})" -- connectId+sessions masked
    | .verifyConnect p =>
      s!"verifyConnect(outPid={p.outgoingPeerId},mtu={p.mtu},win={p.windowSize},ch={p.channelCount}," ++
      s!"inBw={p.incomingBandwidth},outBw={p.outgoingBandwidth},pti={p.packetThrottleInterval}," ++
      s!"acc={p.packetThrottleAcceleration},dec={p.packetThrottleDeceleration})" -- connectId+sessions masked
    | .disconnect d => s!"disconnect(d={d})"
    | .ping => "ping"
    | .sendReliable d => s!"sendReliable({cmpBytes d})"
    | .sendUnreliable un d => s!"sendUnreliable(un={un},{cmpBytes d})"
    | .sendFragment fp =>
      s!"sendFragment(start={fp.startSequenceNumber},cnt={fp.fragmentCount},n={fp.fragmentNumber}," ++
      s!"tot={fp.totalLength},off={fp.fragmentOffset},len={fp.data.size})"
    | .sendUnsequenced g d => s!"sendUnsequenced(g={g},{cmpBytes d})"
    | .bandwidthLimit i o => s!"bandwidthLimit(in={i},out={o})"
    | .throttleConfigure i a d => s!"throttleConfigure(i={i},a={a},d={d})"
    | .sendUnreliableFragment fp =>
      s!"sendUnreliableFragment(start={fp.startSequenceNumber},cnt={fp.fragmentCount},n={fp.fragmentNumber}," ++
      s!"tot={fp.totalLength},off={fp.fragmentOffset},len={fp.data.size})"
  s!"[{fl} ch={c.channelId} seq={c.reliableSequenceNumber}] {body}"

/-- Decode a datagram byte string into its command list. -/
def decodeDatagram (bytes : ByteArray) : Except CodecError (Array Protocol.Command) :=
  (ReaderM.run (Protocol.Datagram.decodeWith false none) bytes).map (·.commands)

/-! ## Replay -/

structure ReplayState where
  host : Host
  events : Array Event := #[]
  outCmds : Array Protocol.Command := #[]
  emitted : Array ByteArray := #[]
  errors : Array String := #[]
  stoppedFlag : Bool := false

structure ReplayResult where
  role : Role
  events : Array Event
  outCmds : Array Protocol.Command
  emitted : Array ByteArray
  errors : Array String
  expEvents : Array ExpEvent
  expCmds : Array Protocol.Command
  expDecodeErrors : Array CodecError

/-- Addresses mirroring the recorded harness topology. -/
def proxyAddr : Address := Address.ipv4 127 0 0 1 40000
def clientAddr : Address := Address.ipv4 127 0 0 1 40001
def serverAddr : Address := Address.ipv4 127 0 0 1 40002

private def collectOutgoing (st : ReplayState) (outs : Array (Address × ByteArray)) : ReplayState :=
  outs.foldl (init := st) fun s (_, bytes) =>
    match decodeDatagram bytes with
    | .ok cmds => { s with outCmds := s.outCmds ++ cmds, emitted := s.emitted.push bytes }
    | .error e => { s with errors := s.errors.push s!"emitted datagram failed to decode: {e}" }

private def service (st : ReplayState) (now : UInt32) : ReplayState :=
  if st.stoppedFlag then st
  else
    let (h, outs, evs) := st.host.service now
    collectOutgoing { st with host := h, events := st.events ++ evs } outs

private def applyApi (st : ReplayState) (ms : UInt32) : ApiCall → ReplayState
  | .connect channels data =>
    match st.host.connect proxyAddr channels data with
    | .ok (h, _) => service { st with host := h } ms
    | .error e => service { st with errors := st.errors.push s!"connect failed: {e}" } ms
  | .send ch flags payload =>
    match st.host.send 0 ch { data := payload, delivery := DeliveryMode.fromFlags flags } with
    | .ok h => service { st with host := h } ms
    | .error e => service { st with errors := st.errors.push s!"send failed: {e}" } ms
  | .disconnect peer data => service { st with host := st.host.disconnect peer data } ms
  | .peertimeout limit mn mx =>
    let st2 :=
      if h : 0 < st.host.peers.size then
        let peer := st.host.peers[0]
        let peer' := { peer with timeoutLimit := limit, timeoutMinimum := mn, timeoutMaximum := mx }
        { st with host := { st.host with peers := st.host.peers.set 0 peer' h } }
      else st
    service st2 ms
  | .stop => { st with stoppedFlag := true }

private def step (role : Role) (st : ReplayState) (line : Line) : ReplayState :=
  if st.errors.size ≥ 3 then st -- stop accumulating after a blow-up
  else
    match line with
    | .api ms r call =>
      if r == role then applyApi st ms call else service st ms
    | .ev ms _ _ =>
      -- expected events are checked at the end; just keep the clock moving
      service st ms
    | .dat ms dir bytes =>
      if dir.targets role then
        let (h, evs) := st.host.handleDatagram ms proxyAddr bytes
        service { st with host := h, events := st.events ++ evs } ms
      else
        service st ms

def initialHost (role : Role) : Host :=
  match role with
  | .client => Host.create clientAddr 1 2 0 0 0x12345678
  | .server => Host.create serverAddr 16 2 0 0 0x12345678

def replayRole (role : Role) (lines : Array Line) : ReplayResult :=
  let st := lines.foldl (step role) { host := initialHost role }
  let expEvents := lines.filterMap fun
    | .ev _ r e => if r == role then some e else none
    | _ => none
  let expDatagrams := lines.filterMap fun
    | .dat _ d bytes => if d == role.outDir then some bytes else none
    | _ => none
  let (expCmds, expDecodeErrors) := expDatagrams.foldl (init := (#[], #[])) fun (cs, es) b =>
    match decodeDatagram b with
    | .ok cmds => (cs ++ cmds, es)
    | .error e => (cs, es.push e)
  { role
    events := st.events
    outCmds := st.outCmds
    emitted := st.emitted
    errors := st.errors
    expEvents
    expCmds
    expDecodeErrors }

/-! ## Comparison and reporting -/

private def expToEvent (e : ExpEvent) : Event :=
  match e with
  | .eConnect p d => .connect p d
  | .eDisconnect p d => .disconnect p d
  | .eReceive p ch flags payload =>
    .receive p ch { data := payload, delivery := DeliveryMode.fromFlags flags }

private def eventLabel (e : Event) : String :=
  match e with
  | .connect p d => s!"connect(peer={p}, data={d})"
  | .disconnect p d => s!"disconnect(peer={p}, data={d})"
  | .receive p ch k => s!"receive(peer={p}, ch={ch}, flags={k.delivery.toFlags}, len={k.data.size}, hex={cmpBytes k.data})"

private def eventEq (a b : Event) : Bool :=
  match a, b with
  | .connect p1 d1, .connect p2 d2 => p1 == p2 && d1 == d2
  | .disconnect p1 d1, .disconnect p2 d2 => p1 == p2 && d1 == d2
  | .receive p1 c1 k1, .receive p2 c2 k2 =>
    p1 == p2 && c1 == c2 && k1.data == k2.data && k1.delivery.toFlags == k2.delivery.toFlags
  | _, _ => false

private def firstDiff (n : Nat) (labelOf : Nat → Option String) : Option (Nat × String) :=
  ((List.range n).filterMap fun i =>
    (labelOf i).map (fun d => (i, d))).head?

private def eventDiffOf (exp : Array ExpEvent) (act : Array Event) : Option (Nat × String) :=
  let n := max exp.size act.size
  firstDiff n fun i =>
    match exp[i]?, act[i]? with
    | none, some a => some s!"unexpected extra event: {eventLabel a}"
    | some e, none => some s!"missing event: {eventLabel (expToEvent e)}"
    | some e, some a =>
      if eventEq (expToEvent e) a then none
      else some s!"expected {eventLabel (expToEvent e)}  but got {eventLabel a}"
    | none, none => none

private def cmdDiffOf (exp act : Array Protocol.Command) : Option (Nat × String) :=
  let n := max exp.size act.size
  firstDiff n fun i =>
    match exp[i]?, act[i]? with
    | none, some c => some s!"unexpected extra command: {maskCmd c}"
    | some c, none => some s!"missing command: {maskCmd c}"
    | some e, some a =>
      let me := maskCmd e
      let ma := maskCmd a
      if me == ma then none
      else some s!"ENet:  {me}\n         lenet: {ma}"
    | none, none => none

private def replayAndReport (scenario : String) (lines : Array Line) : IO Bool := do
  let results := [Role.client, Role.server].map (fun r => replayRole r lines)
  let mut allOk := true
  for res in results do
    let label := s!"{scenario}/{res.role.label}"
    let maxLen := res.emitted.foldl (init := 0) fun acc b => max acc b.size
    let sizeOk := maxLen ≤ 4096
    let eventDiff := eventDiffOf res.expEvents res.events
    let cmdDiff := cmdDiffOf res.expCmds res.outCmds
    let ok := eventDiff.isNone && cmdDiff.isNone && res.errors.isEmpty && res.expDecodeErrors.isEmpty && sizeOk
    if ok then
      IO.println s!"  PASS {label}  (events={res.events.size}, commands={res.outCmds.size}, datagrams={res.emitted.size})"
    else
      allOk := false
      IO.println s!"  FAIL {label}"
      match eventDiff with
      | some (i, d) => IO.println s!"    event[{i}] mismatch: {d}"
      | none => pure ()
      match cmdDiff with
      | some (i, d) => IO.println s!"    command[{i}] mismatch:\n         {d}"
      | none => pure ()
      for e in res.errors do
        IO.println s!"    error: {e}"
      for e in res.expDecodeErrors do
        IO.println s!"    ENet datagram failed to decode with lenet's decoder: {e}"
      IO.println s!"    (ENet commands={res.expCmds.size}, lenet commands={res.outCmds.size}; ENet events={res.expEvents.size}, lenet events={res.events.size})"
  pure allOk

def scenarioNames : Array String :=
  #["connect", "send_c2s", "send_s2c", "frag", "disc_client", "disc_server", "idle", "timeout"]

end Replay

open Replay in
def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "traces"
  let wanted := if args.length > 1 then (args.drop 1).toArray else scenarioNames
  let mut allOk := true
  for name in wanted do
    let path := s!"{dir}/{name}.trace"
    let text ← IO.FS.readFile path
    let lines := parseTrace text
    IO.println s!"{name} ({lines.size} trace lines)"
    let ok ← replayAndReport name lines
    if !ok then allOk := false
  if allOk then
    IO.println "ALL PASS"
    return 0
  else
    IO.println "FAILED"
    return 1
