/-
Lenet.Net against real ENet over a bad link: the Lean side of
`make -C test lossy-interop`, whose ENet side is test/c/stream.c and whose
link is test/c/proxy.c.

  netstream server <port> <rounds> <per round> [long] [clock <ms>] [bw <bytes/s>]
  netstream client <port> <rounds> <per round> [long] [clock <ms>] [bw <bytes/s>]

The stream both ends send, what they check and how the run ends are
described in test/c/stream.c; this file follows it line by line.
Exit code 0 = passed.
-/
import Lenet.Net

open Lenet Lenet.Net Std.Net

namespace NetStream

namespace Kind
def reliable : Nat := 0
def unreliable : Nat := 1
def unsequenced : Nat := 2
def done : Nat := 3
end Kind


def size (kind ch i : Nat) : Nat :=
  if kind == Kind.reliable then
    if ch == 0 then (if i % 10 == 1 then 3000 + (i * 353) % 6000 else 5 + (i * 97) % 1000)
    else 5 + (i * 53) % 400
  else if kind == Kind.unreliable then
    if ch == 1 then 5 + (i * 71) % 1100
    else if i % 8 == 0 then 1500 + (i * 211) % 3000 else 5 + (i * 29) % 300
  else if kind == Kind.unsequenced then 5 + (i * 13) % 200
  else 5

def packet (kind ch i : Nat) : ByteArray := Id.run do
  let n := size kind ch i
  let mut b := ByteArray.emptyWithCapacity n
  b := b.push kind.toUInt8
  b := b.push (i >>> 24).toUInt8 |>.push (i >>> 16).toUInt8 |>.push (i >>> 8).toUInt8 |>.push i.toUInt8
  for j in [5:n] do
    b := b.push ((j * 31 + i + kind * 7 + ch * 3) % 251).toUInt8
  return b

structure Received where
  /-- Packets per channel and kind, but channel 1's unreliable ones. -/
  total          : Nat
  reliable       : Array Nat := #[0, 0]
  /-- Last index seen per channel; none before the first. -/
  unreliable     : Array (Option Nat) := #[none, none, none]
  unreliableSeen : Array Nat := #[0, 0, 0]
  /-- Seen, by index. -/
  unsequenced    : Array Bool
  unsequencedSeen : Nat := 0
  done           : Bool := false

def Received.allReliable (r : Received) : Bool :=
  r.reliable[0]! == r.total && r.reliable[1]! == r.total

/-- Checks one packet: the new state, or what is wrong. -/
def Received.receive (r : Received) (ch : Nat) (d : ByteArray) : Except String Received := do
  if d.size < 5 then throw "packet under 5 bytes"
  let kind := d[0]!.toNat
  let i := d[1]!.toNat <<< 24 ||| d[2]!.toNat <<< 16 ||| d[3]!.toNat <<< 8 ||| d[4]!.toNat
  if kind > Kind.done || ch > 2 then throw "unknown kind or channel"
  if d.size != size kind ch i then
    throw s!"kind {kind} channel {ch} packet {i} has {d.size} bytes, not {size kind ch i}"
  if d != packet kind ch i then throw s!"kind {kind} channel {ch} packet {i} is corrupt"
  if kind == Kind.reliable then
    if ch > 1 || i != r.reliable[ch]! then
      throw s!"reliable packet {i} on channel {ch}, expected {r.reliable[ch]?.getD 0}"
    return { r with reliable := r.reliable.modify ch (· + 1) }
  else if kind == Kind.unreliable then
    if ch == 0 || r.unreliable[ch]!.any (i ≤ ·) then
      throw s!"unreliable packet {i} on channel {ch} after {r.unreliable[ch]!}"
    return { r with unreliable := r.unreliable.set! ch (some i),
                    unreliableSeen := r.unreliableSeen.modify ch (· + 1) }
  else if kind == Kind.unsequenced then
    if ch != 2 || i ≥ r.total || r.unsequenced[i]! then
      throw s!"unsequenced packet {i} twice or out of range"
    return { r with unsequenced := r.unsequenced.set! i true, unsequencedSeen := r.unsequencedSeen + 1 }
  else
    if ch != 0 || r.done || r.reliable[0]! != r.total then
      throw "done before every reliable packet, or twice"
    return { r with done := true }

def loopback (port : UInt16) : SocketAddress := .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port }

def idle (e : Endpoint) (peer : PeerHandle) : IO Bool := do
  let some i ← e.info peer | return false
  return i.queuedCommands == 0 && i.reliableInFlight == 0 && i.reliableDataInTransit == 0

/-- `long` timeouts: limit, minimum, maximum (see test/c/stream.c). -/
def longTimeouts (e : Endpoint) (peer : PeerHandle) : IO Unit := e.setTimeout peer 256 20000 60000

structure Run where
  isServer      : Bool
  rounds        : Nat
  per           : Nat
  long          : Bool
  clock         : Option UInt32 := none
  me            : String
  start         : Nat
  lastReceive   : Nat
  lastReport    : Nat := 0
  conn          : Option Connection := none
  connectedAt   : Nat := 0
  sentRounds    : Nat := 0
  doneSent      : Bool := false
  disconnecting : Bool := false
  disconnectedAt : Nat := 0
  received      : Received

/-- Queues a packet; a refused one fails the run. -/
def sendOrFail (e : Endpoint) (conn : Connection) (ch : conn.Channel) (p : Lenet.Packet) : IO Unit := do
  match ← e.send conn ch p with
  | .ok () => pure ()
  | .error err => throw (IO.userError s!"FAIL: send refused a packet: {err}")

def sendRound (e : Endpoint) (conn : Connection) (per k : Nat) : IO Unit := do
  let some ch1 := conn.channel? 1 | throw (IO.userError "FAIL: no channel 1")
  let some ch2 := conn.channel? 2 | throw (IO.userError "FAIL: no channel 2")
  for i in [k * per:(k + 1) * per] do
    sendOrFail e conn conn.first (.reliable (packet Kind.reliable 0 i))
  for i in [k * per:(k + 1) * per] do
    sendOrFail e conn ch1 (.reliable (packet Kind.reliable 1 i))
  sendOrFail e conn ch1 (.unreliable (packet Kind.unreliable 1 k))
  for i in [k * per:(k + 1) * per] do
    sendOrFail e conn ch2 (.unreliableFragment (packet Kind.unreliable 2 i))
  for i in [k * per:(k + 1) * per] do
    sendOrFail e conn ch2 (.unsequenced (packet Kind.unsequenced 2 i))

/-- What the host holds for the connection: printed when nothing has come in
for a while, to see where a stuck link is stuck. -/
def stallReport (e : Endpoint) (st : Run) : IO Unit := do
  let some conn := st.conn | return
  let s ← e.state.get
  let some p := s.host.peers[conn.peer.slot.toNat]? | return
  let now ← e.now
  let cmd (c : OutgoingCommand) :=
    s!"ch {c.command.channelId} seq {c.command.reliableSequenceNumber} tries {c.sendAttempts} rto {c.roundTripTimeout} age {Time.difference now c.sentTime}"
  let chans := p.channels.toList.map fun c =>
    s!"[out {c.outgoingReliableSequenceNumber} in {c.incomingReliableSequenceNumber} staged {c.stagedReliable.size} windows {c.reliableWindows.toArray.toList}]"
  let r := st.received
  IO.eprintln s!"  stall {st.me}: got {r.reliable[0]!}+{r.reliable[1]!} of {r.total}, rounds {st.sentRounds}, state {repr p.state}, rtt {p.roundTripTime}/{p.roundTripTimeVariance}, transit {p.reliableDataInTransit}/{p.windowSize}, queued {p.outgoingCommands.size} (first {p.outgoingCommands[0]?.map cmd}), in flight {p.sentReliableCommands.size} (oldest {p.sentReliableCommands[0]?.map cmd}), assemblers {p.fragmentAssemblers.size}, channels {chans}"

/-- Gives up after this long without receiving a packet. -/
def giveUpMs : Nat := 90000

partial def loop (e : Endpoint) (st : Run) : IO UInt32 := do
  let now ← IO.monoMsNow
  if now - st.lastReceive ≥ giveUpMs then
    let r := st.received
    let idle ← match st.conn with | some c => idle e c.peer | none => pure false
    IO.eprintln s!"FAIL: {st.me} gave up: connected {st.conn.isSome}, rounds {st.sentRounds} of {st.rounds}, reliable {r.reliable[0]!}+{r.reliable[1]!} of {r.total}, done {r.done}, idle {idle}"
    return 1
  let mut st := st
  if now - st.lastReceive ≥ 2000 && now - st.lastReport ≥ 2000 then
    stallReport e st
    st := { st with lastReport := now }
  if let some conn := st.conn then
    let queued := (← e.info conn.peer).map (·.queuedCommands) |>.getD 0
    if st.sentRounds < st.rounds && now - st.connectedAt ≥ st.sentRounds * 10 && queued < 1000 then
      sendRound e conn st.per st.sentRounds
      st := { st with sentRounds := st.sentRounds + 1 }
    if st.sentRounds == st.rounds && st.received.allReliable && (← idle e conn.peer) then
      if st.isServer && !st.doneSent then
        let _ ← e.send conn conn.first (.reliable (packet Kind.done 0 st.received.total))
        st := { st with doneSent := true }
      else if !st.isServer && st.received.done && !st.disconnecting then
        e.disconnect conn.peer 9
        st := { st with disconnecting := true, disconnectedAt := now }
    if st.disconnecting && now - st.disconnectedAt ≥ 5000 then
      IO.println s!"  {st.me}: {st.received.total} reliable per channel in order; no ACK of the DISCONNECT in 5 s (lost)"
      e.reset conn.peer
      return 0
  match ← e.service 5 with
  | some (.connect conn _) =>
    if st.conn.isSome then
      IO.eprintln s!"FAIL: {st.me}: a second connection"; return 1
    if conn.channelCount != 3 then
      IO.eprintln s!"FAIL: {st.me}: {conn.channelCount} channels, not 3"; return 1
    if st.long then longTimeouts e conn.peer
    loop e { st with conn := some conn, connectedAt := ← IO.monoMsNow }
  | some (.receive _ ch pk) =>
    match st.received.receive ch.val pk.data with
    | .ok r => loop e { st with received := r, lastReceive := ← IO.monoMsNow }
    | .error err => IO.eprintln s!"FAIL: {st.me}: {err}"; return 1
  | some (.disconnect _ (data : UInt32)) =>
    let r := st.received
    if (if st.isServer then !(st.doneSent && data == 9) else !st.disconnecting) then
      IO.eprintln s!"FAIL: {st.me}: DISCONNECT (data {data}) before the end: {r.reliable[0]!}+{r.reliable[1]!} of {r.total} reliable, done {r.done}"
      return 1
    -- unreliable packets may be lost or throttled, but not all of them:
    -- some of each kind must get through
    if r.total > 0 && (r.unreliableSeen[1]! == 0 || r.unreliableSeen[2]! == 0 || r.unsequencedSeen == 0) then
      IO.eprintln s!"FAIL: {st.me}: unreliable {r.unreliableSeen[1]!}+{r.unreliableSeen[2]!}, unsequenced {r.unsequencedSeen}: a kind never arrived"
      return 1
    let secs := (← IO.monoMsNow) - st.start
    let hostNow ← e.now
    let clock := match st.clock with
      | some c => s!"; clock {c} to {hostNow}"
      | none => ""
    IO.println s!"  {st.me}: {r.total} reliable per channel in order; unreliable {r.unreliableSeen[1]!}+{r.unreliableSeen[2]!}, unsequenced {r.unsequencedSeen} of {r.total}; clean end, {secs / 1000}.{secs % 1000 / 100} s{clock}"
    -- let the ACK of the DISCONNECT go out
    if st.isServer then let _ ← e.serviceFor 100
    return 0
  | none => loop e st

structure Options where
  long      : Bool := false
  clock     : Option UInt32 := none
  bandwidth : UInt32 := 0

def run (isServer : Bool) (port : UInt16) (rounds per : Nat) (o : Options) : IO UInt32 := do
  let long := o.long
  let e ← Endpoint.bind (loopback (if isServer then port else 0))
    { peerCount := 4, channelLimit := 3, clock := o.clock, incomingBandwidth := o.bandwidth,
      outgoingBandwidth := o.bandwidth }
  let me := if isServer then "lenet server" else "lenet client"
  if !isServer then
    match ← e.connect (loopback port) 3 7 with
    | .ok peer => if long then longTimeouts e peer
    | .error err => IO.eprintln s!"FAIL: connect: {err}"; return 1
  let start ← IO.monoMsNow
  loop e
    { isServer, rounds, per, long, clock := o.clock, me, start, lastReceive := start, received := { total := rounds * per, unsequenced := .replicate (rounds * per) false } }

end NetStream

def usage : IO UInt32 := do
  IO.eprintln "usage: netstream server|client <port> <rounds> <per round> [long] [clock <ms>] [bw <bytes/s>]"
  return 2

def options (o : NetStream.Options) : List String → Option NetStream.Options
  | [] => some o
  | "long" :: rest => options { o with long := true } rest
  | "clock" :: ms :: rest => ms.toNat?.bind fun ms => options { o with clock := some ms.toUInt32 } rest
  | "bw" :: b :: rest => b.toNat?.bind fun b => options { o with bandwidth := b.toUInt32 } rest
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | role :: port :: rounds :: per :: rest =>
    match options {} rest with
    | some o =>
      if role != "server" && role != "client" then usage
      else NetStream.run (role == "server") port.toNat!.toUInt16 rounds.toNat! per.toNat! o
    | none => usage
  | _ => usage
