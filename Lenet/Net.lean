import Lenet.Host
import Std.Async.UDP
import Std.Async.Timer

/-!
# Lenet over a UDP socket

`Lenet.Host` is sans-I/O: something has to move its datagrams and call its
timers. `Endpoint` does that over a `Std.Async.UDP` socket, so a Lean
program can use ENet the way a C program does: bind, `connect`, `send`, and
call `service` in a loop to get events (ENet's enet_host_service).

Connections are named by `PeerHandle`s rather than raw peer IDs. A peer
slot is reused once its connection ends, so a raw ID can silently start
meaning someone else; a handle carries the generation of the connection it
names, and once that connection is over, calls with it do nothing (or fail
with `peerNotConnected`).

Once a connection is up, `service` hands out a `Connection`: the handle and
the channels the two sides agreed on (the server may grant fewer than the
client asked for). Its channels are `Fin`s of that count, so a send cannot
name a channel the connection does not have.

This lives in its own library (`LenetNet`): the engine and the C
distribution do not depend on it.
-/

namespace Lenet.Net

open Std.Net

-- `open Lenet.Net` is all a program needs (opening `Lenet` too would make
-- `Event` ambiguous). Lean resolves `Packet.reliable` through such an alias
-- only as `.reliable` (or `Lenet.Packet.reliable`).
export Lenet (Packet DeliveryMode LenetError PeerState)

/-- One connection: its peer slot and a generation number that no other
connection of the endpoint shares. -/
structure PeerHandle where
  slot       : UInt16
  generation : Nat
deriving BEq, Hashable, Repr, Inhabited

instance : ToString PeerHandle where
  toString p := s!"peer {p.slot}#{p.generation}"

/-- A connection that is up: its handle and how many channels it has.
Only `service` makes these, so the count is the one both sides agreed on. -/
structure Connection where
  private mk ::
  peer         : PeerHandle
  channelCount : Nat
  channelCount_pos : 0 < channelCount
deriving Repr

instance : BEq Connection where
  beq a b := a.peer == b.peer && a.channelCount == b.channelCount

instance : Hashable Connection where
  hash c := mixHash (hash c.peer) (hash c.channelCount)

instance : Coe Connection PeerHandle := ⟨Connection.peer⟩

instance : ToString Connection where
  toString c := toString c.peer

/-- A channel of connection `c`. There is no numeric literal for it
(`Fin`'s would wrap around the count): take `c.channel? i`, `c.first` or
the channel a packet came in on. -/
abbrev Connection.Channel (c : Connection) := Fin c.channelCount

namespace Connection

/-- Channel `i`, if the connection has it. -/
def channel? (c : Connection) (i : Nat) : Option c.Channel :=
  if h : i < c.channelCount then some ⟨i, h⟩ else none

/-- Channel 0, which every connection has. -/
def first (c : Connection) : c.Channel := ⟨0, c.channelCount_pos⟩

/-- Every channel of the connection, in order. -/
def channels (c : Connection) : List c.Channel := List.finRange c.channelCount

end Connection

/-- What `Endpoint.service` reports. -/
inductive Event where
  /-- A connection completed; `data` is what the client sent with its
  CONNECT (0 on the client's own side, as in ENet). -/
  | connect (conn : Connection) (data : UInt32)
  /-- A connection ended: gracefully (with the remote's data) or by timeout
  (data 0). The handle is dead from now on. -/
  | disconnect (peer : PeerHandle) (data : UInt32)
  /-- A packet arrived on one of the connection's channels. -/
  | receive (conn : Connection) (channel : conn.Channel) (packet : Packet)

instance : BEq Event where
  beq
    | .connect a d, .connect b e => a == b && d == e
    | .disconnect a d, .disconnect b e => a == b && d == e
    | .receive a c p, .receive b d q => a == b && c.val == d.val && p == q
    | _, _ => false

instance : Inhabited Event := ⟨.disconnect default 0⟩

/-- How to set up an endpoint (the parameters of ENet's enet_host_create). -/
structure Config where
  /-- Peer slots: how many connections, in and out, can be open at once. -/
  peerCount         : Nat := 32
  /-- Most channels an incoming connection gets; 0 means 255. -/
  channelLimit      : Nat := Constants.maximumChannelCount
  /-- Bytes per second; 0 means unlimited. -/
  incomingBandwidth : UInt32 := 0
  outgoingBandwidth : UInt32 := 0
  mtu               : UInt32 := Constants.defaultMtu.toUInt32
  /-- CRC32 on every datagram; the remote side must agree. -/
  checksum          : Bool := false
  /-- Seed for connect IDs; by default taken from the clock. -/
  seed              : Option UInt32 := none
  /-- What the host's millisecond clock reads at `bind`; by default the
  monotonic clock's value. It wraps at 2^32 like ENet's, so a test can
  start it just before the wrap (ENet's enet_time_set). -/
  clock             : Option UInt32 := none

/-- A peer as seen from its endpoint. -/
structure PeerInfo where
  address               : SocketAddress
  state                 : PeerState
  roundTripTime         : UInt32
  roundTripTimeVariance : UInt32
  packetThrottle        : UInt32
  /-- Commands queued and not yet sent (ENet's outgoing queues). -/
  queuedCommands        : Nat
  /-- Reliable commands sent and not yet acknowledged. -/
  reliableInFlight      : Nat
  /-- Bytes of those, as counted against the congestion window. -/
  reliableDataInTransit : Nat

/-- ENet speaks IPv4 only. -/
def toAddress : SocketAddress → Option Address
  | .v4 a => some { host := Address.fromOctets a.addr.octets[0] a.addr.octets[1] a.addr.octets[2] a.addr.octets[3],
                    port := a.port }
  | .v6 _ => none

def ofAddress (a : Address) : SocketAddress :=
  let (b0, b1, b2, b3) := Address.toOctets a.host
  .v4 { addr := IPv4Addr.ofParts b0 b1 b2 b3, port := a.port }

/-- A slot's connection, while the application may use it. -/
structure Slot where
  generation   : Nat
  /-- The connection's channels, from its connect event on (the client
  starts connecting before it knows how many the server grants). -/
  channelCount : Nat := 0

structure State where
  host       : Host
  /-- Each slot's connection: set when the client starts connecting or the
  server reports the connect, cleared when the connection ends. -/
  live       : Array (Option Slot)
  generation : Nat := 0
  pending    : Std.Queue Event := .empty

/-- What went wrong on the socket. A send or receive that fails loses one
datagram, which UDP may do anyway, so `service` goes on; these say it
happened. -/
structure SocketErrors where
  sendFailures    : Nat := 0
  receiveFailures : Nat := 0
  /-- The most recent failure. -/
  last            : Option IO.Error := none

/-- A receive on the socket, resolved once a datagram is in. -/
abbrev Inbox := IO.Promise (Except IO.Error (ByteArray × Option SocketAddress))

/-- A Lenet host bound to a UDP socket. -/
structure Endpoint where
  private mk ::
  socket : Std.Async.UDP.Socket
  state  : IO.Ref State
  /-- One receive is always outstanding, so checking for a datagram never
  blocks and never loses one (`Std.Async`'s own non-blocking receive,
  `Selectable.tryOne` on `recvSelector`, never finds one). -/
  inbox  : IO.Ref Inbox
  /-- Who to wake when the receive completes, while `service` sleeps. -/
  waiter : IO.Ref (Option (Std.Async.Waiter Unit))
  /-- The host's clock minus the monotonic clock (`Config.clock`). -/
  clockOffset : UInt32
  errors : IO.Ref SocketErrors

namespace State

/-- Whether `peer` still names the connection in its slot. -/
def isLive (s : State) (peer : PeerHandle) : Bool :=
  (s.live[peer.slot.toNat]?.bind id).map (·.generation) == some peer.generation

/-- The connection in slot `slot`, if the application may use it. -/
def slot? (s : State) (slot : UInt16) : Option Slot := s.live[slot.toNat]?.bind id

/-- A new generation for slot `slot`. -/
def openSlot (s : State) (slot : UInt16) : State × Nat :=
  ({ s with live := s.live.setIfInBounds slot.toNat (some { generation := s.generation }),
            generation := s.generation + 1 },
    s.generation)

def closeSlot (s : State) (slot : UInt16) : State :=
  { s with live := s.live.setIfInBounds slot.toNat none }

/-- Turns the host's events into handle events and queues them. A connect
the application has no handle for yet (the server side) opens a generation;
a disconnect closes it. -/
def push (s : State) (events : Array Lenet.Event) : State :=
  events.foldl (init := s) fun s ev =>
    match ev with
    | .connect id data =>
      let (s, g) := match s.slot? id with
        | some slot => (s, slot.generation)
        | none => s.openSlot id
      -- a connected peer has at least one channel; 0 only if something
      -- later in the same batch already reset it, and then every call
      -- with the handle fails anyway
      let count := max 1 ((s.host.peers[id.toNat]?.map (·.channels.size)).getD 0)
      let conn : Connection := ⟨⟨id, g⟩, count, by omega⟩
      { s with live := s.live.setIfInBounds id.toNat (some { generation := g, channelCount := count }),
               pending := s.pending.enqueue (.connect conn data) }
    | .disconnect id data =>
      match s.slot? id with
      | some slot => { s.closeSlot id with pending := s.pending.enqueue (.disconnect ⟨id, slot.generation⟩ data) }
      -- a connection the application never had a handle for
      | none => s
    | .receive id ch packet =>
      match s.slot? id with
      | some slot =>
        if h : 0 < slot.channelCount then
          let conn : Connection := ⟨⟨id, slot.generation⟩, slot.channelCount, h⟩
          if hc : ch.toNat < slot.channelCount then
            { s with pending := s.pending.enqueue (.receive conn ⟨ch.toNat, hc⟩ packet) }
          else s
        else s
      | none => s

end State

namespace Endpoint

/-- The clock the host runs on, in milliseconds. It wraps like ENet's. -/
def now (e : Endpoint) : IO UInt32 := return (← IO.monoMsNow).toUInt32 + e.clockOffset

/-- The largest datagram ENet sends. -/
def maximumDatagram : UInt64 := Constants.maximumMtu.toUInt64

/-- Wakes the sleeping `service`, if there is one. -/
def wake (waiter : IO.Ref (Option (Std.Async.Waiter Unit))) : IO Unit := do
  if let some w ← waiter.swap none then
    w.race (pure ()) fun promise => promise.resolve (.ok ())

/-- Starts the next receive. Its one continuation wakes whoever sleeps on
it then; registering one per sleep instead would pile them up on an idle
socket. -/
def arm (socket : Std.Async.UDP.Socket) (waiter : IO.Ref (Option (Std.Async.Waiter Unit))) : IO Inbox := do
  let p ← socket.native.recv maximumDatagram
  discard <| IO.mapTask (t := p.result?) fun _ => wake waiter
  return p

/-- Binds a new endpoint to `address` (port 0 picks a free one). -/
def bind (address : SocketAddress) (config : Config := {}) : IO Endpoint := do
  let some local_ := toAddress address | throw (.userError "Lenet: ENet speaks IPv4 only")
  let socket ← Std.Async.UDP.Socket.mk
  socket.bind address
  let clock ← IO.monoNanosNow
  let seed := config.seed.getD clock.toUInt32
  let host := Host.create local_ config.peerCount config.channelLimit config.incomingBandwidth
    config.outgoingBandwidth seed config.mtu
  let host := { host with checksumEnabled := config.checksum }
  let state ← IO.mkRef { host, live := Array.replicate host.peers.size none }
  let waiter ← IO.mkRef none
  let inbox ← IO.mkRef (← arm socket waiter)
  let mono := (← IO.monoMsNow).toUInt32
  return ⟨socket, state, inbox, waiter, config.clock.getD mono - mono, ← IO.mkRef {}⟩

/-- The address the socket is bound to. -/
def localAddress (e : Endpoint) : IO SocketAddress := e.socket.getSockName

/-- The socket's failures so far. -/
def socketErrors (e : Endpoint) : IO SocketErrors := e.errors.get

/-- Sends each datagram. One that fails (a destination the network refuses,
such as port 0) is counted and lost, and the rest still go: the host has
already moved on, as if it was sent. -/
def transmit (e : Endpoint) (datagrams : Array (Address × ByteArray)) : IO Unit :=
  for (to, bytes) in datagrams do
    try (e.socket.send bytes (some (ofAddress to))).block
    catch err => e.errors.modify fun s => { s with sendFailures := s.sendFailures + 1, last := some err }

/-- Starts connecting to `address` with `channelCount` channels, sending
`data` with the CONNECT. The connection is up once `service` reports
`.connect` for the handle; it may instead report `.disconnect` if the remote
never answers. -/
def connect (e : Endpoint) (address : SocketAddress) (channelCount : Nat := 2) (data : UInt32 := 0) :
    IO (Except LenetError PeerHandle) := do
  let some to := toAddress address | throw (.userError "Lenet: ENet speaks IPv4 only")
  e.state.modifyGet fun s =>
    match s.host.connect to channelCount data with
    | .ok (host, id) =>
      let (s, g) := { s with host }.openSlot id
      (.ok ⟨id, g⟩, s)
    | .error err => (.error err, s)

/-- Queues `packet` for `conn` on `channel`; it goes out on the next
`service` or `flush`. Fails with `peerNotConnected` once the connection is
over, and for a packet ENet cannot send (too large, too many fragments). -/
def send (e : Endpoint) (conn : Connection) (channel : conn.Channel) (packet : Packet) :
    IO (Except LenetError Unit) :=
  e.state.modifyGet fun s =>
    if !s.isLive conn.peer then (.error (.peerNotConnected conn.peer.slot), s)
    else
      let (host, result) := s.host.trySend conn.peer.slot channel.val.toUInt8 packet
      (result, { s with host })

/-- Queues `packet` for every connected peer on `channel`, skipping peers
without that channel. -/
def broadcast (e : Endpoint) (channel : UInt8) (packet : Packet) : IO Unit :=
  e.state.modify fun s => { s with host := s.host.broadcast channel packet }

/-- Runs `f` on `peer`'s slot if the handle is live. -/
def withLive (e : Endpoint) (peer : PeerHandle) (f : State → State) : IO Unit :=
  e.state.modify fun s => if s.isLive peer then f s else s

/-- Whether the peer's handshake is still under way: disconnecting it then
resets it without an event (ENet same), so its handle dies at once. -/
def handshaking (s : State) (slot : UInt16) : Bool :=
  match s.host.peers[slot.toNat]?.map (·.state) with
  | some PeerState.connecting | some PeerState.acknowledgingConnect => true
  | _ => false

/-- Starts a graceful disconnect; `service` reports `.disconnect` when it
completes. -/
def disconnect (e : Endpoint) (peer : PeerHandle) (data : UInt32 := 0) : IO Unit :=
  e.withLive peer fun s =>
    let s' := { s with host := s.host.disconnect peer.slot data }
    if handshaking s peer.slot then s'.closeSlot peer.slot else s'

/-- Disconnects once everything queued for the peer has been delivered. -/
def disconnectLater (e : Endpoint) (peer : PeerHandle) (data : UInt32 := 0) : IO Unit :=
  e.withLive peer fun s =>
    let s' := { s with host := s.host.disconnectLater peer.slot data }
    if handshaking s peer.slot then s'.closeSlot peer.slot else s'

/-- Ends the connection at once, without an event; the remote gets one
unacknowledged DISCONNECT on the next `service` or `flush`. -/
def disconnectNow (e : Endpoint) (peer : PeerHandle) (data : UInt32 := 0) : IO Unit :=
  e.withLive peer fun s => { s with host := s.host.disconnectNow peer.slot data }.closeSlot peer.slot

/-- Drops the connection at once, telling no one. -/
def reset (e : Endpoint) (peer : PeerHandle) : IO Unit :=
  e.withLive peer fun s => { s with host := s.host.resetPeer peer.slot }.closeSlot peer.slot

/-- Sends a PING now (an RTT sample without waiting for the keepalive). -/
def ping (e : Endpoint) (peer : PeerHandle) : IO Unit :=
  e.withLive peer fun s => { s with host := s.host.ping peer.slot }

/-- How long the peer may be idle before the keepalive PING; 0 means the
default. -/
def setPingInterval (e : Endpoint) (peer : PeerHandle) (interval : UInt32) : IO Unit :=
  e.withLive peer fun s => { s with host := s.host.setPingInterval peer.slot interval }

/-- The peer's timeout parameters (ENet's enet_peer_timeout); 0 means the
default. -/
def setTimeout (e : Endpoint) (peer : PeerHandle) (limit minimum maximum : UInt32) : IO Unit :=
  e.withLive peer fun s => { s with host := s.host.setPeerTimeout peer.slot limit minimum maximum }

/-- The peer's packet throttle parameters, sent to the remote too. -/
def throttleConfigure (e : Endpoint) (peer : PeerHandle) (interval accel decel : UInt32) : IO Unit :=
  e.withLive peer fun s => { s with host := s.host.throttleConfigure peer.slot interval accel decel }

/-- New bandwidth limits for the endpoint (bytes per second, 0 = unlimited). -/
def bandwidthLimit (e : Endpoint) (incoming outgoing : UInt32) : IO Unit :=
  e.state.modify fun s => { s with host := s.host.bandwidthLimit incoming outgoing }

/-- What the endpoint knows about `peer`, while the handle is live. -/
def info (e : Endpoint) (peer : PeerHandle) : IO (Option PeerInfo) := do
  let s ← e.state.get
  if !s.isLive peer then return none
  return s.host.peers[peer.slot.toNat]?.map fun p =>
    { address := ofAddress p.address, state := p.state, roundTripTime := p.roundTripTime
      roundTripTimeVariance := p.roundTripTimeVariance, packetThrottle := p.packetThrottle
      queuedCommands := p.outgoingCommands.size, reliableInFlight := p.sentReliableCommands.size
      reliableDataInTransit := p.reliableDataInTransit }

/-- Sends everything queued now, without running the timers (ENet's
enet_host_flush). -/
def flush (e : Endpoint) : IO Unit := do
  let now ← e.now
  let datagrams ← e.state.modifyGet fun s =>
    let (host, datagrams, events) := s.host.pollOutgoing now
    (datagrams, { s with host }.push events)
  e.transmit datagrams

def popEvent (e : Endpoint) : IO (Option Event) :=
  e.state.modifyGet fun s =>
    match s.pending.dequeue? with
    | some (ev, rest) => (some ev, { s with pending := rest })
    | none => (none, s)

/-- Feeds one received datagram to the host. One from port 0 is dropped:
no answer could reach it. -/
def deliver (e : Endpoint) (bytes : ByteArray) (from? : Option SocketAddress) : IO Unit := do
  let some from_ := from? >>= toAddress | return
  if from_.port == 0 then return
  let now ← e.now
  e.state.modify fun s =>
    let (host, events) := s.host.handleDatagram now from_ bytes
    { s with host }.push events

/-- Runs the host's timers and sends what they and the queues produce. -/
def serviceHost (e : Endpoint) : IO Unit := do
  let now ← e.now
  let datagrams ← e.state.modifyGet fun s =>
    let (host, datagrams, events) := s.host.service now
    (datagrams, { s with host }.push events)
  e.transmit datagrams

/-- The receive that completed, if one did, without waiting: a datagram, or
the error it failed with. -/
def poll (e : Endpoint) : IO (Option (Except IO.Error (ByteArray × Option SocketAddress))) := do
  let p ← e.inbox.get
  if !(← p.isResolved) then return none
  e.inbox.set (← arm e.socket e.waiter)
  match ← IO.wait p.result? with
  | some r => return some r
  | none => return some (.error (.userError "Lenet: the receive was dropped"))

/-- Counts a failed receive. -/
def receiveFailed (e : Endpoint) (err : IO.Error) : IO Unit :=
  e.errors.modify fun s => { s with receiveFailures := s.receiveFailures + 1, last := some err }

/-- Ready once a datagram is in; takes nothing, so losing the race loses
no datagram. -/
def ready (e : Endpoint) : Std.Async.Selector Unit where
  tryFn := return if ← (← e.inbox.get).isResolved then some () else none
  registerFn w := do
    e.waiter.set (some w)
    -- the datagram may have come in before the waiter was there
    if ← (← e.inbox.get).isResolved then wake e.waiter
  unregisterFn := e.waiter.set none

/-- Waits up to `ms` milliseconds for a datagram. A failed receive is
counted and the wait sleeps out its time, so a socket that keeps failing
costs a sleep per round, not a busy loop. -/
def receive (e : Endpoint) (ms : UInt32) : IO (Option (ByteArray × Option SocketAddress)) := do
  match ← e.poll with
  | some (.ok d) => return some d
  | some (.error err) => e.receiveFailed err; IO.sleep ms; return none
  | none =>
  (do
    let sleep ← Std.Async.Sleep.mk (Std.Time.Millisecond.Offset.ofNat ms.toNat)
    Std.Async.Selectable.one #[.case e.ready pure, .case sleep.selector pure]
    sleep.stop : Std.Async.Async Unit).block
  match ← e.poll with
  | some (.ok d) => return some d
  | some (.error err) => e.receiveFailed err; IO.sleep ms; return none
  | none => return none

/-- Takes up to `budget` datagrams that have arrived, without waiting. -/
def drain (e : Endpoint) : (budget : Nat) → IO Unit
  | 0 => pure ()
  | budget + 1 => do
    match ← e.poll with
    | some (.ok (bytes, from?)) => e.deliver bytes from?; e.drain budget
    | some (.error err) => e.receiveFailed err
    | none => pure ()

/-- Rounds `service` may take past one per millisecond of its timeout: a
round that delivers no datagram sleeps at least 1 ms, so `timeout` of those
use it up; one that a datagram ends early costs a round of these. Past them
`service` returns `none` before its time, which a caller servicing in a
loop cannot tell from a timeout. -/
def extraRounds : Nat := 64

/-- ENet's enet_host_service: the next event, waiting up to `timeout`
milliseconds for one while it moves datagrams and runs the timers. `none`
when the time is up with nothing to report; 0 checks once without waiting.
Call it regularly: nothing is sent or received in between. -/
def service (e : Endpoint) (timeout : UInt32 := 0) : IO (Option Event) := do
  if let some ev ← e.popEvent then return some ev
  let start ← e.now
  for _ in [0:timeout.toNat + extraRounds] do
    e.drain 256
    e.serviceHost
    if let some ev ← e.popEvent then return some ev
    let t ← e.now
    let elapsed := Time.difference t start
    if elapsed ≥ timeout then return none
    -- sleep until a datagram comes, the host's next timer, or the timeout
    let left := timeout - elapsed
    let wait := match (← e.state.get).host.nextDeadline with
      | some d => min left (if Time.less t d then Time.difference d t else 0)
      | none => left
    if let some (bytes, from?) ← e.receive (max wait 1) then e.deliver bytes from?
  return none

/-- Every event that turns up within `timeout` milliseconds (it keeps
servicing until then). Each round either reports an event or services until
the time is up, so there are at most as many rounds as events, bounded like
`service`'s. -/
def serviceFor (e : Endpoint) (timeout : UInt32) : IO (Array Event) := do
  let start ← e.now
  let mut acc := #[]
  for _ in [0:timeout.toNat + extraRounds] do
    let elapsed := Time.difference (← e.now) start
    if elapsed ≥ timeout then break
    match ← e.service (timeout - elapsed) with
    | some ev => acc := acc.push ev
    | none => break
  return acc

end Endpoint

end Lenet.Net
