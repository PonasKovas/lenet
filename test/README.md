# ENet compatibility tests

Lenet is tested against the real [ENet](https://github.com/lsalzman/enet)
C library, not against a spec. There are three parts:

1. **Recorder** (`c/harness.c`). Runs real ENet hosts (a server and up to
   two clients) in one process and routes their UDP traffic through logging
   proxy sockets. Each scripted scenario is saved as a readable trace in
   `traces/`: the API calls (with the peer they act on), ENet's events, and
   every datagram's bytes. Every scenario is recorded three times: with
   ENet's clock starting at 0 (`<name>.trace`), and starting just before
   the 16-bit sent-time wrap at 65536 ms and just before the 32-bit clock
   wrap (`<name>@<start>.trace`, whose `O <start>` line gives the clock
   start; trace times stay relative to it). The traces are only a few
   seconds long, so without the shifted clocks they never reach either wrap.
   On a shifted clock ENet really does behave differently. For example, a
   client pings right after connecting, because `lastReceiveTime = 0`
   stands for "nothing received yet".
2. **Replayer** (`Replay.lean`, the `replay` executable). Feeds each trace
   into Lenet's `Host`, once per role, at the recorded times, applying the
   recorded API calls, and compares Lenet's events and outgoing commands
   with ENet's. Time advances by Lenet's own timer deadlines
   (`Host.nextDeadline`) between trace lines, so retransmits, pings and
   timeouts fire where Lenet's clock says, regardless of how the recording's
   pump happened to line up.
3. **Live interop** (`c/interop.c`). A real ENet host and a Lenet host talk
   over real UDP sockets in one process, in both directions and every
   delivery mode. Lenet is used only through the public C API. ENet's
   decoder is the strictest check of Lenet's encoder, and the other way
   round.

ENet is built out of tree from a checkout at `../enet` (next to this
repository); the checkout is never modified. CI clones it at the pinned
revision the traces were recorded with (`5a9c537`, v1.3.18-17).

## Usage

```sh
# replay every trace (no ENet needed: traces are committed)
lake build replay
./.lake/build/bin/replay test/traces

# one scenario, with a full command-stream dump on failure
LENET_DEBUG=1 ./.lake/build/bin/replay test/traces frag

# live interop
make -C test interop           # builds everything, runs all scenarios
./test/c/interop connect       # one scenario

# re-record the traces (only when scenarios change; not byte-reproducible,
# since recording uses the real clock and ENet's randomness)
make -C test traces
./test/c/harness record idle 65203   # one scenario, ENet's clock starting at 65203 ms
```

Each scenario prints one PASS/FAIL line (per role for the replay, one line
per shifted clock); the exit
code is 0 only if all pass. The replay is fully deterministic: no sockets,
no real time.

## What is compared

- **Events** (connect, receive, disconnect, with payload bytes) must match
  exactly, in order.
- **Outgoing commands.** Lenet's datagrams are decoded and the resulting
  command stream is compared with ENet's as a multiset. The order of
  independent control commands within one millisecond depends on how the two
  hosts' service calls interleave and is not compared; ordering that matters
  is still checked through the events and the per-channel sequence numbers.
  One field is masked: `connectID`, which ENet draws at random. The replay
  instead pins each Lenet connection to the connectID the recorded client
  used, since the other side echoes it and checksums with it.
- **Multi-peer scenarios.** The server's expected stream is the union of what
  it sent to both clients, and `SEND`/`DISCONNECT` lines name the peer they
  act on, so the replay targets the same peer.
- **Checksums** (`checksum` scenario). Recorded datagrams are only accepted
  if their CRC32 verifies, and Lenet's own must verify on the other side, so
  a wrong CRC drops datagrams and fails the scenario. Quirk: `connectID` is
  the one field ENet passes through without byte-order conversion, which is
  why the checksum placeholder uses its big-endian form.
- **Sanity.** Every datagram Lenet sends must decode with Lenet's decoder
  and be at most 4096 bytes (ENet's receive buffer).
- **Resource bounds** (see DESIGN.md) are checked after every service step.

## Scenarios

| name           | exercises                                                        |
|----------------|------------------------------------------------------------------|
| `connect`      | handshake both roles, CONNECT/VERIFY_CONNECT/ACK sequence        |
| `send_c2s`     | reliable + unreliable + unsequenced sends, near-MTU packet       |
| `send_s2c`     | same, server → client                                            |
| `frag`         | 40 KB reliable packet split into MTU-bounded fragments           |
| `fragthen`     | fragmentation span dispatch: more reliable/unreliable traffic queued behind and sent after a full fragment set, plus a second set - a span-naive dispatch frontier (advance-by-1 per set) deadlocks the channel and loses the follow-up traffic (regression for the fixed fragmentation frontier bug, see divergence triage) |
| `disc_client`  | client-initiated graceful disconnect                             |
| `disc_server`  | server-initiated graceful disconnect                             |
| `idle`         | keepalive: ping/ACK duty with no traffic                         |
| `timeout`      | unacked reliable command → retransmit backoff → peer timeout     |
| `checksum`     | CRC32 checksums enabled on both C hosts (`enet_crc32`): lenet must compute and verify checksums byte-compatibly (the replay drops datagrams whose checksum it cannot verify) |
| `bandwidth`    | hosts created with nonzero in/out bandwidth (1MB/512KB): BANDWIDTH_LIMIT commands + ENet's iterative per-peer share algorithm, bandwidth-derived windowSize negotiation in CONNECT/VERIFY_CONNECT |
| `unfrag`       | 8000-byte unreliable-fragmented packet (`ENET_PACKET_FLAG_UNRELIABLE_FRAGMENT`) split into SEND_UNRELIABLE_FRAGMENT commands |
| `disclater`    | `enet_peer_disconnect_later` while reliable commands are in flight: deferred DISCONNECT once queues drain |
| `multip`       | two clients → one server (second proxy), server broadcast + unicast to a specific peer; exercises the peer-address check in the receive path |
| `inject`       | hand-crafted hostile datagrams spliced into the C2S path (INJECT action) against the live server: pins ENet's receive-path validation gates (see below) |
| `multichannel` | 8 channels: per-channel sequencing, sends across channels 0-7 both directions |
| `dup`          | DUP action re-sends captured datagrams: duplicate reliable command (idempotent, double ACK) + duplicate unsequenced (deduplicated) |
| `reconnect`    | disconnect → reconnect: slot reuse, fresh sequence counters, session-ID carry-over on the reused slot (ENet's reset keeps sessions) |
| `retimeout`    | client-side timeout: server stops responding → retransmit backoff → client timeout event |
| `mtu576`       | hosts at minimum MTU: 40000-byte fragmented send at MTU 576 (~73 fragments) |
| `throttleconf` | `enet_peer_throttle_configure` both directions (THROTTLE_CONFIGURE commands) |

## Hostile-input probes (`inject` scenario)

The `INJECT` action splices raw datagram bytes into the client→server proxy
path (logged as direction `X2S`: they target the server only and are never
attributed to the client role). Each probe pins one gate of ENet's receive
path (protocol.c); the replay verifies lenet behaves identically:

| probe                          | pins                                                          |
|--------------------------------|---------------------------------------------------------------|
| valid header, zero commands    | empty command loop is legal, no response                       |
| unknown command number first   | malformed first command → nothing applied, no response         |
| valid PING + unknown command   | **per-command processing**: prefix applied (ping ACKed), malformed tail dropped |
| truncated command body         | break, nothing applied                                         |
| PING with wrong header session | dropped by the peer-lookup session check                       |
| compressed flag                | dropped (compression is not supported)                         |
| CONNECT `channelCount = 0`     | rejected outright (must be in [1, 255])                        |
| CONNECT `mtu = 0`              | accepted, MTU clamped to 576 in the advertised VERIFY_CONNECT  |
| PING to a zombie peer          | dropped by the peer-lookup state check                         |

These are differential probes with ENet as the oracle, not fuzzing: the
interesting inputs (ENet's validation gates) are few and can be listed from
protocol.c, and the proofs cover the rest (see DESIGN.md, "No fuzzer").

## Divergence triage

Behavioral differences from ENet, found by the tests or by reading both
code bases, with their classification (DESIGN.md, "Correctness over
compatibility"). Open, undecided differences are listed in TODO.md.

- **Lenet bugs fixed in the 2026-09 review** (none visible to the corpus,
  whose clocks start at 0, whose traces are short and loss-free):
  retransmitted commands stayed counted as in transit, so every
  retransmission shrank the congestion window for good; the sender never
  occupied its reliable windows (`canSendReliable` always passed); RTT
  samples mixed the 32-bit clock with the 16-bit echoed sent time, so they
  were off by 65.5 s multiples once the clock passed 65535 ms; a client
  accepted any VERIFY_CONNECT and took the server's MTU unclamped; a reused
  peer slot kept the previous connection's bandwidths, window, throttle
  and timeout settings; each throttle epoch's lowest RTT was never reset.
  All now follow ENet (`protocol.c` check_timeouts,
  check_outgoing_commands, handle_acknowledge, handle_verify_connect,
  `peer.c` enet_peer_reset).

- **Fragment-set dispatch span (lenet bug - fixed).** ENet treats a fragment
  set as one incoming reliable command spanning `fragmentCount` sequence
  numbers; dispatching the reassembled packet advances the receive frontier
  by the whole span (`peer.c dispatch_incoming_reliable_commands`:
  `incomingReliableSequenceNumber += fragmentCount - 1`). Lenet dispatched
  every reliable delivery as one sequence number wide, so after the first
  fragmented delivery the frontier no longer lined up with later commands -
  they were classified duplicates/out-of-order and staged forever: the
  channel silently stopped receiving everything after the first fragment
  set. Found by the benchmark's fragmented batches (the old `frag`
  scenario sends nothing after the set, which is why the corpus missed it).
  Fixed: staged deliveries are now `StagedReliable {seq, span, packet}`,
  delivery goes through `Channel.receiveReliableSpan` (plain packets span 1,
  reassembled sets span `fragmentCount`), and the drain advances the
  frontier by each staged entry's span. Also added ENet's reliable-fragment
  receive gate (`Peer.fragmentGateOk`: cyclic receive-window plus
  frontier-duplicate check on the set's start sequence, `protocol.c
  handle_send_fragment` + `peer.c queue_incoming_command`) - Lenet used to
  assemble stale and duplicate fragment sets that ENet discards. Pinned by
  the `fragthen` golden scenario; the span arithmetic is pinned by proofs
  (`Lenet/Proofs/Channel.lean`).
- **Receive window gate on reliable commands (lenet bug - fixed).** ENet
  discards reliable commands outside the cyclic receive window
  (`peer.c:877-883`, `enet_peer_queue_incoming_command`) before any
  staleness/ordering logic. Lenet had ported the window test
  (`Channel.isIncomingReliableInWindow`) but never applied it, and used a
  wrap-naive staleness test (`seq <= incoming`) instead. Two consequences,
  both invisible to the golden corpus (which would need ~65k commands per
  channel to reach): (a) at `incomingReliableSequenceNumber = 0xFFFF` the
  legitimately next command `0x0000` was dropped forever - the channel
  deadlocks at the 16-bit wrap, where ENet delivers (the window test is
  cyclic and `incoming + 1` wraps to `0x0000`); (b) far-future sequence
  numbers were staged without bound, where ENet discards beyond
  `currentWindow + FREE_RELIABLE_WINDOWS - 1` windows. Fixed in
  `Channel.receiveReliable`: out-of-window commands are discarded, the
  frontier duplicate (`seq == incoming`) is dropped, and delivery/staging
  happen exactly as before for in-window traffic. The wrap boundary is now
  pinned by proofs (`Lenet/Proofs/Channel.lean`), since golden traces cannot
  reach it.
- **Throttle drops of unreliable packets (lenet bug - fixed).** ENet drops
  unreliable, unsequenced and unreliable-fragment packets on send in
  proportion to the packet throttle (`protocol.c` check_outgoing_commands,
  `packetThrottleCounter`); Lenet sent them all and only applied the
  throttle to the reliable congestion window. Now `PackState.packUnreliable`
  follows ENet: the counter steps by 7 modulo 32 per packet and a packet
  whose step lands above the throttle is dropped, all its fragments with it.
  Invisible to the corpus: its throttle stays at the full 32, where nothing
  is dropped.
- **Outgoing bandwidth throttle input (lenet bug - fixed).** ENet sets each
  peer's throttle limit from the bytes queued for it during the epoch
  (`outgoingDataTotal`, counted in setup_outgoing_command and
  queue_acknowledgement) and first limits peers that exceed their own
  incoming bandwidth (`host.c` enet_host_bandwidth_throttle). Lenet split
  the host bandwidth evenly and compared it with the reliable bytes in
  flight. `Host.outgoingThrottleLimits` now ports ENet's loop. Invisible to
  the corpus: no trace queues data across a throttle epoch.
- **Bandwidth throttle overflow (enet bug - not copied).** ENet computes
  `bandwidth * elapsedTime` in 32 bits, which wraps once a bandwidth passes
  about 4.3 MB/s, and subtracts a limited peer's bandwidth from a host
  budget that can be smaller, which wraps to a near-unlimited budget. Lenet
  computes on `Nat`: no wrap, and an exhausted budget stays exhausted. Only
  the sender's own throttle changes, so interop does not see it.
- **Unsequenced drop cascade (enet bug - not copied).** When ENet's throttle
  drops a packet it also drops every directly following command with the
  same sequence numbers, meant for the rest of a fragment set. Unsequenced
  packets all carry (0, 0), so one dropped unsequenced packet takes every
  unsequenced packet queued right behind it along. Lenet drops only the
  packet the counter picked. Sender-side only, so invisible to interop.
- **Disconnect events for peers never reported (lenet bug - fixed).** ENet
  reports a disconnect only for a peer the application saw connect, or for
  a client whose connection attempt failed. A server peer still in its
  handshake (VERIFY_CONNECT sent, not yet acknowledged) that times out or
  receives a DISCONNECT is reset silently (`protocol.c`
  enet_protocol_notify_disconnect, handle_disconnect). Lenet reported both,
  so a server application got disconnect events for connections it never
  heard of. `Host.checkPeerTimeouts` and `Peer.handleDisconnect` now reset
  such a peer without an event.
- **ACK of a command queued for resend (lenet bug - fixed).** A timed-out
  command goes back into the queue; when a late ACK of its first send
  arrives before the resend goes out, ENet's remove_sent_reliable_command
  finds it there (among the reliable commands up to the first one never
  sent), drops it and frees its window slot. Lenet searched only the
  in-flight list, so it sent the command again and kept its window slot
  until that resend was acknowledged. `Peer.removeSentReliableCommand`
  now looks in the queue too.
- **Data while disconnecting later (lenet bug - fixed).** ENet's
  enet_peer_queue_incoming_command discards everything for a peer in
  DISCONNECT_LATER: data is acknowledged but never delivered, an
  unsequenced packet still marks its group, and a fragment that would start
  a set is refused (discarded with a fragment count: notifyError), while a
  set already under way still completes. Lenet delivered it all.
  `Peer.applyCommand` now drains as ENet does.
- **Disconnects during service skip the bandwidth recalculation (lenet
  bug - fixed).** ENet sets `recalculateBandwidthLimits` for every
  disconnect it reports but a timeout of a client still connecting
  (notify_disconnect, the ZOMBIE dispatch), so the next throttle epoch
  sends the remaining peers their new BANDWIDTH_LIMIT. Lenet set it only
  for events from a received datagram, missing timeouts and the remote
  DISCONNECT that completes once its ACK is out. `Host.service` now sets
  it too.
- **Fragment validation (lenet bug - fixed, hostile input).** ENet refuses
  an empty fragment and one whose total length or fragment count differs
  from the set under way (no ACK, the rest of the datagram dropped). Lenet
  took both: an empty fragment could complete a set, and a mismatched one
  was copied into it. `Peer.handleFragment` now refuses them. Still
  different, and only for hostile input: ENet also refuses a fragment whose
  start sequence number is the dispatch frontier or a staged plain packet,
  where Lenet acknowledges and ignores it (it keeps no record of whether a
  staged entry was a fragment set).
- **Header bytes (lenet bug - fixed).** ENet sets the SENT_TIME flag and
  writes the 2-byte sent time only when the datagram carries a command
  that asks for an ACK, and adds the session bits only once the remote
  peer ID is known. Lenet always wrote both, so datagrams with only ACKs or
  unreliable data were 2 bytes longer and a fresh client's CONNECT carried
  session bits. Harmless to ENet, but not its bytes; the replay compares
  decoded commands, so it never saw this. `Host.encodeDatagram` now writes
  what ENet writes.
- **No maximum packet size on send (lenet bug - fixed).** ENet's
  enet_peer_send refuses packets over `host->maximumPacketSize` (32 MB by
  default). Lenet only capped the fragment count, which allows about
  1.4 GB. `Peer.sendError?` now refuses packets over 32 MB
  (`packetTooLarge`). A Lenet receiver still assembles at most 4 MB (a
  resource cap, DESIGN.md), so a larger reliable packet sent to Lenet is
  never acknowledged.
- **Client's connect event data (lenet bug - fixed).** ENet's client
  reports its connect event with data 0: enet_host_connect puts the data in
  the CONNECT and leaves the peer's eventData at its reset value. Lenet
  reported the client's own data. The live `connect` scenario pinned the
  old value; it now expects 0, as from ENet.
- **Channel count of a connect (lenet bug - fixed).** ENet's
  enet_host_connect clamps the channel count to [1, 255]; the host's
  channel limit only caps incoming CONNECTs. Lenet also capped its own
  connects at the limit, so a host created with channel limit 1 could not
  open more than one channel to a server that allowed them.
- **Client's throttle parameters (lenet bug - fixed).** ENet's
  handle_connect takes over the packet-throttle interval, acceleration and
  deceleration a CONNECT carries and echoes them in the VERIFY_CONNECT,
  which the client checks. Lenet echoed the server slot's own values, so a
  client with other throttle parameters refused the VERIFY_CONNECT, and the
  server throttled with the wrong ones. `Host.handleIncomingConnect` now
  takes them over.
- **Retransmitted CONNECT (lenet bug - fixed).** ENet's handle_connect
  ignores a CONNECT when a peer that is not a client still connecting
  already has its address, port and connect ID: the client resent it
  because the VERIFY_CONNECT was late or lost. Lenet took a second slot and
  sent a second VERIFY_CONNECT with another peer ID; the slot the client
  did not pick retransmitted until it timed out, and a burst of them could
  fill a server. `Host.handleIncomingConnect` now ignores the duplicate.
- **Zero timeout parameters (lenet bug - fixed).** ENet's
  enet_peer_timeout replaces each 0 by its default (32, 5000, 30000 ms).
  Lenet stored the 0, so the common call `timeout(peer, 0, 0, 5000)` made
  the peer disconnect at the first missed retransmit. `Host.setPeerTimeout`
  now does what ENet does.
- **No keepalive while unreliable data is queued (lenet bug - fixed).**
  ENet's send_outgoing_commands adds a PING once a pass packed no reliable
  command, nothing reliable is in flight and the peer has been idle for
  its ping interval; queued unreliable data does not stop it. Lenet pinged
  only with an empty queue, so a peer streaming unreliable data never
  pinged: its RTT and throttle went stale, and a dead remote was never
  timed out. `Host.pingEligible` now follows ENet (ENet also needs room
  for the PING in the datagram; Lenet sends it in the next one).
- **Unreliable sequence numbers used up (lenet bug - fixed).** Once a
  channel's unreliable sequence number reaches 0xFFFF, ENet's
  enet_peer_send sends the next unreliable packet reliably (and an
  unreliable fragment set as reliable fragments), which starts the
  unreliable numbering again. Lenet wrapped the number to 0, so the
  receiver dropped that packet and every later one as older than the last
  it delivered: a channel that only streams unreliable data went silent
  after 65535 packets (18 minutes at 60 Hz). `Peer.packetCommand` and
  `Peer.fragmentCommands` now fall back to reliable as ENet does.
- **Refused commands (lenet bug - fixed).** ENet's handlers refuse some
  commands (they return -1, `goto commandError` in
  handle_incoming_commands): data, PING, BANDWIDTH_LIMIT and
  THROTTLE_CONFIGURE for a peer that is not connected, data for a missing
  channel, a CONNECT for an existing peer, an ACK for anything but the
  VERIFY_CONNECT or DISCONNECT a handshake or disconnect waits for, a
  VERIFY_CONNECT that does not answer the CONNECT, and a fragment that
  does not fit its set. A refused command is not acknowledged, and ENet
  drops the rest of its datagram. Otherwise ENet decides the ACK from the
  peer's state after the command: none while disconnecting, still
  handshaking as the server, or gone, and only the DISCONNECT while
  acknowledging one. Lenet acknowledged every command up front, applied
  BANDWIDTH_LIMIT and THROTTLE_CONFIGURE in any state, and always read the
  whole datagram. So a disconnecting peer acknowledged data it threw away,
  and a stray ACK ahead of the DISCONNECT's ACK in one datagram did not
  delay the disconnect as it does in ENet. `Peer.applyCommand` now says
  which commands ENet accepts, `Peer.handleCommand` queues the ACK after
  it (`Peer.acksIn`), and `Host.readCommand` stops at a refused command.
- **Remote DISCONNECT keeps the queues (lenet bug - fixed).** On a
  DISCONNECT from the remote, ENet drops everything queued, in flight or
  waiting for delivery (enet_peer_reset_queues) before it queues the ACK.
  Lenet kept the queue, so packets queued before the DISCONNECT still went
  out. `Peer.resetQueues` does what ENet does, for this and for the local
  disconnect (which also left the channels' window counts behind).
- **Reliable packets overtaking a held one (lenet bug - fixed).** ENet
  queues reliable data commands in their own list
  (`outgoingSendReliableCommands`), and once one of them is held back, by
  its sequence window or by congestion, check_outgoing_commands stops
  reading that list for the pass. So no reliable packet goes out before an
  earlier one, on any channel. Lenet only held back the one command: behind
  a large packet that did not fit the congestion window, smaller reliable
  packets still went out. That breaks the order the window accounting
  relies on, and the large packet can starve while the ones behind it fill
  the window. `PackState.reliableHeld` now holds back every later reliable
  data command, as ENet does. Control commands and unreliable packets still
  go, in ENet too. The corpus never congests a sender that far.
- **Empty reliable packets and congestion (lenet bug - fixed).** ENet runs
  its congestion check on every command with a packet, empty or not. Lenet
  skipped it when the payload was empty, so while more bytes were in flight
  than the window allows (after the throttle falls on an RTT spike) an empty
  reliable packet went out where ENet holds it back.
- **More than 4095 peer slots (lenet bug - fixed).** ENet's
  enet_host_create refuses more than ENET_PROTOCOL_MAXIMUM_PEER_ID (4095)
  peers. Lenet took any count: slot 4095 then carried peer ID 0xFFF, the ID
  CONNECTs are addressed to, so no datagram could reach it, and past 65536
  slots the 16-bit peer IDs repeated, so two slots shared their events.
  `Host.create` now caps the count at 4095 and `lenet_host_create` returns
  NULL above it, as ENet does. A host-level event proof needs slot `i`
  to hold peer ID `i`, which this makes true.
- **Local disconnect (lenet bug - fixed).** ENet's enet_peer_disconnect
  does nothing for a peer already disconnecting, disconnected or a zombie;
  otherwise it drops everything queued or in flight (enet_peer_reset_queues)
  before queuing the DISCONNECT, and a peer still handshaking gets one
  unacknowledged DISCONNECT and is reset at once, without an event. Lenet
  queued a DISCONNECT in every case: a second call sent a second one, a
  call on a free slot sent one to an empty address, queued data still went
  out ahead of it, and a handshaking peer waited for an ACK that never
  comes, then reported a disconnect. `Peer.queueDisconnect` now follows
  ENet; the handshaking peer waits as `zombie` until the next service sends
  its DISCONNECT (there is no socket to flush to). The corpus only ever
  disconnects connected peers with nothing queued.
- **Unsequenced window (enet quirk - not copied).** ENet deduplicates
  unsequenced packets in aligned blocks of 1024 groups
  (`protocol.c` handle_send_unsequenced): a group in a newer block moves
  the block there and forgets the old bitmap, and every group below the
  current block is dropped, seen or not. So when 1024 overtakes 1023,
  ENet delivers 1024 and drops 1023. Lenet slides the window behind the
  highest group (`UnsequencedWindow.checkAndAdd`) and delivers any unseen
  group less than 1024 behind it. Both drop every duplicate; Lenet only
  delivers some reordered packets ENet loses. Invisible to the corpus,
  which never reorders; pinned by `test/Unit.lean`.
- **Receive window gate on unreliable commands (lenet bug - fixed).** ENet
  gates unreliable and unreliable-fragment commands by the reliable sequence
  number they were sent after (`peer.c` queue_incoming_command,
  `protocol.c` handle_send_unreliable_fragment): out of the receive window
  is dropped, ahead of the dispatch frontier waits until the frontier gets
  there (dispatch_incoming_unreliable_commands). Lenet ignored that number
  and compared unreliable sequence numbers only, so with loss or reordering
  it delivered a packet from before the last reliable one after newer ones,
  and let one sent after a still-missing reliable command overtake it. Now
  `Channel.receiveUnreliable` gates and stages like ENet, the stage capped at
  `maximumStagedUnreliable` (1024) per channel, and `Peer.fragmentGateOk`
  applies ENet's gate before unreliable fragments are reassembled.
  Invisible to the loss-free corpus. One ordering case stays stricter than
  ENet on purpose: ENet delivers an unreliable fragment set that completes
  after newer packets went out, and moves the channel's unreliable counter
  back; Lenet drops it.

- **Fragment assembler lifetime (lenet bug - fixed).** ENet keeps a
  fragment set's reassembly state in the channel's incoming queues: keyed
  by the channel and, for unreliable sets, by the reliable command they
  were sent after; kept until the set is dispatched, so a retransmitted
  fragment of a complete set finds it and is ignored; and discarded with
  the unreliable queue once the frontier passes it. Lenet keyed its
  assemblers by the start sequence number alone, so sets on different
  channels (or a reliable and an unreliable one) could share one; a
  retransmitted fragment of a complete but still staged reliable set opened
  a new assembler that never completed; and an unreliable set that lost a
  fragment held its assembler forever. After 32 such leftovers every new
  set was refused, reliable fragments included, and those had already been
  acknowledged: silent loss of reliable data. Now assemblers carry their
  `FragmentOrigin`, one check (`Peer.fragmentSetLive`) gates fragments and
  prunes dead assemblers after each delivery, a full cap evicts the oldest
  unreliable assembler, and a reliable fragment that still finds no room is
  not acknowledged, so the sender retransmits it (ENet skips the ACK of a
  command it failed to handle). Found by the benchmark's lossy link, where
  a reliable 4096 B run delivered 153 of 512 packets.

- **Reliable packets staged inside a span (lenet bug - fixed).** A
  reassembled reliable set moves the dispatch frontier over its whole span.
  A hostile sender can first send a plain reliable packet numbered inside
  that span; it stages, the set jumps over it, and nothing drains it again.
  Repeated, this grows the stage past the seven-window bound the replay
  asserted. ENet keeps such a packet at the head of its
  sorted queue, where it stalls dispatch until the numbers wrap. An
  in-order delivery now drops the staged packets that are no longer ahead
  of the new frontier (`Channel.receiveReliableSpan`), which makes the
  bound a theorem (`Proofs.stagedReliableInv_size`). Found while trying to
  prove that bound.

- **Address check before negotiation (lenet bug - fixed).** ENet drops a
  datagram for a peer unless it comes from the peer's address (or the peer
  was connected to the broadcast address), whether or not the remote peer ID
  is known yet, and then records the sender as the peer's address
  (`protocol.c` handle_incoming_commands). Lenet only checked the address
  once the remote peer ID was known, so a connecting client took datagrams
  from anyone, and a client connected to the broadcast address never learned
  the server's real one. `Host.acceptsDatagram` and `handleDatagram` now
  follow ENet.

## Live interop scenarios

| name           | direction            | exercises                                            |
|----------------|----------------------|------------------------------------------------------|
| `connect`      | lenet → C            | handshake (with user data), one reliable packet each way |
| `connect_r`    | C → lenet            | reverse handshake, session ID negotiation            |
| `send`         | both                 | reliable / unreliable / unsequenced, byte-exact      |
| `frag`         | both                 | 40000-byte reliable fragmented send, byte-exact      |
| `disconnect`   | lenet initiates      | graceful disconnect + ack dance, data passthrough    |
| `disconnect_r` | C initiates          | reverse graceful disconnect                          |
| `timeout`      | lenet goes silent    | ENet retransmit backoff → timeout                     |
| `checksum`     | both                 | CRC32 checksums on (`enet_crc32` ↔ lenet checksum), byte-exact |
| `bandwidth`    | both                 | hosts created with 1MB/500KB bandwidths: windowSize negotiation, throttled window |
| `disclater`    | lenet initiates      | packets queued + `disconnect_later` without pumping: flush-then-disconnect |
| `multip`       | two C clients → lenet| address-based peer demux, broadcast to both peers, unicast |
| `unfrag`       | both                 | 8000-byte unreliable-fragmented send, byte-exact     |
