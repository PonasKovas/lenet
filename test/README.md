# ENet compatibility tests

Lenet is tested against the real [ENet](https://github.com/lsalzman/enet)
C library, not against a spec. There are three parts:

1. **Recorder** (`c/harness.c`). Runs real ENet hosts (a server and up to
   two clients) in one process and routes their UDP traffic through logging
   proxy sockets. Each scripted scenario is saved as a readable trace in
   `traces/`: the API calls (with the peer they act on), ENet's events, and
   every datagram's bytes.
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
```

Each scenario prints one PASS/FAIL line (per role for the replay); the exit
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
- **Unsequenced drop cascade (enet bug - not copied).** When ENet's throttle
  drops a packet it also drops every directly following command with the
  same sequence numbers, meant for the rest of a fragment set. Unsequenced
  packets all carry (0, 0), so one dropped unsequenced packet takes every
  unsequenced packet queued right behind it along. Lenet drops only the
  packet the counter picked. Sender-side only, so invisible to interop.
- **Receive window gate on unreliable commands (documented, not mirrored).**
  ENet applies the same cyclic window gate to unreliable and
  unreliable-fragment commands (anything but SEND_UNSEQUENCED,
  `peer.c:869-883`). Lenet's `Channel.receiveUnreliable` accepts an
  unreliable command whenever its unreliable sequence number beats the
  channel's counter, ignoring the command's reliable sequence number.
  Classification: hostile-input hardening only - legitimate senders emit
  unreliable commands at (or within a window of) their current reliable
  sequence number, so the gate never fires for them; the structural
  difference (ENet queues out-of-order unreliable commands and dispatches
  them when the reliable frontier advances, Lenet delivers by unreliable
  sequence number alone) is interop-invisible in all recorded scenarios.
  Not fixed; revisit only if hostile-input coverage demands it.

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
