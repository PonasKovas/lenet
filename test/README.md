# ENet compatibility tests

Verifies that Lenet interoperates with real [ENet](https://github.com/lsalzman/enet)
(1.3.x) by comparing it against the actual C library — not against a spec.

Two parts:

1. **Recorder** (`c/harness.c`) — runs *real* ENet hosts (up to two clients +
   one server) inside one process, with all UDP traffic routed through
   in-process logging proxy sockets. Records scripted scenarios into
   human-readable trace files: application calls (with the acting peer for
   sends/disconnects), ENet events, and the raw datagram bytes on the wire.
2. **Replayer** (`Replay.lean`, built as the `replay` lake exe) — feeds
   each trace into the Lenet sans-I/O core (`Host.handleDatagram` /
   `Host.service`) per role, at the recorded timestamps, applying the recorded
   API calls. Compares Lenet's emitted event stream and outgoing commands
   against ENet's.
3. **Live interop** (`c/interop.c`) — a real ENet host and a Lenet host
   (via the Lean FFI) talk over actual UDP sockets in one process, in both
   directions, across every delivery mode. This is the strongest check:
   ENet's decoder is the strictest validator of Lenet's encoder, and vice
   versa.

Real ENet sources are built out-of-tree; the ENet checkout is never modified.

## Usage

```sh
# record golden traces from real ENet (requires gcc; see test/Makefile)
make -C test traces

# replay every trace through Lenet and diff against ENet's behavior
lake build replay
./.lake/build/bin/replay test/traces

# single scenario, with a full command-stream diff on failure
LENET_DEBUG=1 ./.lake/build/bin/replay test/traces frag

# live interop: Lenet (Lean FFI) <-> real ENet over real UDP
lake build Lenet:static
make -C test c/interop
make -C test interop        # runs all 7 scenarios
./test/c/interop connect    # single scenario
```

Output is one PASS/FAIL line per scenario/role (client + server per scenario
for replay; one line per scenario for interop); exit code 0 iff all pass.
The recording step is only needed when scenarios change — traces are committed
and the replay is fully deterministic (no sockets, no real time).

## Scenarios

| name           | exercises                                                        |
|----------------|------------------------------------------------------------------|
| `connect`      | handshake both roles, CONNECT/VERIFY_CONNECT/ACK sequence        |
| `send_c2s`     | reliable + unreliable + unsequenced sends, near-MTU packet       |
| `send_s2c`     | same, server → client                                            |
| `frag`         | 40 KB reliable packet split into MTU-bounded fragments           |
| `disc_client`  | client-initiated graceful disconnect                             |
| `disc_server`  | server-initiated graceful disconnect                             |
| `idle`         | keepalive: ping/ACK duty with no traffic                         |
| `timeout`      | unacked reliable command → retransmit backoff → peer timeout     |
| `checksum`     | CRC32 checksums enabled on both C hosts (`enet_crc32`): lenet must compute and verify checksums byte-compatibly (the replay drops datagrams whose checksum it cannot verify) |
| `bandwidth`    | hosts created with nonzero in/out bandwidth (1MB/512KB): BANDWIDTH_LIMIT commands + ENet's iterative per-peer share algorithm, bandwidth-derived windowSize negotiation in CONNECT/VERIFY_CONNECT |
| `unfrag`       | 8000-byte unreliable-fragmented packet (`ENET_PACKET_FLAG_UNRELIABLE_FRAGMENT`) split into SEND_UNRELIABLE_FRAGMENT commands |
| `disclater`    | `enet_peer_disconnect_later` while reliable commands are in flight: deferred DISCONNECT once queues drain |
| `multip`       | two clients → one server (second proxy), server broadcast + unicast to a specific peer; exercises the peer-address check in the receive path |

## What is compared

- **Events** (CONNECT / RECEIVE / DISCONNECT, payload bytes): must match exactly.
- **Outgoing commands** — Lenet's emitted datagrams are decoded and the merged
  command stream is compared against ENet's, as multisets of masked commands.
  Masked (non-deterministic): `connectId` (drawn from ENet randomness at
  record time; the replay pins the peer's checksum key to the recorded value
  right after connecting). Control-command order within one millisecond is a
  scheduling artifact and not compared; order-sensitive behavior is still
  verified by events and per-channel sequence numbers.
- **Server commands in multi-peer scenarios** are compared per direction: the
  server's expected stream is the union of its S2C and S2D datagrams, and
  `SEND`/`DISCONNECT` lines record the acting peer index so the replay
  targets the same peer.
- **Checksums** (checksum scenario): datagrams recorded from ENet are only
  accepted by lenet if their CRC32 verifies against the peer's `connectID`,
  and lenet's own checksummed datagrams must decode (via the recorded peers'
  behavior) — an incorrect CRC32 computation drops datagrams and fails the
  scenario. Note ENet's quirk: `connectID` is the one command field passed
  through the body without byte-order conversion, which is why the checksum
  substitution uses the connectID's big-endian serialization.
- **Sanity**: every datagram Lenet emits must decode with Lenet's own decoder
  and be ≤ 4096 bytes (ENet's receive buffer).

## Live interop scenarios

| name           | direction            | exercises                                            |
|----------------|----------------------|------------------------------------------------------|
| `connect`      | lenet → C            | handshake (with user data), one reliable packet each way |
| `connect_r`    | C → lenet            | reverse handshake, session ID negotiation            |
| `send`         | both                 | reliable / unreliable / unsequenced, byte-exact      |
| `frag`         | both                 | 40000-byte reliable fragmented send, byte-exact      |
| `disconnect`   | lenet initiates      | graceful disconnect + ack dance, data passthrough    |
| `disconnect_r` | C initiates          | reverse graceful disconnect                          |
| `timeout`      | —                    | lenet goes silent → ENet retransmit backoff → timeout |

These exercise the FFI boundary too: `include/lenet.h` is implemented by
`c/interop.c` as a shim over the raw `lenet_ffi_*` Lean exports.

## Layout

- `c/harness.c` — recorder (scripted scenarios, proxy, wire logging)
- `c/interop.c` — live interop runner (Lenet FFI vs real ENet over UDP)
- `Makefile`    — builds both binaries against `../../enet` out-of-tree; `make traces` records traces, `make interop` runs all 7 scenarios
- `traces/*.trace` — committed golden corpus (`A` = API call, `E` = event, `N` = network datagram)
- `Replay.lean` — the replayer (`lake build replay`)
