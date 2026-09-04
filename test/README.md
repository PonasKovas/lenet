# ENet compatibility tests

Verifies that Lenet interoperates with real [ENet](https://github.com/lsalzman/enet)
(1.3.x) by comparing it against the actual C library — not against a spec.

Two parts:

1. **Recorder** (`c/harness.c`) — runs two *real* ENet hosts (client + server)
   inside one process on localhost, with all UDP traffic routed through an
   in-process logging proxy. Records scripted scenarios into human-readable
   trace files: application calls, ENet events, and the raw datagram bytes on
   the wire.
2. **Replayer** (`Test/Replay.lean`, built as the `replay` lake exe) — feeds
   each trace into the Lenet sans-I/O core (`Host.handleDatagram` /
   `Host.service`) per role, at the recorded timestamps, applying the recorded
   API calls. Compares Lenet's emitted event stream and outgoing commands
   against ENet's.

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
```

Output is one PASS/FAIL line per scenario/role (client + server per scenario);
exit code 0 iff all pass. The recording step is only needed when scenarios
change — traces are committed and the replay is fully deterministic
(no sockets, no real time).

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

## What is compared

- **Events** (CONNECT / RECEIVE / DISCONNECT, payload bytes): must match exactly.
- **Outgoing commands** — Lenet's emitted datagrams are decoded and the merged
  command stream is compared against ENet's, as multisets of masked commands.
  Masked (non-deterministic): `connectId`, session IDs. Control-command order
  within one millisecond is a scheduling artifact and not compared; order-
  sensitive behavior is still verified by events and per-channel sequence
  numbers.
- **Sanity**: every datagram Lenet emits must decode with Lenet's own decoder
  and be ≤ 4096 bytes (ENet's receive buffer).

## Layout

- `c/harness.c` — recorder (scripted scenarios, proxy, logging)
- `Makefile`    — builds `c/harness` against `../enet` out-of-tree, `make traces` records all scenarios into `traces/`
- `traces/*.trace` — committed golden corpus (`A` = API call, `E` = event, `N` = network datagram)
- `../Test/Replay.lean` — the replayer (`lake build replay`)
