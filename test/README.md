# Tests

Besides the unit tests (`Unit.lean`) and `Lenet.Net` over loopback
(`Net.lean`), Lenet is tested against the real
[ENet](https://github.com/lsalzman/enet) C library in four ways:

1. **Trace replay** (`c/harness.c`, `Replay.lean`). The harness runs real
   ENet hosts in one process, routes their traffic through logging
   proxies, and saves each scripted scenario as a trace in `traces/`: the
   API calls, ENet's events and every datagram. Each scenario is recorded
   with ENet's clock starting at 0, just before the 16-bit sent-time wrap
   and just before the 32-bit clock wrap. The replayer feeds each trace to
   Lenet, once per role, and compares Lenet's events and outgoing commands
   with ENet's. No sockets and no real time, so it is deterministic.
2. **Live interop** (`c/interop.c`). An ENet host and a Lenet host (through
   the C API) talk over real UDP sockets in one process.
3. **`Lenet.Net` against ENet** (`NetInterop.lean`, `c/echo.c`). The Lean
   API in one process and ENet in another, both ways round: one side sends
   reliable (many fragmented) and unsequenced packets, the other echoes
   them back.
4. **Over a lossy link** (`NetStream.lean`, `c/stream.c`, `c/proxy.c`). As
   3, but through a UDP proxy that drops, duplicates, delays and reorders
   datagrams from a seed. Both ends send a mixed stream on three channels
   and check what arrives: reliable packets once each and in order,
   unreliable ones at most once and in order, nothing corrupt, nothing left
   unacknowledged, and a clean disconnect at the end.

The ENet tests build ENet from a checkout at `../enet` (next to this
repository) at `5a9c537` (v1.3.18-17), the revision the traces were
recorded with. The checkout is never modified.

## Running

```sh
./.lake/build/bin/replay test/traces              # every trace (no ENet needed)
LENET_DEBUG=1 ./.lake/build/bin/replay test/traces frag   # one, with a dump on failure

make -C test interop          # live interop, every scenario
./test/c/interop connect      # one scenario
make -C test net-interop      # Lenet.Net against ENet
make -C test lossy-interop    # the same through the lossy proxy
make -C test lossy-interop ROUNDS=1000 PER=4 SEEDS="1 2 3 4 5"   # longer
make -C test lossy-wrap       # every 16-bit counter wraps (long)
make -C test lossy-clock      # both clocks cross 2^32 (long)
make -C test lossy-enet       # ENet against ENet through the proxy

make -C test traces           # re-record every trace
```

Each scenario prints a PASS or FAIL line, and the exit code is 0 only if
all pass. Recording is not byte-reproducible (it uses the real clock and
ENet's randomness), so re-record only when scenarios change.

## What the replay compares

- **Events** (connect, receive, disconnect, with their data) must match
  exactly and in order.
- **Outgoing commands**, decoded from Lenet's datagrams, must match ENet's
  as a multiset: every field, with its datagram's peer ID, session and
  flags. Payloads up to 64 bytes are compared byte for byte, larger ones by
  size and CRC-32. When a retransmit or ping fires and which commands share
  a datagram depend on how the two hosts' service calls interleave, so
  order is checked through the events and sequence numbers instead.
- **Masked:** only `connectID`, which ENet draws at random. The replay
  gives each Lenet connection the one the recording used.
- **Checks on Lenet alone:** every datagram decodes, is at most 4096
  bytes and carries a sent time exactly when it asks for an ACK, and the
  resource bounds hold after every service step.

## Trace scenarios

| name           | exercises                                                        |
|----------------|------------------------------------------------------------------|
| `connect`      | handshake, both roles                                            |
| `send_c2s`     | reliable, unreliable and unsequenced sends, client to server     |
| `send_s2c`     | the same, server to client                                       |
| `frag`         | a 40 KB reliable packet in fragments                             |
| `fragthen`     | traffic queued behind a fragment set, then a second set          |
| `disc_client`  | graceful disconnect by the client                                |
| `disc_server`  | graceful disconnect by the server                                |
| `idle`         | keepalive pings with no traffic                                  |
| `timeout`      | an unacknowledged command: retransmit backoff, then timeout      |
| `checksum`     | CRC32 checksums on both hosts                                    |
| `bandwidth`    | bandwidth limits: BANDWIDTH_LIMIT, per-peer shares, window size  |
| `unfrag`       | an 8000-byte unreliable fragmented packet                        |
| `disclater`    | disconnect later with reliable commands in flight                |
| `multip`       | two clients: broadcast and unicast                               |
| `inject`       | hostile datagrams (below)                                        |
| `multichannel` | 8 channels, both directions                                      |
| `dup`          | duplicate reliable and unsequenced datagrams                     |
| `reconnect`    | disconnect and reconnect on the same slot                        |
| `retimeout`    | the server goes silent: client-side timeout                      |
| `mtu576`       | a 40000-byte packet at the minimum MTU                           |
| `throttleconf` | THROTTLE_CONFIGURE both ways                                     |

The `inject` scenario splices hand-made datagrams into the client-to-server
path, each testing one check in ENet's receive path: an empty datagram, an
unknown command (alone and after a valid PING), a truncated command, a
wrong session, the compressed flag, a CONNECT with 0 channels or MTU 0, and
a PING to a zombie peer.

## Live interop scenarios

| name           | direction              | exercises                                        |
|----------------|------------------------|--------------------------------------------------|
| `connect`      | Lenet to ENet          | handshake with data, one reliable packet each way |
| `connect_r`    | ENet to Lenet          | the reverse handshake                            |
| `send`         | both                   | reliable, unreliable and unsequenced             |
| `frag`         | both                   | a 40000-byte reliable packet                     |
| `disconnect`   | Lenet disconnects      | graceful disconnect with data                    |
| `disconnect_r` | ENet disconnects       | the reverse                                      |
| `timeout`      | Lenet goes silent      | ENet's retransmit backoff and timeout            |
| `checksum`     | both                   | CRC32 checksums                                  |
| `bandwidth`    | both                   | bandwidth limits and the throttled window        |
| `disclater`    | Lenet disconnects      | queued packets, then disconnect later            |
| `multip`       | two ENet clients       | peers told apart by address, broadcast, unicast  |
| `unfrag`       | both                   | an 8000-byte unreliable fragmented packet        |

## Lossy-link runs

`lossy-interop` runs each profile with each seed in `SEEDS`, once with a
Lenet client and an ENet server and once the other way round. A run is
`ROUNDS` rounds 10 ms apart (default 200). Each round sends `PER` (default
2) reliable packets on channels 0 and 1, every tenth on channel 0
fragmented, plus one unreliable, one unreliable fragmented and one
unsequenced packet.

| profile | each way, per datagram                        | timeouts            |
|---------|-----------------------------------------------|---------------------|
| `light` | drop 1 in 20, double 1 in 50, 0-20 ms delay   | ENet's defaults     |
| `heavy` | drop 1 in 5, double 1 in 20, 0-40 ms delay    | raised on both ends |
| `burst` | 0-10 ms delay, drop everything for 200-500 ms every 2-4 s | ENet's defaults |

CI runs `light` and `burst`. `heavy` is too harsh for ENet itself to pass
every time; `make -C test lossy-enet` shows that. When a run fails, both
programs print a stall report after 2 s without a packet, and
`PROXY_LOG=<file>` logs every datagram and what the proxy did with it.

`lossy-wrap` sends 94500 packets of each kind per channel, so every 16-bit
sequence counter wraps, with fragment sets straddling the reliable wraps.
`lossy-clock` starts both clocks 10 s before 2^32 with bandwidth limits
on, so RTT, retransmit timeouts, pings and the throttle all cross the wrap.
Both take about 50 s per run; CI runs a short clock wrap instead.
