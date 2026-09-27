# Open work

Done so far: full ENet 1.3.x interop except compression (21 golden-trace
scenarios, each recorded at three clock starts, and 12 live interop
scenarios pass), unit tests, a lossy-link benchmark, the C distribution,
and the proofs listed in [DESIGN.md](DESIGN.md#what-is-proven). What
follows is what is left, roughly in priority order.

## Next step (handoff, 2026-09-27)

Done this session:

- **Sender-side window span proof** (`Proofs/Window.lean`). `run_span`:
  from `Host.create`, after any sequence of operations, the reliable
  commands in flight on a channel lie within seven windows ending at the
  last one sent. Along the way: first sends go out in sequence order and
  the window counters count exactly what is in flight. `SpanInv` is the
  per-peer invariant; every writer of the peer's queues and channels keeps
  it. `disconnectNow_inv` and `resetPeer_inv` cover the two calls `Op`
  leaves out.
- Two code changes the proof needed, both the same behavior on every
  reachable state: `removeSentReliableCommand` erases the index it found
  (was `find?` then `erase` by value), and a reliable command too big for
  any datagram sets `reliableHeld` like every other deferral (fragments are
  sized to fit, so it does not happen).
- Proof hazards worth knowing (from earlier sessions, still true): when a
  value must stay unshared, `swapAt` alone is not enough, since the
  compiler may sink its write (`takeAt` is `@[noinline]` for that); and
  never let the kernel compare `h` with a host whose `randomSeed` was
  advanced (`h.randomSeed + 0x6D2B79F5`): it unfolds the addition one
  successor at a time and the build gets killed. Go through
  `random_peers`.
- Lean tips from this one: a structure literal split over lines must keep
  its fields aligned, or the parser stops with "expected '}'"; and `split`
  picks the outermost `if`, so an `if` inside another's condition needs
  `by_cases` or a lemma over the general shape (`scanStep`, `ite_map_inv`).

- **Typed Lean API** (`Lenet/Net.lean`, library `LenetNet`): an
  `Endpoint` runs a host over a `Std.Async.UDP` socket with ENet's calls
  (`connect`, `send`, `service timeout`, ...). Connections are
  `PeerHandle`s (slot plus a generation), dead once their connection ends.
  `test/Net.lean` (exe `net`, in CI) runs two endpoints on 127.0.0.1.
  Found on the way: `Selectable.tryOne` on `recvSelector` never finds a
  datagram, so `Endpoint` keeps one low-level receive outstanding and
  checks whether it resolved; a sleep registers one waiter, woken by that
  receive's single continuation.

- `make -C test net-interop` (in CI): `Lenet.Net` in one process against
  an ENet echo peer (`test/c/echo.c`) in another, both ways round.

- **Channel handles** (later the same day): see API and bindings below.
  `test/Net.lean` checks a server's channel limit shows up on both sides'
  connections and that packets echo back on the channel they came in on.

- **Receiver-side delivery proof** (`Proofs/Delivery.lean`, later still).
  An honest sender's reliable packets are a `Stream` (message `i` spans
  `span i` sequence numbers, unwrapped). Fed any arrivals that each `Fits`
  (no more than 9 windows behind the frontier, fewer than 16 ahead), a
  channel hands out exactly messages 0, 1, 2, ... once each, in order
  (`feed_spec`), and the next message's arrival always delivers it
  (`step_next`). `receiveReliableAndRelease_spec` covers the peer's receive
  path with unreliable packets mixed in. `admitted_iff` (the receive gate
  unwrapped) and `drain_spec` are the reusable pieces. To see a proof
  depends on code, break the code and stub any earlier proof that fails
  first with `sorry`, or Lake never gets to the new one.

Suggested next: tie `Delivery` to `Window` (see Proofs).

Checks before each commit: `lake build` (library and proofs, including the
no-panic audit in `Proofs/Panic.lean`), `./.lake/build/bin/unit`,
`./.lake/build/bin/replay test/traces`. For code changes also
`make -C csrc check`, `make -C test interop` (needs ENet in `../enet`) and
the bench. For a new test, break the code it guards once to see it fail.

## Testing gaps

Several bugs fixed recently were invisible to the corpus: RTT samples broke
after 65 s of uptime, retransmissions leaked in-transit bytes, the sender's
reliable windows were never occupied. The benchmark's lossy link now covers
loss (and found the fragment assembler leak), and `test/Unit.lean` pins the
fragment-assembler rules, retransmission, timeouts and disconnect-later.
The candidate list is done (unsequenced window, `nextDeadline` against
`service`, packet throttle, bandwidth limits across peers); add more there
as bugs show where the corpus is blind.

## Proofs

- Open: the whole connection. `Delivery` assumes each arrival `Fits` the
  receiver's frontier; the sender side (`Window`) bounds what is in flight
  but not how far behind a delayed datagram can be. A connection-level
  statement needs a network model with bounded delay (or the sender's
  in-flight span plus "the receiver acked everything before the oldest
  command in flight"), then `Fits` follows and so does in-order delivery
  from `Host.create`.

## Performance

Baseline (`./.lake/build/bin/bench`, two runs, i5-8350U @ 1.7 GHz, Lean
4.33.1, 2026-09-26 after the one-pass packing; run-to-run noise is about
10%, and this machine ran ~25% slower than usual all day, so compare
against a fresh run of the old code, not these numbers):

| scenario               | pkts/s | ns/pkt |
|------------------------|--------|--------|
| reliable 1200B         | ~280k  | ~3550  |
| unreliable 1200B       | ~480k  | ~2080  |
| unsequenced 1200B      | ~290k  | ~3480  |
| reliable 4096B (frag)  | ~62k   | ~16200 |
| unrelfrag 4096B (frag) | ~88k   | ~11400 |

Service tick: idle pair ~3.1 µs, loaded (64 reliable sends) ~226 µs. One
reliable packet end to end: 1 MB ~5 ms, 4 MB ~24 ms, 16 MB ~230 ms.

Measured back to back on the same machine, the one-pass packing (every
datagram of a service in one scan of the queue, where the scan per
datagram was quadratic in the queue) took reliable 1200B from ~214k to
~285k, the loaded tick from ~300 to ~225 µs, and 16 MB from 2.5 s to
0.23 s; in-place reassembly took 4 MB from 3.3 s to 0.17 s before that.

What the profile shows now: most time is allocation and freeing, spread
thin. Lean updates an array or record in place only while one reference
holds it, so a value read out of a container that still holds it, or kept
alive for an error branch, gets copied on its next change. To find such a
copy, wrap the value in `dbgTraceIfShared "tag" x` for a moment and count
the messages a bench run prints (that is how the reassembly copies were
found). Known costs left:

- Tried and dropped: `Peer.enqueue` and `Peer.receiveOnChannel` copy the
  channel record on each send and receive. Removing those copies with an
  out-of-line swap made the bench 1-4% slower, not faster.
- Fragmented sends copy each fragment out of the packet (`extract`).
- `Datagram.parseCommands` copies the rest of the datagram after every
  command, but that is 0.3% of the profile: not worth a cursor rewrite.

## API and bindings

- **Typed Lean API**: done (`Lenet.Net`). Channels are typed too: the
  connect event hands out a `Connection` (handle plus the channel count
  both sides agreed on) and `send` takes a `conn.Channel`, a
  `Fin channelCount`. No numeric literal for it on purpose, since `Fin`'s
  wraps around the count: `conn.first`, `conn.channel? i`, `conn.channels`
  or the channel a packet came in on. `broadcast` still takes a `UInt8`
  and skips peers without that channel.
- **ENet API parity** (2026-09-26): disconnect_now, peer reset, ping,
  ping interval, bandwidth limit, channel limit, flush and a peer-info
  getter now exist in Lean (`Host.*`) and C (`lenet.h`).
- **lenet-rs** (async Rust bindings over the C API) lives in its own
  repository. Anything it needs from the C API gets added here first.
- **Shared library** once Lean ships a `-fPIC` runtime.
