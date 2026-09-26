# Open work

Done so far: full ENet 1.3.x interop except compression (21 golden-trace
scenarios, each recorded at three clock starts, and 12 live interop
scenarios pass), unit tests, a lossy-link benchmark, the C distribution,
and the proofs listed in [DESIGN.md](DESIGN.md#what-is-proven). What
follows is what is left, roughly in priority order.

## Next step (handoff, 2026-09-26, second session)

Done this session:

- **Staging bound, proven.** It did not follow from the receiver: a
  reliable set's span could jump the frontier over a staged plain packet
  and strand it (test/README.md "Reliable packets staged inside a span").
  Fixed; `Proofs.stagedReliableInv_size` bounds every channel at
  `(freeReliableWindows - 1) * reliableWindowSize`, and `PeerStagedInv`
  lifts it over every writer of `Peer.channels`.
- **Array-level assembler invariant, proven** (`AssemblersOk`,
  `handleFragment_assemblersOk`, `assemblerOk_footprint`).
- **Sender-side window invariant: false as stated**, for ENet too.
  `canSendReliable` at the start of window `w` only asks windows
  `w .. w+9` to be empty, so in-flight commands may sit in `w-6 .. w-1`,
  while the receiver admits its frontier's window and the next six.
  Reachable: 1..4095 acked, 4096 lost, 4097..28671 in flight but for one
  acked number in window 6; the sender may send 28672, the receiver
  (frontier 4095) refuses it. It is not acked and is resent once 4096 gets
  through, so nothing breaks and there is nothing to fix. What does hold is
  the sender-only span item under Proofs.
- **In-place updates** (Performance): 15-35% faster across the bench.
  The C API's send no longer copies the host.

Suggested next: the unit-test candidates below (cheap, and past bugs hid
exactly there), then the event-level properties.

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
Worth adding there as they come up:

- **More unit tests.** Candidates: the packet throttle under RTT swings
  and bandwidth limits across several peers.

## Proofs

- **Sender-side window span.** The in-flight reliable commands of a channel
  span fewer than seven windows (see the handoff note: the stronger "always
  in the receiver's window" is false, for ENet too).
- **Event-level properties.** For example "a connection produces exactly
  one connect and at most one disconnect event", stated over
  `handleDatagram`/`service` traces.

## Performance

Baseline (`./.lake/build/bin/bench`, median of 3 runs of the bench's own
median of 5, i5-8350U @ 1.7 GHz, Lean 4.33.1; run-to-run noise is about
10%). Before the in-place peer updates of 2026-09-26 it was ~233k / ~420k /
~255k / ~43k / ~59k pkts/s, idle ~2.7 µs, loaded ~276 µs.

| scenario               | pkts/s | MB/s | ns/pkt |
|------------------------|--------|------|--------|
| reliable 1200B         | ~318k  | ~380 | ~3150  |
| unreliable 1200B       | ~518k  | ~620 | ~1930  |
| unsequenced 1200B      | ~343k  | ~410 | ~2920  |
| reliable 4096B (frag)  | ~49k   | ~200 | ~20400 |
| unrelfrag 4096B (frag) | ~64k   | ~263 | ~15500 |

Service tick: idle pair ~2.2 µs, loaded (64 reliable sends) ~206 µs.

What the profile shows now: most time is allocation and freeing, spread
thin. Lean updates an array or record in place only while one reference
holds it, so a value read out of a container that still holds it, or kept
alive for an error branch, gets copied on its next change. To find such a
copy, wrap the value in `dbgTraceIfShared "tag" x` for a moment and count
the messages a bench run prints. Known costs left:

- `Peer.enqueue` and `Peer.receiveOnChannel` read the channel out of
  `Peer.channels` while the array still holds it, so each send and each
  receive copies the channel record (and its window vector on the next
  acquire). `Array.modifyM` in `StateM` fixes it (as `Host.withPeer`
  does); the Resources proofs over both functions need redoing with it.
- Fragmented sends copy each fragment out of the packet (`extract`).
- `Datagram.parseCommands` copies the rest of the datagram after every
  command, but that is 0.3% of the profile: not worth a cursor rewrite.

## API and bindings

- **Typed Lean API.** The Lean surface is the raw `Host` functions. A thin
  typed layer (peer and channel handles instead of `UInt16`/`UInt8`,
  events as a stream) would make Lenet pleasant to use from Lean itself.
- **lenet-rs** (async Rust bindings over the C API) lives in its own
  repository. Anything it needs from the C API gets added here first.
- **Shared library** once Lean ships a `-fPIC` runtime.
