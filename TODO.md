# Open work

Done so far: full ENet 1.3.x interop except compression (21 golden-trace
scenarios, each recorded at three clock starts, and 12 live interop
scenarios pass), unit tests, a lossy-link benchmark, the C distribution,
and the proofs listed in [DESIGN.md](DESIGN.md#what-is-proven). What
follows is what is left, roughly in priority order.

## Next step (handoff, 2026-09-26)

Last done: the lossy link in `bench/Bench.lean` (it found the fragment
assembler bug fixed in `9881b31`, see test/README.md "Fragment assembler
lifetime") and the unit tests in `test/Unit.lean`. The testing gaps are
closed apart from the candidate list below.

Next: the first proof item, **sender-side window invariant**, in small
steps, each one building and committed on its own:

1. Read `Lenet/Proofs/Resources.lean` (item 2, staged reliable) and
   `Lenet/Proofs/Channel.lean`. The staging bound the replay asserts
   (`checkResourceBounds` in `test/Replay.lean`: at most
   `freeReliableWindows * reliableWindowSize` staged per channel) may
   follow from the receiver alone: `receiveReliableSpan` stages only
   sequence numbers the window gate admits (a range of
   `(freeReliableWindows - 1) * reliableWindowSize` values past the
   frontier) and never the same one twice. Check that first; if it holds,
   prove it and fix the Resources header, which says the sender side is
   needed.
2. Then the sender side proper: `Channel.acquireReliableWindow` /
   `releaseReliableWindow` / `canSendReliable` and where `PackState.packCommand`
   (`Lenet/Host.lean`) calls them. State that the in-flight reliable
   sequence numbers of a channel never span more windows than the
   receiver's gate admits, so everything the sender sends is in window.

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

- **More unit tests.** Candidates: the packet throttle under RTT swings,
  bandwidth limits across several peers, `nextDeadline` against what
  `service` actually does, and the unsequenced window.

## Proofs

- **Sender-side window invariant.** Connect `Peer.send`'s window discipline
  (now that windows are really tracked) to the receiver's window gate, and
  derive the staging bound the replay currently only asserts.
- **Array-level assembler invariant.** Every assembler in
  `Peer.fragmentAssemblers` satisfies `Proofs.Reassembly.Inv`; the
  per-assembler lemmas exist, the lift over the array does not.
- **Event-level properties.** For example "a connection produces exactly
  one connect and at most one disconnect event", stated over
  `handleDatagram`/`service` traces.

## Performance

Baseline (`./.lake/build/bin/bench`, median of 5 runs, i5-8350U @ 1.7 GHz,
Lean 4.33.1; run-to-run noise is about 10%):

| scenario               | pkts/s | MB/s | ns/pkt |
|------------------------|--------|------|--------|
| reliable 1200B         | ~233k  | ~280 | ~4300  |
| unreliable 1200B       | ~420k  | ~510 | ~2400  |
| unsequenced 1200B      | ~255k  | ~305 | ~3900  |
| reliable 4096B (frag)  | ~43k   | ~175 | ~23500 |
| unrelfrag 4096B (frag) | ~59k   | ~240 | ~17000 |

Service tick: idle pair ~2.7 µs, loaded (64 reliable sends) ~276 µs.

Known costs, in likely order of payoff:

- `Datagram.parseCommands` copies the rest of the datagram after every
  command (`extract`); parsing with a cursor would make it linear.
- Peers are read out of `Host.peers` and written back, which shares them
  with the array for a moment and forces a copy of the peer record. A
  take-modify-put pattern (`Array.modify`) through the whole call chain
  would avoid it.
- Fragmented sends copy each fragment out of the packet (`extract`).

## API and bindings

- **Typed Lean API.** The Lean surface is the raw `Host` functions. A thin
  typed layer (peer and channel handles instead of `UInt16`/`UInt8`,
  events as a stream) would make Lenet pleasant to use from Lean itself.
- **lenet-rs** (async Rust bindings over the C API) lives in its own
  repository. Anything it needs from the C API gets added here first.
- **Shared library** once Lean ships a `-fPIC` runtime.
