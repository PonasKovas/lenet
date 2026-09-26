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

Done since: step 1 of the window invariant. The staging bound did not
follow from the receiver: a reliable set's span could jump the frontier
over a staged plain packet and strand it (test/README.md "Reliable packets
staged inside a span"). Fixed, and `Proofs.stagedReliableInv_size` now
proves at most `(freeReliableWindows - 1) * reliableWindowSize` staged per
channel from the receiver alone.

Then step 2 turned out false as stated. "Everything the sender sends is
in the receiver's window" does not hold, for ENet either. `canSendReliable`
at the start of window `w` only asks windows `w .. w+9` to be empty, so
in-flight commands may sit in the six windows `w-6 .. w-1`. The receiver
admits its frontier's window and the next six. Reachable example: 1..4095
acked, 4096 lost, 4097..28671 in flight but for one acked number in window
6. The sender may send 28672 (`canSendReliable` is true), the receiver's
frontier is 4095 and its gate refuses 28672. Nothing breaks: it is not
acked and is resent once 4096 gets through. Lenet matches ENet here, so
there is nothing to fix.

What is true, sender side only: when a reliable command is first sent,
every command still in flight on its channel is fewer than seven windows
(28672 numbers) behind it. Proving that needs an invariant tying
`Channel.reliableWindows` to `Peer.sentReliableCommands` through
`packCommand`, `removeSentReliableCommand`, retransmission and reset.
Undecided whether that is worth it; the other proof items may pay more.

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

- **Sender-side window span.** The in-flight reliable commands of a channel
  span fewer than seven windows (see the handoff note: the stronger "always
  in the receiver's window" is false, for ENet too).
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
