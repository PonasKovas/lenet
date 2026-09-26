# Open work

Done so far: full ENet 1.3.x interop except compression (21 golden-trace
scenarios, each recorded at three clock starts, and 12 live interop
scenarios pass), unit tests, a lossy-link benchmark, the C distribution,
and the proofs listed in [DESIGN.md](DESIGN.md#what-is-proven). What
follows is what is left, roughly in priority order.

## Next step (handoff, 2026-09-26, third and fourth sessions)

Done this session:

- **Host-level event proof** (`Proofs/HostEvents.lean`). `run_wf`: from
  `Host.create`, after any sequence of datagrams, `service` calls and
  application calls (`Op`), every slot's events are well formed and name
  an existing slot; `EventsWf.disconnect_between` says what that rules
  out. The per-slot projection works because slot `i` holds peer ID `i`
  (`IdsOk`). The command fold of `handleDatagram` is now its own function,
  `Host.handlePeerDatagram`, so the proof can name it (bench unchanged).
- **Peer count capped at 4095** (test/README.md): found by that proof.
- **Reliable send order follows ENet** (test/README.md, two entries): a
  reliable packet held back by congestion or its window now holds back
  every later one for the pass, and empty ones get the congestion check.
  This matters for the sender-side span proof below: first sends of a
  channel's reliable commands now happen strictly in sequence order,
  which is the fact that argument needs.
- **Incoming commands follow ENet's refusals** (test/README.md, "Refused
  commands" and "Remote DISCONNECT keeps the queues"): a refused command
  gets no ACK and ends its datagram, ACKs depend on the state after the
  command, and both disconnects drop the queues and channels.
- **ENet audit** (fourth session): four parallel read-only audits
  (connection setup, incoming data, outgoing data, timers) compared ENet's
  C line by line with Lenet. Fixed, each with a unit test that fails
  without its fix (test/README.md has an entry per item): unreliable
  numbers used up (a streaming channel went silent after 65535 packets),
  no ping while unreliable data was queued (a dead remote was never timed
  out), zero timeout parameters, retransmitted CONNECT, bandwidth
  recalculation after disconnects in service, data while disconnecting
  later, ACK of a command queued for resend, the client's throttle
  parameters, a connect's channel count, the client's own connect event
  data (0, as ENet; the live `connect` scenario expected the old value),
  the 32 MB send limit, header bytes, and fragment validation. Four ENet
  quirks are recorded as not copied.
- Receiver cap raised to ENet's 32 MB (was 4 MB), the user's call, so
  sender and receiver agree.
- A proof hazard worth knowing: never let the kernel compare `h` with a
  host whose `randomSeed` was advanced (`h.randomSeed + 0x6D2B79F5`). It
  unfolds the addition one successor at a time, with no heartbeat limit,
  and the build just gets killed. Go through `random_peers` instead.

The bench ran about 25% under the baseline below all session, old code
included (tested with the change stashed): the machine was slower, not
the code. Re-measure before trusting a regression.

Suggested next: the sender-side window span proof, or the typed Lean API.

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

- **Sender-side window span.** The in-flight reliable commands of a channel
  span at most seven windows (the stronger "always in the receiver's
  window" is false, for ENet too). The argument: first sends go in sequence
  order (`PackState.reliableHeld`), and the first command of window `w`
  only goes when windows `w .. w+9` are empty, so what is in flight sits in
  `w-6 .. w`. The proof needs an invariant tying each channel's
  `reliableWindows` counts to the peer's in-flight and queued commands,
  kept by enqueue, packing, ACKs, timeouts and the two disconnects (which
  now drop the channels, `Peer.resetQueues`).

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

- **Sending a large packet is quadratic.** `packOutgoingCommands` folds
  over the whole outgoing queue for every datagram, so a 16 MB packet
  (about 12,000 fragments, one per datagram) rescans a queue of thousands
  each time: `packCommand` is a quarter of the profile. ENet's linked
  lists stop at `break` and cut the reliable list instead. Bench, large
  packets: 1 MB ~16 ms, 4 MB ~170 ms, 16 MB ~2.5 s. The fix is a queue
  that packing need not rebuild, for example ENet's split into a
  reliable-data list and the rest.
- Receiving a large packet is linear since 2026-09-26: `Host.withPeer`
  and `Peer.handleFragment` take the peer, the assembler array and the
  assembler out before changing them (`takeAt`), so each fragment is
  copied into the buffer in place (before: 4 MB took 3.3 s). This costs the
  small-packet rows 2-5%, measured back to back.
- Tried and dropped: `Peer.enqueue` and `Peer.receiveOnChannel` copy the
  channel record on each send and receive. Removing those copies with an
  out-of-line swap made the bench 1-4% slower, not faster.
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
