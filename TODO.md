# Open work

Done so far: full ENet 1.3.x interop except compression (21 golden-trace
scenarios and 12 live interop scenarios pass), the C distribution, and the
proofs listed in [DESIGN.md](DESIGN.md#what-is-proven). What follows is
what is left, roughly in priority order.

## Known differences from ENet

Not yet triaged as bugs or accepted; each needs a decision per
DESIGN.md's rules.

- **Address check before negotiation.** ENet checks the sender address of
  every datagram for a peer; Lenet only once the remote peer ID is known.

## Testing gaps

Several bugs fixed recently were invisible to the corpus: RTT samples broke
after 65 s of uptime, retransmissions leaked in-transit bytes, the sender's
reliable windows were never occupied. They share causes worth fixing:

- **Clocks start at 0 and traces are short.** Replaying every trace with
  the clock shifted (for example to just before the 2^32 ms wrap, and past
  65 s) would exercise the wrap and 16-bit timestamp paths on real traffic.
- **No loss.** A deterministic lossy link in the benchmark's in-process
  pair (drop every n-th datagram) would exercise retransmission, backoff
  and the window accounting, with the same "no packet lost or corrupted"
  check the benchmark already does.
- **No unit tests for the Lean API.** Small, targeted checks (a Lean test
  executable next to `replay`) would pin behavior the traces cannot reach.

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
