# Design

## Principles

**Sans-I/O.** The engine is a pure state machine: `(host, input) -> (host,
output)`. Inputs are received datagrams and the current time; outputs are
datagrams to send and application events. The driver (a C loop, a Tokio
task) owns the socket and the clock. Time is `UInt32` milliseconds and
wraps, like ENet's; all time comparisons go through `Lenet.Time`, which
uses ENet's wrap-aware order.

**Correctness over compatibility.** Lenet has to interoperate with ENet, not
copy it. Every behavioral difference found is sorted into one of three
kinds, and the decision is written down in
[test/README.md](test/README.md#divergence-triage):

- *lenet bug*: Lenet is wrong, fix Lenet.
- *enet bug*: ENet is wrong. Lenet does the right thing and the difference
  is recorded. Never copy the bug.
- *don't care*: invisible to interop. The comparison masks it, with the
  reason written next to the mask.

**Robust against hostile input.** Every value from the wire is validated
before it is used, and memory an attacker can make Lenet hold is bounded
(see [Resource bounds](#resource-bounds)). Where ENet is looser, Lenet is
deliberately stricter.

## Architecture

```
driver ──datagram──▶ Host.handleDatagram ──▶ Datagram.decode ──▶ Peer.handleCommand ──▶ Channel
driver ──time──────▶ Host.service ─┬─ bandwidthThrottle      (every 1 s)
                                   ├─ checkTimeoutsAndPings  (retransmit, timeout, keepalive)
                                   └─ pollOutgoing ──▶ packOutgoingCommands ──▶ Datagram.encode ──▶ driver
driver ◀──when─────  Host.nextDeadline
```

| module                     | role |
|----------------------------|------|
| `Host`                     | peer slots, connection setup, the API calls, `service`, `nextDeadline` |
| `Peer`                     | one connection: state machine, RTT and throttle, command queues, incoming command handling |
| `Channel`                  | per-channel sequence numbers, reliable windows, staging of out-of-order reliable deliveries |
| `Reassembly`, `Unsequenced`| fragment reassembly; duplicate filter for unsequenced packets |
| `Protocol.*`, `Codec`, `Checksum` | the wire format and ENet's CRC32 |
| `FFI`                      | `IO` wrappers exported to the C shim (`csrc/lenet_capi.c`); the only place with `IO` |

Every function in the core follows ENet's structure closely and names the
ENet function it mirrors (`protocol.c handle_acknowledge`, ...), so the two
can be read side by side. The replay and interop tests pin ENet
1.3.18-17 (`5a9c537`).

## Code rules

These hold for everything under `Lenet/`.

- **No panics.** No `xs[i]!`, `get!`, `unsafe`, `partial`, `sorry` or
  incomplete matches. Array access is either proof-guarded
  (`if h : i < xs.size`), total (`?`, `modify`, `setIfInBounds`), or a
  `?`-match whose `none` case is handled. `Proofs/Panic.lean` enforces this
  at build time.
- **No invented state.** `getD` is fine when the default is the right
  answer for "absent" (no event, an empty slot reads 0). It is not fine
  when absence means a broken invariant: then handle the case.
- **Total by construction.** Recursion is structural or fuel-bounded, and
  the loop says why its fuel is enough.
- **Sizes in types.** Fixed-size rings are `Vector _ N`, and the index
  bound is proven once next to the index function.
- **Typed errors.** Fallible API calls return `Except LenetError _`; wire
  decoding fails with `CodecError`.
- **Deliberate arithmetic.** `UInt*` arithmetic wraps like ENet's C code
  (timers, sequence numbers); that is intended. `Nat` subtraction saturates;
  code that relies on it says why it cannot underflow.
- **One source of truth for wire sizes.** `CommandBody.fixedWireSize` and
  `payloadSize`; the encoder, the decoder and the packer all use them.
- **Performance idiom.** Lean updates a value in place only while it is
  uniquely referenced. Hot loops are top-level functions over a state
  record (see `Host.PackState`), and `IO.Ref`s are updated with
  `modify`, not `get` then `set`.

## What is proven

The proofs live in the `LenetProofs` library (`Lenet/Proofs/`), which the
default build and CI compile. The C library never includes them.

| file            | result |
|-----------------|--------|
| `Codec`         | every reader primitive either advances past a bounds-checked region or fails in place; field-level write/read inverses; the command parser's fuel is always enough (`parseCommands_fuel_adequate`) |
| `Roundtrip`     | every command kind roundtrips (`rt_command`), canonical headers roundtrip (`rt_header`), the command list is recovered exactly (`parseCommands_cmdsBytes`), and the full wire datagram roundtrips through the host's real encode/decode pair, checksum verification included (`wire_roundtrip`) |
| `Reassembly`    | the assembler's bitmap and counter stay in step, writes stay in bounds, and a packet is only released when every fragment arrived (`addFragment_completion_sound`) |
| `Channel`       | the staged-delivery drain has enough fuel and advances the frontier by exactly the delivered span; delivery works across the 16-bit wrap (`wrap_delivery`) |
| `Unsequenced`   | a group accepted once is always rejected afterwards (`checkAndAdd_idempotent`) |
| `Time`          | time differences don't depend on when the clock started; 16-bit wire timestamps are recovered exactly (`fromWire_recovers`) |
| `Deadline`      | `nextDeadline` is always one of the host's timers and no timer is earlier (`nextDeadline_mem`, `nextDeadline_earliest`) |
| `Resources`     | the fragment-assembler cap holds and every assembler stays well formed with its memory fixed at creation (`handleFragment_assemblersOk`), and a channel stages at most seven windows of reliable packets whatever the sender does (`stagedReliableInv_size`) |
| `Events`        | every per-peer step keeps the peer's events consistent: connect only when not already connected, receives only while connected, no way back but a disconnect (`handleCommand_wf`, `checkPeerTimeouts_wf`, `pollPeer_wf`) |
| `HostEvents`    | the same for the whole host: from `Host.create`, after any sequence of received datagrams, `service` calls and application calls, every peer slot's events are consistent, so between two connects of a slot there is always a disconnect (`run_wf`, `EventsWf.disconnect_between`) |
| `Panic`         | a build-time scan of every `Lenet.*` definition fails the build on any panicking construct; every division is listed with a proof its divisor is not zero |

A kernel theorem cannot say "does not panic", because in Lean's logic
`panic!` is just `default`. That is why the no-panic guarantee is a
build-time audit rather than a theorem.

## Scope decisions

- **No compression.** ENet's optional order-2 range coder is not
  implemented, and datagrams with the compressed flag are dropped. The
  feature is opt-in and rarely used, and a decoder would have to copy
  ENet's coder model exactly, which is a large port with no user asking
  for it.
- **Static library only.** The stock Lean runtime is built without
  `-fPIC`, so a shared `liblenet.so` cannot be made.
- **One host, one thread.** A host is not thread-safe; drive it from one
  thread or put a lock around it.
- **Tests compare with ENet, not a spec.** Golden traces are recorded from
  ENet at a pinned revision. Moving the pin means re-recording
  (`make -C test traces`) and reviewing the diff.
- **No fuzzer.** Hostile input is covered by hand-picked `inject` probes
  (with ENet as the oracle) plus the proofs. Random fuzzing would cost more
  than it finds here.
- **Not covered by traces:** sequence-number wrap (it takes ~65k commands
  per channel; the proofs cover it) and packet loss or reordering
  (recording those is not deterministic). The benchmark's lossy link covers
  loss: it drops every n-th datagram between two Lenet hosts and checks
  that reliable packets all arrive, once and in order, and that nothing is
  left in transit afterwards.

## Resource bounds

Memory an attacker can make a host hold is bounded:

- **Fragment assemblers:** at most `maximumFragmentAssemblers` (32) per peer
  are in progress. Each one allocates its full packet up front, capped by
  the validated total length (4 MB) and a fragment count of at most
  `maximumReceivedFragmentCount` (65536). ENet has no such cap. When it is
  full, a new set evicts the oldest unreliable one; if all 32 are reliable,
  the fragment is dropped without an ACK, so the sender retransmits it
  later instead of losing it.
- **Staged reliable packets:** only in-window sequence numbers are staged,
  each at most once, and a delivery drops the ones its span jumped over, so
  a channel never holds more than 28672 (seven windows). ENet keeps those
  jumped-over packets, where they stall its dispatch.
- **Staged unreliable packets:** only those sent after an in-window reliable
  command, each at most once, at most `maximumStagedUnreliable` (1024) per
  channel. ENet bounds them only by `maximumWaitingData`.
- **ACK queue:** not capped on purpose. It grows by at most 32 entries per
  received datagram and each service call drains it; capping it would only
  force retransmissions. This matches ENet.

The replay checks all four bounds after every service step.
