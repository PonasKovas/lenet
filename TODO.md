# Roadmap & Working Notes

Lenet is a sans-I/O reimplementation of the ENet protocol in Lean 4, with a
plain C API distribution. This file is the living plan: what is done, what is
next, and the decisions that are not up for relitigating. New to the project?
Read `DESIGN.md` (architecture + principles) and `test/README.md` (how the
compatibility testing works), then come back here.

## How the pieces fit

- `Lenet/` — the sans-I/O core. Pure state machine: datagrams in, events +
  outgoing datagrams out, time supplied by the caller.
- `csrc/` — the C distribution: `include/lenet.h` (public API),
  `lenet_capi.c` (shim over the Lean FFI), and the built `liblenet.a`.
  Static-only by design.
- `test/` — the compatibility corpus (see `test/README.md` for the full
  picture):
  - `c/harness.c` records golden traces from *real* ENet (pinned revision)
  - `test/Replay.lean` (`lake build replay`) replays them through Lenet and
    diffs events + outgoing commands against ENet's. Ticking is
    deadline-driven: the replay services Lenet at the host's own timer
    boundaries (`Host.nextDeadline`) between trace lines, so retransmit /
    timeout / ping / throttle timing is insensitive to where recorded
    datagram lines happen to fall (pump jitter between ENet's internal
    serviceTime and the logged timestamps is ~1ms)
  - `c/interop.c` runs Lenet (via FFI) against real ENet over live UDP
- CI (`.github/workflows/lean_action_ci.yml`) runs: build, replay (Tier 1),
  C API check (Tier 1), live interop (Tier 2, clones ENet at the pin).

## Current state

- 21 golden-trace scenarios, all roles PASS (connect, send_c2s, send_s2c,
  frag, fragthen, disc_client, disc_server, idle, timeout, checksum,
  bandwidth, unfrag, disclater, multip, inject, multichannel, dup,
  reconnect, retimeout, mtu576, throttleconf).
- Live interop: 12/12 PASS. C API distribution builds and self-checks.
- Phase 1 (code quality) is done: typed errors, `Vector`-backed fixed-size
  windows, no panicking constructs, conventions in DESIGN.md 1.7.
- Phase 2 (formal proofs) first pass is done: separate `LenetProofs` lib in
  CI - codec reader algebra + parse fuel adequacy, reassembly invariant +
  completion soundness, channel drain/advance theorems + wrap-boundary pin,
  time translation invariance, unsequenced idempotence, divisor audit (see
  the Phase 2 section for the deferred remainder).

## Roadmap

Phases in order; each one gates the next. Exit criteria per phase listed.

### Phase 0 — ENet compatibility (current task)

**Pass A (done):**
1. ~~Fix the three known divergences~~ — done: per-command processing
   (`Datagram.parseCommands`: sequential parse, apply prefix, stop at the
   first malformed command), CONNECT validation (reject channelCount
   ∉ [1,255], clamp MTU to [576,4096] before the host-MTU min), and
   disconnected/zombie datagrams dropped at the peer lookup.
2. ~~Harness `INJECT` action + `inject` scenario~~ — done: 9 hand-picked
   hostile datagrams pinning ENet's receive-path validation gates (see the
   matrix in test/README.md). Recorded ENet responses confirmed all three
   fixes on the wire.

**Pass B (done):**
3. ~~Scenarios~~ — done: `multichannel` (8 channels), `dup` (DUP action
   re-sending captured datagrams), `reconnect` (slot reuse + session
   carry-over), `retimeout` (client-side timeout), `mtu576` (MTU param on
   `Host.create`), `throttleconf`. Found and fixed along the way: the
   disconnect lifecycle (peers are now reset when their disconnect event is
   dispatched - slots are reusable), `Peer.queueDisconnect` in the
   `disconnectLater` ack path (the DISCONNECT was never queued), and the
   timeout condition now evaluates against the freshly updated
   `earliestTimeout` (ENet same-iteration parity).
4. ~~Interop extensions~~ — done: FFI/C API additions
   (`lenet_host_enable_checksum`, `lenet_host_disconnect_later`,
   `lenet_peer_throttle_configure`, MTU on `lenet_host_create`) + interop
   scenarios `checksum`, `bandwidth`, `disclater`, `multip`, `unfrag`.

**Exit criteria (met):** 20 scenarios all PASS; interop 12/12; DESIGN.md
constraints recorded; divergence triage documented.

### Phase 1 — Code quality (done)

Idiomatic Lean pass over `Lenet/`: eliminate imperative leftovers from the C
rewrite (mutable-accumulator patterns, `getD`-defaults masking logic,
`Except String` -> typed errors), total-by-construction patterns.

Done in the pass:
1. Typed errors: `LenetError` (new `Lenet/Error.lean`) replaces `Except
   String` on `Host.connect` / `Host.send` / `Peer.send`.
2. Total-by-construction fixed-size state: `Channel.reliableWindows` and
   `UnsequencedWindow.window` are `Vector _ N` with `*_lt` index lemmas;
   `FragmentAssembler.addFragment` handles the impossible-bitset case with an
   explicit `CodecError` instead of a `getD false` that could have masked a
   desync (decrement-without-record).
3. No fabricated defaults: the default-`Peer`/default-`Channel`/default
   assembler `getD` fallbacks are gone (`Host.connect`,
   `Host.handleDatagram`'s connect path, `Peer.removeSentReliableCommand` now
   `find?`+`erase`-based, `Peer.handleFragment` extracted - the two duplicated
   fragment branches collapsed into one helper).
4. Checksum table lookup is provably in-bounds (UInt8 index +
   `crcTable_size`), no `getD 0` that would silently corrupt a CRC.
5. `Peer.send` fragment loop de-mutated (`let mut` + `for` -> `map`/`foldl`
   over the fragment range); channel access is bounds-guarded with a typed
   error, not a default channel.
6. FFI event/outgoing polling no longer uses `getElem!` (`[0]!`) - guarded
   access instead.
7. Wire-size tables unified: `CommandBody.fixedWireSize` / `payloadSize` /
   `Command.wireSize` are the single source of truth for both the datagram
   parser's advance logic and the packer's MTU budget.
8. Dead `Lenet/Compress.lean` removed: it contained a non-roundtripping fake
   range coder and a decompress that returned its input unchanged -
   misleading and dangerous if ever wired in (compression remains descoped;
   the `Compressor` hook in `Codec.lean` stays).
9. Style conventions written down: DESIGN.md 1.7.

**Exit criteria (met):** zero warnings (lib + replay); zero panicking
constructs (`getElem!`, `unsafe`, `partial`, unguarded array indexing) in
`Lenet/` - the one remaining `getD` is an `Option` default (`no event ->
#[]`), the semantically-correct-for-absent idiom; corpus 20/20 PASS and
interop 12/12 PASS unchanged (refactors are behavior-preserving).

### Phase 2 — Formal proofs

Prove what the corpus showed matters: codec roundtrip; decode totality on
arbitrary input; fragment reassembly bounds safety; reliable in-order
delivery; no-panics across `Host.handleDatagram` / `Host.service`.
**Exit criteria:** proofs compile and are maintained in CI; corpus still
passes (proofs must not break the tested behavior).

**Progress (first pass):** separate `LenetProofs` lib (in defaultTargets, so
CI builds it; the C distribution never compiles proofs). Proven so far:

- Wave 0 (fix + pin): ENet's cyclic receive-window gate applied to
  `receiveReliable` (wrap deadlock at 0xFFFF fixed, staging bounded - see
  test/README.md triage); `wrap_delivery` pins the fixed boundary.
- Codec (`Proofs/Codec.lean`): reader primitives in ok/err form; append-based
  byte layout with field-level write/read inverses (`write_read_u16/u32`,
  bv_decide for the fixed-width identities); `parseCommands` fuel adequacy
  (fuel = payload size achieves the maximal parse).
- Reassembly (`Proofs/Reassembly.lean`): the bitmap/counter invariant
  (`fragmentsRemaining + received.count = fragmentCount`) established by
  `init` and preserved by `addFragment`; write-bounds; completion soundness
  (all slots received when the buffer dispatches - no completion via
  replayed fragment numbers).
- Channel (`Proofs/Channel.lean`): drain fuel adequacy + the drain advances
  its frontier by exactly the delivered span total; `receiveReliableSpan_advance`
  (incoming counter advances by the delivered span total, wrap-aware).
- Time (`Proofs/Time.lean`): translation invariance of `difference`/`less`
  (cyclic subtraction invariance, bv_decide).
- Unsequenced (`Proofs/Unsequenced.lean`): `checkAndAdd` idempotence in all
  three acceptance cases (re-receiving an accepted group is always a
  duplicate).
- Panic (`Proofs/Panic.lean`): the divisor audit - every division site named
  with its non-zero-divisor proof; a new unguarded division fails review by
  its absence here. Combined with Phase 1's conventions (proof-carrying
  indexing, no getElem!/unsafe/partial), this is the no-panics gate.

**Remaining for the full exit criteria (deferred, in order of value):**
- roundtrip composition theorems at the full-`Datagram` level (the
  per-command groundwork is done; needs a reader-algebra composition lemma
  for multi-field payloads)
- `nextDeadline` upper-bound property (fold-is-min; driver-facing)
- Peer-level window-skew invariant connecting `Peer.send`'s window
  discipline to the receive-path preconditions (stretch; cut from the
  first pass)
- formal no-panics composition over `Host.handleDatagram` / `Host.service`
  (the ingredient lemmas exist; needs the top-level statement)

### Phase 3 — Performance

Benchmark executable done (`bench/Bench.lean`, `lake build bench`; compile-only
in CI, run locally): closed-loop client/server pair in one process,
throughput per delivery mode + CPU cost per service tick. The bench fails
(exit 1) if any scenario loses or corrupts a packet, so its numbers are only
printed when they mean something. Note: `IO.lazyPure` is `pure (f ())`, so a
pure timed body must depend on a value read from IO (the bench seeds each run
from the starting clock read) or the optimizer hoists it out of the timed
region entirely.

Baseline (median of 5 runs; i5-8350U @ 1.70 GHz, Lean 4.33.1, release build;
run-to-run jitter ~±10% — regenerate locally for current numbers):

| scenario                | pkts/s | MB/s | ns/pkt |
|-------------------------|--------|------|--------|
| reliable 1200B          | ~250k  | ~300 | ~3950  |
| unreliable 1200B        | ~360k  | ~430 | ~2800  |
| unsequenced 1200B       | ~260k  | ~315 | ~3830  |
| reliable 4096B (frag)   | ~44k   | ~180 | ~22800 |
| unrelfrag 4096B (frag)  | ~54k   | ~220 | ~18400 |

Service tick (one pump round: service both hosts + route datagrams): idle
connected pair ~2.7 µs/tick; loaded (64 reliable 1200 B sends + pump) ~255
µs/tick ≈ 4.0 µs/packet — consistent with the throughput case's ns/packet.

Remaining: easy wins only (buffer reuse vs `extract`, fold/array churn,
encode paths), gated on the baseline above. **Exit criteria:** recorded
baseline numbers (done); proofs + corpus stay green.

### Phase 4 — lenet-rs (async Rust bindings)

Separate repository: `-sys` crate over the (by then extended) C API with
hand-written externs and `build.rs` linking `liblenet.a`; sans-I/O API maps
to a tokio driver (one task owns the host: socket + `lenet_host_service(now)`
+ poll loops, scheduling ticks via the host's timer deadlines — the same
primitive the replay uses, exposed to the driver as `Host.nextDeadline`);
builder-style API, event stream. Threading contract: one host,
one thread (or external serialization).
**Exit criteria:** async interop test vs real ENet from Rust.

**Progress (first pass, in `../lenet-rs`, git):**
- C API extended first (this repo, uncommitted): `lenet_host_next_deadline`
  added to `include/lenet.h` + `lenet_capi.c` + a new `lenet_ffi_host_next_deadline`
  export in `Lenet/FFI.lean`; `make -C csrc check` green. The driver needs
  the deadline to schedule service ticks without busy-pumping.
- Workspace crates: `lenet-sys` (hand-written externs, `build.rs` links
  `liblenet.a`, `LENET_LIB_DIR` override), `lenet` (safe sans-I/O API:
  `HostBuilder`→`Host`, typed errors, payload-buffered `poll_event`),
  `lenet-tokio` (one pump task: recv → handle_datagram, `service` at
  wrap-aware `next_deadline` + 100 ms fallback tick, outgoing/events
  flushed to socket/mpsc; `Connection` handles for send/disconnect,
  `Endpoint::peer` for server-role sends, `with_host` escape hatch),
  `enet-helper` (real ENet oracle binary: cmake-builds the pinned ENet,
  echo server + client modes).
- Tests: sans-I/O unit tests (`lenet/tests/sansio.rs`: two hosts routed by
  hand — handshake + connect data, reliable roundtrip, 40 KB fragment
  reassembly, graceful disconnect, idle stability, deadline presence) and
  the exit-criterion async interop (`lenet-tokio/tests/interop.rs`): Rust
  client ↔ ENet server (handshake + reliable echo + disconnect data,
  fragmented 40 KB echo), and Rust as server ↔ ENet client roundtrip.
  `cargo test --workspace`: 10/10 PASS, clippy clean.
- Notes: outgoing datagrams only materialize on `service` (ENet parity,
  ACKs included) — drivers must service before polling outgoing; the
  initiator's own DISCONNECT event carries data 0; server-side CONNECT
  events fire when the client ACKs the VERIFY_CONNECT, not on receipt.

## Explicitly out of scope

- **Compression** (ENet's optional PPM range coder): descoped — see
  DESIGN.md 1.4. Compressed datagrams are rejected.
- **Sequence-wrap golden traces** (~65k commands per channel needed; the
  wrap logic is exercised by proofs instead).
- **Packet loss / reordering chaos scenarios** (recording is
  non-deterministic; the replay needs determinism).
- **Packet loss / reordering chaos scenarios** (recording is
  non-deterministic; the replay needs determinism).
- **Resource-exhaustion *parity***: matching ENet's exact memory behavior
  under hostile input is out of scope (and ENet has similar pressure
  points). This does **not** descope Lenet's own robustness - see
  `Lenet/Proofs/Resources.lean` for the enforced bounds: fragment
  assemblers are hard-capped (`maximumFragmentAssemblers`, proven in
  `handleFragment_cap_preserved`), received fragment counts are
  wire-guarded (`maximumReceivedFragmentCount`), staging is bounded by the
  receive-window gate, and the replay corpus asserts all three after every
  service step (`checkResourceBounds` in test/Replay.lean). The ack queue
  is intentionally uncapped (driver-pump-coupled; capping would drop ACKs
  for no robustness gain) - documented, and the only remaining
  ENet-comparable pressure point.

## Decided constraints (do not relitigate)

- **Correctness over compatibility** (DESIGN.md 1.5, in stone): an ENet bug
  is fixed in Lenet, never mirrored. First applications are the Phase 0
  Pass A divergence fixes.
- Golden traces are pinned to ENet `5a9c537` (v1.3.18-17); bumping enet
  requires re-recording traces (`make -C test traces`) and a diff review.
- Shared library is impossible with a stock Lean toolchain (leanrt built
  without -fPIC); the C distribution is static-only by design.
- Test philosophy: Lenet must interop, not bit-clone ENet. Divergences are
  triaged per DESIGN.md 1.5 (lenet bug / enet bug -> fix, don't mirror /
  don't-care mask with rationale in `test/README.md`).
- No fuzzing executable: hostile-input coverage comes from hand-picked INJECT
  scenarios (ENet as the record-time oracle) plus formal proofs; seeded fuzz
  adds sampling cost without finding what proofs won't already cover.
- Compression is descoped (DESIGN.md 1.4).

## Operational notes (CI, recording)

- ENet is cloned in CI at the pinned revision the golden traces were
  recorded against: upstream `lsalzman/enet` @ `5a9c537fd464b3c6d3c55e1d3bd47588faf71b42`
  (= v1.3.18-17). Re-recording traces is only needed when scenarios change,
  and must be done locally (`make -C test traces`) — recording is not
  byte-reproducible (real clock + ENet randomness), the replay tolerates
  this because it replays committed traces.
- Watch the first CI run for runner-specific issues; locally-verified
  fixes were: shim compiles with plain `$(CC)` (leanc's bundled clang
  lacks system headers), lake must run with `-d ..` from `csrc/`.
