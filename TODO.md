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

- 20 golden-trace scenarios, all roles PASS (connect, send_c2s, send_s2c,
  frag, disc_client, disc_server, idle, timeout, checksum, bandwidth, unfrag,
  disclater, multip, inject, multichannel, dup, reconnect, retimeout, mtu576,
  throttleconf).
- Live interop: 12/12 PASS. C API distribution builds and self-checks.
- Phase 1 (code quality) is done: typed errors, `Vector`-backed fixed-size
  windows, no panicking constructs, conventions in DESIGN.md 1.7.

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

### Phase 3 — Performance

Benchmark executable (throughput per delivery mode, CPU cost per service
tick), then easy wins only (buffer reuse vs `extract`, fold/array churn,
encode paths). **Exit criteria:** recorded baseline numbers; proofs + corpus
stay green.

### Phase 4 — lenet-rs (async Rust bindings)

Separate repository: `-sys` crate over the (by then extended) C API with
hand-written externs and `build.rs` linking `liblenet.a`; sans-I/O API maps
to a tokio driver (one task owns the host: socket + `lenet_host_service(now)`
+ poll loops, scheduling ticks via the host's timer deadlines — the same
primitive the replay uses, exposed to the driver as `Host.nextDeadline`);
builder-style API, event stream. Threading contract: one host,
one thread (or external serialization).
**Exit criteria:** async interop test vs real ENet from Rust.

## Explicitly out of scope

- **Compression** (ENet's optional PPM range coder): descoped — see
  DESIGN.md 1.4. Compressed datagrams are rejected.
- **Sequence-wrap golden traces** (~65k commands per channel needed; the
  wrap logic is exercised by proofs instead).
- **Packet loss / reordering chaos scenarios** (recording is
  non-deterministic; the replay needs determinism).
- **Resource-exhaustion parity** (e.g. fragment-assembler growth on rejected
  fragments): documented, not tested; ENet has similar pressure points.

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
