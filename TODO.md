# Roadmap & Working Notes

Lenet is a sans-I/O reimplementation of the ENet protocol in Lean 4, with a
plain C API distribution. This file is the living plan: what is done, what is
next, and the decisions that are not up for relitigating. New to the project?
Read `DESIGN.md` (architecture + principles) and `test/README.md` (how the
compatibility testing works), then come back here.

## How the pieces fit

- `Lenet/` — the sans-I/O core. Pure state machine: datagrams in, events +
  outgoing datagrams out, time supplied by the caller.
- `csrc/` + `include/lenet.h` — the C distribution (`liblenet.a`), built from
  the compiled Lean core. Static-only by design.
- `test/` — the compatibility corpus (see `test/README.md` for the full
  picture):
  - `c/harness.c` records golden traces from *real* ENet (pinned revision)
  - `test/Replay.lean` (`lake build replay`) replays them through Lenet and
    diffs events + outgoing commands against ENet's
  - `c/interop.c` runs Lenet (via FFI) against real ENet over live UDP
- CI (`.github/workflows/lean_action_ci.yml`) runs: build, replay (Tier 1),
  C API check (Tier 1), live interop (Tier 2, clones ENet at the pin).

## Current state

- 14 golden-trace scenarios, all roles PASS (connect, send_c2s, send_s2c,
  frag, disc_client, disc_server, idle, timeout, checksum, bandwidth, unfrag,
  disclater, multip, inject).
- Live interop: 7/7 PASS. C API distribution builds and self-checks.

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

**Pass B:**
3. Scenarios: `multichannel` (8 channels), `dup` (DUP action re-sending a
   captured datagram: duplicate reliable/ACK idempotency), `reconnect`
   (disconnect -> reconnect, slot reuse, state reset), `retimeout`
   (client-side timeout), `mtu576` (needs an MTU parameter on `Host.create`,
   clamped to [576, 4096]), `throttleconf` (`enet_peer_throttle_configure`).
4. Interop extensions: FFI/C API additions (`lenet_host_enable_checksum`,
   `lenet_host_disconnect_later`, MTU on create) + interop scenarios
   `checksum`, `bandwidth`, `disclater`, `multip`, `unfrag`.

**Exit criteria:** ~19 scenarios all PASS; interop ~12/12; DESIGN.md
constraints recorded; divergence triage documented.

### Phase 1 — Code quality

Idiomatic Lean pass over `Lenet/`: eliminate imperative leftovers from the C
rewrite (mutable-accumulator patterns, `getD`-defaults masking logic, `Except
String` -> typed errors), total-by-construction patterns.
**Exit criteria:** zero warnings; zero panicking constructs (`get!`, `unsafe`,
partial matches, unguarded arithmetic) anywhere in `Lenet/` — this is the
hard gate; style conventions written down.

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
+ poll loops); builder-style API, event stream. Threading contract: one host,
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
