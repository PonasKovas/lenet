# Remaining goals

State at end of session: M1 golden-trace replay 16/16 PASS, M2 live interop
7/7 PASS, C API distribution builds and self-checks, CI wired up
(`.github/workflows/lean_action_ci.yml`). All on `master`.

## CI notes

- ENet is cloned in CI at the pinned revision the golden traces were
  recorded against: upstream `lsalzman/enet` @ `5a9c537fd464b3c6d3c55e1d3bd47588faf71b42`
  (= v1.3.18-17). Re-recording traces is only needed when scenarios change,
  and must be done locally (`make -C test traces`) — recording is not
  byte-reproducible (real clock + ENet randomness), the replay tolerates
  this because it replays committed traces.
- Watch the first CI run for runner-specific issues; locally-verified
  fixes were: shim compiles with plain `$(CC)` (leanc's bundled clang
  lacks system headers), lake must run with `-d ..` from `csrc/`.

## Test completeness (base behavior is covered; gaps below, cheap first)

1. Tighten M1 replay: unmask session IDs in `maskCmd` — negotiation is now
   implemented, values are deterministic (client sends 0xFF/0xFF, server
   negotiates via `(x+1) & 3`), so byte-verify them.
2. Session-ID validation on receive: ENet drops datagrams whose header
   session != `peer->incomingSessionID` (protocol.c peer lookup); lenet
   accepts anything. Add the check + a hostile-input scenario.
3. Checksum: crc32 exists (`Lenet/Checksum.lean`) but is not wired into
   `Datagram.encodeWith`/`decodeWith`. Wire compute/verify, then re-record
   one scenario with checksum enabled on both C hosts.
4. Feature-completion scenarios (mostly test-side): nonzero bandwidth
   configs + `windowSize` negotiation (lenet currently ignores windowSize
   on BANDWIDTH_LIMIT receive - C recomputes it), multi-peer + broadcast,
   unreliable-fragment delivery, `disconnectLater`.
5. Robustness fuzz: seeded random/truncated datagrams into
   `Host.handleDatagram`, assert no panics (design rule). Goes in the
   replay exe, no new deps.
6. Compression: `Compress.compressBytes`/`decompressBytes` are stubs.
   Implement the real order-2 PPM range coder, then add a compression
   interop scenario (`enet_host_compress_with_range_coder` on both sides).
   Largest remaining feature chunk.
7. Optional M3 twin differential: parallel C-server vs lenet-server fed
   identical inputs, byte-diff outputs with masks.

## Next major goals (the original reason for all this)

- **Async-Rust wrapper**: `-sys` crate over `include/lenet.h` (bindgen or
  hand-written externs), `build.rs` linking `csrc/build/liblenet.a`;
  sans-I/O API maps directly to a tokio driver (one task owns the host:
  socket + `lenet_host_service(now)` + poll loops). Threading contract:
  one host driven from one thread (or serialize externally).
- **Formal proofs in Lean**: codec roundtrip, reassembly bounds safety,
  no-panics invariant, reliable in-order delivery. The compatibility test
  corpus tells which invariants matter for real interop.

## Decided constraints (do not relitigate)

- Golden traces are pinned to ENet `5a9c537` (v1.3.18-17); bumping enet
  requires re-recording traces (`make -C test traces`) and a diff review.
- Shared library is impossible with a stock Lean toolchain (leanrt built
  without -fPIC); the C distribution is static-only by design.
- Test philosophy: lenet must interop, not bit-clone ENet. Divergences are
  triaged as lenet bug / enet bug (whitelist w/ reason) / don't-care (mask
  w/ rationale in `test/README.md`).