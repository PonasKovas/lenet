# Lenet: Architecture & Design Specification

`Lenet` is a modern, formally verified reimplementation of the ENet protocol in Lean 4, providing wire compatibility with ENet 1.3.x while delivering a robust, ergonomic API suitable for both native Lean applications and external async runtimes (such as async Rust via Tokio/sans-I/O FFI).

---

## 1. Core Principles

### 1.1 Pure Sans-I/O Protocol Engine
- **No Direct Sockets or Clock Syscalls in the Core**: The core protocol engine is a pure state machine:
  $$\text{State} \times \text{InputEvent} \to \text{State} \times \text{OutputActions}$$
- The host application (Lean 4 async task, Tokio/Rust runtime, C driver) owns the UDP socket and event loop, passing timestamps and datagrams into Lenet and executing returned transmission actions.

### 1.2 Formally Verified Correctness
- Lean 4 serves as both the implementation language and proof assistant.
- Invariants to be proved:
  - **Codec Roundtrip**: $\forall x, \text{decode}(\text{encode}(x)) = \text{ok}(x)$.
  - **Memory & Bounds Safety**: No out-of-bounds indexing or integer overflows on untrusted input.
  - **Reliable In-Order Delivery**: Channel sequence numbers and sliding windows guarantee exactly-once, in-order packet delivery without deadlocks.
  - **Reassembly Safety**: Fragment reassembly logic is memory-safe and cannot be tricked into buffer overruns by malicious offsets/counts.
  - **Throttling** and other features correctness.
- Which invariants matter most is informed by the compatibility corpus (`test/`) - the corpus shows what real ENet interop actually exercises.

### 1.3 Ergonomic, Type-Safe API
- Replace C's untyped bitmasks and `void*` fields with strongly typed Lean 4 data structures (`ChannelId`, `Packet`, `PeerState`, `CommandBody`, `Event`).
- Idiomatic high-level API with typed channels, streams, and event handlers on top of the sans-I/O core.

### 1.4 Wire Compatibility
- Binary wire layout, packet headers, command structures, CRC32 checksums, and timeout backoff curves remain strictly compatible with standard ENet 1.3.18 (pinned revision, see `TODO.md`).
- **Compression is explicitly out of scope** (descoped): ENet's optional order-2 PPM range coder is not implemented. Compressed datagrams are rejected. Rationale: the feature is opt-in and rarely used in ENet deployments, the wire format is ENet-specific (no library exists; a decoder must mirror ENet's encoder model exactly), and a faithful port of the pointer-heavy C coder is a large task with no current demand. Revisit only if a consumer needs it.

### 1.5 Correctness Over Compatibility (in stone)

Lenet's primary objective is always **correctness and robustness**. Compatibility with ENet is a goal, never an excuse:

- **If a divergence is caused by a bug in original ENet, fix it in Lenet. Never mirror the bug.**
- Every observed divergence is triaged into one of three classes:
  - **lenet bug**: Lenet deviates where ENet is right -> fix Lenet.
  - **enet bug**: ENet behaves incorrectly -> implement the *correct* behavior in Lenet, and record the divergence and its rationale in `test/README.md`.
  - **don't-care**: behaviorally invisible to interop -> mask it in the comparison with a written rationale.
- The triage decision is always documented, never silent.

### 1.6 Quality Gates (enforced before/alongside formal verification)

- **NO PANICS** anywhere in the library: no panicking constructs (`get!`-style indexing without proofs, `unsafe`, partial pattern matches, unguarded arithmetic). Any possible error is an exception returned to the caller. This gate is a precondition for the no-panics formal proof and is checked in the code-quality phase.
- The core is total by construction: every function terminates on every input.

---

## 2. Project Roadmap

The living roadmap (phases, exit criteria, task state) is maintained in `TODO.md`. Phase order: compatibility -> code quality -> formal proofs -> performance -> `lenet-rs` (async Rust bindings).

---

## 3. Repository Layout

- `Lenet/` - the sans-I/O protocol core (pure Lean)
- `csrc/` - the C API distribution incl. `include/lenet.h` (static-only; Lean runtime archive is not built with `-fPIC`)
- `test/` - ENet compatibility harness: golden-trace recorder (`c/harness.c`), replay diff (`test/Replay.lean`), live interop (`c/interop.c`); see `test/README.md`
- `TODO.md` - roadmap and decided constraints
