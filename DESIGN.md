# Lenet: Architecture & Design Specification

`Lenet` is a modern, formally verified reimplementation of the ENet protocol in Lean 4, providing 100% wire compatibility with ENet 1.3.x while delivering a robust, ergonomic API suitable for both native Lean applications and external async runtimes (such as async Rust via Tokio/sans-IO FFI).

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

### 1.3 Ergonomic, Type-Safe API
- Replace C's untyped bitmasks and `void*` fields with strongly typed Lean 4 data structures (`ChannelId`, `Packet`, `PeerState`, `CommandBody`, `Event`).
- Idiomatic high-level API with typed channels, streams, and event handlers on top of the sans-I/O core.

### 1.4 Wire Compatibility
- Binary wire layout, packet headers, command structures, PPM range-coder compression, CRC32 checksums, and timeout backoff curves remain strictly compatible with standard ENet 1.3.18.


NO PANICS should be possible within the library. Any possible error should be an exception and returned to the caller.