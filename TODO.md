# Open work

**Not done: the audit below found real bugs (2026-09-27).** The two tasks
further down pass locally, both ways round; the lossy and clock-wrap steps
are in CI but have not run there yet (nothing pushed).

## Audit (2026-09-27)

A full read of the engine, wire codec, C API, `Lenet.Net`, proofs, tests
and docs. Worked through in order; each item says what was done.

### Bugs

1. **Unbounded memory from held-back packets.** A fragment claiming 1 of
   1 with a 32 MB total and 1 byte of data completes at once into a 32 MB
   zeroed packet. Staged ahead of the frontier, it leaves the assemblers,
   so `maximumWaitingData` no longer counts it; staging is capped by count
   only. 40 such fragments (1160 wire bytes) held 1.5 GB. ENet charges
   every queued incoming packet to `totalWaitingData`.
   **Done:** the budget counts staged packets (`Peer.heldBytes`,
   `handleHeldData`), except the packet or set the channel delivers next;
   a set completes only once its fragments carried its total
   (`bytesFit`); assemblers store what arrived and build the packet at the
   end, and the sets under way claim at most 65536 fragments. Proofs
   updated, five unit tests, test/README.md triage. Bench: small packets
   within noise, 4096-byte fragmented ~5% slower (more allocations), large
   packets unchanged.
2. **C API: one outgoing buffer per thread, not per host**
   (`lenet_capi.c` `g_out_buf`). lenet-rs promises per host and its `Host`
   is `Send`, so two hosts on a thread, or a task moved between threads,
   read the wrong or freed bytes.
   **Done:** `lenet_host` is now a C struct holding the Lean host and the
   last polled datagram, so `data` points into that host's own bytes (no
   copy either); `check.c` polls two hosts and checks each keeps its own.
3. **`Lenet.Net.transmit` rethrows the first send error.** State is
   already advanced, so the rest of the batch is lost, and a CONNECT
   spoofed from port 0 makes every `service` throw until that peer times
   out.
   **Done:** a failed send is counted (`Endpoint.socketErrors`) and lost,
   and the rest of the batch goes; datagrams from port 0 are dropped.
   `test/Net.lean` sends to port 0 alongside a real packet.
4. **Receive cost grows with what is staged.** `drainContiguousLoop` is
   O(n²) (`findIdx?` + `eraseIdx` per packet); each push onto a stage
   copies the array while the peer's channel array still shares it;
   `fragmentSetLive` scans the stage for up to 32 assemblers per data
   command.
   **Done:** staged packets live in hash maps by sequence number
   (unreliable ones by the reliable command they wait for, then their own
   number), with byte and count totals kept alongside; the drain looks up
   the next number, what the frontier jumps over is erased by range
   (`Channel.eraseAfter`), and `receiveOnChannel` takes the channel out of
   the peer so the maps change in place. Staging 16000 packets behind a gap
   took 45 s under `lean --run`, now 0.4 s, linear. Proofs moved to the
   maps (`Staged`, `Keyed`, `eraseAfter_get`). Bench: small packets 3-6%
   slower, within reach of the noise; fragmented unchanged.
5. **A freed slot keeps its queue.** `throttleConfigure` (and friends) on
   a free slot queue a command that the next `connect` or incoming CONNECT
   sends ahead of CONNECT / VERIFY_CONNECT, and the handshake fails.
   **Done:** `throttleConfigure` leaves a free or zombie slot alone (the
   only call that queued there; it also left its throttle settings for the
   next connection). Unit test.
6. **`lenet_host_poll_event` with a NULL buffer loses the packet.** The
   header says NULL learns the size, but the event is popped.
   **Done:** a receive event whose payload does not fit is kept and the
   call returns -2 with the size needed; the next call returns it again.
   Pinned in `check.c`. lenet-rs must handle -2 (see "API and bindings").
7. **Datagram parsing copies the rest of the buffer after every command**
   (O(n²) in the datagram, before any peer or session check).
   **Done:** each command is read at an offset into the datagram; proofs
   follow (`go_cmdsBytes` now takes a prefix). Unit test parses 16000
   PINGs.
8. **With checksums on, datagrams can be MTU + 4** (the checksum field is
   not counted when packing). `Lenet.Net` receives 4096 bytes, so at MTU
   4096 such a datagram is cut short and dropped. ENet has the same bug.
   **Done:** an empty datagram counts 8 bytes with checksums on
   (`PackState.headerSize`). Unit test fills a 576-byte datagram exactly.
9. **`csrc/Makefile` picks the first installed toolchain**, not the one in
   `lean-toolchain`.
   **Done:** `lean --print-prefix` from the repo root. (The archive now
   also merges `libStd`, which the hash maps of item 4 need.)
10. **`liblenet.a` exports every bundled symbol** (mimalloc, libuv, GMP,
    OpenSSL, libc++abi, libunwind, the Lean runtime), so apps linking any
    of those can clash.
11. **Connect IDs seeded from `time(NULL)`** in the C API: hosts made in
    the same second pick the same IDs.
12. **`lenet_host_send` / `broadcast` copy before the size check**, so a
    huge length aborts on out-of-memory instead of returning -1.
13. **`Lenet.Net` swallows receive errors** and can spin at full CPU on a
    dead socket.
    **Done** with 3: a failed receive is counted and its round sleeps out
    its wait. (No test: a receive error is hard to provoke on loopback.)
14. **Smaller hot-path costs:** the unsequenced window is copied on every
    accepted packet (shared with the peer); each ACK erases from the
    in-flight array; `packOutgoingCommands` rebuilds the whole queue every
    service; the bandwidth throttle's `contains` in a fold is O(P³) worst
    case.

### Tests that check less than they say

15. The replay compares fragment payloads by length, other payloads by
    their first 64 bytes, never headers; test/README.md says only
    `connectID` is masked.
16. The lossy runs never require unreliable or unsequenced packets to
    arrive, and `NetStream` ignores `send` results.
17. `net-interop` accepts a timeout as the far end's clean disconnect.
18. `make -C test traces` ignores failed recordings; `record` re-records
    only clock offset 0.
19. `interop` `multip` never checks client 2's bytes.
20. `test/Net.lean` has tight wall-clock bounds; the workflow has no
    `timeout-minutes`.

### Proofs that claim more than they prove

21. `run_wf` / `run_span`: `Op` leaves out `disconnectNow`, `resetPeer`,
    `pollOutgoing` and the checksum toggle, all exported.
22. Resource bounds are per step, not composed over whole runs.
23. `nextDeadline_earliest` only says the fold finds the minimum of the
    list it folds; nothing says `service` before the deadline does no
    work.
24. `checkAndAdd_idempotent` covers the next check only; DESIGN says
    "always".
    **Done (claim):** DESIGN now says what is proven. That a group stays
    rejected while the window slides is not proven.
25. `addFragment_completion_sound` does not tie the released data to the
    fragments written.
26. `Panic.lean`'s division list is stale; its claim that library code
    panics only through a `…!` name is false (`Array.get!Internal`).
    **Done:** the audit now follows the library code Lenet uses,
    transitively, and fails on any name with a `!`, except four that only
    instance fields mention (listed with the reason); the division list is
    current and the lemmas say they are facts about each guard.
27. `wire_roundtrip` and `nextDeadline_earliest` use `bv_decide` axioms;
    DESIGN does not say so.
    **Done:** DESIGN, "What the proofs trust".
28. `Connection` models fragment sets sent whole; the real receiver ACKs
    each fragment (already listed under "Proofs" below).

### Docs and repo

29. No LICENSE (needs the owner's choice).
30. Undocumented: the first host ignores SIGPIPE process-wide and starts
    two threads; `lenet_host_flush` produces datagrams too; the C build is
    Linux / GNU binutils only.
31. Stale docs: "seven windows" in test/README.md, "near-MTU" `send_c2s`,
    "one fragmented", a list of undecided divergences that does not exist,
    TODO's "What is left" and "big gap left", three different lossy-wrap
    run times, "What is compared" in test/README.md.
    **Partly done:** all but the run times and "What is compared" (with
    item 15).

Done: full ENet 1.3.x interop except compression (21 golden-trace
scenarios, each recorded at three clock starts, and 12 live interop
scenarios pass), Lenet against ENet over lossy links and through every
wrap, unit tests, a lossy-link benchmark, the C distribution, and the
proofs listed in [DESIGN.md](DESIGN.md#what-is-proven).

## The last two tasks (decided 2026-09-27, both done the same day)

Two tasks, then the engine is done. Everything else in this file is
history, notes, or explicitly not planned (see the end of this section).

Why these two: the bugs of the last sessions (retransmissions leaking
in-transit bytes, sender windows never occupied, the fragment assembler
leak, the ACK that lost a packet) all lived in the loss and resend paths,
and every test against real ENet runs on a clean link. The lossy benchmark
is Lenet against Lenet only, so it cannot catch a divergence from ENet.

### 1. Interop with real ENet over a bad link (done 2026-09-27)

Done: `make -C test lossy-interop` (in CI with the light and burst
profiles), `c/proxy.c`, `c/stream.c`, `NetStream.lean`; see test/README.md,
"Lossy-link interop". No divergence found in long runs both ways round.
Two changes from the plan below, both because ENet fails against itself
otherwise (measured with `make -C test lossy-enet`): heavy is 1 in 5 each
way (about a third of round trips) with raised timeouts, and stays out of
CI; bursts come every 2-4 s with no random loss on top. The plan as it was:

- A small UDP proxy (C, in `test/c/`, or Lean over `Std.Async.UDP`) that
  sits between the two processes of `make -C test net-interop` and drops,
  duplicates, reorders and delays datagrams. Driven by a seed so a failure
  replays. Loss rates worth running: light (1 in 20), heavy (1 in 3), and
  bursts (drop everything for a few hundred ms, which also exercises
  timeouts without disconnecting).
- Both ways round: Lenet client against ENet server, and ENet client
  against Lenet server (`test/c/echo.c` is the ENet side today).
- Traffic: reliable, fragmented reliable (several fragment sets in flight
  at once), unreliable, unreliable fragments, unsequenced, on more than one
  channel. Check on both ends: reliable packets arrive once each, in order,
  none missing; unreliable ones arrive at most once and in order;
  nothing is left in flight at the end; the connection ends with a clean
  disconnect, not a timeout.
- Add it to CI next to `net-interop` (short runs), with a longer run
  available locally.
- For every divergence: triage in test/README.md ("Divergence triage"),
  fix Lenet or record the ENet bug, and pin it with a unit test.

### 2. Long runs through the wraps (done 2026-09-27)

Done: `make -C test lossy-wrap` (94500 packets of each kind per channel,
two fragment sets straddling the reliable wraps) and `make -C test
lossy-clock` (both clocks start 10 s before 2^32, bandwidth limits on),
light and burst loss, both ways round, two seeds each; see test/README.md.
Both are local only (a minute or more each way); CI runs a short clock
wrap. `Lenet.Net.Config.clock` sets an endpoint's clock. No divergence
found. The plan as it was:

- More than 65536 reliable packets per channel through the proxy of task
  1, against ENet both ways, so the 16-bit sequence numbers wrap for real
  (the reliable and unreliable counters, the receive window, staging and
  the sender's windows across the wrap). Include fragmented packets that
  straddle the wrap.
- The 32-bit millisecond clock wrapping during a live connection: start
  Lenet's clock a little before 2^32 (the driver owns the clock, so the
  test can offset it) and run long enough to cross it under loss, so RTT,
  retransmission timeouts, pings and the bandwidth throttle all cross it.
- Keep a short version in CI if it runs in under a minute; otherwise
  local only, with the command in test/README.md.

### Done means

Both tasks pass both ways round and in CI, every divergence found is
triaged and fixed or recorded, and the checks listed under "Checks before
each commit" pass. Then update this file to say the engine is done.

### Not planned (decided, not forgotten)

- Compression (DESIGN.md, "Scope decisions").
- More proofs. The fragment-by-fragment connection proof and the
  two-host proof from `Host.create` (under "Proofs") would cost far more
  than they find; they stay listed as known limits of what is proven.
- A fuzzer (DESIGN.md). More loss-free trace scenarios.
- Performance work and a comparison with C ENet: nice to know, not
  blocking. The shared library waits on Lean shipping a `-fPIC` runtime.

## Next step (handoff, 2026-09-27)

Done this session:

- **Sender-side window span proof** (`Proofs/Window.lean`). `run_span`:
  from `Host.create`, after any sequence of operations, the reliable
  commands in flight on a channel lie within seven windows ending at the
  last one sent. Along the way: first sends go out in sequence order and
  the window counters count exactly what is in flight. `SpanInv` is the
  per-peer invariant; every writer of the peer's queues and channels keeps
  it. `disconnectNow_inv` and `resetPeer_inv` cover the two calls `Op`
  leaves out.
- Two code changes the proof needed, both the same behavior on every
  reachable state: `removeSentReliableCommand` erases the index it found
  (was `find?` then `erase` by value), and a reliable command too big for
  any datagram sets `reliableHeld` like every other deferral (fragments are
  sized to fit, so it does not happen).
- Proof hazards worth knowing (from earlier sessions, still true): when a
  value must stay unshared, `swapAt` alone is not enough, since the
  compiler may sink its write (`takeAt` is `@[noinline]` for that); and
  never let the kernel compare `h` with a host whose `randomSeed` was
  advanced (`h.randomSeed + 0x6D2B79F5`): it unfolds the addition one
  successor at a time and the build gets killed. Go through
  `random_peers`.
- Lean tips from this one: a structure literal split over lines must keep
  its fields aligned, or the parser stops with "expected '}'"; and `split`
  picks the outermost `if`, so an `if` inside another's condition needs
  `by_cases` or a lemma over the general shape (`scanStep`, `ite_map_inv`).

- **Typed Lean API** (`Lenet/Net.lean`, library `LenetNet`): an
  `Endpoint` runs a host over a `Std.Async.UDP` socket with ENet's calls
  (`connect`, `send`, `service timeout`, ...). Connections are
  `PeerHandle`s (slot plus a generation), dead once their connection ends.
  `test/Net.lean` (exe `net`, in CI) runs two endpoints on 127.0.0.1.
  Found on the way: `Selectable.tryOne` on `recvSelector` never finds a
  datagram, so `Endpoint` keeps one low-level receive outstanding and
  checks whether it resolved; a sleep registers one waiter, woken by that
  receive's single continuation.

- `make -C test net-interop` (in CI): `Lenet.Net` in one process against
  an ENet echo peer (`test/c/echo.c`) in another, both ways round.

- **Channel handles** (later the same day): see API and bindings below.
  `test/Net.lean` checks a server's channel limit shows up on both sides'
  connections and that packets echo back on the channel they came in on.

- **Receiver-side delivery proof** (`Proofs/Delivery.lean`, later still).
  An honest sender's reliable packets are a `Stream` (message `i` spans
  `span i` sequence numbers, unwrapped). Fed any arrivals that each `Fits`
  (no more than 9 windows behind the frontier, fewer than 16 ahead), a
  channel hands out exactly messages 0, 1, 2, ... once each, in order
  (`feed_spec`), and the next message's arrival always delivers it
  (`step_next`). `receiveReliableAndRelease_spec` covers the peer's receive
  path with unreliable packets mixed in. `admitted_iff` (the receive gate
  unwrapped) and `drain_spec` are the reusable pieces. To see a proof
  depends on code, break the code and stub any earlier proof that fails
  first with `sorry`, or Lake never gets to the new one.

- **Found and fixed: an ACK could lose a reliable packet** (ENet too). The
  receiver ACKed a reliable command it dropped for being one window past
  its receive window, and the sender can be that far ahead: seven windows
  in flight, the frontier just before the oldest. Lose the first command
  of a window while the sender goes six windows on, and the command
  opening the seventh is retired, never delivered, and the channel stalls
  behind it for good (repro: 30000 empty reliable packets, one lost
  datagram). Now `Peer.handleCommand` withholds that ACK
  (`Peer.tooFarAhead`, `Channel.isReliableTooFarAhead`); two unit tests
  pin it, and test/README.md records it as an ENet bug not copied.

- **Connection proof** (`Proofs/Connection.lean`): `Delivery` joined to
  `Window` over one channel. The model runs the sender's window code
  (`nextReliableSequenceNumber`, `canSendReliable`, acquire/release) and
  the receiver's `receiveReliableSpan` plus the new ACK rule, with a
  network that loses, duplicates, reorders and delays, bounded only by
  "lost once the sender made more than `D ≤ 12288` first sends since".
  From the start: every arrival `Fits` (`run_fits`), delivery is messages
  0, 1, 2, ... in order (`run_out`), a retired command's message is
  delivered or staged (`run_retired`), and the next message's copy
  delivers it (`deliver_next`). The key step is `sent_window`: the
  receiver's frontier is at most one before the oldest command in flight,
  so the last one sent is at most six windows past the frontier's window
  (seven before the sender-side fix below). `Delivery.step_spec` is the arrival step with what that needed
  (staged messages stay staged, nothing made up, an in-window arrival is
  received); `Inv` now keeps staged entries inside the receive window.
  Breaking `isReliableTooFarAhead` breaks the proof (`tooFarAhead_of`).
  Lean tips: there is no Mathlib, so no `by_contra` (use
  `Nat.lt_of_not_le fun h => ...`); `Inv` alone resolves to another
  namespace's `Inv` here, so write `Delivery.Inv`; and a staged entry
  names its message only within a wrap, so facts about "the message of
  this entry" carry the index with them (`step_spec`'s `P`).

- **Sender-side half of the ACK fix** (later still): `canSendReliable`
  now holds the first command of a window until the window six back is
  empty too (range of 11 windows, ENet 10), so a Lenet sender keeps six
  windows in flight and never gets past an ENet receiver's window.
  `Window`'s span is now five windows and a part; `Connection` gains
  `run_ahead_admitted` and no longer needs the receiver's ACK rule (which
  stays, as the defense against ENet senders). The host-level unit test
  now checks the sender holds seq 28672 back while seq 4096 is lost.

- **Task 1 done** (later the same day): Lenet against ENet through a lossy
  proxy, both ways, see above and test/README.md. `Lenet.Net.PeerInfo`
  now also reports what is queued and in flight. Tools for task 2: the
  stream programs take any round count (`ROUNDS=`, `PER=`), print a stall
  report after 2 s without a packet, and the proxy logs every datagram
  with `PROXY_LOG=`. A decoder for that log is quick to write (ENet header,
  then commands with their fixed sizes plus data lengths); the one used
  here did not stay in the repo.

- **Task 2 done** (later still): the stream programs send `PER` of every
  kind per round (so channel 2's unreliable counter and the unsequenced
  group wrap too), hold new rounds while more than 1000 commands are
  queued (without that the Lean program fell behind, then sent hundreds of
  rounds without servicing and the peer timed out), and take `clock <ms>`
  and `bw <bytes/s>`. `Lenet.Net.Endpoint.now` now takes the endpoint.

Suggested next: push and watch the new CI steps (the lossy runs have only
run on this machine). After that, nothing is planned; see "Not planned".


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
as bugs show where the corpus is blind. ENet under loss and across the
wraps, the gap this used to name, is covered by tasks 1 and 2.

## Proofs

- Done: the whole connection over one channel (`Proofs/Connection`).
  Not planned any further (see "Not planned" above); the known limits of
  what is proven are:
  - Fragments one by one. The model sends and resends a fragment set
    whole, and the receiver ACKs its fragments once the set is complete;
    the real receiver ACKs each fragment as it arrives and the assembler
    holds it. Needs the assemblers in the invariant ("a retired
    fragment is in an assembler, or its set is delivered or staged").
  - From `Host.create` on both ends. The model's sender and receiver are
    channels, not the peers `Window` and `HostEvents` reason about; a
    simulation from peer operations to `Link` operations (first sends in
    order is `SpanInv.consecutive`) would close that. The handshake and
    reconnects need care: a slot's session number is two bits, so a stale
    datagram from an earlier connection can pass `acceptsDatagram`.
  - The delay bound is in first sends, not time. That is the natural unit
    here (like TCP's segment lifetime); task 1's proxy should keep its
    delays under it (a datagram outlived by three windows of first sends
    is lost).

## Performance

Baseline (`./.lake/build/bin/bench`, two runs, i5-8350U @ 1.7 GHz, Lean
4.33.1, 2026-09-26 after the one-pass packing; run-to-run noise is about
10%, and this machine ran ~25% slower than usual all day, so compare
against a fresh run of the old code, not these numbers):

| scenario               | pkts/s | ns/pkt |
|------------------------|--------|--------|
| reliable 1200B         | ~280k  | ~3550  |
| unreliable 1200B       | ~480k  | ~2080  |
| unsequenced 1200B      | ~290k  | ~3480  |
| reliable 4096B (frag)  | ~62k   | ~16200 |
| unrelfrag 4096B (frag) | ~88k   | ~11400 |

Service tick: idle pair ~3.1 µs, loaded (64 reliable sends) ~226 µs. One
reliable packet end to end: 1 MB ~5 ms, 4 MB ~24 ms, 16 MB ~230 ms.

Measured back to back on the same machine, the one-pass packing (every
datagram of a service in one scan of the queue, where the scan per
datagram was quadratic in the queue) took reliable 1200B from ~214k to
~285k, the loaded tick from ~300 to ~225 µs, and 16 MB from 2.5 s to
0.23 s; in-place reassembly took 4 MB from 3.3 s to 0.17 s before that.

What the profile shows now: most time is allocation and freeing, spread
thin. Lean updates an array or record in place only while one reference
holds it, so a value read out of a container that still holds it, or kept
alive for an error branch, gets copied on its next change. To find such a
copy, wrap the value in `dbgTraceIfShared "tag" x` for a moment and count
the messages a bench run prints (that is how the reassembly copies were
found). Known costs left:

- `Peer.enqueue` copies the channel record on each send. Removing that
  copy with an out-of-line swap made the bench 1-4% slower, not faster.
  `Peer.receiveOnChannel` does take the channel out (`takeAt`), since the
  staged maps must change in place however many packets are staged; the
  cost is within the noise.
- Fragmented sends copy each fragment out of the packet (`extract`).
- `Datagram.parseCommands` copies the rest of the datagram after every
  command, but that is 0.3% of the profile: not worth a cursor rewrite.

## API and bindings

- **Typed Lean API**: done (`Lenet.Net`). Channels are typed too: the
  connect event hands out a `Connection` (handle plus the channel count
  both sides agreed on) and `send` takes a `conn.Channel`, a
  `Fin channelCount`. No numeric literal for it on purpose, since `Fin`'s
  wraps around the count: `conn.first`, `conn.channel? i`, `conn.channels`
  or the channel a packet came in on. `broadcast` still takes a `UInt8`
  and skips peers without that channel.
- **ENet API parity** (2026-09-26): disconnect_now, peer reset, ping,
  ping interval, bandwidth limit, channel limit, flush and a peer-info
  getter now exist in Lean (`Host.*`) and C (`lenet.h`).
- **lenet-rs** (async Rust bindings over the C API) lives in its own
  repository. Anything it needs from the C API gets added here first.
  Found in the audit, to fix there: its receive buffer is 4 MB
  (`MAX_RECV_PAYLOAD`, on the stale belief that the engine caps packets at
  `maximumMtu * 1024`), but packets go up to 32 MB. It used to truncate
  them silently; since the C API change it gets -2 from
  `lenet_host_poll_event` and must grow its buffer to `*payload_len` and
  call again. Its per-host `poll_outgoing` promise now holds.
- **Shared library** once Lean ships a `-fPIC` runtime.
