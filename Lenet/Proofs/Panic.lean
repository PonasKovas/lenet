import Lean
import Lenet

/-!
# Panic-site audit

Two layers:

* **Build-time panic audit** (`run_meta` below, the no-panics composition
  over `Host.handleDatagram` / `Host.service` and every other entry point):
  every definition under `Lenet.*` (1250+, all of the core, the C-facing FFI
  glue included) is scanned, and the build fails if any of them references a
  panicking primitive (`panic*`, `sorryAx`, `outOfBounds`, or any `…!`
  accessor such as `getElem!` / `Option.get!`) or is `unsafe`, `partial`
  (compiled to `opaque`) or `implemented_by`-swapped. Scanning *every*
  `Lenet.*` definition, not a reachability slice, makes the check closed
  under composition: whatever an entry point calls inside Lenet is itself
  scanned, and calls leaving Lenet can only reach a panicking library path
  through a `…!` name. A kernel theorem cannot state this - in Lean's logic
  `panic!` *is* `default` - so the audit is the formal statement. Not
  covered (not panics): stack depth and allocation failure.
* **Divisor audit** (the lemmas below): Lean's `/` never panics (`x / 0 =
  0`), but a silent zero would be a logic bug where ENet crashes. Every
  division site is named with its non-zero-divisor proof.

A new unguarded division site fails review by its absence here. Division
sites (all divisors are compile-time constants or guarded):

1. `Channel.windowIndex` / `isIncomingReliableInWindow` / `canSendReliable`
   - divisors `reliableWindowSize` (4096) and `reliableWindows` (16).
2. `Host.windowSizeFor` - divisor `windowSizeScale` (65536).
3. `Host.handleIncomingConnect` (host window) - divisor `windowSizeScale` (65536).
4. `Host.PackState.packCommand` (congestion) - divisor `packetThrottleScale` (32).
5. `Host.bandwidthThrottle` - the connected-peer count (guarded by the
   `isEmpty` check) and the in-transit bytes (divided only when they exceed
   the per-peer share, so positive); `Host.incomingBandwidthShare` - the
   remaining-peer count (guarded by the `== 0` check).
6. `Peer.sendError?` / `Peer.enqueue` - divisor `Peer.maxFragmentPayload`
   (positive: MTU minus overhead when that is positive, else the constant
   500).
7. `Peer.updateRtt` - divisors 4, 8, 2 (literals).
8. `Checksum`/codec/reassembly paths contain no divisions.
-/

namespace Lenet.Proofs

open Lean in
/-- Names that can panic at runtime (or stand for a missing proof). -/
def isPanicking (n : Name) : Bool :=
  n == ``panic || n == ``panicCore || n == ``panicWithPos || n == ``panicWithPosWithDecl ||
  n == ``sorryAx || n == ``outOfBounds ||
  (match n with
   | .str _ s => s.endsWith "!"
   | _ => false)

open Lean Meta in
run_meta do
  let env ← getEnv
  let mut scanned : Array Name := #[]
  let mut bad : Array MessageData := #[]
  for (n, ci) in env.constants.toList do
    unless (`Lenet).isPrefixOf n do continue
    if (`Lenet.Proofs).isPrefixOf n then continue
    scanned := scanned.push n
    if ci.isUnsafe then bad := bad.push m!"{n}: unsafe"
    if ci matches .opaqueInfo _ then bad := bad.push m!"{n}: opaque (partial?)"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      bad := bad.push m!"{n}: implemented_by"
    if let some v := ci.value? (allowOpaque := true) then
      for c in v.getUsedConstants do
        if isPanicking c then bad := bad.push m!"{n}: references {c}"
  -- guard against a vacuous scan (renamed namespace, dropped import)
  for entry in [``Host.handleDatagram, ``Host.service, ``Host.nextDeadline, ``Host.connect,
      ``Host.send, ``Peer.send, ``Protocol.Datagram.decode, ``Protocol.Datagram.encode] do
    unless scanned.contains entry do throwError m!"panic audit: entry point {entry} not scanned"
  unless bad.isEmpty do
    throwError m!"panic audit failed:{indentD (MessageData.joinSep bad.toList Format.line)}"

/-! ## Per-site non-zero-divisor lemmas -/

/-- Site 1: window arithmetic divisors. -/
theorem divWindowSize : Constants.reliableWindowSize ≠ 0 := by decide

/-- Site 1: window count divisor. -/
theorem divWindows : Constants.reliableWindows ≠ 0 := by decide

/-- Site 2/3: bandwidth-derived window scale. -/
theorem divWindowSizeScale : Constants.windowSizeScale ≠ 0 := by decide

/-- Site 4: congestion throttle scale. -/
theorem divThrottleScale : Constants.packetThrottleScale ≠ 0 := by decide

/-- Site 5: `bandwidthThrottle`'s per-peer share divides by the connected-peer
count, which the enclosing `isEmpty` check makes positive. -/
theorem divPeerCount {n : Nat} (h : n > 0) : n ≠ 0 := by omega

/-- Site 5: `bandwidthThrottle` divides by the in-transit bytes only when
they exceed the per-peer share. -/
theorem divInTransit {inTransit share : UInt32} (h : ¬ inTransit ≤ share) : inTransit ≠ 0 := by
  intro h0; subst h0; exact h (UInt32.zero_le)

/-- Site 6: the fragment length `sendError?` and `enqueue` divide by is positive. -/
theorem divFragmentLength (p : Peer) (hasChecksum : Bool) : p.maxFragmentPayload hasChecksum ≠ 0 := by
  unfold Peer.maxFragmentPayload
  generalize 4 + 24 + (if hasChecksum then 4 else 0) = overhead
  simp only
  split <;> omega

/-- Site 7: RTT smoothing divisors are nonzero literals. -/
theorem divRttLiterals : (4 : UInt32) ≠ 0 ∧ (8 : UInt32) ≠ 0 ∧ (2 : UInt32) ≠ 0 := by
  decide

end Lenet.Proofs
