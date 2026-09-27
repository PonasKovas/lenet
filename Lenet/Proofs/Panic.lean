import Lean
import Lenet
import Lenet.Net

/-!
# Panic-site audit

Two layers:

* **Build-time panic audit** (`run_meta` below, the no-panics composition
  over `Host.handleDatagram` / `Host.service` and every other entry point):
  every definition under `Lenet.*` (all of the core, the C-facing FFI glue
  and the socket driver `Lenet.Net` included) is scanned, and the build
  fails if any of them references a panicking primitive (`panic*`,
  `sorryAx`, `outOfBounds`, or any name with a `!` such as `getElem!` /
  `Option.get!`) or is `unsafe`, `partial` (compiled to `opaque`) or
  `implemented_by`-swapped. Then every library constant those definitions
  use is followed, transitively, and checked for the same names; the few a
  library instance mentions without Lenet calling them are listed in
  `allowed` with the reason. Scanning *every* `Lenet.*` definition, not a
  reachability slice, makes the check closed under composition. A kernel
  theorem cannot state this - in Lean's logic `panic!` *is* `default` - so
  the audit is the formal statement. Not covered (not panics): stack depth,
  allocation failure, and what `extern` library code does in C.
* **Divisor audit** (the lemmas below): Lean's `/` never panics (`x / 0 =
  0`), but a silent zero would be a logic bug where ENet crashes. Every
  division site is listed with the fact that makes its divisor positive.
  The lemmas state those facts about each guard in general; that each site
  is guarded that way is kept by review, and a new division site fails
  review by its absence here.

Division sites:

1. `Channel.windowIndex` / `isIncomingReliableInWindow` /
   `isReliableTooFarAhead` / `canSendReliable` - divisors
   `reliableWindowSize` (4096) and `reliableWindows` (16).
2. `Host.windowSizeFor` and `Host.handleIncomingConnect` (host window) -
   divisor `windowSizeScale` (65536).
3. `Host.PackState.packCommand` (congestion) - divisor `packetThrottleScale` (32).
4. `Host.incomingBandwidthShare.go` - the remaining-peer count, after its
   `remaining == 0` check (and below 2^32: at most 4095 peers).
5. `Host.OutgoingBudget.throttle` - the queued bytes, in the branch where
   they exceed the budget.
6. `Host.outgoingThrottleLimits` - 1000 and `packetThrottleScale`, and in
   `limitPeers` a peer's queued bytes, in the branch where the throttled
   share of them exceeds its bandwidth.
7. `Peer.sendError?` / `Peer.enqueue` - divisor `Peer.maxFragmentPayload`
   (positive: MTU minus overhead when that is positive, else the constant
   500).
8. `Peer.updateRtt` - divisors 4, 8, 2 (literals).
9. The codec, checksum, reassembly, unsequenced window, `FFI` and `Net`
   contain no divisions.
-/

namespace Lenet.Proofs

open Lean in
/-- Names that can panic at runtime (or stand for a missing proof): the
panic primitives, and any name with a `!` in a component (`get!`,
`get!Internal`, ...). -/
def isPanicking (n : Name) : Bool :=
  n == ``panic || n == ``panicCore || n == ``panicWithPos || n == ``panicWithPosWithDecl ||
  n == ``sorryAx || n == ``outOfBounds ||
  n.components.any fun
   | .str _ s => s.contains '!'
   | _ => false

open Lean in
/-- Panicking library constants that a library instance Lenet uses mentions
in a field Lenet never calls. Each needs its reason. -/
def allowed : List Name := [
  -- the `GetElem?` instances for arrays, lists and hash maps carry `xs[i]!`
  -- as a field (and `LawfulGetElem` states facts about it); Lenet reads by
  -- `xs[i]?` or with a proof, never `xs[i]!` (the direct scan above
  -- enforces that)
  ``Array.get!Internal, ``List.get!Internal, ``Std.HashMap.get!, ``GetElem?.getElem!
]

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
      ``Host.send, ``Peer.send, ``Protocol.Datagram.decode, ``Protocol.Datagram.encode,
      ``Net.Endpoint.service] do
    unless scanned.contains entry do throwError m!"panic audit: entry point {entry} not scanned"
  unless bad.isEmpty do
    throwError m!"panic audit failed:{indentD (MessageData.joinSep bad.toList Format.line)}"
  -- then the library code Lenet uses, followed transitively
  let mut seen : NameSet := scanned.foldl (·.insert ·) {}
  let mut todo : Array Name := scanned
  let mut libBad : Array MessageData := #[]
  let mut followed : Nat := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    let some ci := env.find? n | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for c in v.getUsedConstants do
      if seen.contains c then continue
      seen := seen.insert c
      if isPanicking c then
        -- an allowed one is not followed: what it calls is what was allowed
        unless allowed.contains c do libBad := libBad.push m!"{c} (reached from {n})"
      else if !(`Lenet).isPrefixOf c then
        followed := followed + 1
        todo := todo.push c
  unless libBad.isEmpty do
    throwError m!"panic audit failed in library code:{indentD (MessageData.joinSep libBad.toList Format.line)}"
  if followed < 500 then throwError m!"panic audit: only {followed} library constants followed"

/-! ## Per-site non-zero-divisor lemmas -/

/-- Site 1: window arithmetic divisors. -/
theorem divWindowSize : Constants.reliableWindowSize ≠ 0 := by decide

/-- Site 1: window count divisor. -/
theorem divWindows : Constants.reliableWindows ≠ 0 := by decide

/-- Site 2: bandwidth-derived window scale. -/
theorem divWindowSizeScale : Constants.windowSizeScale ≠ 0 := by decide

/-- Site 3 and 6: congestion throttle scale. -/
theorem divThrottleScale : Constants.packetThrottleScale ≠ 0 := by decide

/-- Site 4: the remaining-peer count, nonzero after its check and below
2^32, stays nonzero as a `UInt32`. -/
theorem divRemaining {n : Nat} (h : ¬ (n == 0) = true) (h' : n < 2 ^ 32) : n.toUInt32 ≠ 0 := by
  intro h0
  have := congrArg UInt32.toNat h0
  simp [UInt32.toNat_ofNat'] at this
  simp at h
  omega

/-- Site 5: the queued bytes, in the branch where they exceed the budget. -/
theorem divDataTotal {dataTotal bandwidth : Nat} (h : ¬ dataTotal ≤ bandwidth) : dataTotal ≠ 0 := by
  omega

/-- Site 6: a peer's queued bytes, in the branch where their throttled share
exceeds its bandwidth. -/
theorem divOutgoingDataTotal {throttle total bandwidth : Nat}
    (h : ¬ throttle * total / Constants.packetThrottleScale.toNat ≤ bandwidth) : total ≠ 0 := by
  intro h0; subst h0; simp at h

/-- Site 7: the fragment length `sendError?` and `enqueue` divide by is positive. -/
theorem divFragmentLength (p : Peer) (hasChecksum : Bool) : p.maxFragmentPayload hasChecksum ≠ 0 := by
  unfold Peer.maxFragmentPayload
  generalize 4 + 24 + (if hasChecksum then 4 else 0) = overhead
  simp only
  split <;> omega

/-- Site 8: RTT smoothing divisors are nonzero literals. -/
theorem divRttLiterals : (4 : UInt32) ≠ 0 ∧ (8 : UInt32) ≠ 0 ∧ (2 : UInt32) ≠ 0 := by
  decide

end Lenet.Proofs
