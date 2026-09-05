import Lenet.Constants
import Lenet.Host

/-!
# Panic-site audit

After the Phase 1 conventions (DESIGN.md 1.7), the only runtime panic source
left in `Lenet/` is division by zero: all array indexing is proof-carrying by
construction (checked at elaboration), `getElem!`/`unsafe`/`partial` are
banned by the gate, and every loop is structural or fuel-bounded (termination
is checked by the kernel).

This module names every division site with its non-zero-divisor proof. A new
unguarded division site fails review by its absence here.

Division sites (all divisors are compile-time constants or guarded):

1. `Channel.windowIndex` / `isIncomingReliableInWindow` / `canSendReliable`
   - divisors `reliableWindowSize` (4096) and `reliableWindows` (16).
2. `Host.windowSizeFor` - divisor `windowSizeScale` (65536).
3. `Host.handleDatagram` (hostInWindow) - divisor `windowSizeScale` (65536).
4. `Host.packOutgoingCommands` (congestion) - divisor `packetThrottleScale` (32).
5. `Host.bandwidthThrottle` - `connectedPeers.size` (guarded by the
   `isEmpty` check) and `totalData` (guarded by the `== 0` fallback).
6. `Peer.send` - divisor `fragmentLength` (guarded: `maxPayload` is
   `mtu - overhead` when positive, else the constant 500).
7. `Peer.updateRtt` - divisors 4, 8, 2 (literals).
8. `Checksum`/codec/reassembly paths contain no divisions.
-/

namespace Lenet.Proofs

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

/-- Site 5: the in-transit fallback in `bandwidthThrottle`
(`(peerShare * packetThrottleScale) / (if totalData == 0 then 1 else totalData)`). -/
theorem divTransitFallback (totalData : Nat) :
    (if totalData == 0 then 1 else totalData) ≠ 0 := by
  by_cases h : totalData == 0
  · simp only [h, reduceIte]; omega
  · simp only [h]
    intro hc
    simp only [Bool.false_eq_true, if_false] at hc
    exact h (by simp [hc])

/-- Site 6: `Peer.send`'s fragment length is positive on the fragmentation
path - `maxPayload` is the MTU minus overhead when that is positive, else
the constant 500. -/
theorem divFragmentLength (mtu : UInt32) (hasChecksum : Bool) :
    (if mtu.toNat > 4 + (if hasChecksum then 4 else 0) + 24
     then mtu.toNat - (4 + (if hasChecksum then 4 else 0) + 24) else 500) ≠ 0 := by
  by_cases h : mtu.toNat > 4 + (if hasChecksum then 4 else 0) + 24
  · simp only [h, reduceIte]; omega
  · simp only [h, reduceIte]; omega

/-- Site 7: RTT smoothing divisors are nonzero literals. -/
theorem divRttLiterals : (4 : UInt32) ≠ 0 ∧ (8 : UInt32) ≠ 0 ∧ (2 : UInt32) ≠ 0 := by
  decide

end Lenet.Proofs
