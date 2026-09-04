import Lenet.Constants

namespace Lenet

/--
Modular distance on 16-bit sequence numbers.
Returns the signed difference in `[-32768, 32767]`.
-/
@[inline]
def sequenceDistance (a b : UInt16) : Int :=
  let diff := (a.toNat : Int) - (b.toNat : Int)
  if diff > 32767 then diff - 65536
  else if diff < -32768 then diff + 65536
  else diff

/--
Continuous sliding window for unsequenced packet deduplication using a circular ring buffer.
-/
structure UnsequencedWindow where
  highestGroup : UInt16 := 0
  hasReceived  : Bool := false
  /-- Received-group ring of `Constants.unsequencedWindowSize` slots.
  Fixed-size by construction. -/
  window       : Vector Bool Constants.unsequencedWindowSize := Vector.replicate Constants.unsequencedWindowSize false
deriving BEq, Inhabited

namespace UnsequencedWindow

/-- Creates an initialized unsequenced window. -/
def init : UnsequencedWindow := {}

/-- Any index reduced mod the window size is a valid ring slot. -/
theorem modSlot_lt (i : Nat) :
    i % Constants.unsequencedWindowSize < Constants.unsequencedWindowSize :=
  Nat.mod_lt _ (by decide)

/-- Clears a range of skipped slots in the circular buffer `(fromGroup, toGroup)`. -/
def clearRange (win : Vector Bool Constants.unsequencedWindowSize) (fromGroup : UInt16) (count : Nat) :
    Vector Bool Constants.unsequencedWindowSize :=
  (List.range count).foldl (init := win) fun w step =>
    let slot := (fromGroup.toNat + 1 + step) % Constants.unsequencedWindowSize
    w.set slot false (modSlot_lt (fromGroup.toNat + 1 + step))

/--
Deduplicates incoming unsequenced packets.
- Returns `some updatedWindow` if accepted.
- Returns `none` if duplicate or stale.
-/
def checkAndAdd (w : UnsequencedWindow) (group : UInt16) : Option UnsequencedWindow :=
  let winSize := Constants.unsequencedWindowSize
  let slot := group.toNat % winSize

  if !w.hasReceived then
    -- First unsequenced packet ever received:
    some { highestGroup := group, hasReceived := true,
           window := w.window.set slot true (modSlot_lt group.toNat) }
  else
    let diff := sequenceDistance group w.highestGroup
    if diff > 0 then
      -- 1. Newer packet:
      let gap := diff.toNat
      let clearedWin :=
        if gap ≥ winSize then
          Vector.replicate winSize false
        else
          -- Clear only the skipped slots (for gap = 1, clears 0 slots)
          clearRange w.window w.highestGroup (gap - 1)
      some { highestGroup := group, hasReceived := true,
             window := clearedWin.set slot true (modSlot_lt group.toNat) }
    else
      -- 2. Older packet: check if within the 1024-packet history
      let offset := (-diff).toNat
      if offset < winSize then
        if w.window[slot]'(modSlot_lt group.toNat) then
          none -- Duplicate
        else
          some { w with window := w.window.set slot true (modSlot_lt group.toNat) }
      else
        none -- Stale / too old

end UnsequencedWindow

end Lenet
