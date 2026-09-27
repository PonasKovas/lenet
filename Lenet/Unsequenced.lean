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

/-- Any index reduced mod the window size is a valid ring slot. -/
theorem modSlot_lt (i : Nat) :
    i % Constants.unsequencedWindowSize < Constants.unsequencedWindowSize :=
  Nat.mod_lt _ (by decide)

/-- Clears the `count` slots after `fromGroup` in the circular buffer (the
groups a newer one skipped). A loop, not a list of the slots. -/
def clearRange (win : Vector Bool Constants.unsequencedWindowSize) (fromGroup : UInt16) :
    (count : Nat) → Vector Bool Constants.unsequencedWindowSize
  | 0 => win
  | n + 1 =>
    let slot := (fromGroup.toNat + 1 + n) % Constants.unsequencedWindowSize
    clearRange (win.set slot false (modSlot_lt (fromGroup.toNat + 1 + n))) fromGroup n

/-- Whether an unsequenced packet of `group` is new: the first one, newer
than the highest so far, or within the 1024-group history and not seen. -/
def accepts (w : UnsequencedWindow) (group : UInt16) : Bool :=
  if !w.hasReceived then true
  else
    let diff := sequenceDistance group w.highestGroup
    if diff > 0 then true
    else
      (-diff).toNat < Constants.unsequencedWindowSize &&
        !w.window[group.toNat % Constants.unsequencedWindowSize]'(modSlot_lt group.toNat)

/-- The window after taking an unsequenced packet of `group`: its slot
marked, and when it is the newest, the window slid up to it. The fields
leave `w` first, so a window held once changes in place. -/
def add (w : UnsequencedWindow) (group : UInt16) : UnsequencedWindow :=
  let winSize := Constants.unsequencedWindowSize
  let slot := group.toNat % winSize
  match w with
  | { highestGroup, hasReceived, window } =>
  if !hasReceived then
    -- First unsequenced packet ever received:
    { highestGroup := group, hasReceived := true, window := window.set slot true (modSlot_lt group.toNat) }
  else
    let diff := sequenceDistance group highestGroup
    if diff > 0 then
      -- 1. Newer packet:
      let gap := diff.toNat
      let clearedWin :=
        if gap ≥ winSize then
          Vector.replicate winSize false
        else
          -- Clear only the skipped slots (for gap = 1, clears 0 slots)
          clearRange window highestGroup (gap - 1)
      { highestGroup := group, hasReceived := true,
        window := clearedWin.set slot true (modSlot_lt group.toNat) }
    else
      -- 2. Older packet within the history: mark it
      { highestGroup, hasReceived, window := window.set slot true (modSlot_lt group.toNat) }

/--
Deduplicates incoming unsequenced packets.
- Returns `some updatedWindow` if accepted.
- Returns `none` if duplicate or stale.
-/
def checkAndAdd (w : UnsequencedWindow) (group : UInt16) : Option UnsequencedWindow :=
  if w.accepts group then some (w.add group) else none

end UnsequencedWindow

end Lenet
