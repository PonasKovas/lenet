import Std.Tactic.BVDecide
import Lenet.Unsequenced
import Lenet.Proofs.Basic

/-!
# Unsequenced dedup proofs

Idempotence of `checkAndAdd`: once a group is accepted, receiving the same
group again is always a duplicate. This is the exact-dedup guarantee
unsequenced delivery relies on - the ring bit written on acceptance is
exactly the slot the duplicate probes, in every acceptance case (fresh,
newer, older-within-history).
-/

namespace Lenet.Proofs

open UnsequencedWindow

/-- `sequenceDistance x x = 0`. -/
theorem sequenceDistance_self (g : UInt16) : sequenceDistance g g = 0 := by
  unfold sequenceDistance
  simp

/-- The ring slot written by an acceptance reads back `true`. -/
theorem set_self {i : Nat} {v : Vector Bool Constants.unsequencedWindowSize}
    (hi : i % Constants.unsequencedWindowSize < Constants.unsequencedWindowSize) :
    (v.set (i % Constants.unsequencedWindowSize) true hi)[i % Constants.unsequencedWindowSize]
      = true := by
  rw [Vector.getElem_set (hj := hi)]
  simp

/-- Generic duplicate rejection: given the window has `g`'s bit set and `g`
is within the history, `checkAndAdd` rejects. -/
theorem checkAndAdd_rejects {w : UnsequencedWindow} {g : UInt16}
    (hrec : w.hasReceived = true)
    (hle : ¬ ((sequenceDistance g w.highestGroup : Int) > 0))
    (hhist : (-sequenceDistance g w.highestGroup).toNat < Constants.unsequencedWindowSize)
    (hbit : w.window[g.toNat % Constants.unsequencedWindowSize]'(modSlot_lt g.toNat) = true) :
    UnsequencedWindow.checkAndAdd w g = none := by
  unfold UnsequencedWindow.checkAndAdd UnsequencedWindow.accepts
  simp only [hrec, Bool.not_true, Bool.false_eq_true, reduceIte, hle, hhist, hbit, decide_true,
    Bool.not_true, Bool.and_false]

/-- The idempotence of unsequenced dedup: acceptance of `g` writes the ring
slot that a duplicate `g` probes, so the second lookup always reads
`true` and rejects. -/
theorem checkAndAdd_idempotent (w w' : UnsequencedWindow) (g : UInt16)
    (hw : UnsequencedWindow.checkAndAdd w g = some w') :
    UnsequencedWindow.checkAndAdd w' g = none := by
  unfold UnsequencedWindow.checkAndAdd at hw
  split at hw
  · next hacc =>
    cases hw
    obtain ⟨hg, hr, win⟩ := w
    unfold UnsequencedWindow.add
    dsimp only
    cases hr
    · refine checkAndAdd_rejects rfl ?_ ?_ (set_self (modSlot_lt g.toNat))
      · simp [sequenceDistance_self]
      · simp [sequenceDistance_self, Constants.unsequencedWindowSize]
    · by_cases hnewer : (sequenceDistance g hg : Int) > 0
      · simp only [Bool.not_true, Bool.false_eq_true, reduceIte, hnewer]
        refine checkAndAdd_rejects rfl ?_ ?_ (set_self (modSlot_lt g.toNat))
        · simp [sequenceDistance_self]
        · simp [sequenceDistance_self, Constants.unsequencedWindowSize]
      · simp only [Bool.not_true, Bool.false_eq_true, reduceIte, hnewer]
        unfold UnsequencedWindow.accepts at hacc
        simp only [Bool.not_true, Bool.false_eq_true, reduceIte, hnewer, Bool.and_eq_true,
          decide_eq_true_eq] at hacc
        exact checkAndAdd_rejects rfl hnewer hacc.1 (set_self (modSlot_lt g.toNat))
  · cases hw

end Lenet.Proofs