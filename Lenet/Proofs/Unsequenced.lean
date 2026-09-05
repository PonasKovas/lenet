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
  unfold UnsequencedWindow.checkAndAdd
  simp only [hrec, Bool.not_true, Bool.false_eq_true, reduceIte]
  simp only [hle, reduceIte]
  simp only [hhist, reduceIte]
  simp only [hbit, reduceIte]

/-- The idempotence of unsequenced dedup: acceptance of `g` writes the ring
slot that a duplicate `g` probes, so the second lookup always reads
`true` and rejects. -/
theorem checkAndAdd_idempotent (w w' : UnsequencedWindow) (g : UInt16)
    (hw : UnsequencedWindow.checkAndAdd w g = some w') :
    UnsequencedWindow.checkAndAdd w' g = none := by
  unfold UnsequencedWindow.checkAndAdd at hw
  by_cases hfresh : (!w.hasReceived) = true
  · simp only [hfresh, reduceIte] at hw
    cases hw
    refine checkAndAdd_rejects (by simp) ?_ ?_ ?_
    · simp [sequenceDistance_self]
    · simp [sequenceDistance_self, Constants.unsequencedWindowSize]
    · simp
  by_cases hnewer : (sequenceDistance g w.highestGroup : Int) > 0
  · simp only [hfresh, hnewer, Bool.false_eq_true, reduceIte] at hw
    cases hw
    refine checkAndAdd_rejects (by simp) ?_ ?_ ?_
    · simp [sequenceDistance_self]
    · simp [sequenceDistance_self, Constants.unsequencedWindowSize]
    · simp
  · simp only [hfresh, hnewer, Bool.false_eq_true, reduceIte] at hw
    by_cases hhist : (-sequenceDistance g w.highestGroup).toNat < Constants.unsequencedWindowSize
    · by_cases hdup : w.window[g.toNat % Constants.unsequencedWindowSize]'
          (modSlot_lt g.toNat) = true
      · simp only [hhist, hdup, reduceIte] at hw
        simp at hw
      · simp only [hhist, hdup, Bool.false_eq_true, reduceIte] at hw
        simp only [Option.some.injEq] at hw
        obtain ⟨rfl⟩ := hw
        refine checkAndAdd_rejects ?_ hnewer hhist ?_
        · cases hb : w.hasReceived
          · simp [hb] at hfresh
          · rfl
        · exact set_self (modSlot_lt g.toNat)
    · simp only [hhist, reduceIte] at hw
      simp at hw

end Lenet.Proofs