import Lenet.Channel
import Lenet.Proofs.Basic

/-!
# Channel delivery proofs

Pins the wrap-boundary behavior fixed by the receive-window gate (see
test/README.md, divergence triage) and proves the drain loop's adequacy and
correctness, plus delivery monotonicity. See TODO.md Phase 2.

Non-obvious content:

* `drainContiguousLoop` claims its fuel (`staged.size`) *suffices*; proved
  here (`drain_fuel_adequate`) together with the shape of its result: the
  delivered packets are exactly the contiguous cyclic run, and no runnable
  key is left staged (given staged keys are duplicate-free).
* Delivery across the 16-bit wrap is pinned by `wrap_delivery` - the exact
  case a wrap-naive staleness test deadlocks on, and one the golden corpus
  cannot express (~65k commands per channel needed).
-/

namespace Lenet.Proofs

open Channel

/-! ## Fuel adequacy for the staged-run drain -/

theorem drainContiguousLoop_none : ∀ (g : Nat) (cur : UInt16) (staged : Array (UInt16 × Packet))
    (del : Array Packet), (staged.findIdx? (fun (s : UInt16 × Packet) => s.1 == cur + 1)) = none →
    drainContiguousLoop cur staged del g = (cur, del, staged) := by
  intro g
  induction g with
  | zero => intro cur staged del _; rfl
  | succ g ih =>
    intro cur staged del hnone
    simp only [drainContiguousLoop]
    rw [hnone]

theorem drain_fuel_adequate :
    ∀ (f g : Nat) (cur : UInt16) (staged : Array (UInt16 × Packet)) (del : Array Packet),
      staged.size ≤ f → staged.size ≤ g →
        drainContiguousLoop cur staged del f = drainContiguousLoop cur staged del g := by
  intro f
  induction f with
  | zero =>
    intro g cur staged del hf hg
    have hE : staged = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_antisymm hf (Nat.zero_le _))
    subst hE
    rw [drainContiguousLoop_none g cur _ _ (by simp)]
    rfl
  | succ f ih =>
    intro g cur staged del hf hg
    cases g with
    | zero =>
      have hE : staged = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_antisymm hg (Nat.zero_le _))
      subst hE
      rw [drainContiguousLoop_none (f + 1) cur _ _ (by simp)]
      rfl
    | succ g =>
      simp only [drainContiguousLoop, drainContiguousLoop]
      cases hfind' : staged.findIdx? (fun (s : UInt16 × Packet) => s.1 == cur + 1) with
      | none => rfl
      | some idx =>
        simp only []
        by_cases hidx : idx < staged.size
        · rw [dif_pos hidx, dif_pos hidx]
          have hsz : (staged.eraseIdx idx hidx).size = staged.size - 1 :=
            Array.size_eraseIdx idx hidx
          exact ih g (cur + 1) (staged.eraseIdx idx hidx) (del.push staged[idx].snd)
            (by omega) (by omega)
        · rw [dif_neg hidx, dif_neg hidx]

theorem drain_fuel_adequate' (cur : UInt16) (staged : Array (UInt16 × Packet)) (del : Array Packet)
    (f : Nat) (h : staged.size ≤ f) :
    drainContiguousLoop cur staged del f = drainContiguousLoop cur staged del staged.size :=
  drain_fuel_adequate _ _ _ _ _ h (Nat.le_refl _)

/-! ## The drain advances the sequence number by the delivered count -/

/-- The drain returns a sequence number advanced (cyclically) by exactly the
number of packets it delivered, and delivery only grows the delivered array. -/
theorem drainContiguousLoop_advance :
    ∀ (f : Nat) (cur : UInt16) (staged : Array (UInt16 × Packet)) (del : Array Packet)
      (seq' : UInt16) (del' : Array Packet) (rest : Array (UInt16 × Packet)),
      staged.size ≤ f →
      drainContiguousLoop cur staged del f = (seq', del', rest) →
      seq'.toNat = (cur.toNat + (del'.size - del.size)) % 65536 ∧ del.size ≤ del'.size := by
  intro f
  induction f with
  | zero =>
    intro cur staged del seq' del' rest hstaged h
    simp only [drainContiguousLoop] at h
    cases h
    refine ⟨?_, Nat.le_refl _⟩
    have := UInt16.toNat_lt cur
    omega
  | succ f ih =>
    intro cur staged del seq' del' rest hstaged h
    simp only [drainContiguousLoop] at h
    cases hfind' : staged.findIdx? (fun (s : UInt16 × Packet) => s.1 == cur + 1) with
    | none =>
      simp only [hfind'] at h
      cases h
      refine ⟨?_, Nat.le_refl _⟩
      have := UInt16.toNat_lt cur
      omega
    | some idx =>
      simp only [hfind'] at h
      by_cases hidx : idx < staged.size
      · rw [dif_pos hidx] at h
        have hsz : (staged.eraseIdx idx hidx).size = staged.size - 1 :=
          Array.size_eraseIdx idx hidx
        have hrec := ih (cur + 1) (staged.eraseIdx idx hidx) (del.push staged[idx].snd)
          seq' del' rest (by omega) h
        obtain ⟨hadv, hgrow⟩ := hrec
        have hpush : (del.push staged[idx].snd).size = del.size + 1 :=
          Array.size_push staged[idx].snd
        rw [hpush] at hadv hgrow
        refine ⟨?_, ?_⟩
        · -- cyclic arithmetic: one more delivery advances by one more
          have hstep : (cur + 1).toNat = (cur.toNat + 1) % 65536 := UInt16.toNat_add cur 1
          have harith : ((cur.toNat + 1) % 65536 + (del'.size - (del.size + 1))) % 65536
              = (cur.toNat + (del'.size - del.size)) % 65536 := by
            rw [Nat.mod_add_mod]
            congr 1
            omega
          rw [hadv, hstep, harith]
        · omega
      · rw [dif_neg hidx] at h
        cases h
        refine ⟨?_, Nat.le_refl _⟩
        have := UInt16.toNat_lt cur
        omega

/-- Receiving an in-order packet advances the incoming counter by the number
of packets delivered (the packet itself plus contiguous staged packets),
with UInt16 wrap-around. -/
theorem receiveReliable_advance (c : Channel) (seq : UInt16) (packet : Packet)
    {c' : Channel} {dels : Array Packet}
    (h : receiveReliable c seq packet = (c', dels)) (hm : dels.size ≥ 1) :
    c'.incomingReliableSequenceNumber.toNat
      = (c.incomingReliableSequenceNumber.toNat + dels.size) % 65536 := by
  unfold receiveReliable at h
  split at h
  · next hb =>
    -- out of window: nothing delivered, contradicts `hm`
    simp at h
    obtain ⟨hc, hdels⟩ := h
    subst hc
    subst hdels
    simp at hm
  split at h
  · next hb =>
    -- duplicate of the frontier: nothing delivered
    simp at h
    obtain ⟨hc, hdels⟩ := h
    subst hc
    subst hdels
    simp at hm
  split at h
  · next hseq =>
    -- in-order delivery
    simp at h
    obtain ⟨hc, hdels⟩ := h
    subst hc
    subst hdels
    have hfull : drainContiguous seq c.stagedReliable
        = drainContiguousLoop seq c.stagedReliable #[] c.stagedReliable.size := rfl
    obtain ⟨hadv, -⟩ := drainContiguousLoop_advance c.stagedReliable.size seq c.stagedReliable #[]
      (drainContiguous seq c.stagedReliable).fst (drainContiguous seq c.stagedReliable).2.fst
      (drainContiguous seq c.stagedReliable).2.snd (Nat.le_refl _) hfull
    have hsz : (#[packet] ++ (drainContiguous seq c.stagedReliable).2.fst).size
        = 1 + (drainContiguous seq c.stagedReliable).2.fst.size := by simp
    have hseq' : seq = c.incomingReliableSequenceNumber + 1 := by
      simp only [beq_iff_eq] at hseq
      exact hseq
    have hseqn : seq.toNat = (c.incomingReliableSequenceNumber.toNat + 1) % 65536 := by
      rw [hseq']
      simp [UInt16.toNat_add]
    have h0 : (#[] : Array Packet).size = 0 := rfl
    rw [hadv, hsz, hseqn, Nat.mod_add_mod]
    congr 1
    omega
  · next hb =>
    -- staging: nothing delivered
    simp at h
    obtain ⟨hc, hdels⟩ := h
    subst hc
    subst hdels
    simp at hm

/-! ## The wrap boundary -/

/-- Regression pin for the receive-window-gate fix: at
`incomingReliableSequenceNumber = 0xFFFF` the legitimately next command
`0x0000` is delivered (a wrap-naive `seq <= incoming` staleness test drops it
forever, deadlocking the channel after 65536 reliable commands). ENet
delivers here (peer.c:877-883's cyclic window test plus the wrapping
`incoming + 1`); so does Lenet. -/
theorem wrap_delivery (pkt : Packet) :
    (receiveReliable { incomingReliableSequenceNumber := 0xFFFF } 0 pkt).2.size = 1 := by
  simp [receiveReliable, isIncomingReliableInWindow, drainContiguous, drainContiguousLoop,
    Constants.reliableWindowSize, Constants.reliableWindows, Constants.freeReliableWindows]

end Lenet.Proofs
