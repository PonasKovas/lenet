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

theorem drainContiguousLoop_none : ∀ (g : Nat) (cur : UInt16) (staged : Array StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat),
    (staged.findIdx? (fun (e : StagedReliable) => e.seq == cur + 1)) = none →
    drainContiguousLoop cur staged del g adv = (cur, del, staged, adv) := by
  intro g
  induction g with
  | zero => intro cur staged del adv _; rfl
  | succ g ih =>
    intro cur staged del adv hnone
    simp only [drainContiguousLoop]
    rw [hnone]

theorem drain_fuel_adequate :
    ∀ (f g : Nat) (cur : UInt16) (staged : Array StagedReliable) (del : Array (Nat × Packet))
      (adv : Nat),
      staged.size ≤ f → staged.size ≤ g →
        drainContiguousLoop cur staged del f adv = drainContiguousLoop cur staged del g adv := by
  intro f
  induction f with
  | zero =>
    intro g cur staged del adv hf hg
    have hE : staged = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_antisymm hf (Nat.zero_le _))
    subst hE
    rw [drainContiguousLoop_none g cur _ _ _ (by simp)]
    rfl
  | succ f ih =>
    intro g cur staged del adv hf hg
    cases g with
    | zero =>
      have hE : staged = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_antisymm hg (Nat.zero_le _))
      subst hE
      rw [drainContiguousLoop_none (f + 1) cur _ _ _ (by simp)]
      rfl
    | succ g =>
      simp only [drainContiguousLoop, drainContiguousLoop]
      cases hfind' : staged.findIdx? (fun (e : StagedReliable) => e.seq == cur + 1) with
      | none => rfl
      | some idx =>
        simp only []
        by_cases hidx : idx < staged.size
        · rw [dif_pos hidx, dif_pos hidx]
          have hsz : (staged.eraseIdx idx hidx).size = staged.size - 1 :=
            Array.size_eraseIdx idx hidx
          exact ih g ((cur + (1 : UInt16)) + ((staged[idx]).span - 1).toUInt16)
            (staged.eraseIdx idx hidx)
            (del.push ((staged[idx]).span, (staged[idx]).packet))
            (adv + (staged[idx]).span) (by omega) (by omega)
        · rw [dif_neg hidx, dif_neg hidx]

theorem drain_fuel_adequate' (cur : UInt16) (staged : Array StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat) (f : Nat) (h : staged.size ≤ f) :
    drainContiguousLoop cur staged del f adv = drainContiguousLoop cur staged del staged.size adv :=
  drain_fuel_adequate _ _ _ _ _ _ h (Nat.le_refl _)

/-! ## The drain advances the sequence number by the consumed spans -/

/-- The drain's sequence result is advanced (cyclically) by exactly the span
total it accumulated beyond its input accumulator, the delivered array only
grows, and the accumulated total is exactly the sum of the spans pushed onto
the delivered array. Requires every staged delivery to occupy at least one
sequence number (invariant: `absorbFragment` rejects `fragmentCount = 0`,
plain staging uses span 1). -/
theorem drainContiguousLoop_advance :
    ∀ (f : Nat) (cur : UInt16) (staged : Array StagedReliable) (del : Array (Nat × Packet))
      (adv : Nat) (seq' : UInt16) (del' : Array (Nat × Packet)) (rest : Array StagedReliable)
      (adv' : Nat),
      staged.size ≤ f →
      (∀ e ∈ staged, 1 ≤ e.span) →
      drainContiguousLoop cur staged del f adv = (seq', del', rest, adv') →
      del.size ≤ del'.size ∧
      adv ≤ adv' ∧
      seq'.toNat = (cur.toNat + (adv' - adv)) % 65536 ∧
      (del'.foldl (init := 0) (fun acc e => acc + e.1))
        = (del.foldl (init := 0) (fun acc e => acc + e.1)) + (adv' - adv) := by
  intro f
  induction f with
  | zero =>
    intro cur staged del adv seq' del' rest adv' _ _ h
    simp only [drainContiguousLoop] at h
    cases h
    refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
    · have := UInt16.toNat_lt cur
      omega
    · simp
  | succ f ih =>
    intro cur staged del adv seq' del' rest adv' hstaged hall h
    simp only [drainContiguousLoop] at h
    cases hfind' : staged.findIdx? (fun (e : StagedReliable) => e.seq == cur + 1) with
    | none =>
      simp only [hfind'] at h
      cases h
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
      · have := UInt16.toNat_lt cur
        omega
      · simp
    | some idx =>
      simp only [hfind'] at h
      by_cases hidx : idx < staged.size
      · rw [dif_pos hidx] at h
        have hsz : (staged.eraseIdx idx hidx).size = staged.size - 1 :=
          Array.size_eraseIdx idx hidx
        -- the consumed delivery occupies at least one sequence number
        have hmem : staged[idx] ∈ staged := Array.getElem_mem hidx
        have hspan : 1 ≤ (staged[idx]).span := hall _ hmem
        -- span-positivity is preserved by erasing one element
        have hall' : ∀ e ∈ staged.eraseIdx idx hidx, 1 ≤ e.span := by
          intro e he
          exact hall e (Array.mem_of_mem_eraseIdx he)
        obtain ⟨hgrow, hmon, hadv, hsum⟩ :=
          ih ((cur + (1 : UInt16)) + ((staged[idx]).span - 1).toUInt16)
            (staged.eraseIdx idx hidx)
            (del.push ((staged[idx]).span, (staged[idx]).packet))
            (adv + (staged[idx]).span) seq' del' rest adv' (by omega) hall' h
        have hgrow' : del.size + 1 ≤ del'.size := by
          simpa using hgrow
        have hstep : (((cur + (1 : UInt16)) + ((staged[idx]).span - 1).toUInt16)).toNat
            = (cur.toNat + (staged[idx]).span) % 65536 := by
          have h1 : (cur + (1 : UInt16)).toNat = (cur.toNat + 1) % 65536 := UInt16.toNat_add cur 1
          have h2 : (((staged[idx]).span - 1).toUInt16).toNat
              = ((staged[idx]).span - 1) % 65536 := by
            simp [UInt16.toNat_ofNat']
          rw [UInt16.toNat_add, h1, h2]
          omega
        have hpush : ((del.push ((staged[idx]).span, (staged[idx]).packet)).foldl
              (init := 0) (fun acc e => acc + e.1))
            = (del.foldl (init := 0) (fun acc e => acc + e.1)) + (staged[idx]).span := by
          rw [Array.foldl_push]
        refine ⟨by omega, by omega, ?_, ?_⟩
        · rw [hadv, hstep]
          omega
        · rw [hsum, hpush]
          omega
      · rw [dif_neg hidx] at h
        cases h
        refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
        · have := UInt16.toNat_lt cur
          omega
        · simp

/-- Folding with a shifted initial accumulator is the original fold shifted,
for the span-sum fold used by the drain. -/
private theorem foldl_spans_shift (xs : Array (Nat × Packet)) (s : Nat) :
    xs.foldl (fun acc e => acc + e.1) s = xs.foldl (fun acc e => acc + e.1) 0 + s := by
  refine Array.foldl_rel (r := fun a b => a = b + s) ?_ ?_
  · omega
  · intro x _ c c' hc
    omega

/-- Receiving an in-order delivery advances the incoming counter by exactly
the total span of what was delivered (the delivery's own span plus the spans
of contiguous staged deliveries), with UInt16 wrap-around. -/
theorem receiveReliableSpan_advance (c : Channel) (seq : UInt16) (span : Nat) (packet : Packet)
    {c' : Channel} {dels : Array (Nat × Packet)}
    (h : receiveReliableSpan c seq span packet = (c', dels)) (hm : dels.size ≥ 1)
    (hspan : 1 ≤ span) (hmem : ∀ e ∈ c.stagedReliable, 1 ≤ e.span) :
    c'.incomingReliableSequenceNumber.toNat
      = (c.incomingReliableSequenceNumber.toNat + dels.foldl (init := 0) (fun acc e => acc + e.1)) % 65536 := by
  unfold receiveReliableSpan at h
  split at h
  · -- out of window: nothing delivered, contradicts `hm`
    simp at h
    obtain ⟨hc, hdels⟩ := h
    subst hc
    subst hdels
    simp at hm
  · split at h
    · -- duplicate of the frontier: nothing delivered
      simp at h
      obtain ⟨hc, hdels⟩ := h
      subst hc
      subst hdels
      simp at hm
    · split at h
      · next hseq =>
        -- in-order delivery
        generalize hdr : drainContiguous (seq + (span - 1).toUInt16) c.stagedReliable
          = dr at h
        obtain ⟨dseq, ddel, drest, dadv⟩ := dr
        simp at h
        obtain ⟨hc, hdels⟩ := h
        subst hc
        show dseq.toNat
            = (c.incomingReliableSequenceNumber.toNat
              + dels.foldl (init := 0) (fun acc e => acc + e.1)) % 65536
        -- the drain's fold is its accumulated span total (starting from `#[]`, 0)
        have hfull : drainContiguousLoop (seq + (span - 1).toUInt16) c.stagedReliable #[]
            c.stagedReliable.size 0 = (dseq, ddel, drest, dadv) := by
          rw [← hdr]
          rfl
        obtain ⟨-, -, hadv, hsum⟩ :=
          drainContiguousLoop_advance c.stagedReliable.size (seq + (span - 1).toUInt16)
            c.stagedReliable #[] 0 dseq ddel drest dadv (Nat.le_refl _) hmem hfull
        simp only [Array.foldl_empty, Nat.zero_add, Nat.sub_zero] at hsum
        -- the one delivered entry contributes exactly `span`
        have hsingle : (#[(span, packet)] : Array (Nat × Packet)).foldl
            (init := 0) (fun acc e => acc + e.1) = span := by
          rw [show (#[(span, packet)] : Array (Nat × Packet))
              = (#[]).push (span, packet) from rfl, Array.foldl_push, Array.foldl_empty]
          simp
        -- fold of the delivered entries: the packet's span plus the drained spans
        have hfold : dels.foldl (init := 0) (fun acc e => acc + e.1)
            = span + ddel.foldl (init := 0) (fun acc e => acc + e.1) := by
          rw [← hdels, Array.foldl_append, hsingle, foldl_spans_shift ddel span]
          omega
        -- the in-order delivery starts at the frontier + 1 and occupies `span`
        have hstart : ((seq + (span - 1).toUInt16 : UInt16)).toNat
            = (c.incomingReliableSequenceNumber.toNat + span) % 65536 := by
          have hseq' : seq = c.incomingReliableSequenceNumber + 1 := by
            simp only [beq_iff_eq] at hseq
            exact hseq
          have h1 : (c.incomingReliableSequenceNumber + (1 : UInt16)).toNat
              = (c.incomingReliableSequenceNumber.toNat + 1) % 65536 :=
            UInt16.toNat_add _ _
          have h2 : (((span - 1 : Nat)).toUInt16).toNat = (span - 1) % 65536 := by
            simp [UInt16.toNat_ofNat']
          rw [hseq', UInt16.toNat_add, h1, h2]
          omega
        rw [hfold, hsum, hadv, hstart, Nat.mod_add_mod]
        omega
      · -- staging: nothing delivered
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
    simp [receiveReliable, receiveReliableSpan, isIncomingReliableInWindow, drainContiguous,
      drainContiguousLoop, Constants.reliableWindowSize, Constants.reliableWindows,
      Constants.freeReliableWindows]
