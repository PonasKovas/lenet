import Lenet.Channel
import Lenet.Proofs.Basic

/-!
# Channel delivery proofs

Pins the wrap-boundary behavior fixed by the receive-window gate (see
test/README.md, divergence triage) and proves the drain loop's adequacy and
correctness, plus delivery monotonicity.

Non-obvious content:

* `drainContiguousLoop` claims its fuel (`staged.size`) *suffices*; proved
  here (`drain_fuel_adequate`) together with how far it moves the frontier.
* `eraseAfter`, which drops what the frontier jumped over, erases exactly
  the keys in the range it is given (`eraseAfter_get`).
* Delivery across the 16-bit wrap is pinned by `wrap_delivery` - the exact
  case a wrap-naive staleness test deadlocks on, and one the golden corpus
  cannot express (~65k commands per channel needed).
-/

namespace Lenet.Proofs

open Channel

/-! ## The staged map

Staged deliveries live in a map by the sequence number each starts at. -/

/-- `e` is staged in `m`: stored under the sequence number it starts at. -/
def Staged (m : Std.HashMap UInt16 StagedReliable) (e : StagedReliable) : Prop := m[e.seq]? = some e

/-- Every entry of `m` is stored under the sequence number it starts at. -/
def Keyed (m : Std.HashMap UInt16 StagedReliable) : Prop :=
  ∀ (k : UInt16) (e : StagedReliable), m[k]? = some e → e.seq = k

theorem Keyed.staged {m : Std.HashMap UInt16 StagedReliable} (h : Keyed m) {k : UInt16} {e : StagedReliable}
    (he : m[k]? = some e) : Staged m e := by
  unfold Staged; rw [h k e he]; exact he

/-- A map with an entry at `k` is not empty. -/
theorem size_pos_of_get {β} {m : Std.HashMap UInt16 β} {k : UInt16} {v : β} (h : m[k]? = some v) :
    0 < m.size := by
  have hk : k ∈ m := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])
  rcases Nat.eq_zero_or_pos m.size with h0 | h0
  · have : m.isEmpty = true := by rw [Std.HashMap.isEmpty_eq_size_eq_zero]; simp [h0]
    exact absurd hk (Std.HashMap.isEmpty_iff_forall_not_mem.mp this k)
  · exact h0

/-- Erasing a key that has an entry takes one from the size. -/
theorem size_erase_of_get {β} {m : Std.HashMap UInt16 β} {k : UInt16} {v : β} (h : m[k]? = some v) :
    (m.erase k).size = m.size - 1 := by
  have hk : k ∈ m := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])
  rw [Std.HashMap.size_erase, if_pos hk]

theorem get_erase_of_get {β} {m : Std.HashMap UInt16 β} {k k' : UInt16} {v : β}
    (h : (m.erase k)[k']? = some v) : m[k']? = some v ∧ k ≠ k' := by
  rw [Std.HashMap.getElem?_erase] at h
  split at h
  · cases h
  · next hne => exact ⟨h, by simpa using hne⟩

/-- The offset of `k` past `after`, as a number below 65536. -/
theorem sub_toNat_lt (k after : UInt16) : (k - after).toNat < 65536 := UInt16.toNat_lt _

theorem add_sub_cancel' (after : UInt16) (i : Nat) (hi : i < 65536) :
    (after + i.toUInt16 - after).toNat = i := by
  rw [show after + i.toUInt16 - after = i.toUInt16 by grind]
  simp [UInt16.toNat_ofNat']; omega

/-- `after + (n + 1)` is `k` exactly when `k` is `n + 1` past `after`. -/
theorem add_beq_iff (after k : UInt16) (i : Nat) (hi : i < 65536) :
    (after + i.toUInt16 == k) = decide ((k - after).toNat = i) := by
  by_cases h : (k - after).toNat = i
  · simp only [h, decide_true, beq_iff_eq]
    have : k - after = i.toUInt16 :=
      UInt16.toNat_inj.mp (by rw [h]; simp [UInt16.toNat_ofNat']; omega)
    rw [← this]; grind
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq; apply h; subst heq; exact add_sub_cancel' _ _ hi

theorem isAfter_succ (after k : UInt16) (n : Nat) :
    isAfter after (n + 1) k = (isAfter after n k || decide ((k - after).toNat = n + 1)) := by
  simp only [isAfter]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  omega

theorem isAfter_zero (after k : UInt16) : isAfter after 0 k = false := by
  simp only [isAfter]
  apply Bool.eq_false_iff.mpr
  simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem eraseAfterLoop_get {β} (after : UInt16) (w : β → Nat × Nat) :
    ∀ (n : Nat) (m : Std.HashMap UInt16 β) (acc : Nat × Nat) (k : UInt16), n ≤ 65535 →
      (eraseAfterLoop m after w acc n).1[k]? = if isAfter after n k then none else m[k]? := by
  intro n
  induction n with
  | zero =>
    intro m acc k _
    simp [eraseAfterLoop, isAfter_zero]
  | succ n ih =>
    intro m acc k hn
    simp only [eraseAfterLoop]
    rw [ih (m.erase _) _ k (by omega), Std.HashMap.getElem?_erase, add_beq_iff _ _ _ (by omega),
      isAfter_succ]
    cases isAfter after n k <;> cases decide ((k - after).toNat = n + 1) <;> rfl

/-- What `eraseAfter` leaves: every key but the `count` after `after`. -/
theorem eraseAfter_get {β} (m : Std.HashMap UInt16 β) (after : UInt16) (count : Nat) (w : β → Nat × Nat)
    (k : UInt16) :
    (eraseAfter m after count w).1[k]? = if isAfter after (min count 65535) k then none else m[k]? := by
  unfold eraseAfter
  dsimp only
  split
  · next hemp =>
    have : m[k]? = none :=
      Std.HashMap.getElem?_eq_none (Std.HashMap.isEmpty_iff_forall_not_mem.mp hemp k)
    simp [this]
  split
  · rw [Std.HashMap.getElem?_filter']
    cases m[k]? with
    | none => simp
    | some v => by_cases hk : isAfter after (min count 65535) k <;> simp [hk]
  · exact eraseAfterLoop_get after w _ m _ k (by omega)


/-! ## The receive gate in unwrapped terms -/

theorem toNat_toUInt16 (n : Nat) : n.toUInt16.toNat = n % 65536 := by
  simp [UInt16.toNat_ofNat']

/-- The receive gate in unwrapped terms: for an arrival starting at `x`,
no more than 9 windows behind the frontier `F` and fewer than 16 ahead,
the channel admits it exactly when it is ahead of the frontier by fewer
than seven windows. -/
theorem admitted_iff (c : Channel) (F x : Nat)
    (hc : c.incomingReliableSequenceNumber.toNat = F % 65536)
    (h1 : F / 4096 ≤ x / 4096 + 9) (h2 : x / 4096 < F / 4096 + 16) :
    (c.isIncomingReliableInWindow x.toUInt16 = true ∧ x.toUInt16 ≠ c.incomingReliableSequenceNumber)
      ↔ (F < x ∧ x / 4096 < F / 4096 + 7) := by
  have hne : x.toUInt16 ≠ c.incomingReliableSequenceNumber ↔ x % 65536 ≠ F % 65536 := by
    rw [ne_eq, ← UInt16.toNat_inj, toNat_toUInt16, hc]
  rw [hne]
  simp only [isIncomingReliableInWindow, Constants.reliableWindowSize, Constants.reliableWindows,
    Constants.freeReliableWindows, UInt16.lt_iff_toNat_lt, toNat_toUInt16, hc]
  split <;> simp <;> omega

/-- A sequence number the receive path admits lies fewer than
`(freeReliableWindows - 1) * reliableWindowSize` numbers past the frontier
(cyclically): the gate admits the frontier's window and the next six. -/
theorem isReliableAhead_offset (c : Channel) (s : UInt16) (h : c.isReliableAhead s = true) :
    (s - c.incomingReliableSequenceNumber).toNat
      < (Constants.freeReliableWindows - 1) * Constants.reliableWindowSize := by
  simp only [isReliableAhead, isIncomingReliableInWindow, Constants.reliableWindowSize,
    Constants.reliableWindows, Constants.freeReliableWindows, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at h ⊢
  obtain ⟨hw, -⟩ := h
  have hs := UInt16.toNat_lt s
  have hf := UInt16.toNat_lt c.incomingReliableSequenceNumber
  rw [UInt16.toNat_sub]
  split at hw
  · next hlt =>
    rw [UInt16.lt_iff_toNat_lt] at hlt
    simp at hw
    omega
  · next hlt =>
    rw [UInt16.lt_iff_toNat_lt] at hlt
    simp at hw
    omega

/-- A sequence number ahead of the frontier stays ahead, inside the receive
window, when the frontier moves `A` numbers on without reaching it (it is
not among the `A` after the old frontier). -/
theorem isReliableAhead_after_advance {c d : Channel} {k : UInt16} {A : Nat}
    (hk : c.isReliableAhead k = true)
    (hnot : isAfter c.incomingReliableSequenceNumber (min A 65535) k = false)
    (hd : d.incomingReliableSequenceNumber.toNat = (c.incomingReliableSequenceNumber.toNat + A) % 65536) :
    d.isReliableAhead k = true := by
  let F := c.incomingReliableSequenceNumber.toNat
  let o := (k - c.incomingReliableSequenceNumber).toNat
  have hF : F < 65536 := UInt16.toNat_lt _
  have hkx : k = (F + o).toUInt16 := by
    apply UInt16.toNat_inj.mp
    rw [toNat_toUInt16]
    show k.toNat = (c.incomingReliableSequenceNumber.toNat + (k - c.incomingReliableSequenceNumber).toNat) % 65536
    rw [UInt16.toNat_sub]
    have := UInt16.toNat_lt k
    omega
  -- where `k` lies, from the old frontier's gate
  have hwin : c.isIncomingReliableInWindow k = true ∧ k ≠ c.incomingReliableSequenceNumber := by
    simp only [isReliableAhead, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
    exact hk
  have ho : o < 28672 := by
    have := isReliableAhead_offset c k hk
    simpa [Constants.freeReliableWindows, Constants.reliableWindowSize] using this
  have hold := (admitted_iff c F (F + o) (by simp [F]) (by omega) (by omega)).mp (hkx ▸ hwin)
  -- the frontier stops short of it
  have hA : A < o := by
    simp only [isAfter, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hnot
    have : 1 ≤ o := by omega
    rcases hnot with h | h <;> omega
  have hnew := (admitted_iff d (F + A) (F + o) (by rw [hd]) (by omega) (by omega)).mpr
    ⟨by omega, by omega⟩
  rw [hkx]
  simp only [isReliableAhead, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact hnew

/-! ## Fuel adequacy for the staged-run drain -/

theorem drainContiguousLoop_none : ∀ (g : Nat) (cur : UInt16) (staged : Std.HashMap UInt16 StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat),
    staged[cur + 1]? = none →
    drainContiguousLoop cur staged del g adv = (cur, del, staged, adv) := by
  intro g
  cases g with
  | zero => intro cur staged del adv _; rfl
  | succ g =>
    intro cur staged del adv hnone
    simp only [drainContiguousLoop]
    rw [hnone]

theorem drain_fuel_adequate :
    ∀ (f g : Nat) (cur : UInt16) (staged : Std.HashMap UInt16 StagedReliable) (del : Array (Nat × Packet))
      (adv : Nat),
      staged.size ≤ f → staged.size ≤ g →
        drainContiguousLoop cur staged del f adv = drainContiguousLoop cur staged del g adv := by
  intro f
  induction f with
  | zero =>
    intro g cur staged del adv hf hg
    cases hget : staged[cur + 1]? with
    | none => rw [drainContiguousLoop_none _ _ _ _ _ hget, drainContiguousLoop_none _ _ _ _ _ hget]
    | some e => have := size_pos_of_get hget; omega
  | succ f ih =>
    intro g cur staged del adv hf hg
    cases g with
    | zero =>
      cases hget : staged[cur + 1]? with
      | none => rw [drainContiguousLoop_none _ _ _ _ _ hget, drainContiguousLoop_none _ _ _ _ _ hget]
      | some e => have := size_pos_of_get hget; omega
    | succ g =>
      simp only [drainContiguousLoop]
      cases hget : staged[cur + 1]? with
      | none => rfl
      | some e =>
        have hsz := size_erase_of_get hget
        have := size_pos_of_get hget
        exact ih g _ _ _ _ (by omega) (by omega)

/-- The drain only takes entries out: what it leaves was staged before. -/
theorem drainContiguousLoop_get : ∀ (f : Nat) (cur : UInt16) (staged : Std.HashMap UInt16 StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat) (k : UInt16) (e : StagedReliable),
    (drainContiguousLoop cur staged del f adv).2.2.1[k]? = some e → staged[k]? = some e := by
  intro f
  induction f with
  | zero => intro cur staged del adv k e h; simpa [drainContiguousLoop] using h
  | succ f ih =>
    intro cur staged del adv k e h
    simp only [drainContiguousLoop] at h
    split at h
    · exact (get_erase_of_get (ih _ _ _ _ k e h)).1
    · exact h

theorem drain_fuel_adequate' (cur : UInt16) (staged : Std.HashMap UInt16 StagedReliable)
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
    ∀ (f : Nat) (cur : UInt16) (staged : Std.HashMap UInt16 StagedReliable) (del : Array (Nat × Packet))
      (adv : Nat) (seq' : UInt16) (del' : Array (Nat × Packet)) (rest : Std.HashMap UInt16 StagedReliable)
      (adv' : Nat),
      (∀ (k : UInt16) (e : StagedReliable), staged[k]? = some e → 1 ≤ e.span) →
      drainContiguousLoop cur staged del f adv = (seq', del', rest, adv') →
      del.size ≤ del'.size ∧
      adv ≤ adv' ∧
      seq'.toNat = (cur.toNat + (adv' - adv)) % 65536 ∧
      (del'.foldl (init := 0) (fun acc e => acc + e.1))
        = (del.foldl (init := 0) (fun acc e => acc + e.1)) + (adv' - adv) := by
  intro f
  induction f with
  | zero =>
    intro cur staged del adv seq' del' rest adv' _ h
    simp only [drainContiguousLoop] at h
    cases h
    refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
    · have := UInt16.toNat_lt cur
      omega
    · simp
  | succ f ih =>
    intro cur staged del adv seq' del' rest adv' hall h
    simp only [drainContiguousLoop] at h
    cases hget : staged[cur + 1]? with
    | none =>
      simp only [hget] at h
      cases h
      refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
      · have := UInt16.toNat_lt cur
        omega
      · simp
    | some entry =>
      simp only [hget] at h
      -- the consumed delivery occupies at least one sequence number
      have hspan : 1 ≤ entry.span := hall _ _ hget
      -- span-positivity is preserved by erasing one entry
      have hall' : ∀ (k : UInt16) (e : StagedReliable), (staged.erase (cur + 1))[k]? = some e → 1 ≤ e.span :=
        fun k e he => hall k e (get_erase_of_get he).1
      obtain ⟨hgrow, hmon, hadv, hsum⟩ :=
        ih ((cur + (1 : UInt16)) + (entry.span - 1).toUInt16) (staged.erase (cur + 1))
          (del.push (entry.span, entry.packet)) (adv + entry.span) seq' del' rest adv' hall' h
      have hgrow' : del.size + 1 ≤ del'.size := by
        simpa using hgrow
      have hstep : (((cur + (1 : UInt16)) + (entry.span - 1).toUInt16)).toNat
          = (cur.toNat + entry.span) % 65536 := by
        have h1 : (cur + (1 : UInt16)).toNat = (cur.toNat + 1) % 65536 := UInt16.toNat_add cur 1
        have h2 : ((entry.span - 1).toUInt16).toNat = (entry.span - 1) % 65536 := by
          simp [UInt16.toNat_ofNat']
        rw [UInt16.toNat_add, h1, h2]
        omega
      have hpush : ((del.push (entry.span, entry.packet)).foldl (init := 0) (fun acc e => acc + e.1))
          = (del.foldl (init := 0) (fun acc e => acc + e.1)) + entry.span := by
        rw [Array.foldl_push]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [hadv, hstep]
        omega
      · rw [hsum, hpush]
        omega

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
    (hspan : 1 ≤ span) (hmem : ∀ (k : UInt16) (e : StagedReliable), c.stagedReliable[k]? = some e → 1 ≤ e.span) :
    c'.incomingReliableSequenceNumber.toNat
      = (c.incomingReliableSequenceNumber.toNat + dels.foldl (init := 0) (fun acc e => acc + e.1)) % 65536 := by
  unfold receiveReliableSpan at h
  simp only [Nat.max_eq_left hspan] at h
  split at h
  · -- out of window: nothing delivered, contradicts `hm`
    cases h; simp at hm
  split at h
  · -- duplicate of the frontier: nothing delivered
    cases h; simp at hm
  split at h
  · next hseq =>
    -- in-order delivery
    try dsimp only at h
    generalize hdr : drainContiguous _ c.stagedReliable = dr at h
    obtain ⟨dseq, ddel, drest, dadv⟩ := dr
    dsimp only at h
    generalize eraseAfter drest _ _ _ = er at h
    obtain ⟨erest, _, jumped⟩ := er
    cases h
    show dseq.toNat
        = (c.incomingReliableSequenceNumber.toNat
          + (#[(span, packet)] ++ ddel).foldl (init := 0) (fun acc e => acc + e.1)) % 65536
    -- the drain's fold is its accumulated span total (starting from `#[]`, 0)
    have hfull : drainContiguousLoop (seq + (span - 1).toUInt16) c.stagedReliable #[]
        c.stagedReliable.size 0 = (dseq, ddel, drest, dadv) := by
      rw [← hdr]
      rfl
    obtain ⟨-, -, hadv, hsum⟩ :=
      drainContiguousLoop_advance c.stagedReliable.size (seq + (span - 1).toUInt16)
        c.stagedReliable #[] 0 dseq ddel drest dadv hmem hfull
    simp only [Array.foldl_empty, Nat.zero_add, Nat.sub_zero] at hsum
    -- the one delivered entry contributes exactly `span`
    have hsingle : (#[(span, packet)] : Array (Nat × Packet)).foldl
        (init := 0) (fun acc e => acc + e.1) = span := by
      rw [show (#[(span, packet)] : Array (Nat × Packet))
          = (#[]).push (span, packet) from rfl, Array.foldl_push, Array.foldl_empty]
      simp
    -- fold of the delivered entries: the packet's span plus the drained spans
    have hfold : (#[(span, packet)] ++ ddel).foldl (init := 0) (fun acc e => acc + e.1)
        = span + ddel.foldl (init := 0) (fun acc e => acc + e.1) := by
      rw [Array.foldl_append, hsingle, foldl_spans_shift ddel span]
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
  · -- staging, or staged already: nothing delivered
    split at h <;> (cases h; simp at hm)

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
