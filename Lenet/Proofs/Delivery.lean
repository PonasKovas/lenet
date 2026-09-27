import Lenet.Proofs.Resources

/-!
# Reliable delivery on the receiving side

What one channel does with an honest sender's reliable packets, whatever
the network does to them. The sender's packets are a `Stream`: message `i`
occupies `span i` sequence numbers (a fragmented packet one per fragment),
numbered from 1 without wrapping; the wire carries them wrapped to 16 bits.
Arrivals may be lost, duplicated, reordered or delayed, as long as each
`Fits`: it starts no more than 9 windows behind the frontier and fewer than
16 ahead. Past those bounds a wrapped sequence number names two messages a
whole wrap apart, and neither ENet nor Lenet can tell them apart.

* `feed_spec`, `feed_fresh`: the reliable packets the channel hands out are
  exactly messages `0, 1, 2, ...`: each once, in order, none made up.
* `step_next`, `fits_next`: an arrival of the next message always delivers
  it, so the channel never stalls on a message it has.
* `receiveReliableAndRelease_spec`, `receiveUnreliable_inv`: the same for
  the receive path `Peer` runs, where a reliable delivery hands out its
  reliable packets first, then the unreliable ones it released.

`admitted_iff` is the receive gate in unwrapped terms, and `drain_spec`
what the drain of staged packets does. `step_spec` is one arrival with all
that `Proofs/Connection` needs to join this to the sender side: a staged
message stays staged until delivered, nothing is staged or delivered but
the staged messages and the arrival, and an arrival inside the receive
window is received. There every arrival is shown to `Fits`.
-/

namespace Lenet.Proofs.Delivery

open Channel

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

theorem nodup_map_getElem {α β} {l : List α} {f : α → β} (h : (l.map f).Nodup) {i k : Nat}
    (hi : i < l.length) (hk : k < l.length) (hik : i ≠ k) : f l[i] ≠ f l[k] := by
  rw [List.Nodup, List.pairwise_iff_getElem] at h
  rcases Nat.lt_or_gt_of_ne hik with hlt | hlt
  · have := h i k (by simpa using hi) (by simpa using hk) hlt
    simpa only [List.getElem_map] using this
  · have := h k i (by simpa using hk) (by simpa using hi) hlt
    simp only [List.getElem_map] at this
    exact fun e => this e.symm

/-- What an honest sender sends reliably on one channel, in order: message
`i` is `packet i`, occupying `span i` sequence numbers (1 for a plain
packet, the fragment count for a fragmented one). -/
structure Stream where
  span     : Nat → Nat
  packet   : Nat → Packet
  span_pos : ∀ i, 1 ≤ span i

namespace Stream

variable (s : Stream)

/-- The first sequence number of message `i`, unwrapped (numbering starts
at 1, as ENet's). -/
def start : Nat → Nat
  | 0 => 1
  | i + 1 => start i + s.span i

/-- The staged entry message `i` makes. -/
def entry (i : Nat) : StagedReliable := ⟨(s.start i).toUInt16, s.span i, s.packet i⟩

/-- What the channel hands out for message `i`. -/
def out (i : Nat) : Nat × Packet := (s.span i, s.packet i)

variable {s}

theorem start_pos : ∀ i, 1 ≤ s.start i
  | 0 => Nat.le_refl _
  | i + 1 => Nat.le_trans (start_pos i) (Nat.le_add_right _ _)

theorem start_lt_succ (i : Nat) : s.start i < s.start (i + 1) := by
  show s.start i < s.start i + s.span i
  have := s.span_pos i
  omega

theorem start_lt {i j : Nat} (h : i < j) : s.start i < s.start j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact Nat.lt_trans (ih h) (start_lt_succ j)
    · exact start_lt_succ i

theorem start_le {i j : Nat} (h : i ≤ j) : s.start i ≤ s.start j := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Nat.le_of_lt (start_lt h)
  · exact Nat.le_refl _

theorem start_inj {i j : Nat} (h : s.start i = s.start j) : i = j := by
  rcases Nat.lt_trichotomy i j with hl | he | hl
  · exact absurd h (Nat.ne_of_lt (start_lt hl))
  · exact he
  · exact absurd h (Nat.ne_of_gt (start_lt hl))

/-- Two messages whose first sequence numbers lie within one wrap of each
other, past `F`, are told apart by the wrapped numbers. -/
theorem eq_of_wrapped {F i j : Nat} (h : (s.start i).toUInt16 = (s.start j).toUInt16)
    (hi : F < s.start i) (hi' : s.start i < F + 65536)
    (hj : F < s.start j) (hj' : s.start j < F + 65536) : i = j := by
  have := congrArg UInt16.toNat h
  rw [toNat_toUInt16, toNat_toUInt16] at this
  exact start_inj (s := s) (by omega)

end Stream

/-! ## The drain -/

theorem mem_eraseIdx_or {α} {xs : Array α} {e : α} (he : e ∈ xs) (idx : Nat) (h : idx < xs.size) :
    e ∈ xs.eraseIdx idx h ∨ e = xs[idx] := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp he
  by_cases hik : i = idx
  · subst hik; exact Or.inr rfl
  · left
    rw [← Array.mem_toList_iff, Array.toList_eraseIdx]
    exact List.mem_eraseIdx_iff_getElem.mpr ⟨i, by simpa using hi, hik, by simp⟩

/-- The drain, from just before message `j`, delivers messages `j`, `j+1`,
... while they are staged, and leaves staged only messages past where it
stopped. Staged entries are messages at `j` or later, within half a wrap
of `F0`, with distinct sequence numbers. It delivers only staged messages
and takes out only the ones it delivers, and whatever `P` says of the
staged messages' numbers still holds of those it leaves and delivers. -/
theorem drain_spec (s : Stream) (F0 : Nat) (P : Nat → Prop) : ∀ (fuel j : Nat) (staged : Array StagedReliable)
    (del : Array (Nat × Packet)) (adv : Nat),
    staged.size ≤ fuel → F0 < s.start j →
    (staged.toList.map (·.seq)).Nodup →
    (∀ e ∈ staged, ∃ i, j ≤ i ∧ s.start i < F0 + 32768 ∧ e = s.entry i ∧ P i) →
    let r := drainContiguousLoop (s.start j - 1).toUInt16 staged del fuel adv
    ∃ j', j ≤ j' ∧ r.1 = (s.start j' - 1).toUInt16 ∧
      r.2.1.toList = del.toList ++ (List.range' j (j' - j)).map s.out ∧
      r.2.2.1.toList.Sublist staged.toList ∧
      (∀ e ∈ r.2.2.1, ∃ i, j' < i ∧ s.start i < F0 + 32768 ∧ e = s.entry i ∧ P i) ∧
      (∀ i, j ≤ i → i < j' → s.start i < F0 + 32768 ∧ P i) ∧
      (∀ e ∈ staged, e ∈ r.2.2.1 ∨ ∃ i, j ≤ i ∧ i < j' ∧ s.start i < F0 + 32768 ∧ e = s.entry i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j staged del adv hsz _ _ _
    have hE : staged = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    subst hE
    exact ⟨j, Nat.le_refl _, rfl, by simp [drainContiguousLoop], by simp [drainContiguousLoop],
      by simp [drainContiguousLoop], fun i h1 h2 => by omega, by simp⟩
  | succ fuel ih =>
    intro j staged del adv hsz hF hnd hall
    have hT : (s.start j - 1).toUInt16 + 1 = (s.start j).toUInt16 := by
      have := Stream.start_pos (s := s) j
      rw [← UInt16.toNat_inj, UInt16.toNat_add, toNat_toUInt16, toNat_toUInt16]
      simp
      omega
    simp only [drainContiguousLoop, hT]
    cases hf : staged.findIdx? (fun (e : StagedReliable) => e.seq == (s.start j).toUInt16) with
    | none =>
      simp only []
      refine ⟨j, Nat.le_refl _, rfl, by simp, List.Sublist.refl _, fun e he => ?_,
        fun i h1 h2 => by omega, fun e he => Or.inl he⟩
      obtain ⟨i, hij, hib, rfl, hPi⟩ := hall e he
      have hne := Array.findIdx?_eq_none_iff.mp hf _ he
      refine ⟨i, Nat.lt_of_le_of_ne hij fun h => ?_, hib, rfl, hPi⟩
      subst h
      simp [Stream.entry] at hne
    | some idx =>
      obtain ⟨hidx, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
      simp only [dif_pos hidx]
      obtain ⟨i, hij, hib, hei, hPi⟩ := hall _ (Array.getElem_mem hidx)
      have hseq : (s.start i).toUInt16 = (s.start j).toUInt16 := by
        simpa [hei, Stream.entry] using hp
      have hi : i = j := Stream.eq_of_wrapped hseq (F := F0)
        (Nat.lt_of_lt_of_le hF (Stream.start_le hij)) (by omega) hF
        (by have := Stream.start_le (s := s) hij; omega)
      subst hi
      have hcur : (s.start i).toUInt16 + (staged[idx].span - 1).toUInt16
          = (s.start (i + 1) - 1).toUInt16 := by
        rw [hei]
        show (s.start i).toUInt16 + (s.span i - 1).toUInt16 = (s.start i + s.span i - 1).toUInt16
        have := s.span_pos i
        rw [← UInt16.toNat_inj, UInt16.toNat_add, toNat_toUInt16, toNat_toUInt16, toNat_toUInt16]
        omega
      rw [hcur]
      have hsub : (staged.eraseIdx idx hidx).toList.Sublist staged.toList := by
        rw [Array.toList_eraseIdx]
        exact List.eraseIdx_sublist _ _
      have hall' : ∀ e ∈ staged.eraseIdx idx hidx,
          ∃ m, i + 1 ≤ m ∧ s.start m < F0 + 32768 ∧ e = s.entry m ∧ P m := by
        intro e he
        have he' := Array.mem_toList_iff.mpr he
        rw [Array.toList_eraseIdx] at he'
        obtain ⟨p, hp', hpk, hpe⟩ := List.mem_eraseIdx_iff_getElem.mp he'
        obtain ⟨m, hm, hmb, hme, hPm⟩ := hall e (Array.mem_of_mem_eraseIdx he)
        refine ⟨m, Nat.lt_of_le_of_ne hm fun h => ?_, hmb, hme, hPm⟩
        subst h
        have := nodup_map_getElem hnd hp' (by simpa using hidx) hpk
        rw [hpe, hme, Array.getElem_toList, hei] at this
        exact this rfl
      have hstep : staged[idx] = s.entry i := hei
      obtain ⟨j', hj', hr1, hr2, hr3, hr4, hr5, hr6⟩ := ih (i + 1) (staged.eraseIdx idx hidx)
        (del.push (staged[idx].span, staged[idx].packet)) (adv + staged[idx].span)
        (by rw [Array.size_eraseIdx]; omega)
        (Nat.lt_trans hF (Stream.start_lt_succ i))
        (hnd.sublist (hsub.map _)) hall'
      refine ⟨j', by omega, hr1, ?_, hr3.trans hsub, hr4, fun m h1 h2 => ?_, fun e he => ?_⟩
      · rw [hr2, hstep]
        obtain ⟨n, rfl⟩ : ∃ n, j' = i + 1 + n := ⟨j' - (i + 1), by omega⟩
        rw [show i + 1 + n - i = n + 1 by omega, List.range'_succ]
        simp [Stream.entry, Stream.out]
      · rcases Nat.lt_or_ge i m with hm | hm
        · exact hr5 m hm h2
        · have : m = i := by omega
          subst this
          exact ⟨hib, hPi⟩
      · rcases mem_eraseIdx_or he idx hidx with he | he
        · rcases hr6 e he with h | ⟨m, h1, h2, h3, h4⟩
          · exact Or.inl h
          · exact Or.inr ⟨m, by omega, h2, h3, h4⟩
        · exact Or.inr ⟨i, Nat.le_refl _, by omega, hib, he.trans hstep⟩

/-! ## One arrival -/

/-- The receiver after delivering messages `0 .. d-1`: the frontier is the
last sequence number message `d-1` occupies, and the staged entries are
distinct later messages inside the receive window (fewer than seven
windows past the frontier's). -/
structure Inv (s : Stream) (c : Channel) (d : Nat) : Prop where
  frontier : c.incomingReliableSequenceNumber = (s.start d - 1).toUInt16
  staged   : ∀ e ∈ c.stagedReliable, ∃ i, d < i ∧ s.start i / 4096 < (s.start d - 1) / 4096 + 7 ∧ e = s.entry i
  nodup    : (c.stagedReliable.toList.map (·.seq)).Nodup

/-- An arrival of message `k` while the receiver has delivered `d`
messages starts no more than 9 windows (of 4096 sequence numbers) behind
the frontier's window and fewer than 16 ahead: past either bound the wrapped
sequence numbers cannot tell it from a message a whole wrap away. -/
def Fits (s : Stream) (d k : Nat) : Prop :=
  (s.start d - 1) / 4096 ≤ s.start k / 4096 + 9 ∧ s.start k / 4096 < (s.start d - 1) / 4096 + 16

/-- A fresh channel has delivered nothing and staged nothing. -/
theorem inv_default (s : Stream) : Inv s {} 0 :=
  ⟨rfl, by simp, by simp⟩

theorem pred_add_one (s : Stream) (d : Nat) : (s.start d - 1).toUInt16 + 1 = (s.start d).toUInt16 := by
  have := Stream.start_pos (s := s) d
  rw [← UInt16.toNat_inj, UInt16.toNat_add, toNat_toUInt16, toNat_toUInt16]
  simp
  omega

theorem last_of (s : Stream) (d : Nat) :
    (s.start d).toUInt16 + (s.span d - 1).toUInt16 = (s.start (d + 1) - 1).toUInt16 := by
  show (s.start d).toUInt16 + (s.span d - 1).toUInt16 = (s.start d + s.span d - 1).toUInt16
  have := s.span_pos d
  rw [← UInt16.toNat_inj, UInt16.toNat_add, toNat_toUInt16, toNat_toUInt16, toNat_toUInt16]
  omega

/-- Inside the receive window means less than half a wrap ahead. -/
theorem half_of_window {F x : Nat} (h : x / 4096 < F / 4096 + 7) : x < F + 32768 := by omega

/-- Two messages with the same entry, both less than a wrap past `F`, are
the same message. -/
theorem entry_inj {s : Stream} {F i j : Nat} (h : s.entry i = s.entry j)
    (hi : F < s.start i) (hi' : s.start i < F + 65536) (hj : F < s.start j) (hj' : s.start j < F + 65536) :
    i = j :=
  Stream.eq_of_wrapped (by simpa [Stream.entry] using congrArg StagedReliable.seq h) hi hi' hj hj'

/-- **One arrival**, all that the connection proof needs. The channel
delivers the next messages in order, none twice (`Inv` and the output);
the arrival of message `d` itself always delivers it; a staged message
stays staged until it is delivered, and a message is delivered or staged
only if it was staged or is the arrival (whatever `P` says of those still
holds); and an arrival inside the receive window is received. -/
theorem step_spec {s : Stream} {c : Channel} {d : Nat} (h : Inv s c d) (k : Nat) (hk : Fits s d k)
    (P : Nat → Prop) (hP : ∀ e ∈ c.stagedReliable, ∃ i, d < i ∧ s.start i < s.start d + 32768 ∧ e = s.entry i ∧ P i)
    (hPk : P k) :
    let r := receiveReliableSpan c (s.start k).toUInt16 (s.span k) (s.packet k)
    ∃ j, d ≤ j ∧ Inv s r.1 j ∧ r.2.toList = (List.range' d (j - d)).map s.out ∧ (k = d → d < j) ∧
      (∀ i, d < i → s.start i < s.start d + 32768 → s.entry i ∈ c.stagedReliable →
        i < j ∨ s.entry i ∈ r.1.stagedReliable) ∧
      (∀ e ∈ r.1.stagedReliable, ∃ i, j < i ∧ s.start i < s.start j + 32768 ∧ e = s.entry i ∧ P i) ∧
      (∀ i, d ≤ i → i < j → P i) ∧
      (d ≤ k → s.start k / 4096 < (s.start d - 1) / 4096 + 7 → k < j ∨ s.entry k ∈ r.1.stagedReliable) := by
  obtain ⟨hfr, hst, hnd⟩ := h
  have hpos := Stream.start_pos (s := s) d
  have hc : c.incomingReliableSequenceNumber.toNat = (s.start d - 1) % 65536 := by
    rw [hfr, toNat_toUInt16]
  have hadm := admitted_iff c (s.start d - 1) (s.start k) hc hk.1 hk.2
  -- a staged entry names one message: the one `Inv` bounds is the one `P` holds of
  have hPi : ∀ e ∈ c.stagedReliable, ∃ i, d < i ∧ s.start i / 4096 < (s.start d - 1) / 4096 + 7 ∧
      e = s.entry i ∧ P i := by
    intro e he
    obtain ⟨i, hi, hib, hei⟩ := hst e he
    obtain ⟨i', hi', hib', hei', hP'⟩ := hP e he
    have := Stream.start_lt (s := s) hi
    have := Stream.start_lt (s := s) hi'
    have : i = i' := entry_inj (F := s.start d - 1) (hei.symm.trans hei') (by omega)
      (by have := half_of_window hib; omega) (by omega) (by omega)
    subst this
    exact ⟨i, hi, hib, hei, hP'⟩
  have hPold : ∀ e ∈ c.stagedReliable, ∃ i, d < i ∧ s.start i < s.start d + 32768 ∧ e = s.entry i ∧ P i :=
    hP
  unfold receiveReliableSpan
  split
  · next hw =>
    simp only [Bool.not_eq_true'] at hw
    refine ⟨d, Nat.le_refl _, ⟨hfr, hst, hnd⟩, by simp, fun hkd => ?_, fun i _ _ hi => Or.inr hi,
      hPold, fun i h1 h2 => by omega, fun hdk hkw => ?_⟩
    · subst hkd
      have := hadm.mpr ⟨by omega, by omega⟩
      rw [hw] at this
      exact absurd this.1 (by simp)
    · have := Stream.start_le (s := s) hdk
      have := (hadm.mpr ⟨by omega, hkw⟩).1
      rw [hw] at this
      exact absurd this (by simp)
  · next hw =>
    split
    · next hdup =>
      simp only [beq_iff_eq] at hdup
      refine ⟨d, Nat.le_refl _, ⟨hfr, hst, hnd⟩, by simp, fun hkd => ?_, fun i _ _ hi => Or.inr hi,
        hPold, fun i h1 h2 => by omega, fun hdk hkw => ?_⟩
      · subst hkd
        exact absurd hdup (hadm.mpr ⟨by omega, by omega⟩).2
      · have := Stream.start_le (s := s) hdk
        exact absurd hdup (hadm.mpr ⟨by omega, hkw⟩).2
    · next hdup =>
      simp only [beq_iff_eq] at hdup
      obtain ⟨hF, hW⟩ := hadm.mp ⟨by simpa using hw, hdup⟩
      split
      · next hnext =>
        -- in order: it is message `d`
        simp only [beq_iff_eq, hfr, pred_add_one] at hnext
        have hkd : k = d := Stream.eq_of_wrapped hnext (F := s.start d - 1) hF (by omega)
          (by omega) (by omega)
        subst hkd
        simp only [drainContiguous]
        rw [last_of]
        have hdr := drain_spec s (s.start k) P c.stagedReliable.size (k + 1) c.stagedReliable #[] 0
          (Nat.le_refl _) (Stream.start_lt_succ k) hnd
          (fun e he => by
            obtain ⟨i, hi, hib, rfl, hP'⟩ := hPi e he
            exact ⟨i, hi, by have := half_of_window hib; omega, rfl, hP'⟩)
        generalize drainContiguousLoop _ c.stagedReliable #[] c.stagedReliable.size 0 = r at hdr ⊢
        obtain ⟨newSeq, drained, rest, _⟩ := r
        obtain ⟨j', hj', hr1, hr2, hr3, hr4, hr5, hr6⟩ := hdr
        simp only at hr1 hr2 hr3 hr4 hr5 hr6 ⊢
        have hkj := Stream.start_le (s := s) (by omega : k + 1 ≤ j')
        have hk1 := Stream.start_lt_succ (s := s) k
        -- the new frontier's window test, unwrapped, for a message past it
        have hnew : ∀ i, j' < i → s.start i < s.start k + 32768 →
            (({ c with incomingReliableSequenceNumber := newSeq, incomingUnreliableSequenceNumber := 0 } : Channel).isReliableAhead (s.entry i).seq = true ↔
              s.start i / 4096 < (s.start j' - 1) / 4096 + 7) := by
          intro i hi hib
          have hji := Stream.start_lt (s := s) hi
          have := admitted_iff ({ c with incomingReliableSequenceNumber := newSeq, incomingUnreliableSequenceNumber := 0 } : Channel) (s.start j' - 1) (s.start i)
            (by simp only [hr1, toNat_toUInt16]) (by omega) (by omega)
          simp only [Channel.isReliableAhead, Stream.entry, Bool.and_eq_true, bne_iff_ne, ne_eq]
          constructor
          · intro h; exact (this.mp h).2
          · intro h; exact this.mpr ⟨by omega, h⟩
        refine ⟨j', by omega, ⟨hr1, fun e he => ?_, ?_⟩, ?_, fun _ => by omega, fun i hi hib hmem => ?_,
          fun e he => ?_, fun i h1 h2 => ?_, fun _ _ => Or.inl (by omega)⟩
        · obtain ⟨hm, hk'⟩ := Array.mem_filter.mp he
          obtain ⟨i, hi, hib, rfl, -⟩ := hr4 _ hm
          exact ⟨i, hi, (hnew i hi hib).mp hk', rfl⟩
        · rw [Array.toList_filter]
          exact hnd.sublist ((List.filter_sublist).map _ |>.trans (hr3.map _))
        · rw [Array.toList_append, hr2]
          obtain ⟨n, rfl⟩ : ∃ n, j' = k + 1 + n := ⟨j' - (k + 1), by omega⟩
          rw [show k + 1 + n - k = n + 1 by omega, List.range'_succ]
          simp [Stream.out]
        · -- a staged message is delivered now or stays staged
          have hki := Stream.start_lt (s := s) hi
          rcases hr6 _ hmem with hrest | ⟨i₂, h1, h2, h3, h4⟩
          · obtain ⟨i₃, hi₃, hib₃, he₃, -⟩ := hr4 _ hrest
            have := Stream.start_lt (s := s) (show k < i₃ by omega)
            have : i = i₃ := entry_inj (F := s.start k - 1) he₃ (by omega) (by omega) (by omega) (by omega)
            subst this
            obtain ⟨i₄, hi₄, hib₄, he₄, -⟩ := hPi _ hmem
            have := Stream.start_lt (s := s) hi₄
            have : i = i₄ := entry_inj (F := s.start k - 1) he₄ (by omega) (by omega) (by omega)
              (by have := half_of_window hib₄; omega)
            subst this
            exact Or.inr (Array.mem_filter.mpr ⟨hrest, (hnew i hi₃ hib₃).mpr (by omega)⟩)
          · have := Stream.start_lt (s := s) (show k < i₂ by omega)
            have : i = i₂ := entry_inj (F := s.start k - 1) h4 (by omega) (by omega) (by omega) (by omega)
            subst this
            exact Or.inl h2
        · obtain ⟨i, hi, hib, rfl, hP'⟩ := hr4 e (Array.mem_filter.mp he).1
          exact ⟨i, hi, by omega, rfl, hP'⟩
        · rcases Nat.lt_or_ge k i with hi | hi
          · exact (hr5 i hi h2).2
          · have : i = k := by omega
            subst this; exact hPk
      · next hnext =>
        -- ahead: a later message, staged unless it already is
        simp only [beq_iff_eq, hfr, pred_add_one] at hnext
        have hkd : k ≠ d := fun h => hnext (h ▸ rfl)
        have hdk : d < k := by
          rcases Nat.lt_or_ge k d with hl | hl
          · have := Stream.start_lt (s := s) hl; omega
          · omega
        have hkb : s.start k < s.start d + 32768 := by omega
        have hmem : ∀ e, e ∈ (if c.stagedReliable.any (fun e => e.seq == (s.start k).toUInt16) = true then
              c.stagedReliable else c.stagedReliable.push ⟨(s.start k).toUInt16, s.span k, s.packet k⟩) →
            e ∈ c.stagedReliable ∨ e = s.entry k := by
          intro e he
          split at he
          · exact Or.inl he
          · rcases Array.mem_push.mp he with he | rfl
            · exact Or.inl he
            · exact Or.inr rfl
        refine ⟨d, Nat.le_refl _, ⟨hfr, fun e he => ?_, ?_⟩, by simp, fun h => absurd h hkd,
          fun i _ _ hi => Or.inr ?_, fun e he => ?_, fun i h1 h2 => by omega, fun _ _ => Or.inr ?_⟩
        · rcases hmem e he with he | rfl
          · exact hst e he
          · exact ⟨k, hdk, hW, rfl⟩
        · simp only
          split
          · exact hnd
          · next hany =>
            simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
            refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
            intro a ha b hb
            simp only [List.mem_singleton] at hb
            subst hb
            intro heq
            subst heq
            obtain ⟨e, he, hes⟩ := List.mem_map.mp ha
            exact hany (Array.any_eq_true'.mpr ⟨e, Array.mem_toList_iff.mp he, by simp [hes]⟩)
        · simp only
          split
          · exact hi
          · exact Array.mem_push_of_mem _ hi
        · rcases hmem e he with he | rfl
          · exact hPold e he
          · exact ⟨k, hdk, hkb, rfl, hPk⟩
        · simp only
          split
          · next hany =>
            obtain ⟨e, he, hes⟩ := Array.any_eq_true'.mp hany
            obtain ⟨i, hi, hib, rfl, -⟩ := hPi e he
            have := Stream.start_lt (s := s) hi
            have : i = k := Stream.eq_of_wrapped (F := s.start d - 1) (by simpa [Stream.entry] using hes)
              (by omega) (by have := half_of_window hib; omega) (by omega) (by omega)
            subst this
            exact he
          · exact Array.mem_push_self

/-- One arrival: the channel delivers the next messages in order, none
twice, and the arrival of message `d` itself always delivers it. -/
theorem step {s : Stream} {c : Channel} {d : Nat} (h : Inv s c d) (k : Nat) (hk : Fits s d k) :
    let r := receiveReliableSpan c (s.start k).toUInt16 (s.span k) (s.packet k)
    ∃ j, d ≤ j ∧ Inv s r.1 j ∧ r.2.toList = (List.range' d (j - d)).map s.out ∧ (k = d → d < j) := by
  obtain ⟨j, hj, hinv, hout, hnext, -⟩ := step_spec h k hk (fun _ => True)
    (fun e he => by
      obtain ⟨i, hi, hib, rfl⟩ := h.staged e he
      exact ⟨i, hi, by have := half_of_window hib; have := Stream.start_pos (s := s) d; omega, rfl, trivial⟩)
    trivial
  exact ⟨j, hj, hinv, hout, hnext⟩

/-! ## A run of arrivals -/

/-- The channel fed the reliable arrivals `ks` (message numbers, in the
order they arrive): the channel after, and everything it delivered. -/
def feed (s : Stream) : Channel → List Nat → Channel × List (Nat × Packet)
  | c, [] => (c, [])
  | c, k :: ks =>
    let r := receiveReliableSpan c (s.start k).toUInt16 (s.span k) (s.packet k)
    let r' := feed s r.1 ks
    (r'.1, r.2.toList ++ r'.2)

/-- Every arrival fits the frontier at the moment it arrives, the channel
having delivered `d` messages before the first. -/
def AllFit (s : Stream) : Channel → Nat → List Nat → Prop
  | _, _, [] => True
  | c, d, k :: ks =>
    let r := receiveReliableSpan c (s.start k).toUInt16 (s.span k) (s.packet k)
    Fits s d k ∧ AllFit s r.1 (d + r.2.size) ks

/-- Whatever the network does within the bounds of `Fits` (loses,
duplicates, reorders or delays datagrams), the channel delivers messages
`d`, `d+1`, ... in order, none twice and none made up. -/
theorem feed_spec {s : Stream} : ∀ (ks : List Nat) {c : Channel} {d : Nat}, Inv s c d →
    AllFit s c d ks →
    ∃ n, Inv s (feed s c ks).1 (d + n) ∧ (feed s c ks).2 = (List.range' d n).map s.out
  | [], c, d, h, _ => ⟨0, by simpa [feed] using h, by simp [feed]⟩
  | k :: ks, c, d, h, hf => by
    obtain ⟨hk, hrest⟩ := hf
    obtain ⟨j, hj, hinv, hout, -⟩ := step h k hk
    generalize hr : receiveReliableSpan c (s.start k).toUInt16 (s.span k) (s.packet k) = r at hinv hout hrest
    have hsize : r.2.size = j - d := by
      rw [← Array.length_toList, hout]
      simp
    rw [hsize, show d + (j - d) = j by omega] at hrest
    obtain ⟨n, hinv', hout'⟩ := feed_spec ks hinv hrest
    refine ⟨j - d + n, ?_, ?_⟩
    · simp only [feed, hr]
      rwa [show d + (j - d + n) = j + n by omega]
    · simp only [feed, hr, hout, hout']
      obtain ⟨m, rfl⟩ : ∃ m, j = d + m := ⟨j - d, by omega⟩
      rw [show d + m - d = m by omega, ← List.map_append, List.range'_append_1]

/-- From a fresh channel: the reliable packets delivered are exactly
messages `0 .. n-1` of the stream, each once, in order. -/
theorem feed_fresh (s : Stream) (ks : List Nat) (hf : AllFit s {} 0 ks) :
    ∃ n, (feed s {} ks).2 = (List.range n).map s.out := by
  obtain ⟨n, -, h⟩ := feed_spec ks (inv_default s) hf
  exact ⟨n, by rw [h, List.range_eq_range']⟩

/-- Progress: an arrival of the next message always delivers it (and what
was staged behind it), whatever came before. -/
theorem step_next {s : Stream} {c : Channel} {d : Nat} (h : Inv s c d) (hk : Fits s d d) :
    (receiveReliableSpan c (s.start d).toUInt16 (s.span d) (s.packet d)).2.toList.head?
      = some (s.out d) := by
  obtain ⟨j, -, -, hout, hnext⟩ := step h d hk
  rw [hout]
  obtain ⟨n, hn⟩ : ∃ n, j - d = n + 1 := ⟨j - d - 1, by have := hnext rfl; omega⟩
  rw [hn, List.range'_succ]
  rfl

/-- The next message always fits: it starts one past the frontier. -/
theorem fits_next (s : Stream) (d : Nat) : Fits s d d := by
  have := Stream.start_pos (s := s) d
  constructor <;> omega

/-! ## The receive path the peer runs

`Peer` runs `receiveReliableAndRelease` for a reliable delivery (a plain
packet or a completed fragment set) and `receiveUnreliable` for an
unreliable one. The unreliable side never touches what `Inv` reads, and a
reliable delivery's reliable packets come first in what it hands out,
before the unreliable packets it releases. -/

theorem inv_of_same {s : Stream} {c c' : Channel} {d : Nat}
    (hs : c'.stagedReliable = c.stagedReliable)
    (hf : c'.incomingReliableSequenceNumber = c.incomingReliableSequenceNumber) (h : Inv s c d) :
    Inv s c' d :=
  ⟨hf ▸ h.frontier, hs ▸ h.staged, hs ▸ h.nodup⟩

theorem receiveUnreliable_inv {s : Stream} {c : Channel} {d : Nat} (h : Inv s c d)
    (reliableSeq seq : UInt16) (packet : Packet) : Inv s (receiveUnreliable c reliableSeq seq packet).1 d := by
  unfold receiveUnreliable
  repeat' split
  all_goals first | exact h | exact inv_of_same (c := c) rfl rfl h

theorem receiveReliableAndRelease_spec {s : Stream} {c : Channel} {d : Nat} (h : Inv s c d)
    (k : Nat) (hk : Fits s d k) :
    let r := receiveReliableAndRelease c (s.start k).toUInt16 (s.span k) (s.packet k)
    ∃ j released, d ≤ j ∧ Inv s r.1 j ∧
      r.2.toList = (List.range' d (j - d)).map s.packet ++ released ∧ (k = d → d < j) := by
  obtain ⟨j, hj, hinv, hout, hnext⟩ := step h k hk
  unfold receiveReliableAndRelease
  generalize receiveReliableSpan c (s.start k).toUInt16 (s.span k) (s.packet k) = r at hinv hout ⊢
  obtain ⟨c', dels⟩ := r
  simp only at hinv hout ⊢
  split
  · next hemp =>
    refine ⟨j, [], hj, hinv, ?_, hnext⟩
    have : dels.toList = [] := by simpa using hemp
    rw [this] at hout
    have hlen := congrArg List.length hout
    simp at hlen
    simp [show j - d = 0 by omega]
  · obtain ⟨hs, hf⟩ := releaseStagedUnreliable_reliable c'
    refine ⟨j, (releaseStagedUnreliable c').2.toList, hj, inv_of_same hs hf hinv, ?_, hnext⟩
    simp only [Array.toList_append, Array.toList_map, hout, List.map_map]
    rfl

end Lenet.Proofs.Delivery
