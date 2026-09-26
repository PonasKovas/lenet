import Std.Tactic.BVDecide
import Lenet.Time
import Lenet.Host

/-!
# `Host.nextDeadline`: the earliest scheduled timer

The driver-facing contract (TODO.md Phase 4; lenet-rs schedules its service
ticks from it): the returned deadline

1. is always present and is one of the host's actual timers
   (`nextDeadline_mem`) - never a spurious wakeup time;
2. is no later than any scheduled timer (`nextDeadline_earliest`) - a driver
   that sleeps until it never skips pending work.

(2) is about the **wrap-aware** order, and holds whenever the timers lie
within ENet's 24-hour disambiguation window (`Time.overflow`) of some base
point - the same assumption `Time.less` itself rests on. Proving it exposed
that the original fold used numeric `min`, which is wrong across the 2^32
wrap (now = 2^32-20, timers at 2^32-10 and 5: `min` picked 5, 15 ms late);
the fold now uses `Time.earliest`.

Structure: `nextDeadline` equals a flat left fold of `Time.earliestSome`
over `hostTimers` (`nextDeadline_eq_fold`); the generic fold lemmas
(membership, lower bound) then carry the result.
-/

namespace Lenet.Proofs

open Time

/-! ## Wrap-aware order inside a window -/

/-- `t` lies within the disambiguation window after `base`. -/
def InWindow (base t : UInt32) : Prop := t - base < Time.overflow

/-- Inside a common window, `Time.less` is the plain order of offsets from
the base. -/
theorem less_iff_offset {base a b : UInt32} (ha : InWindow base a) (hb : InWindow base b) :
    Time.less a b = true ↔ a - base < b - base := by
  unfold InWindow at ha hb
  unfold Time.less
  simp only [Time.overflow] at *
  bv_decide

theorem earliest_mem (a b : UInt32) : Time.earliest a b = a ∨ Time.earliest a b = b := by
  unfold Time.earliest
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem earliest_le {base a b : UInt32} (ha : InWindow base a) (hb : InWindow base b) :
    Time.earliest a b - base ≤ a - base ∧ Time.earliest a b - base ≤ b - base := by
  unfold Time.earliest
  split
  · next h =>
    have := (less_iff_offset hb ha).mp h
    exact ⟨UInt32.le_of_lt this, UInt32.le_refl _⟩
  · next h =>
    have : ¬ b - base < a - base := fun h' => h ((less_iff_offset hb ha).mpr h')
    exact ⟨UInt32.le_refl _, UInt32.not_lt.mp this⟩

/-! ## Generic fold lemmas -/

/-- The fold's result is the seed or one of the folded timestamps. -/
theorem fold_mem : ∀ (l : List UInt32) (acc : Option UInt32) (v : UInt32),
    l.foldl Time.earliestSome acc = some v → acc = some v ∨ v ∈ l
  | [], _, _, h => Or.inl h
  | x :: xs, acc, v, h => by
    rcases fold_mem xs _ v h with h1 | h1
    · cases acc with
      | none =>
        simp only [Time.earliestSome, Option.some.injEq] at h1
        exact Or.inr (h1 ▸ List.mem_cons_self)
      | some a =>
        simp only [Time.earliestSome, Option.some.injEq] at h1
        rcases earliest_mem a x with e | e <;> rw [e] at h1
        · exact Or.inl (h1 ▸ rfl)
        · exact Or.inr (h1 ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem x h1)

/-- Folding from a present seed stays present. -/
theorem fold_some : ∀ (l : List UInt32) (a : UInt32),
    ∃ v, l.foldl Time.earliestSome (some a) = some v
  | [], a => ⟨a, rfl⟩
  | x :: xs, a => fold_some xs (Time.earliest a x)

/-- Inside a common window, the fold's result is no later than the seed and
every folded timestamp. -/
theorem fold_le {base : UInt32} : ∀ (l : List UInt32) (acc : Option UInt32) (v : UInt32),
    (∀ t ∈ l, InWindow base t) → (∀ a, acc = some a → InWindow base a) →
    l.foldl Time.earliestSome acc = some v →
      (∀ a, acc = some a → v - base ≤ a - base) ∧ ∀ t ∈ l, v - base ≤ t - base
  | [], acc, v, _, _, h => by
    refine ⟨fun a ha => ?_, fun t ht => absurd ht List.not_mem_nil⟩
    rw [ha] at h; cases h; exact UInt32.le_refl _
  | x :: xs, acc, v, hl, hacc, h => by
    have hx := hl x List.mem_cons_self
    -- the seed after one step, `e`, is below the old seed and `x`
    obtain ⟨e, he, heW, heA, heX⟩ : ∃ e, Time.earliestSome acc x = some e ∧ InWindow base e ∧
        (∀ a, acc = some a → e - base ≤ a - base) ∧ e - base ≤ x - base := by
      cases acc with
      | none =>
        exact ⟨x, rfl, hx, fun _ h => (by cases h), UInt32.le_refl _⟩
      | some a =>
        have ha := hacc a rfl
        refine ⟨Time.earliest a x, rfl, ?_, fun a' h' => ?_, (earliest_le ha hx).2⟩
        · rcases earliest_mem a x with e | e <;> rw [e]
          · exact ha
          · exact hx
        · cases h'; exact (earliest_le ha hx).1
    have ih := fold_le xs (some e) v (fun t ht => hl t (List.mem_cons_of_mem x ht))
      (fun a h => by cases h; exact heW) (he ▸ h)
    have hve := ih.1 e rfl
    refine ⟨fun a ha => UInt32.le_trans hve (heA a ha), fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact UInt32.le_trans hve heX
    · exact ih.2 t ht

/-! ## `nextDeadline` as a flat fold -/

/-- Keepalive eligibility, exactly as `nextDeadline` tests it. -/
abbrev pingEligible (p : Peer) : Prop :=
  p.state == .connected ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty

/-- One peer's scheduled timers: retransmit boundaries of in-flight reliable
commands, then the keepalive boundary if the peer could ping now. -/
def peerTimers (p : Peer) : List UInt32 :=
  p.sentReliableCommands.toList.map (fun c => c.sentTime + c.roundTripTimeout) ++
    (if pingEligible p then [p.lastReceiveTime + p.pingInterval] else [])

/-- Every timer the host has scheduled, in `nextDeadline`'s fold order. -/
def hostTimers (h : Host) : List UInt32 :=
  h.peers.toList.flatMap peerTimers ++
    [h.bandwidthThrottleEpoch + Constants.bandwidthThrottleInterval]

theorem peer_step_eq (acc : Option UInt32) (p : Peer) :
    (let inFlight := p.sentReliableCommands.foldl (init := acc) fun a outCmd =>
        Time.earliestSome a (outCmd.sentTime + outCmd.roundTripTimeout)
      if pingEligible p then Time.earliestSome inFlight (p.lastReceiveTime + p.pingInterval)
      else inFlight) = (peerTimers p).foldl Time.earliestSome acc := by
  simp only [peerTimers, List.foldl_append, List.foldl_map, ← Array.foldl_toList]
  split <;> rfl

theorem peers_fold_eq : ∀ (ps : List Peer) (acc : Option UInt32),
    ps.foldl (fun acc p =>
        let inFlight := p.sentReliableCommands.foldl (init := acc) fun a outCmd =>
          Time.earliestSome a (outCmd.sentTime + outCmd.roundTripTimeout)
        if pingEligible p then Time.earliestSome inFlight (p.lastReceiveTime + p.pingInterval)
        else inFlight) acc =
      (ps.flatMap peerTimers).foldl Time.earliestSome acc
  | [], _ => rfl
  | p :: ps, acc => by
    rw [List.foldl_cons, peer_step_eq, peers_fold_eq ps, List.flatMap_cons, List.foldl_append]

theorem nextDeadline_eq_fold (h : Host) :
    h.nextDeadline = (hostTimers h).foldl Time.earliestSome none := by
  unfold Host.nextDeadline hostTimers
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← peers_fold_eq, Array.foldl_toList]

/-! ## The driver-facing contract -/

/-- `nextDeadline` is always scheduled, and is one of the host's timers. -/
theorem nextDeadline_mem (h : Host) : ∃ d, h.nextDeadline = some d ∧ d ∈ hostTimers h := by
  rw [nextDeadline_eq_fold, hostTimers, List.foldl_append]
  obtain ⟨d, hd⟩ : ∃ d, [h.bandwidthThrottleEpoch + Constants.bandwidthThrottleInterval].foldl
      Time.earliestSome ((h.peers.toList.flatMap peerTimers).foldl Time.earliestSome none) =
        some d := by
    simp only [List.foldl_cons, List.foldl_nil, Time.earliestSome]
    exact ⟨_, rfl⟩
  refine ⟨d, hd, ?_⟩
  rw [← List.foldl_append] at hd
  rcases fold_mem _ none d hd with h1 | h1
  · cases h1
  · exact h1

/-- **No timer is earlier than `nextDeadline`**: when every scheduled timer
lies within the disambiguation window of a common base, the returned
deadline's offset from the base is minimal - equivalently no timer is
wrap-aware `less` than it. -/
theorem nextDeadline_earliest (h : Host) (base : UInt32)
    (hw : ∀ t ∈ hostTimers h, InWindow base t) {d : UInt32} (hd : h.nextDeadline = some d) :
    ∀ t ∈ hostTimers h, d - base ≤ t - base ∧ Time.less t d = false := by
  rw [nextDeadline_eq_fold] at hd
  have hle := (fold_le (base := base) _ none d hw (fun _ h => by cases h) hd).2
  have hdm : d ∈ hostTimers h := by
    rcases fold_mem _ none d hd with h1 | h1
    · cases h1
    · exact h1
  intro t ht
  refine ⟨hle t ht, ?_⟩
  cases hl : Time.less t d
  · rfl
  · have := (less_iff_offset (hw t ht) (hw d hdm)).mp hl
    exact absurd (hle t ht) (UInt32.not_le.mpr this)

end Lenet.Proofs
