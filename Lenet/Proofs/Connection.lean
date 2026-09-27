import Lenet.Proofs.Window
import Lenet.Proofs.Delivery

/-!
# Reliable delivery over a whole connection

The two halves joined: one channel of a connection, the sender's window
code on one side (`Proofs/Window`), the receiver's receive path on the
other (`Proofs/Delivery`), and a network between them. Whatever the network
does, the receiver hands out an honest sender's reliable packets in order,
each once, and loses none the sender stopped sending.

The model (`Link`, `Op`) runs Lenet's own code at both ends:

* The sender numbers each message it queues with `nextReliableSequenceNumber`,
  sends first sends in sequence order (as the peer does,
  `SpanInv.consecutive`), each only when `canSendReliable` lets it, taking
  its window with `acquireReliableWindow`, and resends any message in
  flight at any time. An ACK retires the command in flight with its
  sequence number and releases its window (`releaseReliableWindow`), as
  `removeSentReliableCommand` does.
* The receiver runs `receiveReliableSpan` on each arrival and ACKs it unless
  `isReliableTooFarAhead` (`Peer.tooFarAhead`).
* The network loses, duplicates, reorders and delays copies of messages and
  ACKs, with one bound: a copy or ACK still in transit once the sender has
  made more than `D` first sends since it was sent is lost, for any
  `D ≤ 12288` (three windows). Without a bound, a datagram delayed past a
  whole wrap of sequence numbers is read as a new one, by ENet too.

What the model leaves out: a fragment set travels as one message, sent,
acknowledged and resent whole (`Proofs/Reassembly` and
`receiveReliableAndRelease_spec` cover the receiver's side of fragments);
retransmission timers, which only choose when to resend; the handshake and
the disconnect, which bound the connection's life; and other channels,
which do not touch this one.

Results, from the start of a connection, after any operations:

* `run_out`: the receiver has handed out exactly messages `0 .. d-1`, in order.
* `run_fits`: every copy the network can still deliver `Fits` the receiver
  (`Proofs/Delivery`), which is what the two halves needed from each other.
* `run_retired`: a message the sender retired a command of is delivered or
  staged: no ACK retires a packet the receiver dropped.
* `run_ahead_admitted`: every copy ahead of the receiver's frontier is
  inside its receive window. So the receiver never drops a copy for being
  ahead, and the proof holds with ENet's ACK rule too: a Lenet sender is
  safe with an ENet receiver. (With ENet's sender, whose span is seven
  windows, this fails; `isReliableTooFarAhead` is the receiver's defense.)
* `deliver_next`: a copy of the next message delivers it.

The argument: every command the sender retired belongs to a message the
receiver has (`Good.retired`), so the receiver's frontier is at most one
before the oldest command in flight, and the sender's span (six windows,
`ChanOk.span`) puts every copy within six windows past the frontier's
window (`sent_window`), the last the receive window takes. The delay bound
puts it at most nine behind.
-/

namespace Lenet.Proofs.Connection

open Delivery

/-- One channel of a connection, one way: the sender's channel (the
outgoing side), the receiver's (the incoming side), and what the network
carries. Numbers are unwrapped; the channels hold them wrapped to 16 bits. -/
structure Link where
  /-- The sender's channel. -/
  snd  : Channel := {}
  /-- Messages queued: they take numbers `1 .. start n - 1`. -/
  n    : Nat := 0
  /-- The last number sent (0 before the first). -/
  S    : Nat := 0
  /-- The numbers in flight: sent, not yet acknowledged. -/
  infl : List Nat := []
  /-- The receiver's channel. -/
  rcv  : Channel := {}
  /-- Messages delivered. -/
  d    : Nat := 0
  /-- What the receiver handed out, in order. -/
  out  : List (Nat × Packet) := []
  /-- Copies in transit: the message, and `S` when it was sent. -/
  net  : List (Nat × Nat) := []
  /-- ACKs in transit: the message, the number acknowledged, and `S` when it
  was sent. -/
  acks : List (Nat × Nat × Nat) := []

/-- What can happen next. -/
inductive Op
  /-- The application queues the next message. -/
  | queue
  /-- The sender sends its next number for the first time, if its window
  lets it. -/
  | send
  /-- The sender (re)sends message `k`, if it is in flight. -/
  | emit (k : Nat)
  /-- The network delivers copy `i` to the receiver. -/
  | deliver (i : Nat)
  /-- The network delivers ACK `i` to the sender. -/
  | ack (i : Nat)

variable (s : Stream) (D : Nat)

namespace Link

/-- Queues message `n`: the channel numbers its `span n` commands. -/
def queue (L : Link) : Link :=
  { L with snd := Nat.repeat (fun c => c.nextReliableSequenceNumber.1) (s.span L.n) L.snd, n := L.n + 1 }

/-- The next first send, when the window lets it (`canSendReliable`). -/
def sendNext (L : Link) : Link :=
  if L.S + 1 < s.start L.n ∧ L.snd.canSendReliable (L.S + 1).toUInt16 = true then
    { L with snd := L.snd.acquireReliableWindow (L.S + 1).toUInt16, S := L.S + 1, infl := (L.S + 1) :: L.infl }
  else L

/-- A copy of message `k`, sent whole and in flight. -/
def emit (L : Link) (k : Nat) : Link :=
  if s.start (k + 1) - 1 ≤ L.S ∧ s.start k ∈ L.infl then { L with net := L.net ++ [(k, L.S)] } else L

/-- The receiver takes copy `i`, unless it was lost to the delay bound, and
ACKs each of its numbers unless it is too far ahead. -/
def deliver (L : Link) (i : Nat) : Link :=
  match L.net[i]? with
  | some (k, t) =>
    if L.S ≤ t + D then
      let acked := !L.rcv.isReliableTooFarAhead (s.start k).toUInt16
      let r := L.rcv.receiveReliableSpan (s.start k).toUInt16 (s.span k) (s.packet k)
      { L with rcv := r.1, d := L.d + r.2.size, out := L.out ++ r.2.toList,
               acks := if acked then L.acks ++ (List.range' (s.start k) (s.span k)).map (fun x => (k, x, L.S))
                       else L.acks }
    else L
  | none => L

/-- An ACK of number `x` (wrapped): retires the command in flight with that
sequence number, if any, and releases its window. -/
def retire (L : Link) (x : Nat) : Link :=
  match L.infl.find? (fun y => y.toUInt16 == x.toUInt16) with
  | some y => { L with infl := L.infl.erase y, snd := L.snd.releaseReliableWindow x.toUInt16 }
  | none => L

/-- The sender takes ACK `i`, unless it was lost to the delay bound. -/
def ackArrive (L : Link) (i : Nat) : Link :=
  match L.acks[i]? with
  | some (_, x, t) => if L.S ≤ t + D then L.retire x else L
  | none => L

end Link

def Op.apply (L : Link) : Op → Link
  | .queue => L.queue s
  | .send => L.sendNext s
  | .emit k => L.emit s k
  | .deliver i => L.deliver s D i
  | .ack i => L.ackArrive D i

/-- The link after `ops`, from `L`. -/
def run : Link → List Op → Link
  | L, [] => L
  | L, op :: ops => run (op.apply s D L) ops

/-! ## The invariant -/

/-- The receiver has message `m`: delivered or staged. -/
def Recv (L : Link) (m : Nat) : Prop := m < L.d ∨ Staged L.rcv.stagedReliable (s.entry m)

/-- The numbers queued and not sent yet, wrapped: what `ChanOk` calls
`pend`. -/
def pendW (L : Link) : List UInt16 := (List.range (s.start L.n - 1 - L.S)).map fun i => (L.S + 1 + i).toUInt16

/-- **The invariant.** The sender keeps `ChanOk` (Proofs/Window) over its
numbers, which are the unwrapped ones wrapped; the receiver keeps `Inv`
(Proofs/Delivery) and has handed out messages `0 .. d-1`; what it has was
sent; every number the sender retired belongs to a message the receiver
has; and what is in transit was sent in flight, within the span. -/
structure Good (L : Link) : Prop where
  sent_le  : L.S ≤ s.start L.n - 1
  counter  : L.snd.outgoingReliableSequenceNumber = (s.start L.n - 1).toUInt16
  chan     : ChanOk L.snd (pendW s L) (L.infl.map (·.toUInt16))
  infl_le  : ∀ y ∈ L.infl, y ≤ L.S ∧ L.S < y + 65536
  inv      : Delivery.Inv s L.rcv L.d
  out      : L.out = (List.range L.d).map s.out
  deliv    : s.start L.d - 1 ≤ L.S
  staged   : ∀ (k : UInt16) (e : StagedReliable), L.rcv.stagedReliable[k]? = some e →
    ∃ i, L.d < i ∧ s.start i < s.start L.d + 32768 ∧ e = s.entry i ∧ s.start (i + 1) - 1 ≤ L.S
  retired  : ∀ m x, s.start m ≤ x → x < s.start (m + 1) → x ≤ L.S → x ∉ L.infl → Recv s L m
  net      : ∀ p ∈ L.net, p.2 ≤ L.S ∧ s.start (p.1 + 1) - 1 ≤ p.2 ∧ p.2 - s.start p.1 ≤ p.2 % 4096 + 20480
  acks     : ∀ a ∈ L.acks, s.start a.1 ≤ a.2.1 ∧ a.2.1 < s.start (a.1 + 1) ∧ a.2.2 ≤ L.S ∧
    s.start (a.1 + 1) - 1 ≤ a.2.2 ∧ a.2.2 ≤ s.start a.1 + D + 24575 ∧ Recv s L a.1

theorem good_init : Good s D {} where
  sent_le := by simp [Stream.start]
  counter := by simp [Stream.start]
  chan := by
    have : pendW s {} = [] := by simp [pendW, Stream.start]
    rw [this]
    exact chanOk_default
  infl_le := by simp
  inv := inv_default s
  out := rfl
  deliv := by simp [Stream.start]
  staged := fun k e he => by simp at he
  retired := by
    intro m x h1 _ h3 _
    have := Stream.start_pos (s := s) m
    simp at h3; omega
  net := by simp
  acks := by simp

/-! ## What the invariant gives -/

variable {s D}

/-- The sender's last number sent, wrapped, is the frontier `ChanOk` means. -/
theorem frontier_eq {L : Link} (h : Good s D L) : frontier L.snd (pendW s L) = L.S.toUInt16 := by
  have := h.sent_le
  simp only [frontier, pendW, List.length_map, List.length_range, h.counter]
  apply UInt16.toNat.inj
  simp only [UInt16.toNat_sub, Nat.toUInt16, UInt16.toNat_ofNat', Nat.reducePow]
  omega

theorem toNat_sub_wrap {a b : Nat} (h1 : b ≤ a) (h2 : a < b + 65536) :
    (a.toUInt16 - b.toUInt16).toNat = a - b := by
  simp only [UInt16.toNat_sub, Nat.toUInt16, UInt16.toNat_ofNat', Nat.reducePow]
  omega

/-- **The sender's span, unwrapped**: every number in flight is at most five
windows and a part behind the last one sent. -/
theorem span {L : Link} (h : Good s D L) {y : Nat} (hy : y ∈ L.infl) : L.S - y ≤ L.S % 4096 + 20480 := by
  have hs := h.chan.span y.toUInt16 (List.mem_map_of_mem hy)
  rw [frontier_eq h, toNat_sub_wrap (h.infl_le y hy).1 (h.infl_le y hy).2] at hs
  simp only [Nat.toUInt16, UInt16.toNat_ofNat', Nat.reducePow] at hs
  omega

/-- Message `d`, the next to deliver, is not staged. -/
theorem next_not_staged {c : Channel} {d : Nat} (h : Delivery.Inv s c d) : ¬ Staged c.stagedReliable (s.entry d) := by
  intro hm
  obtain ⟨-, i, hi, hib, he⟩ := h.staged _ _ hm
  have := Stream.start_lt (s := s) hi
  have := Stream.start_pos (s := s) d
  have := entry_inj (F := s.start d - 1) he (by omega) (by omega) (by omega) (by omega)
  omega

/-- **The receiver keeps up**: the last number sent is at most six windows
past the frontier's window, the last one the receive window takes. The
next message's first number is either not sent yet or in flight (it is not
delivered, not staged, so not retired), and what is in flight spans at
most six windows. -/
theorem sent_window {L : Link} (h : Good s D L) : L.S / 4096 ≤ (s.start L.d - 1) / 4096 + 6 := by
  by_cases hsd : s.start L.d ≤ L.S
  · by_cases hin : s.start L.d ∈ L.infl
    · have := span h hin
      omega
    · rcases h.retired L.d (s.start L.d) (Nat.le_refl _) (Stream.start_lt_succ L.d) hsd hin with h' | h'
      · omega
      · exact absurd h' (next_not_staged h.inv)
  · omega

/-- **Every arrival fits**: a copy still in transit starts within nine
windows behind the frontier's window (the delay bound) and six ahead. -/
theorem fits {L : Link} (h : Good s D L) (hD : D ≤ 12288) {k t : Nat} (hp : (k, t) ∈ L.net)
    (ht : L.S ≤ t + D) : Fits s L.d k := by
  obtain ⟨ht1, ht2, ht3⟩ := h.net _ hp
  have := sent_window h
  have := h.deliv
  have := Stream.start_lt_succ (s := s) k
  constructor <;> simp only at ht1 ht2 ht3 <;> omega

/-- Two numbers congruent modulo a wrap and less than a wrap apart are equal. -/
theorem eq_of_toUInt16 {x y : Nat} (h : y.toUInt16 = x.toUInt16) (h1 : y < x + 65536) (h2 : x < y + 65536) :
    y = x := by
  have := congrArg UInt16.toNat h
  simp only [Nat.toUInt16, UInt16.toNat_ofNat', Nat.reducePow] at this
  omega

theorem msg_unique {m m' x : Nat} (h1 : s.start m ≤ x) (h2 : x < s.start (m + 1)) (h1' : s.start m' ≤ x)
    (h2' : x < s.start (m' + 1)) : m = m' := by
  rcases Nat.lt_trichotomy m m' with hl | he | hl
  · have := Stream.start_le (s := s) (show m + 1 ≤ m' by omega); omega
  · exact he
  · have := Stream.start_le (s := s) (show m' + 1 ≤ m by omega); omega

/-! ## Every operation keeps the invariant -/

theorem repeat_next (c : Channel) : ∀ n : Nat,
    (Nat.repeat (fun c => c.nextReliableSequenceNumber.1) n c).outgoingReliableSequenceNumber =
      c.outgoingReliableSequenceNumber + n.toUInt16 ∧
    (Nat.repeat (fun c => c.nextReliableSequenceNumber.1) n c).reliableWindows = c.reliableWindows
  | 0 => by simp [Nat.repeat]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := repeat_next c n
    have e : Nat.repeat (fun c => c.nextReliableSequenceNumber.1) (n + 1) c =
        (Nat.repeat (fun c => c.nextReliableSequenceNumber.1) n c).nextReliableSequenceNumber.1 := rfl
    rw [e]
    generalize Nat.repeat _ n c = c' at h1 h2 ⊢
    refine ⟨?_, h2⟩
    simp only [Channel.nextReliableSequenceNumber, h1]
    have := c.outgoingReliableSequenceNumber.toNat_lt
    u16_omega

theorem pendW_queue {L : Link} (h : Good s D L) :
    pendW s (L.queue s) = pendW s L ++
      (List.range (s.span L.n)).map fun i => L.snd.outgoingReliableSequenceNumber + 1 + i.toUInt16 := by
  have h1 := h.sent_le
  have hsp := s.span_pos L.n
  have hst : s.start (L.n + 1) = s.start L.n + s.span L.n := rfl
  have hpos := Stream.start_pos (s := s) L.n
  simp only [pendW, Link.queue]
  rw [show s.start (L.n + 1) - 1 - L.S = (s.start L.n - 1 - L.S) + s.span L.n by omega, List.range_add,
    List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, h.counter]
  u16_omega

theorem Good.queue {L : Link} (h : Good s D L) : Good s D (L.queue s) := by
  have hst : s.start (L.n + 1) = s.start L.n + s.span L.n := rfl
  have hpos := Stream.start_pos (s := s) L.n
  have hsp := s.span_pos L.n
  obtain ⟨ho, hw⟩ := repeat_next L.snd (s.span L.n)
  refine { sent_le := ?_, counter := ?_, chan := ?_, infl_le := h.infl_le, inv := h.inv, out := h.out,
           deliv := h.deliv, staged := h.staged, retired := h.retired, net := h.net, acks := h.acks }
  · have := h.sent_le
    show L.S ≤ s.start (L.n + 1) - 1
    omega
  · show (Nat.repeat _ _ L.snd).outgoingReliableSequenceNumber = (s.start (L.n + 1) - 1).toUInt16
    rw [ho, h.counter, hst]
    u16_omega
  · rw [pendW_queue h]
    exact h.chan.enqueue (s.span L.n) ho hw

theorem pendW_succ {L : Link} (hlt : L.S + 1 < s.start L.n) :
    pendW s L = (L.S + 1).toUInt16 ::
      (List.range (s.start L.n - 1 - (L.S + 1))).map fun i => (L.S + 1 + 1 + i).toUInt16 := by
  simp only [pendW]
  rw [show s.start L.n - 1 - L.S = (s.start L.n - 1 - (L.S + 1)) + 1 by omega, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 1
  omega

theorem Good.sendNext {L : Link} (h : Good s D L) : Good s D (L.sendNext s) := by
  unfold Link.sendNext
  split
  · next hc =>
    obtain ⟨hlt, hcan⟩ := hc
    have hco := ChanOk.send (pendW_succ hlt ▸ h.chan) hcan
    refine { sent_le := ?_, counter := h.counter, chan := hco, infl_le := ?_, inv := h.inv, out := h.out,
             deliv := ?_, staged := ?_, retired := ?_, net := ?_, acks := ?_ }
    · show L.S + 1 ≤ s.start L.n - 1
      omega
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · show L.S + 1 ≤ L.S + 1 ∧ L.S + 1 < L.S + 1 + 65536
        omega
      · have := span h hy
        have := h.infl_le y hy
        show y ≤ L.S + 1 ∧ L.S + 1 < y + 65536
        omega
    · have := h.deliv
      show s.start L.d - 1 ≤ L.S + 1
      omega
    · intro k e he
      obtain ⟨i, a, b, c, d⟩ := h.staged k e he
      exact ⟨i, a, b, c, by show _ ≤ L.S + 1; omega⟩
    · intro m x h1 h2 h3 h4
      have hne : x ≠ L.S + 1 := fun he => h4 (he ▸ List.mem_cons_self)
      exact h.retired m x h1 h2 (by show x ≤ L.S; simp only at h3; omega) fun hx => h4 (List.mem_cons_of_mem _ hx)
    · intro p hp
      obtain ⟨a, b, c⟩ := h.net p hp
      exact ⟨by show _ ≤ L.S + 1; omega, b, c⟩
    · intro a ha
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.acks a ha
      exact ⟨a1, a2, by show _ ≤ L.S + 1; omega, a4, a5, a6⟩
  · exact h

theorem Good.emit {L : Link} (h : Good s D L) (k : Nat) : Good s D (L.emit s k) := by
  unfold Link.emit
  split
  · next hc =>
    refine { sent_le := h.sent_le, counter := h.counter, chan := h.chan, infl_le := h.infl_le, inv := h.inv,
             out := h.out, deliv := h.deliv, staged := h.staged, retired := h.retired, net := ?_, acks := h.acks }
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.net p hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨Nat.le_refl _, hc.1, span h hc.2⟩
  · exact h

theorem release_out (c : Channel) (x : UInt16) :
    (c.releaseReliableWindow x).outgoingReliableSequenceNumber = c.outgoingReliableSequenceNumber := by
  unfold Channel.releaseReliableWindow
  dsimp only
  split <;> rfl

theorem Good.retire {L : Link} (h : Good s D L) (hD : D ≤ 12288) {m x t : Nat} (ha : (m, x, t) ∈ L.acks)
    (ht : L.S ≤ t + D) : Good s D (L.retire x) := by
  unfold Link.retire
  split
  · next y hy =>
    have hmem : y ∈ L.infl := List.mem_of_find?_eq_some hy
    have hyx : y.toUInt16 = x.toUInt16 := by simpa using List.find?_some hy
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.acks _ ha
    simp only at a1 a2 a3 a4 a5 a6
    have hsp := span h hmem
    have hyle := h.infl_le y hmem
    have := Stream.start_lt_succ (s := s) m
    have hyeq : y = x := eq_of_toUInt16 hyx (by omega) (by omega)
    subst hyeq
    have hperm : (L.infl.map (·.toUInt16)).Perm (y.toUInt16 :: (L.infl.erase y).map (·.toUInt16)) :=
      (List.perm_cons_erase hmem).map _
    refine { sent_le := h.sent_le, counter := ?_, chan := (h.chan.perm hperm).release, infl_le := ?_,
             inv := h.inv, out := h.out, deliv := h.deliv, staged := h.staged, retired := ?_, net := h.net,
             acks := h.acks }
    · show (L.snd.releaseReliableWindow y.toUInt16).outgoingReliableSequenceNumber = _
      rw [release_out, h.counter]
    · intro z hz
      exact h.infl_le z (List.mem_of_mem_erase hz)
    · intro m' x' h1 h2 h3 h4
      by_cases hx : x' = y
      · subst hx
        have := msg_unique (s := s) a1 a2 h1 h2
        subst this
        exact a6
      · exact h.retired m' x' h1 h2 h3 fun hm => h4 ((List.mem_erase_of_ne hx).mpr hm)
  · exact h

theorem Good.ackArrive {L : Link} (h : Good s D L) (hD : D ≤ 12288) (i : Nat) : Good s D (L.ackArrive D i) := by
  unfold Link.ackArrive
  split
  · next m x t hget =>
    split
    · next ht => exact h.retire hD (List.mem_of_getElem? hget) ht
    · exact h
  · exact h

/-- **An arrival**: where the halves meet. The copy fits (`fits`), so the
receiver's step does what `step_spec` says; what the receiver had it
still has; and it has the copy afterwards (delivered or staged) unless the
copy is behind, since every copy ahead is inside the receive window. So
every ACK is for something received. -/
theorem Good.deliver {L : Link} (h : Good s D L) (hD : D ≤ 12288) (i : Nat) : Good s D (L.deliver s D i) := by
  unfold Link.deliver
  split
  · next k t hget =>
    split
    · next ht =>
      have hp : (k, t) ∈ L.net := List.mem_of_getElem? hget
      have hfit := fits h hD hp ht
      obtain ⟨n1, n2, n3⟩ := h.net _ hp
      simp only at n1 n2 n3
      have hsw := sent_window h
      have hdl := h.deliv
      have hk1 := Stream.start_lt_succ (s := s) k
      obtain ⟨j, hj, hinv, hout, -, hpers, hcarry, hdel, hrecv⟩ :=
        step_spec h.inv k hfit (fun i => s.start (i + 1) - 1 ≤ L.S)
          (fun k' e he => by obtain ⟨i, a, b, c, d⟩ := h.staged k' e he; exact ⟨i, a, b, c, d⟩) (by omega)
      dsimp only
      generalize L.rcv.receiveReliableSpan (s.start k).toUInt16 (s.span k) (s.packet k) = r at hinv hout hpers hcarry hdel hrecv ⊢
      have hsize : r.2.size = j - L.d := by rw [← Array.length_toList, hout]; simp
      have hdj : L.d + r.2.size = j := by omega
      -- what the receiver had, it still has
      have hkeep : ∀ m, s.start m ≤ L.S → Recv s L m → m < j ∨ Staged r.1.stagedReliable (s.entry m) := by
        intro m hm hR
        rcases hR with hR | hR
        · left; omega
        · rcases Nat.lt_trichotomy L.d m with hl | he | hl
          · exact hpers m hl (by omega) hR
          · subst he; exact absurd hR (next_not_staged h.inv)
          · left; omega
      -- it receives every copy it ACKs, since every copy ahead is inside the
      -- receive window
      have hrk : k < j ∨ Staged r.1.stagedReliable (s.entry k) := by
        rcases Nat.lt_or_ge k L.d with hl | hl
        · left; omega
        · exact hrecv hl (by omega)
      refine { sent_le := h.sent_le, counter := h.counter, chan := h.chan, infl_le := h.infl_le,
               inv := ?_, out := ?_, deliv := ?_, staged := ?_, retired := ?_, net := h.net, acks := ?_ }
      · show Delivery.Inv s r.1 (L.d + r.2.size)
        rw [hdj]; exact hinv
      · show L.out ++ r.2.toList = (List.range (L.d + r.2.size)).map s.out
        rw [hdj, h.out, hout, ← List.map_append, List.range_eq_range', List.range_eq_range']
        have := @List.range'_append_1 0 L.d (j - L.d)
        simp only [Nat.zero_add] at this
        rw [this, show L.d + (j - L.d) = j by omega]
      · show s.start (L.d + r.2.size) - 1 ≤ L.S
        rw [hdj]
        by_cases hjd : j = L.d
        · rw [hjd]; exact hdl
        · have := hdel (j - 1) (by omega) (by omega)
          rwa [show j - 1 + 1 = j by omega] at this
      · show ∀ (k : UInt16) (e : StagedReliable), r.1.stagedReliable[k]? = some e →
          ∃ i, L.d + r.2.size < i ∧ s.start i < s.start (L.d + r.2.size) + 32768 ∧
            e = s.entry i ∧ s.start (i + 1) - 1 ≤ L.S
        rw [hdj]; exact hcarry
      · intro m x h1 h2 h3 h4
        have h3' : x ≤ L.S := h3
        have := hkeep m (by omega) (h.retired m x h1 h2 h3 h4)
        show m < L.d + r.2.size ∨ _
        rwa [hdj]
      · intro a ha
        have goal : ∀ a ∈ L.acks ++ (List.range' (s.start k) (s.span k)).map (fun x => (k, x, L.S)),
            s.start a.1 ≤ a.2.1 ∧ a.2.1 < s.start (a.1 + 1) ∧ a.2.2 ≤ L.S ∧ s.start (a.1 + 1) - 1 ≤ a.2.2 ∧
              a.2.2 ≤ s.start a.1 + D + 24575 ∧ (a.1 < j ∨ Staged r.1.stagedReliable (s.entry a.1)) ∨
            a ∈ (List.range' (s.start k) (s.span k)).map (fun x => (k, x, L.S)) := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.acks a ha
            exact Or.inl ⟨a1, a2, a3, a4, a5, hkeep a.1 (by omega) a6⟩
          · exact Or.inr ha
        have hnew : ∀ a ∈ (List.range' (s.start k) (s.span k)).map (fun x => (k, x, L.S)),
            s.start a.1 ≤ a.2.1 ∧ a.2.1 < s.start (a.1 + 1) ∧ a.2.2 ≤ L.S ∧ s.start (a.1 + 1) - 1 ≤ a.2.2 ∧
              a.2.2 ≤ s.start a.1 + D + 24575 := by
          intro a ha
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_range'_1] at hx
          have hst : s.start (k + 1) = s.start k + s.span k := rfl
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only <;> omega
        show s.start a.1 ≤ a.2.1 ∧ a.2.1 < s.start (a.1 + 1) ∧ a.2.2 ≤ L.S ∧ s.start (a.1 + 1) - 1 ≤ a.2.2 ∧
          a.2.2 ≤ s.start a.1 + D + 24575 ∧ (a.1 < L.d + r.2.size ∨ Staged r.1.stagedReliable (s.entry a.1))
        rw [hdj]
        split at ha
        · rcases goal a ha with hg | hg
          · exact hg
          · obtain ⟨a1, a2, a3, a4, a5⟩ := hnew a hg
            obtain ⟨x, -, rfl⟩ := List.mem_map.mp hg
            exact ⟨a1, a2, a3, a4, a5, hrk⟩
        · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h.acks a ha
          exact ⟨a1, a2, a3, a4, a5, hkeep a.1 (by omega) a6⟩
    · exact h
  · exact h

theorem Good.apply {L : Link} (h : Good s D L) (hD : D ≤ 12288) : ∀ op : Op, Good s D (op.apply s D L)
  | .queue => h.queue
  | .send => h.sendNext
  | .emit k => h.emit k
  | .deliver i => h.deliver hD i
  | .ack i => h.ackArrive hD i

theorem run_good (hD : D ≤ 12288) : ∀ (ops : List Op) {L : Link}, Good s D L → Good s D (run s D L ops)
  | [], _, h => h
  | op :: ops, _, h => run_good hD ops (h.apply hD op)

/-! ## The results -/

/-- **In order, once each, none made up**: from the start of a connection,
after any operations, the receiver has handed out exactly messages
`0 .. d-1` of the sender's stream, in order. -/
theorem run_out (hD : D ≤ 12288) (ops : List Op) :
    let L := run s D {} ops
    L.out = (List.range L.d).map s.out :=
  (run_good hD ops (good_init s D)).out

/-- **The halves meet**: every copy the network can still deliver fits the
receiver's frontier, the bound `Proofs/Delivery` assumes. -/
theorem run_fits (hD : D ≤ 12288) (ops : List Op) :
    let L := run s D {} ops
    ∀ k t, (k, t) ∈ L.net → L.S ≤ t + D → Fits s L.d k :=
  fun _ _ hp ht => fits (run_good hD ops (good_init s D)) hD hp ht

/-- **Nothing retired is lost**: when the sender has retired a command of
message `m` (sent it, and no longer has it in flight), the receiver has
delivered `m` or holds it staged, to deliver once the gap before it fills. -/
theorem run_retired (hD : D ≤ 12288) (ops : List Op) :
    let L := run s D {} ops
    ∀ m x, s.start m ≤ x → x < s.start (m + 1) → x ≤ L.S → x ∉ L.infl →
      m < L.d ∨ Staged L.rcv.stagedReliable (s.entry m) :=
  (run_good hD ops (good_init s D)).retired

/-- **Never past the receive window**: a copy the network can still
deliver, if it is ahead of the receiver's frontier, is inside the receive
window, so the receiver takes it (`admitted_iff`), whatever its ACK rule. -/
theorem run_ahead_admitted (hD : D ≤ 12288) (ops : List Op) :
    let L := run s D {} ops
    ∀ k t, (k, t) ∈ L.net → L.S ≤ t + D → L.d ≤ k →
      s.start k / 4096 < (s.start L.d - 1) / 4096 + 7 := by
  intro L k t hp _ _
  have h : Good s D L := run_good hD ops (good_init s D)
  obtain ⟨n1, n2, -⟩ := h.net _ hp
  have := sent_window h
  have := Stream.start_lt_succ (s := s) k
  simp only at n1 n2
  omega

/-- **Progress**: a copy of the next message, delivered, delivers it. -/
theorem deliver_next {L : Link} (h : Good s D L) (hD : D ≤ 12288) {i t : Nat} (hi : L.net[i]? = some (L.d, t))
    (ht : L.S ≤ t + D) : L.d < (L.deliver s D i).d := by
  have hp : (L.d, t) ∈ L.net := List.mem_of_getElem? hi
  obtain ⟨j, -, -, hout, hnext, -⟩ := step_spec h.inv L.d (fits h hD hp ht) (fun _ => True)
    (fun k e he => by obtain ⟨i, a, b, c, -⟩ := h.staged k e he; exact ⟨i, a, b, c, trivial⟩) trivial
  unfold Link.deliver
  rw [hi]
  simp only [if_pos ht]
  have hsize := congrArg List.length hout
  simp only [Array.length_toList, List.length_map, List.length_range'] at hsize
  have := hnext rfl
  omega

end Lenet.Proofs.Connection
