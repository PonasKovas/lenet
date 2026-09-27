import Lenet.Host
import Lenet.Proofs.Receive

/-!
# Event-level proofs

The application learns about a connection only through events, so they
have to tell a consistent story. Per peer: a connect event only for a peer
that is not already up, receive events only while it is up, and no way
back down but a disconnect event. Hence between two connects of a peer
there is always a disconnect, and no receive arrives outside a
connection. A disconnect with no connect before it is legal: it is how a
client learns its connection attempt failed (ENet does the same).

`EventsWf` states this for a run of events against the peer's phase before
and after, and every per-peer step of the host keeps it:
`handleCommand_wf` (every incoming command), `checkPeerTimeouts_wf`,
`pollPeer_wf`, `queueDisconnect_phase` (the application's disconnect), and
`checkPeerPing_state`. Writing these found two bugs (test/README.md,
"Disconnect events for peers never reported").

`EventsWf.disconnect_between` spells out what it rules out.
`Proofs/HostEvents.lean` lifts it to the host: `Host.handleDatagram`,
`Host.service`, the application's calls and whole runs.
-/

namespace Lenet.Proofs

open Peer

/-- Whether the application has been told a peer is connected. -/
inductive Phase | down | up deriving DecidableEq

/-- A peer is `up` from its connect event until its disconnect event:
connected, disconnecting later, disconnecting, or acknowledging the remote's
disconnect. -/
def phase : PeerState → Phase
  | .connected | .disconnectLater | .disconnecting | .acknowledgingDisconnect => .up
  | _ => .down

/-- `EventsWf a es b`: the events `es` of one peer fit its phase going from
`a` to `b`. A connect only takes a peer from down to up, a receive only
happens while up, and a disconnect ends down from either phase (from down:
a client's failed connection attempt). -/
inductive EventsWf : Phase → List Event → Phase → Prop
  | nil {ph} : EventsWf ph [] ph
  | connect {es ph id d} : EventsWf .up es ph → EventsWf .down (.connect id d :: es) ph
  | disconnect {es ph ph' id d} : EventsWf .down es ph' → EventsWf ph (.disconnect id d :: es) ph'
  | receive {es ph id c pk} : EventsWf .up es ph → EventsWf .up (.receive id c pk :: es) ph

/-- Event runs compose. -/
theorem EventsWf.append {a b c : Phase} {xs ys : List Event} (h1 : EventsWf a xs b) (h2 : EventsWf b ys c) :
    EventsWf a (xs ++ ys) c := by
  induction h1 with
  | nil => exact h2
  | connect _ ih => exact .connect (ih h2)
  | disconnect _ ih => exact .disconnect (ih h2)
  | receive _ ih => exact .receive (ih h2)

def isReceive : Event → Bool | .receive .. => true | _ => false

theorem EventsWf.receives {es : List Event} (h : ∀ e ∈ es, isReceive e) : EventsWf .up es .up := by
  induction es with
  | nil => exact .nil
  | cons e es ih =>
    have he := h e List.mem_cons_self
    cases e with
    | receive => exact .receive (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    | connect => simp [isReceive] at he
    | disconnect => simp [isReceive] at he

theorem EventsWf.split {a b : Phase} : ∀ {xs ys : List Event}, EventsWf a (xs ++ ys) b →
    ∃ m, EventsWf a xs m ∧ EventsWf m ys b
  | [], _, h => ⟨a, .nil, h⟩
  | x :: xs, ys, h => by
    cases h with
    | connect h => obtain ⟨m, h1, h2⟩ := EventsWf.split h; exact ⟨m, .connect h1, h2⟩
    | disconnect h => obtain ⟨m, h1, h2⟩ := EventsWf.split h; exact ⟨m, .disconnect h1, h2⟩
    | receive h => obtain ⟨m, h1, h2⟩ := EventsWf.split h; exact ⟨m, .receive h1, h2⟩

def isDisconnect : Event → Bool | .disconnect .. => true | _ => false

theorem EventsWf.stays_up {b : Phase} : ∀ {es : List Event}, EventsWf .up es b → (∀ e ∈ es, isDisconnect e = false) → b = .up
  | [], .nil, _ => rfl
  | _ :: _, .receive h, hd => h.stays_up fun e he => hd e (List.mem_cons_of_mem _ he)
  | _ :: _, .disconnect _, hd => by simp [isDisconnect] at hd

/-- **Between two connects of a peer there is a disconnect.** -/
theorem EventsWf.disconnect_between {a b : Phase} {xs ys zs : List Event} {id id' : UInt16} {d d' : UInt32}
    (h : EventsWf a (xs ++ .connect id d :: ys ++ .connect id' d' :: zs) b) : ∃ e ∈ ys, isDisconnect e := by
  obtain ⟨m, _, h⟩ := EventsWf.split (xs := xs) (by simpa using h)
  cases h with
  | connect h =>
    obtain ⟨m', h1, h2⟩ := EventsWf.split h
    refine Classical.byContradiction fun hno => ?_
    have := h1.stays_up fun e he => by simpa using fun hd => hno ⟨e, he, hd⟩
    subst this
    cases h2

theorem peerState_beq {a b : PeerState} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-! ## Steps that leave the state alone -/
theorem queueAck_state (p : Peer) (a) : (p.queueAck a).state = p.state := rfl
theorem queueOutgoingCommand_state (p : Peer) (c) : (p.queueOutgoingCommand c).state = p.state := rfl
theorem queueControlCommand_state (p : Peer) (b) : (p.queueControlCommand b).state = p.state := rfl
theorem throttle_state (p : Peer) (r) : (p.throttle r).state = p.state := by
  unfold throttle; split <;> (try split) <;> (try split) <;> rfl
theorem updateRtt_state (p : Peer) (n r) : (p.updateRtt n r).state = p.state := by
  unfold updateRtt; dsimp only
  split <;> (try split) <;> (try split) <;> (try split) <;> simp [throttle_state]
theorem removeSent_state (p : Peer) (c s) : (p.removeSentReliableCommand c s).1.state = p.state := by
  unfold removeSentReliableCommand; dsimp only; split <;> (repeat' split) <;> rfl
theorem pruneAssemblers_state (p : Peer) (c) : (p.pruneAssemblers c).state = p.state := by
  unfold pruneAssemblers; split; split <;> rfl; rfl
theorem receiveOnChannel_state (p : Peer) (c r) : (p.receiveOnChannel c r).1.state = p.state := by
  by_cases h : c.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ h]; exact pruneAssemblers_state _ _
  · rw [receiveOnChannel_out _ _ _ h]
theorem receiveOnChannel_events (p : Peer) (c r) : ∀ e ∈ (p.receiveOnChannel c r).2, isReceive e := by
  by_cases h : c.toNat < p.channels.size
  · rw [receiveOnChannel_eq _ _ _ h]; intro e he; obtain ⟨x, _, rfl⟩ := Array.mem_map.mp he; rfl
  · rw [receiveOnChannel_out _ _ _ h]; intro e he; simp at he

theorem handleFragment_state (p : Peer) (c s pr u) : (p.handleFragment c s pr u).1.state = p.state := by
  unfold handleFragment; dsimp only
  (repeat' split) <;> first | rfl | exact receiveOnChannel_state _ _ _
theorem handleFragment_events (p : Peer) (c s pr u) : ∀ e ∈ (p.handleFragment c s pr u).2.1, isReceive e := by
  unfold handleFragment; dsimp only
  (repeat' split) <;> first | exact receiveOnChannel_events _ _ _ | (intro e he; simp at he; done)
theorem handleData_state (p : Peer) (cmd) : (p.handleData cmd).1.state = p.state := by
  unfold handleData; split
  · exact receiveOnChannel_state _ _ _
  · exact receiveOnChannel_state _ _ _
  · split <;> rfl
  · rfl
theorem handleData_events (p : Peer) (cmd) : ∀ e ∈ (p.handleData cmd).2, isReceive e := by
  unfold handleData; split
  · exact receiveOnChannel_events _ _ _
  · exact receiveOnChannel_events _ _ _
  · split
    · intro e he; simp at he; subst he; rfl
    · intro e he; simp at he
  · intro e he; simp at he

/-- Only an up peer processes data (`Peer.isConnected`). -/
theorem isConnected_up {p : Peer} (h : p.isConnected = true) : (phase p.state) = .up := by
  unfold isConnected at h; cases hs : p.state <;> simp_all [phase] <;> exact absurd h (by decide)

/-- Starting a disconnect never changes the phase: a connected peer goes
disconnecting, a handshaking one goes zombie. -/
theorem queueDisconnect_phase (p : Peer) (d) : (phase (p.queueDisconnect d).state) = (phase p.state) := by
  cases hs : p.state <;> simp +decide [queueDisconnect, hs, phase, queueControlCommand, queueOutgoingCommand, resetQueues,
    sendLastDisconnect]

/-- An ACK completes a server handshake (connect) or a disconnect
(disconnect), or changes no phase. -/
theorem handleAcknowledge_wf (p : Peer) (n c s t) :
    EventsWf (phase p.state) (p.handleAcknowledge n c s t).2.1.toList (phase (p.handleAcknowledge n c s t).1.state) := by
  unfold handleAcknowledge; dsimp only; split
  · exact .nil
  split
  · exact .nil
  · generalize hq : (p.updateRtt n _).removeSentReliableCommand c s = q
    obtain ⟨q, acked⟩ := q
    have hs : q.state = p.state := by
      have := removeSent_state (p.updateRtt n (Time.difference n (Time.fromWire n t))) c s
      rw [hq] at this; rw [this, updateRtt_state]
    dsimp only
    split
    · next hst =>
      split
      · show EventsWf (phase p.state) [Event.connect _ _] (phase .connected)
        rw [← hs, hst]; exact .connect .nil
      · rw [hs]; exact .nil
    · next hst =>
      split
      · show EventsWf (phase p.state) [Event.disconnect _ _] (phase .disconnected)
        exact .disconnect .nil
      · rw [hs]; exact .nil
    · next hst =>
      split
      · rw [queueDisconnect_phase, hs]; exact .nil
      · rw [hs]; exact .nil
    · rw [hs]; exact .nil

/-- A DISCONNECT reports only a peer the application knows of, or a failed
connection attempt. -/
theorem handleDisconnect_wf (p : Peer) (d) :
    EventsWf (phase p.state) (p.handleDisconnect d).2.toList (phase (p.handleDisconnect d).1.state) := by
  unfold handleDisconnect
  split
  all_goals first
    | exact .nil
    | (rename_i hs; rw [hs]; exact .nil)
    | exact .disconnect .nil

theorem handleVerifyConnect_wf (p : Peer) (pr) :
    EventsWf (phase p.state) (p.handleVerifyConnect pr).2.1.toList (phase (p.handleVerifyConnect pr).1.state) := by
  unfold handleVerifyConnect
  split
  · exact .nil
  · next hc =>
    have hst : p.state = .connecting := by
      cases hs : p.state <;> simp_all <;> exact absurd hc (by decide)
    split
    · exact .disconnect .nil
    · show EventsWf (phase p.state) [Event.connect _ _] (phase .connected)
      rw [hst]; exact .connect .nil

theorem wf_of_state_receives {p q : Peer} {es : Array Event} (hs : q.state = p.state)
    (hup : p.isConnected = true) (he : ∀ e ∈ es, isReceive e) :
    EventsWf (phase p.state) es.toList (phase q.state) := by
  rw [hs, isConnected_up hup]
  exact .receives fun e h => he e (Array.mem_toList_iff.mp h)

/-- `handleHeldData` either refuses the packet, leaving the peer as it was,
or is `handleData`. -/
theorem handleHeldData_cases (p : Peer) (cmd) :
    p.handleHeldData cmd = (p, #[], false) ∨
      p.handleHeldData cmd = ((p.handleData cmd).1, (p.handleData cmd).2, true) := by
  unfold handleHeldData
  generalize p.handleData cmd = r
  obtain ⟨q, ev⟩ := r
  dsimp only
  split
  · exact .inl rfl
  · exact .inr rfl

/-- The data branches of `applyCommand` run only for a connected peer. -/
theorem connected_of_takesData {p : Peer} {c : Nat} {x : Bool}
    (h : ¬((!(p.isConnected && decide (c < p.channels.size)) || x) = true)) : p.isConnected = true := by
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, not_or] at h
  cases hc : p.isConnected <;> simp_all

theorem connected_of_takesData' {p : Peer} {c : Nat}
    (h : ¬((!(p.isConnected && decide (c < p.channels.size))) = true)) : p.isConnected = true :=
  connected_of_takesData (x := false) (by simpa using h)

/-- ENet's handler for any one command keeps the events well formed. -/
theorem applyCommand_wf (p : Peer) (now cmd) :
    EventsWf (phase p.state) (p.applyCommand now cmd).2.1.toList (phase (p.applyCommand now cmd).1.state) := by
  unfold applyCommand
  dsimp only
  split
  · exact handleAcknowledge_wf _ _ _ _ _
  · exact .nil
  · exact handleVerifyConnect_wf _ _
  · exact handleDisconnect_wf _ _
  · exact .nil
  · split <;> exact .nil
  · split <;> exact .nil
  -- reliable and unreliable data
  all_goals first
    | (split
       · exact .nil
       · next h =>
         split
         · exact .nil
         · rcases handleHeldData_cases p cmd with he | he <;> rw [he]
           · exact .nil
           · exact wf_of_state_receives (handleData_state _ _) (connected_of_takesData' h) (handleData_events _ _))
    | (split
       · exact .nil
       · next h =>
         refine wf_of_state_receives (handleData_state _ _) (connected_of_takesData' h) ?_
         split
         · intro e he; simp at he
         · exact handleData_events _ _)
    | (split
       · exact .nil
       · next h =>
         exact wf_of_state_receives (handleFragment_state _ _ _ _ _) (connected_of_takesData h)
           (handleFragment_events _ _ _ _ _))

/-- **Every incoming command keeps its peer's events well formed.** -/
theorem handleCommand_wf (p : Peer) (now cmd st) :
    EventsWf (phase p.state) (p.handleCommand now cmd st).2.1.toList
      (phase (p.handleCommand now cmd st).1.state) := by
  unfold handleCommand
  have h := applyCommand_wf p now cmd
  generalize p.applyCommand now cmd = r at h ⊢
  obtain ⟨q, es, acc⟩ := r
  dsimp only at h ⊢
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · split <;> exact h

/-- A timeout reports a disconnect, except for a server handshake the
application never saw. -/
theorem checkPeerTimeouts_wf (p : Peer) (now) :
    EventsWf (phase p.state) (Host.checkPeerTimeouts p now).2.toList
      (phase (Host.checkPeerTimeouts p now).1.state) := by
  unfold Host.checkPeerTimeouts
  dsimp only
  split
  · split
    · next hs =>
      have hs : p.state = .acknowledgingConnect := by
        cases h : p.state <;> simp_all <;> exact absurd hs (by decide)
      show EventsWf (phase p.state) [] (phase .disconnected)
      rw [hs]; exact .nil
    · exact .disconnect .nil
  · exact .nil

theorem checkPeerPing_state (p : Peer) (now) : (Host.checkPeerPing p now).state = p.state := by
  unfold Host.checkPeerPing; split <;> rfl

theorem packOutgoingCommands_state (p : Peer) (now hc) : (Host.packOutgoingCommands p now hc).1.state = p.state := rfl

theorem pollPeer_go_wf : ∀ (fuel : Nat) (p : Peer) (now cs ds),
    EventsWf (phase p.state) (Host.pollPeer.go now cs fuel p ds).2.2.toList
      (phase (Host.pollPeer.go now cs fuel p ds).1.state) := by
  intro fuel
  induction fuel with
  | zero => intro p now cs ds; exact .nil
  | succ fuel ih =>
    intro p now cs ds
    unfold Host.pollPeer.go
    dsimp only
    have h1 : phase (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p).state = phase p.state := by
      split
      · exact queueDisconnect_phase _ _
      · rfl
    generalize (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p) = q at h1 ⊢
    rw [← h1]
    have h2 := packOutgoingCommands_state q now cs
    generalize Host.packOutgoingCommands q now cs = r at h2 ⊢
    obtain ⟨q', cmds⟩ := r
    dsimp only at h2 ⊢
    rw [← h2]
    split
    · exact ih _ _ _ _
    · split
      · exact .disconnect .nil
      · split
        · next hz =>
          have hz : q'.state = .zombie := peerState_beq.mp hz
          show EventsWf (phase q'.state) [] (phase .disconnected)
          rw [hz]; exact .nil
        · exact .nil

/-- Sending keeps the events well formed: the deferred disconnects it
completes report only up peers, and a zombie resets silently. -/
theorem pollPeer_wf (p : Peer) (now cs) :
    EventsWf (phase p.state) (Host.pollPeer p now cs).2.2.toList (phase (Host.pollPeer p now cs).1.state) := by
  unfold Host.pollPeer
  split
  · exact .nil
  · exact pollPeer_go_wf _ _ _ _ _

end Lenet.Proofs
