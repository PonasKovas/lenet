import Lenet.Host

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

Not yet lifted to the host: `Host.handleDatagram` folds `handleCommand`
over one peer's commands (`EventsWf.append` composes them), and
`Host.service` runs the timeout and poll steps on every peer; the missing
piece is a per-slot projection of the host's event array (events carry
the peer ID, and a slot's peer ID never changes).
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
  unfold removeSentReliableCommand; split <;> rfl
theorem pruneAssemblers_state (p : Peer) (c) : (p.pruneAssemblers c).state = p.state := by
  unfold pruneAssemblers; split; split <;> rfl; rfl
theorem receiveOnChannel_state (p : Peer) (c r) : (p.receiveOnChannel c r).1.state = p.state := by
  unfold receiveOnChannel; split
  · split; exact pruneAssemblers_state _ _
  · rfl
theorem receiveOnChannel_events (p : Peer) (c r) : ∀ e ∈ (p.receiveOnChannel c r).2, isReceive e := by
  unfold receiveOnChannel; split
  · split; intro e he; obtain ⟨x, _, rfl⟩ := Array.mem_map.mp he; rfl
  · intro e he; simp at he

theorem handleFragment_state (p : Peer) (c s pr u) : (p.handleFragment c s pr u).1.state = p.state := by
  unfold handleFragment; split
  · rfl
  · dsimp only; split
    · dsimp only; exact receiveOnChannel_state _ _ _
    · rfl
theorem handleFragment_events (p : Peer) (c s pr u) : ∀ e ∈ (p.handleFragment c s pr u).2.1, isReceive e := by
  unfold handleFragment; split
  · intro e he; simp at he
  · dsimp only; split
    · dsimp only; exact receiveOnChannel_events _ _ _
    · intro e he; simp at he
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
  cases hs : p.state <;> simp +decide [queueDisconnect, hs, phase, queueControlCommand, queueOutgoingCommand]

/-- An ACK completes a server handshake (connect) or a disconnect
(disconnect), or changes no phase. -/
theorem handleAcknowledge_wf (p : Peer) (n c s t) :
    EventsWf (phase p.state) (p.handleAcknowledge n c s t).2.toList (phase (p.handleAcknowledge n c s t).1.state) := by
  unfold handleAcknowledge; dsimp only; split
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
    EventsWf (phase p.state) (p.handleVerifyConnect pr).2.toList (phase (p.handleVerifyConnect pr).1.state) := by
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

theorem ackCommand_state (p : Peer) (c s) : (p.ackCommand c s).state = p.state := by
  unfold ackCommand; split <;> rfl

/-- **Every incoming command keeps its peer's events well formed.** -/
theorem handleCommand_wf (p : Peer) (now cmd st) :
    EventsWf (phase p.state) (p.handleCommand now cmd st).2.toList
      (phase (p.handleCommand now cmd st).1.state) := by
  unfold handleCommand
  dsimp only
  have fragment : ∀ params unreliable,
      EventsWf (phase p.state)
        (if p.isConnected = true then
          match p.handleFragment cmd.channelId cmd.reliableSequenceNumber params unreliable with
          | (q, events, accepted) => (if accepted = true then q.ackCommand cmd st else q, events)
        else (p.ackCommand cmd st, #[])).2.toList
        (phase (if p.isConnected = true then
          match p.handleFragment cmd.channelId cmd.reliableSequenceNumber params unreliable with
          | (q, events, accepted) => (if accepted = true then q.ackCommand cmd st else q, events)
        else (p.ackCommand cmd st, #[])).1.state) := by
    intro params unreliable
    split
    · next hc =>
      have hs := handleFragment_state p cmd.channelId cmd.reliableSequenceNumber params unreliable
      have he := handleFragment_events p cmd.channelId cmd.reliableSequenceNumber params unreliable
      generalize p.handleFragment cmd.channelId cmd.reliableSequenceNumber params unreliable = r at hs he ⊢
      obtain ⟨q, evs, acc⟩ := r
      dsimp only at hs he ⊢
      refine wf_of_state_receives ?_ hc he
      split <;> simp [ackCommand_state, hs]
    · rw [ackCommand_state]; exact .nil
  split
  · exact fragment _ _
  · exact fragment _ _
  · have hp : phase p.state = phase (p.ackCommand cmd st).state := by rw [ackCommand_state]
    rw [hp]
    split
    all_goals first
      | exact handleAcknowledge_wf _ _ _ _ _
      | exact handleDisconnect_wf _ _
      | exact handleVerifyConnect_wf _ _
      | exact .nil
      | (split
         · next hc => exact wf_of_state_receives (handleData_state _ _) hc (handleData_events _ _)
         · exact .nil)

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

theorem packOutgoingCommands_state (p : Peer) (now) : (Host.packOutgoingCommands p now).1.state = p.state := rfl

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
    have h2 := packOutgoingCommands_state q now
    generalize Host.packOutgoingCommands q now = r at h2 ⊢
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
