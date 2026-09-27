import Lenet.Proofs.Window
import Lenet.Proofs.Resources

/-!
# Resource bounds over whole runs

`Proofs/Resources` shows each step of the receive and send paths keeps the
per-peer bounds: the fragment-assembler cap with every assembler well
formed (`AssemblersOk`), what the sets under way claim under 64 MB
(`WaitingOk`), and each channel's reliable staging inside its window
(`PeerStagedInv`, so at most 28672 staged). Here they are carried through
every host operation, from `Host.create` on, whatever arrives off the wire
and whatever the application calls (`runApp_resources`), the same way
`Proofs/Window` carries the sender's invariant.

Most peer operations touch neither the assemblers nor the channels
(`ResInv.of`); the ones that do are the receive steps of `Proofs/Resources`,
the sender's window accounting, and the resets, which leave both empty.
-/

namespace Lenet.Proofs

open Peer Host

/-- Every per-peer resource bound. -/
def ResInv (p : Peer) : Prop :=
  AssemblersOk p ∧ WaitingOk p.fragmentAssemblers ∧ PeerStagedInv p

/-- The bounds read only the assemblers and the channels. -/
theorem ResInv.of {p q : Peer} (h : ResInv p) (hf : q.fragmentAssemblers = p.fragmentAssemblers)
    (hc : q.channels = p.channels) : ResInv q := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact ⟨⟨hf ▸ h1, hf ▸ h2⟩, hf ▸ h3, peerStagedInv_of_channels hc h4⟩

/-- New channels that keep the staging invariant keep the bounds. -/
theorem ResInv.withChannels {p q : Peer} (h : ResInv p) (hf : q.fragmentAssemblers = p.fragmentAssemblers)
    (hc : ∀ ch ∈ q.channels, StagedReliableInv ch) : ResInv q := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := h
  exact ⟨⟨hf ▸ h1, hf ▸ h2⟩, hf ▸ h3, hc⟩

/-- A peer with no assemblers and no channels. -/
theorem resInv_empty {p : Peer} (hf : p.fragmentAssemblers = #[]) (hc : p.channels = #[]) : ResInv p := by
  refine ⟨⟨by rw [hf]; simp [Constants.maximumFragmentAssemblers], by rw [hf]; simp⟩,
    by rw [hf]; exact waitingOk_empty, fun ch hch => by rw [hc] at hch; simp at hch⟩

theorem resInv_reset (p : Peer) : ResInv p.reset := resInv_empty rfl rfl

theorem resInv_resetQueues (p : Peer) : ResInv p.resetQueues := resInv_empty rfl rfl

theorem ResInv.queueOutgoingCommand {p : Peer} (h : ResInv p) (c) : ResInv (p.queueOutgoingCommand c) :=
  h.of rfl rfl

theorem ResInv.queueControlCommand {p : Peer} (h : ResInv p) (b) : ResInv (p.queueControlCommand b) :=
  h.of rfl rfl

theorem resInv_sendLastDisconnect {p : Peer} (h : ResInv p) (d) : ResInv (p.sendLastDisconnect d) :=
  h.of rfl rfl

theorem ResInv.queueDisconnect {p : Peer} (h : ResInv p) (d) : ResInv (p.queueDisconnect d) := by
  unfold Peer.queueDisconnect
  split
  any_goals exact h
  dsimp only
  split <;> exact resInv_empty rfl rfl

theorem ResInv.disconnectNow {p : Peer} (h : ResInv p) (d) : ResInv (p.disconnectNow d) := by
  unfold Peer.disconnectNow
  split <;> first
    | exact h
    | exact resInv_empty rfl rfl

theorem ResInv.queueAck {p : Peer} (h : ResInv p) (a) : ResInv (p.queueAck a) := h.of rfl rfl

theorem ResInv.throttle {p : Peer} (h : ResInv p) (r) : ResInv (p.throttle r) := by
  unfold Peer.throttle; split <;> (try split) <;> (try split) <;> exact h.of rfl rfl

theorem ResInv.updateRtt {p : Peer} (h : ResInv p) (now r) : ResInv (p.updateRtt now r) := by
  have := throttle_kept p
  unfold Peer.updateRtt
  dsimp only
  split <;> (try split) <;> (try split) <;> (try split) <;>
    first | exact h.of rfl rfl | exact (h.of rfl rfl).throttle _ | skip
  all_goals exact (h.of rfl rfl).throttle _

theorem ResInv.removeSent {p : Peer} (h : ResInv p) (c s) : ResInv (p.removeSentReliableCommand c s).1 := by
  refine ⟨⟨?_, ?_⟩, ?_, removeSentReliableCommand_peerStagedInv h.2.2 c s⟩
  all_goals
    have hf : (p.removeSentReliableCommand c s).1.fragmentAssemblers = p.fragmentAssemblers := by
      unfold Peer.removeSentReliableCommand; dsimp only; (repeat' split) <;> rfl
  · rw [hf]; exact h.1.1
  · rw [hf]; exact h.1.2
  · rw [hf]; exact h.2.1

/-! ## The receive path -/

theorem ResInv.handleFragment {p : Peer} (h : ResInv p) (c s pr u) : ResInv (p.handleFragment c s pr u).1 :=
  ⟨handleFragment_assemblersOk h.1 c s pr u, handleFragment_waiting h.2.1 c s pr u,
    handleFragment_peerStagedInv h.2.2 c s pr u⟩

theorem ResInv.receiveOnChannel {p : Peer} (h : ResInv p) (c) (recv : Channel → Channel × Array Packet)
    (hr : ∀ c, StagedReliableInv c → StagedReliableInv (recv c).1) : ResInv (p.receiveOnChannel c recv).1 :=
  ⟨receiveOnChannel_assemblersOk h.1 c recv, receiveOnChannel_waiting h.2.1 c recv,
    receiveOnChannel_peerStagedInv h.2.2 c recv hr⟩

theorem ResInv.handleData {p : Peer} (h : ResInv p) (cmd) : ResInv (p.handleData cmd).1 := by
  refine ⟨?_, ?_, handleData_peerStagedInv h.2.2 cmd⟩
  all_goals
    unfold Peer.handleData
    split
  · exact receiveOnChannel_assemblersOk h.1 _ _
  · exact receiveOnChannel_assemblersOk h.1 _ _
  · split
    · exact h.1
    · exact h.1
  · exact h.1
  · exact receiveOnChannel_waiting h.2.1 _ _
  · exact receiveOnChannel_waiting h.2.1 _ _
  · split
    · exact h.2.1
    · exact h.2.1
  · exact h.2.1

theorem ResInv.handleHeldData {p : Peer} (h : ResInv p) (cmd) : ResInv (p.handleHeldData cmd).1 := by
  rcases handleHeldData_cases p cmd with he | he <;> rw [he]
  · exact h
  · exact h.handleData cmd

theorem ResInv.handleAcknowledge {p : Peer} (h : ResInv p) (now c s t) :
    ResInv (p.handleAcknowledge now c s t).1 := by
  unfold Peer.handleAcknowledge
  dsimp only
  split
  · exact h
  split
  · exact h
  have h1 := (h.updateRtt now (Time.difference now (Time.fromWire now t))).removeSent c s
  generalize (p.updateRtt now _).removeSentReliableCommand c s = r at h1 ⊢
  obtain ⟨q, _⟩ := r
  dsimp only at h1 ⊢
  split
  · split
    · exact h1.of rfl rfl
    · exact h1
  · split
    · exact resInv_reset q
    · exact h1
  · split
    · exact h1.queueDisconnect _
    · exact h1
  · exact h1

theorem ResInv.handleDisconnect {p : Peer} (h : ResInv p) (d) : ResInv (p.handleDisconnect d).1 := by
  unfold Peer.handleDisconnect
  split <;> first
    | exact h
    | exact resInv_empty rfl rfl

theorem ResInv.handleVerifyConnect {p : Peer} (h : ResInv p) (params) :
    ResInv (p.handleVerifyConnect params).1 := by
  unfold Peer.handleVerifyConnect
  split
  · exact h
  split
  · exact resInv_reset p
  · dsimp only
    have h1 := h.removeSent 0xFF 1
    generalize p.removeSentReliableCommand 0xFF 1 = r at h1 ⊢
    obtain ⟨q, _⟩ := r
    exact h1.withChannels rfl (peerStagedInv_take h1.2.2 _)

theorem ResInv.applyCommand {p : Peer} (h : ResInv p) (now cmd) : ResInv (p.applyCommand now cmd).1 := by
  unfold Peer.applyCommand
  dsimp only
  split
  · exact h.handleAcknowledge _ _ _ _
  · exact h
  · exact h.handleVerifyConnect _
  · exact h.handleDisconnect _
  · exact h
  · split
    · exact h.of rfl rfl
    · exact h
  · split
    · exact h.of rfl rfl
    · exact h
  all_goals (repeat' split) <;> first
    | exact h
    | exact h.handleHeldData _
    | exact h.handleData _
    | exact h.handleFragment _ _ _ _

theorem ResInv.handleCommand {p : Peer} (h : ResInv p) (now cmd st) : ResInv (p.handleCommand now cmd st).1 := by
  unfold Peer.handleCommand
  have ha := h.applyCommand now cmd
  dsimp only
  generalize p.applyCommand now cmd = r at ha ⊢
  obtain ⟨q, es, acc⟩ := r
  dsimp only at ha ⊢
  split
  · exact ha
  split
  · exact ha
  split
  · exact ha
  · dsimp only
    split
    · exact ha.queueAck _
    · exact ha

theorem ResInv.handlePeerDatagram {p : Peer} (h : ResInv p) (now fromAddr datagram outBw) :
    ResInv (Host.handlePeerDatagram p now fromAddr datagram outBw).1 := by
  unfold Host.handlePeerDatagram
  dsimp only
  have hl : ResInv (datagram.commands.foldl (Host.readCommand now datagram.header.sentTime)
      ({ p with address := fromAddr }, #[], true, false)).1 := by
    refine Array.foldl_induction (motive := fun _ (r : Peer × Array Event × Bool × Bool) => ResInv r.1)
      (h.of rfl rfl) ?_
    intro i r hr
    obtain ⟨q, es, reading, bw⟩ := r
    unfold Host.readCommand
    dsimp only at hr ⊢
    split
    · exact hr
    · dsimp only
      have := hr.handleCommand now datagram.commands[i] datagram.header.sentTime
      generalize q.handleCommand now _ _ = c at this ⊢
      obtain ⟨q', _, _⟩ := c
      exact this
  generalize datagram.commands.foldl _ _ = r at hl ⊢
  obtain ⟨q, _, _, bw⟩ := r
  dsimp only at hl ⊢
  split
  · exact hl.of rfl rfl
  · exact hl

/-! ## The host's own steps -/

theorem ResInv.checkPeerTimeouts {p : Peer} (h : ResInv p) (now) : ResInv (Host.checkPeerTimeouts p now).1 := by
  unfold Host.checkPeerTimeouts
  dsimp only
  split
  · exact resInv_reset p
  · exact h.of rfl rfl

theorem ResInv.checkPeerPing {p : Peer} (h : ResInv p) (now) : ResInv (Host.checkPeerPing p now) := by
  unfold Host.checkPeerPing
  split
  · exact h.queueControlCommand _
  · exact h

theorem ResInv.packOutgoingCommands {p : Peer} (h : ResInv p) (now hc) :
    ResInv (Host.packOutgoingCommands p now hc).1 :=
  h.withChannels rfl (packOutgoingCommands_peerStagedInv h.2.2 now hc)

theorem ResInv.pollPeer_go {now : UInt32} {cs : Bool} :
    ∀ (fuel : Nat) (p : Peer) (ds), ResInv p → ResInv (Host.pollPeer.go now cs fuel p ds).1
  | 0, _, _, h => h
  | fuel + 1, p, ds, h => by
    unfold Host.pollPeer.go
    dsimp only
    have h1 : ResInv (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p) := by
      split
      · exact h.queueDisconnect _
      · exact h
    generalize (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p) = q at h1 ⊢
    have h2 := h1.packOutgoingCommands now cs
    generalize Host.packOutgoingCommands q now cs = r at h2 ⊢
    obtain ⟨q', cmds⟩ := r
    dsimp only at h2 ⊢
    split
    · exact ResInv.pollPeer_go fuel _ _ h2
    split
    · exact resInv_reset q'
    split
    · exact resInv_reset q'
    · exact h2

theorem ResInv.pollPeer {p : Peer} (h : ResInv p) (now cs) : ResInv (Host.pollPeer p now cs).1 := by
  unfold Host.pollPeer
  split
  · exact h
  · exact ResInv.pollPeer_go _ _ _ h

theorem foldl_queueOutgoingCommand_assemblers (q : Peer) (xs : Array OutgoingCommand) :
    (xs.foldl Peer.queueOutgoingCommand q).fragmentAssemblers = q.fragmentAssemblers :=
  Array.foldl_induction (motive := fun _ (r : Peer) => r.fragmentAssemblers = q.fragmentAssemblers)
    rfl fun _ _ h => h

theorem ResInv.enqueue {p : Peer} (h : ResInv p) (c pk cs) : ResInv (p.enqueue c pk cs) := by
  refine h.withChannels ?_ (enqueue_peerStagedInv h.2.2 c pk cs)
  unfold Peer.enqueue
  split
  · rfl
  · next channel _ =>
    dsimp only
    split
    · generalize Peer.fragmentCommands _ _ _ _ _ = r
      obtain ⟨ch, fr⟩ := r
      exact foldl_queueOutgoingCommand_assemblers _ _
    · have hpc : (p.packetCommand channel c pk).1.fragmentAssemblers = p.fragmentAssemblers := by
        unfold Peer.packetCommand; (repeat' split) <;> rfl
      generalize p.packetCommand channel c pk = r at hpc
      obtain ⟨q, ch, cmd⟩ := r
      exact hpc

/-! ## Over the host -/

/-- Every peer of the host keeps every resource bound. -/
def HostRes (h : Host) : Prop := ∀ p ∈ h.peers, ResInv p

theorem HostRes.modify {h : Host} (hi : HostRes h) (i : Nat) (f : Peer → Peer)
    (hf : ∀ p ∈ h.peers, ResInv p → ResInv (f p)) : ∀ q ∈ h.peers.modify i f, ResInv q := by
  intro q hq
  rcases mem_modify_or' hq with hq | ⟨p, hp, rfl⟩
  · exact hi q hq
  · exact hf p hp (hi p hp)

theorem HostRes.map {h : Host} (hi : HostRes h) (f : Peer → Peer) (hf : ∀ p ∈ h.peers, ResInv p → ResInv (f p)) :
    ∀ q ∈ h.peers.map f, ResInv q := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
  exact hf p hp (hi p hp)

theorem modify_res {h : Host} (hi : HostRes h) (id : UInt16) (f : Peer → Peer)
    (hf : ∀ p, ResInv p → ResInv (f p)) : HostRes (h.modifyPeer id f) := by
  intro q hq
  rw [modifyPeer_peers] at hq
  exact hi.modify _ _ (fun p _ hp => hf p hp) q hq

theorem handleIncomingConnect_res {h : Host} (hi : HostRes h) (fromAddr params data) :
    HostRes (h.handleIncomingConnect fromAddr params data) := by
  unfold Host.handleIncomingConnect
  dsimp only
  split
  · exact hi
  split
  · exact hi
  · next slot hslot =>
    intro q hq
    rw [modifyPeer_peers] at hq
    refine hi.modify _ _ (fun _ _ _ => ?_) q hq
    refine ResInv.queueControlCommand ?_ _
    exact (hi _ (Array.getElem_mem slot.2)).withChannels rfl (peerStagedInv_replicate _)

theorem handleDatagram_res {h : Host} (hi : HostRes h) (now fromAddr bytes) :
    HostRes (h.handleDatagram now fromAddr bytes).1 := by
  unfold Host.handleDatagram
  dsimp only
  split
  · exact hi
  · split
    · split
      · exact handleIncomingConnect_res hi _ _ _
      · exact hi
    · split
      · exact hi
      · split
        · exact hi
        · rw [withPeer_eq]
          exact fun q hq => hi.modify _ _ (fun p _ hp => hp.handlePeerDatagram _ _ _ _) q hq

theorem limitPeers_res (elapsed : Nat) : ∀ (fuel : Nat) budget limited needs (peers : Array Peer),
    (∀ p ∈ peers, ResInv p) →
      ∀ q ∈ (Host.outgoingThrottleLimits.limitPeers elapsed budget limited needs peers fuel).1, ResInv q
  | 0, _, _, _, _, h => h
  | fuel + 1, budget, limited, needs, peers, h => by
    unfold Host.outgoingThrottleLimits.limitPeers
    split
    · exact h
    · dsimp only
      refine limitPeers_res elapsed fuel _ _ _ _ ?_
      refine Array.foldl_induction (motive := fun _ (r : Array Peer × Host.OutgoingBudget × Array UInt16) =>
        ∀ q ∈ r.1, ResInv q) (fun q hq => by simp at hq) ?_
      intro i r hr
      obtain ⟨acc, bud, lim⟩ := r
      dsimp only at hr ⊢
      have hpi := h _ (Array.getElem_mem i.2)
      split
      · intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · exact hr q hq
        · exact hpi
      · intro q hq
        rcases Array.mem_push.mp hq with hq | rfl
        · exact hr q hq
        · exact hpi.of rfl rfl

theorem outgoingThrottleLimits_res {h : Host} (hi : HostRes h) (elapsed : Nat) :
    ∀ q ∈ h.outgoingThrottleLimits elapsed, ResInv q := by
  unfold Host.outgoingThrottleLimits
  dsimp only
  split
  all_goals
    intro q hq
    split at hq
    · exact limitPeers_res _ _ _ _ _ _ hi q hq
    · obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
      have hl := limitPeers_res _ _ _ _ _ _ hi p hp
      split
      · exact hl.of rfl rfl
      · exact hl

theorem bandwidthThrottle_res {h : Host} (hi : HostRes h) (now : UInt32) : HostRes (h.bandwidthThrottle now) := by
  unfold Host.bandwidthThrottle
  split
  · exact hi
  · dsimp only
    split
    · exact hi
    · have hl := outgoingThrottleLimits_res hi (Time.difference now h.bandwidthThrottleEpoch).toNat
      split
      · exact hl
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := Array.mem_map.mp hq
        split
        · exact (hl p hp).queueControlCommand _
        · exact hl p hp

theorem checkTimeoutsAndPings_res {h : Host} (hi : HostRes h) (now : UInt32) :
    HostRes (h.checkTimeoutsAndPings now).1 := by
  unfold Host.checkTimeoutsAndPings
  let F (p : Peer) : Peer :=
    if p.state == .disconnected ∨ p.state == .zombie then p
    else match Host.checkPeerTimeouts p now with
      | (q, some _) => q
      | (q, none) => Host.checkPeerPing q now
  let E (p : Peer) : Array Event :=
    if p.state == .disconnected ∨ p.state == .zombie then #[] else (Host.checkPeerTimeouts p now).2.toArray
  rw [mapPeers_eq _ _ _ F (fun p s => s ++ E p)]
  · refine fun q hq => hi.map F (fun p _ hp => ?_) q hq
    simp only [F]
    split
    · exact hp
    · have hc := hp.checkPeerTimeouts now
      generalize Host.checkPeerTimeouts p now = c at hc ⊢
      obtain ⟨q, _ | e⟩ := c
      · exact hc.checkPeerPing now
      · exact hc
  · intro p s
    simp only [F, E]
    split
    · simp
    · generalize Host.checkPeerTimeouts p now = c
      obtain ⟨q, _ | e⟩ := c <;> simp

theorem pollOutgoing_res {h : Host} (hi : HostRes h) (now : UInt32) : HostRes (h.pollOutgoing now).1 := by
  unfold Host.pollOutgoing
  dsimp only
  rw [mapPeers_eq _ _ _ (fun p => (Host.pollPeer p now h.checksumEnabled).1)
    (fun p s => (s.1 ++ (Host.pollPeer p now h.checksumEnabled).2.1, s.2 ++ (Host.pollPeer p now h.checksumEnabled).2.2))
    (fun p s => rfl)]
  exact fun q hq => hi.map _ (fun p _ hp => hp.pollPeer _ _) q hq

theorem service_res {h : Host} (hi : HostRes h) (now : UInt32) : HostRes (h.service now).1 := by
  unfold Host.service
  dsimp only
  exact pollOutgoing_res (checkTimeoutsAndPings_res (bandwidthThrottle_res hi now) now) now

theorem trySend_res {h : Host} (hi : HostRes h) (id c pk) : HostRes (h.trySend id c pk).1 := by
  unfold Host.trySend
  rw [withPeer_eq]
  intro q hq
  dsimp only at hq
  refine hi.modify _ _ (fun p _ hp => ?_) q hq
  split
  · exact hp
  · exact hp.enqueue _ _ _

theorem broadcast_res {h : Host} (hi : HostRes h) (c pk) : HostRes (h.broadcast c pk) := by
  unfold Host.broadcast
  dsimp only
  rw [mapPeers_eq _ _ _ (fun p =>
      if p.state == .connected && (p.sendError? c pk h.checksumEnabled).isNone then
        p.enqueue c pk h.checksumEnabled
      else p) (fun _ _ => ()) (fun p s => by split <;> simp [*])]
  refine fun q hq => hi.map _ (fun p _ hp => ?_) q hq
  split
  · exact hp.enqueue _ _ _
  · exact hp

theorem connect_res {h h' : Host} {id} (hi : HostRes h) {addr n d} (hc : h.connect addr n d = .ok (h', id)) :
    HostRes h' := by
  unfold Host.connect at hc
  have hp := random_peers h
  rcases hr : h.random with ⟨h2, cid⟩
  rw [hr] at hc hp
  simp only at hp
  split at hc
  · next slot hslot =>
    cases hc
    intro q hq
    rw [modifyPeer_peers, hp] at hq
    refine hi.modify _ _ (fun _ _ _ => ?_) q hq
    refine ResInv.queueControlCommand ?_ _
    exact (hi _ (Array.getElem_mem slot.2)).withChannels rfl (peerStagedInv_replicate _)
  · cases hc

theorem Op.apply_res {h : Host} (hi : HostRes h) : ∀ op : Op, HostRes (op.apply h).1
  | .datagram .. => handleDatagram_res hi _ _ _
  | .service .. => service_res hi _
  | .pollOutgoing now => pollOutgoing_res hi now
  | .enableChecksum => hi
  | .connect addr n d => by
    simp only [Op.apply]
    split
    · next hc => exact connect_res hi hc
    · exact hi
  | .send .. => trySend_res hi _ _ _
  | .broadcast .. => broadcast_res hi _ _
  | .disconnect .. => modify_res hi _ _ fun _ hp => hp.queueDisconnect _
  | .disconnectLater .. => modify_res hi _ _ fun p hp => by
    split
    · exact hp.of rfl rfl
    · exact hp.queueDisconnect _
  | .throttleConfigure .. => modify_res hi _ _ fun p hp => by
    split
    · exact hp
    · exact hp.of rfl rfl
  | .setPeerTimeout .. => modify_res hi _ _ fun _ hp => hp.of rfl rfl
  | .ping .. => modify_res hi _ _ fun p hp => by
    split
    · exact hp.queueControlCommand _
    · exact hp
  | .setPingInterval .. => modify_res hi _ _ fun _ hp => hp.of rfl rfl
  | .bandwidthLimit .. => hi
  | .setChannelLimit .. => hi

theorem AppOp.apply_res {h : Host} (hi : HostRes h) : ∀ op : AppOp, HostRes (op.apply h).1
  | .op o => Op.apply_res hi o
  | .disconnectNow _ d => modify_res hi _ _ fun _ hp => hp.disconnectNow d
  | .resetPeer _ => modify_res hi _ _ fun p _ => resInv_reset p

theorem runApp_res : ∀ (ops : List AppOp) {h : Host}, HostRes h → HostRes (runApp h ops).1
  | [], _, hi => hi
  | op :: ops, _, hi => runApp_res ops (AppOp.apply_res hi op)

theorem create_res (address peerCount channelLimit inBw outBw seed mtu) :
    HostRes (Host.create address peerCount channelLimit inBw outBw seed mtu) := by
  intro p hp
  simp only [Host.create, Array.mem_map, Array.mem_range] at hp
  obtain ⟨i, -, rfl⟩ := hp
  exact resInv_empty rfl rfl

/-- **The resource bounds hold over whole runs.** From `Host.create`,
whatever arrives off the wire and whatever the application calls, every
peer holds at most `maximumFragmentAssemblers` fragment sets under way,
each storing at most 65536 fragments that carry at most 32 MB, the sets
claim under 64 MB between them, and each channel stages at most seven
windows of reliable packets. -/
theorem runApp_resources (address peerCount channelLimit inBw outBw seed mtu) (ops : List AppOp) :
    let h := (runApp (Host.create address peerCount channelLimit inBw outBw seed mtu) ops).1
    ∀ p ∈ h.peers,
      p.fragmentAssemblers.size ≤ Constants.maximumFragmentAssemblers ∧
      (∀ a ∈ p.fragmentAssemblers,
        (a.fragments.toList.map (·.2.size)).sum ≤ Constants.maximumPacketSize ∧
        a.fragments.size ≤ Constants.maximumReceivedFragmentCount) ∧
      waitingBytes p.fragmentAssemblers < Constants.maximumWaitingData + Constants.maximumPacketSize ∧
      ∀ ch ∈ p.channels,
        ch.stagedReliable.size ≤ (Constants.freeReliableWindows - 1) * Constants.reliableWindowSize := by
  intro h p hp
  obtain ⟨⟨hcap, hok⟩, hw, hs⟩ := runApp_res ops (create_res address peerCount channelLimit inBw outBw seed mtu) p hp
  refine ⟨hcap, fun a ha => ?_, hw.2, fun ch hch => stagedReliableInv_size (hs ch hch)⟩
  have := assemblerOk_footprint (hok a ha)
  exact ⟨this.1, this.2.1⟩

end Lenet.Proofs
