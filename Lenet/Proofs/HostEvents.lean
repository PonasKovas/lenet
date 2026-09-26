import Lenet.Proofs.Events

/-!
# Event proofs, host level

`Proofs/Events.lean` shows each per-peer step keeps that peer's events well
formed (`EventsWf`). Here that is lifted to the host. The host's events are
one array for all peers; `slotEvents i` picks slot `i`'s out by peer ID,
which works because slot `i` always holds peer ID `i` (`IdsOk`, true from
`Host.create` on and kept by every step).

`HostStep a b es` says a host step from peer array `a` to `b` reporting
`es` keeps every slot's ID, names only existing slots, and gives every slot
well formed events. It composes (`HostStep.trans`), and holds for
`handleDatagram_step`, `service_step` and each of the application's calls.
`run_wf` puts them together: from a fresh host, after any sequence of
operations (`Op`), every slot's events are well formed.

Writing these found that `Host.create` allowed more than 4095 slots: slot
4095 would carry the CONNECT peer ID 0xFFF, and past 65536 IDs repeat
(test/README.md).
-/

namespace Lenet.Proofs

open Peer

/-- The peer an event is about. -/
def eventPeer : Event → UInt16
  | .connect id _ | .disconnect id _ | .receive id _ _ => id

/-! ## Every per-peer step keeps the peer's ID and names only it -/
theorem throttle_peerId (p : Peer) (r) : (p.throttle r).peerId = p.peerId := by
  unfold throttle; split <;> (try split) <;> (try split) <;> rfl
theorem updateRtt_peerId (p : Peer) (n r) : (p.updateRtt n r).peerId = p.peerId := by
  unfold updateRtt; dsimp only
  split <;> (try split) <;> (try split) <;> (try split) <;> simp [throttle_peerId]
theorem removeSent_peerId (p : Peer) (c s) : (p.removeSentReliableCommand c s).1.peerId = p.peerId := by
  unfold removeSentReliableCommand; split <;> rfl
theorem pruneAssemblers_peerId (p : Peer) (c) : (p.pruneAssemblers c).peerId = p.peerId := by
  unfold pruneAssemblers; split; split <;> rfl; rfl
theorem queueDisconnect_peerId (p : Peer) (d) : (p.queueDisconnect d).peerId = p.peerId := by
  unfold queueDisconnect; split <;> (try split) <;> rfl

theorem receiveOnChannel_peerId (p : Peer) (c r) : (p.receiveOnChannel c r).1.peerId = p.peerId := by
  unfold receiveOnChannel; split
  · split; exact pruneAssemblers_peerId _ _
  · rfl
theorem receiveOnChannel_named (p : Peer) (c r) : ∀ e ∈ (p.receiveOnChannel c r).2, eventPeer e = p.peerId := by
  unfold receiveOnChannel; split
  · split; intro e he; obtain ⟨x, _, rfl⟩ := Array.mem_map.mp he; rfl
  · intro e he; simp at he

theorem handleFragment_peerId (p : Peer) (c s pr u) : (p.handleFragment c s pr u).1.peerId = p.peerId := by
  unfold handleFragment; split
  · rfl
  · dsimp only; split
    · dsimp only; exact receiveOnChannel_peerId _ _ _
    all_goals rfl
theorem handleFragment_named (p : Peer) (c s pr u) :
    ∀ e ∈ (p.handleFragment c s pr u).2.1, eventPeer e = p.peerId := by
  unfold handleFragment; split
  · intro e he; simp at he
  · dsimp only; split
    · dsimp only; exact receiveOnChannel_named _ _ _
    all_goals (intro e he; simp at he)

theorem handleData_peerId (p : Peer) (cmd) : (p.handleData cmd).1.peerId = p.peerId := by
  unfold handleData; split
  · exact receiveOnChannel_peerId _ _ _
  · exact receiveOnChannel_peerId _ _ _
  · split <;> rfl
  · rfl
theorem handleData_named (p : Peer) (cmd) : ∀ e ∈ (p.handleData cmd).2, eventPeer e = p.peerId := by
  unfold handleData; split
  · exact receiveOnChannel_named _ _ _
  · exact receiveOnChannel_named _ _ _
  · split
    · intro e he; simp at he; subst he; rfl
    · intro e he; simp at he
  · intro e he; simp at he

theorem handleAcknowledge_peerId (p : Peer) (n c s t) : (p.handleAcknowledge n c s t).1.peerId = p.peerId := by
  unfold handleAcknowledge; dsimp only; split
  · rfl
  · have hq := removeSent_peerId (p.updateRtt n (Time.difference n (Time.fromWire n t))) c s
    rw [updateRtt_peerId] at hq
    generalize (p.updateRtt n _).removeSentReliableCommand c s = q at hq ⊢
    obtain ⟨q, acked⟩ := q
    dsimp only at hq ⊢
    split <;> (try split) <;> simp [hq, queueDisconnect_peerId, reset]
theorem handleAcknowledge_named (p : Peer) (n c s t) :
    ∀ e ∈ (p.handleAcknowledge n c s t).2.1, eventPeer e = p.peerId := by
  unfold handleAcknowledge; dsimp only; split
  · intro e he; simp at he
  · have hq := removeSent_peerId (p.updateRtt n (Time.difference n (Time.fromWire n t))) c s
    rw [updateRtt_peerId] at hq
    generalize (p.updateRtt n _).removeSentReliableCommand c s = q at hq ⊢
    obtain ⟨q, acked⟩ := q
    dsimp only at hq ⊢
    split <;> (try split) <;> intro e he <;> simp at he <;> (try subst he) <;> simp [eventPeer, hq]

theorem handleDisconnect_peerId (p : Peer) (d) : (p.handleDisconnect d).1.peerId = p.peerId := by
  unfold handleDisconnect; split <;> rfl
theorem handleDisconnect_named (p : Peer) (d) : ∀ e ∈ (p.handleDisconnect d).2, eventPeer e = p.peerId := by
  unfold handleDisconnect; split <;> intro e he <;> simp at he <;> (try subst he) <;> rfl

theorem handleVerifyConnect_peerId (p : Peer) (pr) : (p.handleVerifyConnect pr).1.peerId = p.peerId := by
  unfold handleVerifyConnect; split
  · rfl
  · split
    · rfl
    · exact removeSent_peerId _ _ _
theorem handleVerifyConnect_named (p : Peer) (pr) : ∀ e ∈ (p.handleVerifyConnect pr).2.1, eventPeer e = p.peerId := by
  unfold handleVerifyConnect; split
  · intro e he; simp at he
  · split
    · intro e he; simp at he; subst he; rfl
    · intro e he; simp at he; subst he; exact removeSent_peerId _ _ _

theorem applyCommand_peerId (p : Peer) (now cmd) : (p.applyCommand now cmd).1.peerId = p.peerId := by
  unfold applyCommand; dsimp only
  split
  all_goals first
    | exact handleAcknowledge_peerId _ _ _ _ _
    | exact handleDisconnect_peerId _ _
    | exact handleVerifyConnect_peerId _ _
    | rfl
    | (split
       · first
           | exact handleData_peerId _ _
           | exact handleFragment_peerId _ _ _ _ _
           | rfl
       · rfl)

theorem applyCommand_named (p : Peer) (now cmd) :
    ∀ e ∈ (p.applyCommand now cmd).2.1, eventPeer e = p.peerId := by
  unfold applyCommand; dsimp only
  split
  all_goals first
    | exact handleAcknowledge_named _ _ _ _ _
    | exact handleDisconnect_named _ _
    | exact handleVerifyConnect_named _ _
    | (intro e he; simp at he; done)
    | (split
       · first
           | exact handleData_named _ _
           | exact handleFragment_named _ _ _ _ _
           | (intro e he; simp at he; done)
       · intro e he; simp at he)

theorem handleCommand_peerId (p : Peer) (now cmd st) : (p.handleCommand now cmd st).1.peerId = p.peerId ∧
    ∀ e ∈ (p.handleCommand now cmd st).2.1, eventPeer e = p.peerId := by
  unfold handleCommand
  have hid := applyCommand_peerId p now cmd
  have hn := applyCommand_named p now cmd
  generalize p.applyCommand now cmd = r at hid hn ⊢
  obtain ⟨q, es, acc⟩ := r
  dsimp only at hid hn ⊢
  split
  · exact ⟨hid, hn⟩
  · split
    · exact ⟨hid, hn⟩
    · split
      · exact ⟨hid, hn⟩
      · split <;> exact ⟨hid, hn⟩

theorem checkPeerTimeouts_peerId (p : Peer) (now) : (Host.checkPeerTimeouts p now).1.peerId = p.peerId := by
  unfold Host.checkPeerTimeouts; dsimp only; split <;> rfl
theorem checkPeerTimeouts_named (p : Peer) (now) :
    ∀ e ∈ (Host.checkPeerTimeouts p now).2, eventPeer e = p.peerId := by
  unfold Host.checkPeerTimeouts; dsimp only; split
  · split <;> intro e he <;> simp at he; subst he; rfl
  · intro e he; simp at he
theorem checkPeerPing_peerId (p : Peer) (now) : (Host.checkPeerPing p now).peerId = p.peerId := by
  unfold Host.checkPeerPing; split <;> rfl

theorem pollPeer_go_peerId : ∀ (fuel : Nat) (p : Peer) (now cs ds),
    (Host.pollPeer.go now cs fuel p ds).1.peerId = p.peerId ∧
      ∀ e ∈ (Host.pollPeer.go now cs fuel p ds).2.2, eventPeer e = p.peerId := by
  intro fuel
  induction fuel with
  | zero => intro p now cs ds; exact ⟨rfl, fun e he => by simp [Host.pollPeer.go] at he⟩
  | succ fuel ih =>
    intro p now cs ds
    unfold Host.pollPeer.go
    dsimp only
    have h1 : (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p).peerId = p.peerId := by
      split
      · exact queueDisconnect_peerId _ _
      · rfl
    generalize (if p.state == .disconnectLater ∧ p.outgoingCommands.isEmpty ∧ p.sentReliableCommands.isEmpty
        then p.queueDisconnect p.eventData else p) = q at h1 ⊢
    rw [← h1]
    have h2 : (Host.packOutgoingCommands q now).1.peerId = q.peerId := rfl
    generalize Host.packOutgoingCommands q now = r at h2 ⊢
    obtain ⟨q', cmds⟩ := r
    dsimp only at h2 ⊢
    rw [← h2]
    split
    · exact ih _ _ _ _
    · split
      · exact ⟨rfl, fun e he => by simp at he; subst he; rfl⟩
      · split
        · exact ⟨rfl, fun e he => by simp at he⟩
        · exact ⟨rfl, fun e he => by simp at he⟩

theorem pollPeer_peerId (p : Peer) (now cs) :
    (Host.pollPeer p now cs).1.peerId = p.peerId ∧
      ∀ e ∈ (Host.pollPeer p now cs).2.2, eventPeer e = p.peerId := by
  unfold Host.pollPeer
  split
  · exact ⟨rfl, fun e he => by simp at he⟩
  · exact pollPeer_go_peerId _ _ _ _ _

/-! ## Host steps -/

/-- A step of one peer from `p` to `q` reporting `es`: the peer keeps its ID,
every event names it, and the events fit its phase change. -/
structure PeerStep (p q : Peer) (es : Array Event) : Prop where
  peerId : q.peerId = p.peerId
  named : ∀ e ∈ es, eventPeer e = p.peerId
  wf : EventsWf (phase p.state) es.toList (phase q.state)

theorem PeerStep.trans {p q r : Peer} {e1 e2 : Array Event} (h1 : PeerStep p q e1) (h2 : PeerStep q r e2) :
    PeerStep p r (e1 ++ e2) where
  peerId := h2.peerId.trans h1.peerId
  named e he := by
    rcases Array.mem_append.mp he with he | he
    · exact h1.named e he
    · exact (h2.named e he).trans h1.peerId
  wf := by rw [Array.toList_append]; exact h1.wf.append h2.wf

theorem PeerStep.quiet {p q : Peer} (hid : q.peerId = p.peerId) (hs : q.state = p.state) : PeerStep p q #[] where
  peerId := hid
  named e he := by simp at he
  wf := by rw [hs]; exact .nil

/-- A step followed by changes to neither ID nor state. -/
theorem PeerStep.retarget {p q q' : Peer} {es : Array Event} (h : PeerStep p q es)
    (hid : q'.peerId = q.peerId) (hs : q'.state = q.state) : PeerStep p q' es :=
  ⟨hid.trans h.peerId, h.named, hs ▸ h.wf⟩

/-- The events of `es` about slot `i`. -/
def slotEvents (i : Nat) (es : Array Event) : List Event :=
  es.toList.filter fun e => (eventPeer e).toNat == i

/-- Slot `i` holds peer ID `i`, so an event's peer ID names its slot. -/
def IdsOk (peers : Array Peer) : Prop := ∀ i (hi : i < peers.size), peers[i].peerId.toNat = i

/-- A host step from peer array `a` to `b` reporting `es`: the same slots
with the same IDs, every event names a slot, and every slot's events fit its
phase change. -/
structure HostStep (a b : Array Peer) (es : Array Event) : Prop where
  size : b.size = a.size
  peerId : ∀ i (ha : i < a.size) (hb : i < b.size), b[i].peerId = a[i].peerId
  named : ∀ e ∈ es, (eventPeer e).toNat < a.size
  wf : ∀ i (ha : i < a.size) (hb : i < b.size), EventsWf (phase a[i].state) (slotEvents i es) (phase b[i].state)

theorem HostStep.idsOk {a b : Array Peer} {es} (h : HostStep a b es) (ha : IdsOk a) : IdsOk b := by
  intro i hi
  have hi' : i < a.size := h.size ▸ hi
  rw [h.peerId i hi' hi]; exact ha i hi'

theorem HostStep.trans {a b c : Array Peer} {e1 e2 : Array Event} (h1 : HostStep a b e1) (h2 : HostStep b c e2) :
    HostStep a c (e1 ++ e2) where
  size := h2.size.trans h1.size
  peerId i ha hc := by
    have hb : i < b.size := h1.size ▸ ha
    rw [h2.peerId i hb hc, h1.peerId i ha hb]
  named e he := by
    rcases Array.mem_append.mp he with he | he
    · exact h1.named e he
    · exact h1.size ▸ h2.named e he
  wf i ha hc := by
    have hb : i < b.size := h1.size ▸ ha
    unfold slotEvents; rw [Array.toList_append, List.filter_append]
    exact (h1.wf i ha hb).append (h2.wf i hb hc)

/-- A step that emits nothing and changes no slot's ID or state. -/
theorem HostStep.quiet {a b : Array Peer} (hs : b.size = a.size)
    (h : ∀ i (ha : i < a.size) (hb : i < b.size), b[i].peerId = a[i].peerId ∧ b[i].state = a[i].state) :
    HostStep a b #[] where
  size := hs
  peerId i ha hb := (h i ha hb).1
  named e he := by simp at he
  wf i ha hb := by rw [(h i ha hb).2]; exact .nil

theorem HostStep.rfl' (a : Array Peer) : HostStep a a #[] := .quiet rfl fun _ _ _ => ⟨rfl, rfl⟩

theorem slotEvents_all {es : Array Event} {i : Nat} (h : ∀ e ∈ es, (eventPeer e).toNat = i) :
    slotEvents i es = es.toList := by
  unfold slotEvents; rw [List.filter_eq_self]; intro e he; simp [h e (Array.mem_toList_iff.mp he)]

theorem slotEvents_none {es : Array Event} {i : Nat} (h : ∀ e ∈ es, (eventPeer e).toNat ≠ i) :
    slotEvents i es = [] := by
  unfold slotEvents; rw [List.filter_eq_nil_iff]; intro e he; simp [h e (Array.mem_toList_iff.mp he)]

/-- A step of one slot. -/
theorem hostStep_modify {a : Array Peer} (hids : IdsOk a) (j : Nat) (G : Peer → Peer) (es : Array Event)
    (hG : ∀ hj : j < a.size, PeerStep a[j] (G a[j]) es) (hes : ¬ j < a.size → es = #[]) :
    HostStep a (a.modify j G) es where
  size := Array.size_modify
  peerId i ha hb := by
    rw [Array.getElem_modify]; split
    · next hji => subst hji; exact (hG ha).peerId
    · rfl
  named e he := by
    by_cases hj : j < a.size
    · rw [(hG hj).named e he, hids j hj]; exact hj
    · simp [hes hj] at he
  wf i ha hb := by
    rw [Array.getElem_modify]; split
    · next hji =>
      subst hji
      have hs := hG ha
      rw [slotEvents_all fun e he => by rw [hs.named e he, hids j ha]]
      exact hs.wf
    · next hji =>
      rw [slotEvents_none]; · exact .nil
      intro e he
      by_cases hj : j < a.size
      · rw [(hG hj).named e he, hids j hj]; exact hji
      · simp [hes hj] at he

theorem foldl_append_toList (E : Peer → Array Event) (l : List Peer) (init : Array Event) :
    (l.foldl (fun es p => es ++ E p) init).toList = init.toList ++ l.flatMap fun p => (E p).toList := by
  induction l generalizing init with
  | nil => simp
  | cons p l ih => simp [ih]

theorem slot_flatMap (E : Peer → Array Event) (k : Nat) : ∀ (l : List Peer),
    (∀ j (hj : j < l.length), l[j].peerId.toNat = j + k) →
    (∀ p ∈ l, ∀ e ∈ E p, eventPeer e = p.peerId) → ∀ (i : Nat) (hi : i < l.length),
    (l.flatMap fun p => (E p).toList).filter (fun e => (eventPeer e).toNat == i + k) = (E l[i]).toList
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | p :: l, hid, hn, i, hi => by
    rw [List.flatMap_cons, List.filter_append]
    have hp : p.peerId.toNat = k := by have := hid 0 (by simp); simpa using this
    have tail : ∀ j (hj : j < l.length), l[j].peerId.toNat = j + (k + 1) := by
      intro j hj; have := hid (j + 1) (by simp; omega); simp at this; omega
    have hnl : ∀ q ∈ l, ∀ e ∈ E q, eventPeer e = q.peerId := fun q hq => hn q (List.mem_cons_of_mem _ hq)
    match i with
    | 0 =>
      rw [List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
      · simp
      · intro e he
        obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
        have := hnl _ hq e (Array.mem_toList_iff.mp he)
        simp [this, tail j hj]; omega
      · intro e he
        simp [hn p List.mem_cons_self e (Array.mem_toList_iff.mp he), hp]
    | i + 1 =>
      rw [List.filter_eq_nil_iff.mpr]
      · have := slot_flatMap E (k + 1) l tail hnl i (by simpa using hi)
        simp only [List.nil_append, List.getElem_cons_succ]
        rw [← this]; congr 1; funext e; congr 1; omega
      · intro e he
        simp [hn p List.mem_cons_self e (Array.mem_toList_iff.mp he), hp]

/-- A step of every slot, in order, each one on its own. -/
theorem hostStep_map {a : Array Peer} (hids : IdsOk a) (F : Peer → Peer) (E : Peer → Array Event)
    (hFE : ∀ p ∈ a, PeerStep p (F p) (E p)) :
    HostStep a (a.map F) (a.foldl (fun es p => es ++ E p) #[]) where
  size := Array.size_map
  peerId i ha hb := by rw [Array.getElem_map]; exact (hFE _ (Array.getElem_mem ha)).peerId
  named e he := by
    rw [← Array.mem_toList_iff, ← Array.foldl_toList, foldl_append_toList] at he
    simp only [List.nil_append, List.mem_flatMap, Array.mem_toList_iff] at he
    obtain ⟨p, hp, he⟩ := he
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hp
    rw [(hFE _ hp).named e he, hids j hj]; exact hj
  wf i ha hb := by
    unfold slotEvents
    rw [← Array.foldl_toList, foldl_append_toList, Array.toList_empty, List.nil_append]
    have := slot_flatMap E 0 a.toList (fun j hj => by simpa using hids j (by simpa using hj))
      (fun p hp => (hFE p (Array.mem_toList_iff.mp hp)).named) i (by simpa using ha)
    simp only [Nat.add_zero] at this
    rw [this, Array.getElem_map]
    simpa using (hFE _ (Array.getElem_mem ha)).wf

/-! ## `withPeer` and `mapPeers` as plain array updates -/

theorem mapM_stateM {σ} (l : List Peer) (init : σ) (f : Peer → σ → Peer × σ) (F : Peer → Peer)
    (g : Peer → σ → σ) (hf : ∀ p s, f p s = (F p, g p s)) :
    (l.mapM (m := StateM σ) fun p => modifyGet (f p)).run init = (l.map F, l.foldl (fun s p => g p s) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons p l ih =>
    simp only [List.mapM_cons, List.map_cons, List.foldl_cons]
    simp [hf, ih]; rfl

theorem arrayMapM_stateM {σ} (a : Array Peer) (init : σ) (f : Peer → σ → Peer × σ) (F : Peer → Peer)
    (g : Peer → σ → σ) (hf : ∀ p s, f p s = (F p, g p s)) :
    (a.mapM (m := StateM σ) fun p => modifyGet (f p)).run init = (a.map F, a.foldl (fun s p => g p s) init) := by
  rw [Array.mapM_eq_mapM_toList]
  simp only [StateT.run_map, mapM_stateM _ _ f F g hf, Array.foldl_toList]
  show ((List.map F a.toList).toArray, _) = _
  cases a; simp

theorem mapPeers_eq {σ} (h : Host) (init : σ) (f : Peer → σ → Peer × σ) (F : Peer → Peer)
    (g : Peer → σ → σ) (hf : ∀ p s, f p s = (F p, g p s)) :
    h.mapPeers init f = ({ h with peers := h.peers.map F }, h.peers.foldl (fun s p => g p s) init) := by
  unfold Host.mapPeers Host.takePeers
  dsimp only
  rw [arrayMapM_stateM _ _ f F g hf]

theorem withPeer_eq {α} (h : Host) (i : Nat) (d : α) (f : Peer → Peer × α) :
    h.withPeer i d f =
      ({ h with peers := h.peers.modify i (fun p => (f p).1) },
        if hi : i < h.peers.size then (f h.peers[i]).2 else d) := by
  unfold Host.withPeer Host.takePeers
  simp only [Array.modifyM, Array.modify, Id.run]
  by_cases hi : i < h.peers.size <;> simp [hi] <;> rfl

/-! ## Receiving -/

theorem handleCommand_step (p : Peer) (now cmd st) :
    PeerStep p (p.handleCommand now cmd st).1 (p.handleCommand now cmd st).2.1 :=
  ⟨(handleCommand_peerId _ _ _ _).1, (handleCommand_peerId _ _ _ _).2, handleCommand_wf _ _ _ _⟩

theorem readCommands_step (now st) : ∀ (xs : List Protocol.Command) (p0 : Peer) (acc : Peer × Array Event × Bool × Bool),
    PeerStep p0 acc.1 acc.2.1 →
      PeerStep p0 (xs.foldl (Host.readCommand now st) acc).1 (xs.foldl (Host.readCommand now st) acc).2.1
  | [], _, _, h => h
  | cmd :: xs, p0, ⟨p, es, reading, bw⟩, h => by
    rw [List.foldl_cons]
    refine readCommands_step now st xs p0 _ ?_
    unfold Host.readCommand
    cases reading
    · exact h
    · exact h.trans (handleCommand_step p now cmd st)

theorem hostStep_withPeer {h : Host} (hids : IdsOk h.peers) (i : Nat) (f : Peer → Peer × Array Event)
    (hf : ∀ p, PeerStep p (f p).1 (f p).2) :
    HostStep h.peers (h.withPeer i #[] f).1.peers (h.withPeer i #[] f).2 := by
  rw [withPeer_eq]
  exact hostStep_modify hids i (fun p => (f p).1) _ (fun hj => by rw [dif_pos hj]; exact hf _) (fun hj => by rw [dif_neg hj])

theorem handlePeerDatagram_step (p : Peer) (now fromAddr datagram bw) :
    PeerStep p (Host.handlePeerDatagram p now fromAddr datagram bw).1 (Host.handlePeerDatagram p now fromAddr datagram bw).2 := by
  unfold Host.handlePeerDatagram
  have h1 : PeerStep p { p with address := fromAddr } #[] := .quiet rfl rfl
  have h2 := readCommands_step now datagram.header.sentTime datagram.commands.toList p
    ({ p with address := fromAddr }, #[], true, false) h1
  rw [Array.foldl_toList] at h2
  dsimp only
  generalize Array.foldl _ _ datagram.commands = r at h2 ⊢
  split
  · exact h2.retarget rfl rfl
  · exact h2

/-- Writing peer `q` back to its own slot `j`. -/
theorem hostStep_setPeer {a : Array Peer} (hids : IdsOk a) {j : Nat} (hj : j < a.size) (q : Peer)
    (hq : PeerStep a[j] q #[]) : HostStep a (a.modify q.peerId.toNat fun _ => q) #[] := by
  rw [hq.peerId, hids j hj]
  exact hostStep_modify hids j _ _ (fun _ => hq) (fun _ => rfl)

/-- A CONNECT takes a free slot and reports nothing yet. -/
theorem handleIncomingConnect_step {h : Host} (hids : IdsOk h.peers) (fromAddr params data) :
    HostStep h.peers (h.handleIncomingConnect fromAddr params data).peers #[] := by
  unfold Host.handleIncomingConnect
  dsimp only
  split
  · exact .rfl' _
  · split
    · exact .rfl' _
    · next slot hslot =>
      have hfree : h.peers[slot.1].state = .disconnected := by
        unfold Host.freeSlot? at hslot
        have := (Array.findFinIdx?_eq_some_iff.mp hslot).1
        exact peerState_beq.mp this
      exact hostStep_setPeer hids slot.2 _ ⟨rfl, fun e he => by simp at he, by rw [hfree]; exact .nil⟩

theorem handleDatagram_step {h : Host} (hids : IdsOk h.peers) (now fromAddr bytes) :
    HostStep h.peers (h.handleDatagram now fromAddr bytes).1.peers (h.handleDatagram now fromAddr bytes).2 := by
  unfold Host.handleDatagram
  dsimp only
  split
  · exact .rfl' _
  · split
    · split
      · exact handleIncomingConnect_step hids _ _ _
      · exact .rfl' _
    · split
      · exact .rfl' _
      · split
        · exact .rfl' _
        · exact hostStep_withPeer hids _ _ fun p => handlePeerDatagram_step p _ _ _ _

/-! ## `service` -/

theorem checkPeerTimeouts_step (p : Peer) (now) :
    PeerStep p (Host.checkPeerTimeouts p now).1 (Host.checkPeerTimeouts p now).2.toArray :=
  ⟨checkPeerTimeouts_peerId _ _, fun e he => checkPeerTimeouts_named p now e (by simpa using he),
    by rw [Option.toList_toArray]; exact checkPeerTimeouts_wf _ _⟩

theorem checkTimeoutsAndPings_step {h : Host} (hids : IdsOk h.peers) (now) :
    HostStep h.peers (h.checkTimeoutsAndPings now).1.peers (h.checkTimeoutsAndPings now).2 := by
  unfold Host.checkTimeoutsAndPings
  let E (p : Peer) : Array Event :=
    if p.state == .disconnected ∨ p.state == .zombie then #[] else (Host.checkPeerTimeouts p now).2.toArray
  let F (p : Peer) : Peer :=
    if p.state == .disconnected ∨ p.state == .zombie then p
    else match Host.checkPeerTimeouts p now with
      | (q, some _) => q
      | (q, none) => Host.checkPeerPing q now
  rw [mapPeers_eq _ _ _ F (fun p s => s ++ E p)]
  · refine hostStep_map hids F E fun p _ => ?_
    simp only [F, E]
    split
    · exact .quiet rfl rfl
    · have hc := checkPeerTimeouts_step p now
      generalize Host.checkPeerTimeouts p now = c at hc ⊢
      obtain ⟨q, _ | e⟩ := c
      · exact (hc.trans (.quiet (checkPeerPing_peerId q now) (checkPeerPing_state q now))).retarget rfl rfl
      · exact hc
  · intro p s
    simp only [F, E]
    split
    · simp
    · generalize Host.checkPeerTimeouts p now = c
      obtain ⟨q, _ | e⟩ := c <;> simp

theorem foldl_pair_snd {α β} (D : Peer → Array α) (E : Peer → Array β) (a : Array Peer) (d0 : Array α) (e0 : Array β) :
    (a.foldl (fun s p => (s.1 ++ D p, s.2 ++ E p)) (d0, e0)).2 = a.foldl (fun es p => es ++ E p) e0 := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction a.toList generalizing d0 e0 with
  | nil => rfl
  | cons p l ih => exact ih _ _

theorem pollPeer_step (p : Peer) (now cs) :
    PeerStep p (Host.pollPeer p now cs).1 (Host.pollPeer p now cs).2.2 :=
  ⟨(pollPeer_peerId _ _ _).1, (pollPeer_peerId _ _ _).2, pollPeer_wf _ _ _⟩

theorem pollOutgoing_step {h : Host} (hids : IdsOk h.peers) (now) :
    HostStep h.peers (h.pollOutgoing now).1.peers (h.pollOutgoing now).2.2 := by
  unfold Host.pollOutgoing
  dsimp only
  rw [mapPeers_eq _ _ _ (fun p => (Host.pollPeer p now h.checksumEnabled).1)
    (fun p s => (s.1 ++ (Host.pollPeer p now h.checksumEnabled).2.1, s.2 ++ (Host.pollPeer p now h.checksumEnabled).2.2))
    (fun p s => rfl)]
  dsimp only
  rw [foldl_pair_snd]
  exact hostStep_map hids _ _ fun p _ => pollPeer_step p now _

/-- Same slots, with the same IDs and states. -/
def Similar (a b : Array Peer) : Prop :=
  b.size = a.size ∧ ∀ i (ha : i < a.size) (hb : i < b.size), b[i].peerId = a[i].peerId ∧ b[i].state = a[i].state

theorem Similar.trans {a b c : Array Peer} (h1 : Similar a b) (h2 : Similar b c) : Similar a c := by
  refine ⟨h2.1.trans h1.1, fun i ha hc => ?_⟩
  have hb : i < b.size := h1.1 ▸ ha
  rw [(h2.2 i hb hc).1, (h2.2 i hb hc).2, (h1.2 i ha hb).1, (h1.2 i ha hb).2]; exact ⟨rfl, rfl⟩

theorem Similar.map (a : Array Peer) (F : Peer → Peer) (hF : ∀ p, (F p).peerId = p.peerId ∧ (F p).state = p.state) :
    Similar a (a.map F) :=
  ⟨Array.size_map, fun i _ _ => by rw [Array.getElem_map]; exact hF _⟩

theorem Similar.ite {a x y : Array Peer} (c : Prop) [Decidable c] (hx : Similar a x) (hy : Similar a y) :
    Similar a (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem ite_peer {c : Prop} [Decidable c] {p q : Peer} (h : q.peerId = p.peerId ∧ q.state = p.state) :
    (if c then q else p).peerId = p.peerId ∧ (if c then q else p).state = p.state := by
  by_cases hc : c <;> simp [hc, h]

theorem Similar.hostStep {a b : Array Peer} (h : Similar a b) : HostStep a b #[] := .quiet h.1 h.2

theorem limitPeers_similar (elapsed : Nat) : ∀ (fuel : Nat) budget limited needs (peers : Array Peer),
    Similar peers (Host.outgoingThrottleLimits.limitPeers elapsed budget limited needs peers fuel).1
  | 0, _, _, _, peers => ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | fuel + 1, budget, limited, needs, peers => by
    unfold Host.outgoingThrottleLimits.limitPeers
    split
    · exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
    · dsimp only
      refine Similar.trans ?_ (limitPeers_similar elapsed fuel _ _ _ _)
      let motive (i : Nat) (r : Array Peer × Host.OutgoingBudget × Array UInt16) : Prop :=
        r.1.size = i ∧ ∀ k (h1 : k < peers.size) (h2 : k < r.1.size),
          r.1[k].peerId = peers[k].peerId ∧ r.1[k].state = peers[k].state
      have push : ∀ (i : Fin peers.size) (acc : Array Peer) (q : Peer), acc.size = i.1 →
          (∀ k (h1 : k < peers.size) (h2 : k < acc.size), acc[k].peerId = peers[k].peerId ∧ acc[k].state = peers[k].state) →
          q.peerId = peers[i].peerId → q.state = peers[i].state →
          (acc.push q).size = i.1 + 1 ∧ ∀ k (h1 : k < peers.size) (h2 : k < (acc.push q).size),
            (acc.push q)[k].peerId = peers[k].peerId ∧ (acc.push q)[k].state = peers[k].state := by
        intro i acc q hsz hacc hid hst
        refine ⟨by simp [hsz], fun k h1 h2 => ?_⟩
        rw [Array.getElem_push]
        split
        · exact hacc k h1 _
        · have : k = i.1 := by simp at h2; omega
          subst this; exact ⟨hid, hst⟩
      refine (fun (this : motive peers.size _) => ⟨this.1, fun k ha hb => this.2 k ha hb⟩)
        (Array.foldl_induction (as := peers) motive ⟨rfl, fun k _ h => by simp at h⟩ ?_)
      intro i r ⟨hsz, hr⟩
      obtain ⟨acc, bud, lim⟩ := r
      dsimp only at hsz hr ⊢
      split
      · exact push i acc _ hsz hr rfl rfl
      · exact push i acc _ hsz hr rfl rfl

theorem outgoingThrottleLimits_similar (h : Host) (elapsed : Nat) :
    Similar h.peers (h.outgoingThrottleLimits elapsed) := by
  unfold Host.outgoingThrottleLimits
  dsimp only
  exact .ite _ (limitPeers_similar _ _ _ _ _ _)
    ((limitPeers_similar _ _ _ _ _ _).trans (.map _ _ fun _ => ite_peer ⟨rfl, rfl⟩))

/-- The bandwidth throttle reports nothing and changes no phase. -/
theorem bandwidthThrottle_similar (h : Host) (now) : Similar h.peers (h.bandwidthThrottle now).peers := by
  unfold Host.bandwidthThrottle
  split
  · exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  · dsimp only
    split
    · exact ⟨rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
    · split
      · exact outgoingThrottleLimits_similar _ _
      · exact (outgoingThrottleLimits_similar _ _).trans (.map _ _ fun _ => ite_peer ⟨rfl, rfl⟩)

/-- **`service` keeps every slot's events well formed.** -/
theorem service_step {h : Host} (hids : IdsOk h.peers) (now) :
    HostStep h.peers (h.service now).1.peers (h.service now).2.2 := by
  unfold Host.service
  dsimp only
  have h1 := (bandwidthThrottle_similar h now).hostStep
  have h2 := checkTimeoutsAndPings_step (h1.idsOk hids) now
  have h3 := pollOutgoing_step (h2.idsOk (h1.idsOk hids)) now
  have := h1.trans (h2.trans h3)
  rwa [Array.empty_append] at this

/-! ## The application's calls -/

theorem idsOk_create (address peerCount channelLimit inBw outBw seed mtu) :
    IdsOk (Host.create address peerCount channelLimit inBw outBw seed mtu).peers := by
  intro i hi
  simp only [Host.create, Array.size_map, Array.size_range] at hi
  simp only [Host.create, Array.getElem_map, Array.getElem_range]
  have : i < 4095 := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
  simp [Nat.toUInt16]; omega

theorem Similar.modify (a : Array Peer) (j : Nat) (G : Peer → Peer)
    (hG : ∀ p, (G p).peerId = p.peerId ∧ (G p).state = p.state) : Similar a (a.modify j G) :=
  ⟨Array.size_modify, fun i _ _ => by rw [Array.getElem_modify]; split; exact hG _; exact ⟨rfl, rfl⟩⟩

theorem similar_withPeer {α} (h : Host) (i : Nat) (d : α) (f : Peer → Peer × α)
    (hf : ∀ p, (f p).1.peerId = p.peerId ∧ (f p).1.state = p.state) :
    Similar h.peers (h.withPeer i d f).1.peers := by
  rw [withPeer_eq]; exact .modify _ _ _ hf

theorem similar_mapPeers {σ} (h : Host) (init : σ) (f : Peer → σ → Peer × σ) (F : Peer → Peer) (g : Peer → σ → σ)
    (hfg : ∀ p s, f p s = (F p, g p s)) (hF : ∀ p, (F p).peerId = p.peerId ∧ (F p).state = p.state) :
    Similar h.peers (h.mapPeers init f).1.peers := by
  rw [mapPeers_eq _ _ _ F g hfg]; exact .map _ _ hF

theorem enqueue_same (p : Peer) (c pk cs) :
    (p.enqueue c pk cs).peerId = p.peerId ∧ (p.enqueue c pk cs).state = p.state := by
  have fold : ∀ (xs : List OutgoingCommand) (q : Peer),
      (xs.foldl queueOutgoingCommand q).peerId = q.peerId ∧ (xs.foldl queueOutgoingCommand q).state = q.state := by
    intro xs; induction xs with
    | nil => intro q; exact ⟨rfl, rfl⟩
    | cons x xs ih => intro q; exact ih _
  unfold enqueue
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split
    · rw [← Array.foldl_toList]; exact fold _ _
    · unfold packetCommand; dsimp only; split <;> (try split) <;> exact ⟨rfl, rfl⟩

theorem trySend_similar (h : Host) (id c pk) : Similar h.peers (h.trySend id c pk).1.peers := by
  unfold Host.trySend
  exact similar_withPeer _ _ _ _ fun p => by split; exact ⟨rfl, rfl⟩; exact enqueue_same _ _ _ _

theorem broadcast_similar (h : Host) (c pk) : Similar h.peers (h.broadcast c pk).peers := by
  unfold Host.broadcast
  refine similar_mapPeers _ _ _ (fun p =>
      if p.state == .connected && (p.sendError? c pk h.checksumEnabled).isNone then
        p.enqueue c pk h.checksumEnabled
      else p) (fun _ _ => ()) (fun p s => ?_) fun p => ite_peer (enqueue_same _ _ _ _)
  split <;> simp [*]

theorem throttleConfigure_similar (h : Host) (id i a d) : Similar h.peers (h.throttleConfigure id i a d).peers :=
  .modify _ _ _ fun _ => ⟨rfl, rfl⟩

theorem setPeerTimeout_similar (h : Host) (id l mn mx) : Similar h.peers (h.setPeerTimeout id l mn mx).peers :=
  .modify _ _ _ fun _ => ⟨rfl, rfl⟩

/-- A disconnect starts, but nothing is reported until it completes. -/
theorem disconnect_step {h : Host} (hids : IdsOk h.peers) (id d) :
    HostStep h.peers (h.disconnect id d).peers #[] := by
  unfold Host.disconnect Host.modifyPeer
  exact hostStep_modify hids id.toNat (·.queueDisconnect d) _ (fun _ => ⟨queueDisconnect_peerId _ _, fun e he => by simp at he,
    by rw [queueDisconnect_phase]; exact .nil⟩) fun _ => rfl

theorem disconnectLater_step {h : Host} (hids : IdsOk h.peers) (id d) :
    HostStep h.peers (h.disconnectLater id d).peers #[] := by
  unfold Host.disconnectLater Host.modifyPeer
  refine hostStep_modify hids id.toNat (fun p =>
      if p.isConnected ∧ (!p.outgoingCommands.isEmpty ∨ !p.sentReliableCommands.isEmpty) then
        { p with state := .disconnectLater, eventData := d }
      else p.queueDisconnect d) _ (fun _ => ?_) fun _ => rfl
  split
  · next hc => exact ⟨rfl, fun e he => by simp at he, by rw [isConnected_up hc.1]; exact .nil⟩
  · exact ⟨queueDisconnect_peerId _ _, fun e he => by simp at he, by rw [queueDisconnect_phase]; exact .nil⟩

theorem modifyPeer_peers (h : Host) (i : UInt16) (f : Peer → Peer) :
    (h.modifyPeer i f).peers = h.peers.modify i.toNat f := rfl

/-- `Host.random` leaves the peers alone. Stated over a variable seed on
purpose: letting the kernel compare the reseeded host with `h` field by
field would unfold `h.randomSeed + 0x6D2B79F5` one successor at a time. -/
theorem peers_withSeed (h : Host) (s : UInt32) : ({ h with randomSeed := s } : Host).peers = h.peers := rfl

theorem random_peers (h : Host) : h.random.1.peers = h.peers := by
  unfold Host.random; exact peers_withSeed h _

/-- A connection attempt takes a free slot and reports nothing yet. -/
theorem connect_step {h h' : Host} {id} (hids : IdsOk h.peers) {addr n d}
    (hc : h.connect addr n d = .ok (h', id)) : HostStep h.peers h'.peers #[] := by
  unfold Host.connect at hc
  have hp := random_peers h
  rcases hr : h.random with ⟨h2, cid⟩
  rw [hr] at hc hp
  simp only at hp
  split at hc
  · next slot hslot =>
    have hfree : h.peers[slot.1].state = .disconnected := by
      unfold Host.freeSlot? at hslot
      exact peerState_beq.mp (Array.findFinIdx?_eq_some_iff.mp hslot).1
    cases hc
    rw [modifyPeer_peers, hp]
    exact hostStep_setPeer hids slot.2 _ ⟨rfl, fun e he => by simp at he, by rw [hfree]; exact .nil⟩
  · cases hc

/-! ## Whole runs -/

/-- Everything a driver can do to a host. -/
inductive Op
  | datagram (now : UInt32) (fromAddr : Address) (bytes : ByteArray)
  | service (now : UInt32)
  | connect (remoteAddress : Address) (channelCount : Nat) (data : UInt32)
  | send (peerId : UInt16) (channelId : UInt8) (packet : Packet)
  | broadcast (channelId : UInt8) (packet : Packet)
  | disconnect (peerId : UInt16) (data : UInt32)
  | disconnectLater (peerId : UInt16) (data : UInt32)
  | throttleConfigure (peerId : UInt16) (interval accel decel : UInt32)
  | setPeerTimeout (peerId : UInt16) (limit minimum maximum : UInt32)

/-- One operation: the new host and the events it reports. -/
def Op.apply (h : Host) : Op → Host × Array Event
  | .datagram now fromAddr bytes => h.handleDatagram now fromAddr bytes
  | .service now => ((h.service now).1, (h.service now).2.2)
  | .connect addr n d => match h.connect addr n d with
    | .ok (h, _) => (h, #[])
    | .error _ => (h, #[])
  | .send id c pk => ((h.trySend id c pk).1, #[])
  | .broadcast c pk => (h.broadcast c pk, #[])
  | .disconnect id d => (h.disconnect id d, #[])
  | .disconnectLater id d => (h.disconnectLater id d, #[])
  | .throttleConfigure id i a d => (h.throttleConfigure id i a d, #[])
  | .setPeerTimeout id l mn mx => (h.setPeerTimeout id l mn mx, #[])

/-- A run of operations: the final host and every event, in order. -/
def run (h : Host) : List Op → Host × Array Event
  | [] => (h, #[])
  | op :: ops =>
    let (h', es) := op.apply h
    let (h'', es') := run h' ops
    (h'', es ++ es')

theorem Op.apply_step {h : Host} (hids : IdsOk h.peers) : ∀ op : Op, HostStep h.peers (op.apply h).1.peers (op.apply h).2
  | .datagram .. => handleDatagram_step hids _ _ _
  | .service .. => service_step hids _
  | .connect addr n d => by
    simp only [Op.apply]
    split
    · next hc => exact connect_step hids hc
    · exact .rfl' _
  | .send .. => (trySend_similar _ _ _ _).hostStep
  | .broadcast .. => (broadcast_similar _ _ _).hostStep
  | .disconnect .. => disconnect_step hids _ _
  | .disconnectLater .. => disconnectLater_step hids _ _
  | .throttleConfigure .. => (throttleConfigure_similar _ _ _ _ _).hostStep
  | .setPeerTimeout .. => (setPeerTimeout_similar _ _ _ _ _).hostStep

theorem run_step : ∀ (ops : List Op) {h : Host}, IdsOk h.peers → HostStep h.peers (run h ops).1.peers (run h ops).2
  | [], _, _ => .rfl' _
  | op :: ops, h, hids => by
    have h1 := Op.apply_step hids op
    exact h1.trans (run_step ops (h1.idsOk hids))

/-- **Every run keeps every slot's events well formed.** From a fresh host,
whatever the driver does and whatever arrives off the wire, the events of
each peer slot form a run of connections: a connect only while the slot is
down, receives only while it is up, and between two connects a disconnect.
Every event names an existing slot, so none escape this. -/
theorem run_wf (address peerCount channelLimit inBw outBw seed mtu) (ops : List Op) :
    let h := Host.create address peerCount channelLimit inBw outBw seed mtu
    (∀ e ∈ (run h ops).2, (eventPeer e).toNat < (run h ops).1.peers.size) ∧
      ∀ i (hi : i < (run h ops).1.peers.size),
        EventsWf .down (slotEvents i (run h ops).2) (phase (run h ops).1.peers[i].state) := by
  intro h
  have hs := run_step ops (idsOk_create address peerCount channelLimit inBw outBw seed mtu)
  refine ⟨fun e he => hs.size ▸ hs.named e he, fun i hi => ?_⟩
  have hi0 : i < h.peers.size := hs.size ▸ hi
  have := hs.wf i hi0 hi
  have hfresh : h.peers[i].state = .disconnected := by simp [h, Host.create]
  rwa [hfresh] at this

end Lenet.Proofs
