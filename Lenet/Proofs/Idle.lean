import Std.Tactic.BVDecide
import Lenet.Proofs.Deadline
import Lenet.Proofs.HostEvents

/-!
# Nothing happens before the deadline

`Proofs/Deadline` shows `nextDeadline` is the earliest of the host's
timers. That is only useful to a driver if the timers are all the work
there is: this file shows that on a host with nothing queued, a `service`
call before every timer sends nothing and reports nothing
(`service_before_timers`), so a driver that sleeps until `nextDeadline`
skips nothing (`service_before_deadline`).

"Nothing queued" (`Quiet`): no commands queued, no ACKs owed, and no peer
part-way through a close the next service would complete. Those are not
timers: the driver services right after feeding a datagram or queuing a
send, which is when they appear (`lenet.h`, driver rules). The times the
host recorded are assumed to lie in the past of `now` within ENet's 24-hour
window (`Past`): the driver's clock does not run backwards.
-/

namespace Lenet.Proofs

open Host

/-- Nothing but timers is pending. -/
def Quiet (h : Host) : Prop :=
  ∀ p ∈ h.peers, p.outgoingCommands = #[] ∧ p.acknowledgements = #[] ∧
    p.state ≠ .disconnectLater ∧ p.state ≠ .acknowledgingDisconnect ∧ p.state ≠ .zombie

/-- The times the host recorded are not after `now`. -/
def Past (h : Host) (now : UInt32) : Prop :=
  InWindow h.bandwidthThrottleEpoch now ∧
    ∀ p ∈ h.peers, (∀ c ∈ p.sentReliableCommands, InWindow c.sentTime now) ∧ InWindow p.lastReceiveTime now

/-- Every timer lies after `now`, inside the window. -/
def Before (h : Host) (now : UInt32) : Prop := ∀ t ∈ hostTimers h, InWindow now t ∧ t ≠ now

/-- A timer `s + d` after `now`, for a time `s` not after `now`: less than
`d` has passed since `s`. -/
theorem elapsed_lt {now s d : UInt32} (hs : InWindow s now) (ht : InWindow now (s + d)) (hne : s + d ≠ now) :
    Time.difference now s < d := by
  unfold InWindow at hs ht
  unfold Time.difference
  simp only [Time.overflow] at *
  bv_decide

theorem timers_of_peer {h : Host} {p : Peer} (hp : p ∈ h.peers) {t : UInt32} (ht : t ∈ peerTimers p) :
    t ∈ hostTimers h := by
  unfold hostTimers
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, Array.mem_toList_iff.mpr hp, ht⟩)

/-! ## The timers do not fire -/

theorem bandwidthThrottle_before {h : Host} {now : UInt32} (hp : Past h now) (hb : Before h now) :
    h.bandwidthThrottle now = h := by
  have ht : h.bandwidthThrottleEpoch + Constants.bandwidthThrottleInterval ∈ hostTimers h := by
    unfold hostTimers; simp
  obtain ⟨hw, hne⟩ := hb _ ht
  unfold Host.bandwidthThrottle
  rw [if_pos (elapsed_lt hp.1 hw hne)]

/-- The timeout scan of a peer whose in-flight commands are all younger
than their timeouts keeps them all in flight and queues nothing. -/
theorem checkPeerTimeouts_quiet {p : Peer} {now : UInt32}
    (hc : ∀ c ∈ p.sentReliableCommands, Time.difference now c.sentTime < c.roundTripTimeout) :
    (Host.checkPeerTimeouts p now).2 = none ∧
      (Host.checkPeerTimeouts p now).1.outgoingCommands = p.outgoingCommands ∧
      (Host.checkPeerTimeouts p now).1.sentReliableCommands.size = p.sentReliableCommands.size ∧
      (Host.checkPeerTimeouts p now).1.state = p.state ∧
      (Host.checkPeerTimeouts p now).1.acknowledgements = p.acknowledgements ∧
      (Host.checkPeerTimeouts p now).1.lastReceiveTime = p.lastReceiveTime ∧
      (Host.checkPeerTimeouts p now).1.pingInterval = p.pingInterval := by
  unfold Host.checkPeerTimeouts
  dsimp only
  have hscan := Array.foldl_induction
    (motive := fun i (scan : TimeoutScan) => scan.timedOut = false ∧ scan.retransmits = #[] ∧
      scan.stillInFlight.size = i)
    (as := p.sentReliableCommands) (init := ({ earliestTimeout := p.earliestTimeout } : TimeoutScan))
    (f := fun scan outCmd =>
      if scan.timedOut then scan
      else if Time.difference now outCmd.sentTime < outCmd.roundTripTimeout then
        { scan with stillInFlight := scan.stillInFlight.push outCmd }
      else
        let earliest :=
          if scan.earliestTimeout == 0 ∨ Time.less outCmd.sentTime scan.earliestTimeout then outCmd.sentTime
          else scan.earliestTimeout
        if p.isTimedOut now earliest outCmd.sendAttempts then
          { scan with timedOut := true }
        else
          { scan with
            earliestTimeout := earliest
            retransmits := scan.retransmits.push { outCmd with roundTripTimeout := outCmd.roundTripTimeout * 2 } })
    ⟨rfl, rfl, rfl⟩ (fun i scan ⟨h1, h2, h3⟩ => by
      dsimp only
      rw [if_neg (by simp [h1])]
      have hci := hc p.sentReliableCommands[i] (Array.getElem_mem i.2)
      split
      · exact ⟨h1, h2, by simp [h3]⟩
      · next hn => exact absurd hci hn)
  generalize p.sentReliableCommands.foldl _ _ = scan at hscan ⊢
  obtain ⟨h1, h2, h3⟩ := hscan
  rw [if_neg (by simp [h1])]
  refine ⟨rfl, by simp [h2], h3, rfl, rfl, rfl, rfl⟩

/-- The packer on a peer with nothing queued and no ACKs owed makes no
datagram. -/
theorem packOutgoingCommands_empty {p : Peer} (now hc) (ho : p.outgoingCommands = #[])
    (ha : p.acknowledgements = #[]) : (Host.packOutgoingCommands p now hc).2 = #[] := by
  unfold Host.packOutgoingCommands
  simp only [ho, ha, Array.foldl_empty]
  rfl

/-! ## The whole service call -/

/-- What `checkTimeoutsAndPings` leaves of a quiet peer: still quiet. -/
def QuietPeer (p : Peer) : Prop :=
  p.outgoingCommands = #[] ∧ p.acknowledgements = #[] ∧
    p.state ≠ .disconnectLater ∧ p.state ≠ .acknowledgingDisconnect ∧ p.state ≠ .zombie

theorem pollPeer_quiet {p : Peer} (hq : QuietPeer p) (now cs) :
    (Host.pollPeer p now cs).2.1 = #[] ∧ (Host.pollPeer p now cs).2.2 = #[] := by
  obtain ⟨ho, ha, hl, had, hz⟩ := hq
  unfold Host.pollPeer
  split
  · exact ⟨rfl, rfl⟩
  · unfold Host.pollPeer.go
    dsimp only
    have hnl : (p.state == PeerState.disconnectLater) = false :=
      Bool.eq_false_iff.mpr fun h => hl (peerState_beq.mp h)
    simp only [hnl, Bool.false_eq_true, false_and, if_false]
    have hpk := packOutgoingCommands_empty now cs ho ha
    have hst : (Host.packOutgoingCommands p now cs).1.state = p.state := rfl
    have hack : (Host.packOutgoingCommands p now cs).1.acknowledgements = #[] := by
      show p.acknowledgements.drop _ = #[]; rw [ha]; rfl
    generalize Host.packOutgoingCommands p now cs = r at hpk hst hack ⊢
    obtain ⟨q, packed⟩ := r
    dsimp only at hpk hst hack ⊢
    subst hpk
    have had' : (q.state == PeerState.acknowledgingDisconnect) = false :=
      Bool.eq_false_iff.mpr fun h => had (hst ▸ peerState_beq.mp h)
    have hz' : (q.state == PeerState.zombie) = false :=
      Bool.eq_false_iff.mpr fun h => hz (hst ▸ peerState_beq.mp h)
    simp only [Array.isEmpty_empty, Bool.not_true, Bool.false_eq_true, if_false, had', false_and, hz']
    constructor <;> first | rfl | trivial

/-- **Before every timer, a quiet host's `service` does nothing visible**:
it sends no datagram and reports no event. -/
theorem service_before_timers {h : Host} {now : UInt32} (hq : Quiet h) (hp : Past h now) (hb : Before h now) :
    (h.service now).2.1 = #[] ∧ (h.service now).2.2 = #[] := by
  unfold Host.service
  dsimp only
  rw [bandwidthThrottle_before hp hb]
  -- each peer's step in `checkTimeoutsAndPings`
  let F (p : Peer) : Peer :=
    if p.state == .disconnected ∨ p.state == .zombie then p
    else match Host.checkPeerTimeouts p now with
      | (q, some _) => q
      | (q, none) => Host.checkPeerPing q now
  let E (p : Peer) : Array Event :=
    if p.state == .disconnected ∨ p.state == .zombie then #[] else (Host.checkPeerTimeouts p now).2.toArray
  have hstep : ∀ p ∈ h.peers, E p = #[] ∧ QuietPeer (F p) := by
    intro p hpm
    obtain ⟨ho, ha, hl, had, hz⟩ := hq p hpm
    obtain ⟨hsent, hrecv⟩ := hp.2 p hpm
    -- every in-flight command is younger than its timeout
    have hc : ∀ c ∈ p.sentReliableCommands, Time.difference now c.sentTime < c.roundTripTimeout := by
      intro c hcm
      have ht : c.sentTime + c.roundTripTimeout ∈ hostTimers h :=
        timers_of_peer hpm (List.mem_append_left _ (List.mem_map.mpr ⟨c, Array.mem_toList_iff.mpr hcm, rfl⟩))
      exact elapsed_lt (hsent c hcm) (hb _ ht).1 (hb _ ht).2
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := checkPeerTimeouts_quiet hc
    simp only [E, F]
    split
    · exact ⟨rfl, ho, ha, hl, had, hz⟩
    · refine ⟨by rw [e1]; rfl, ?_⟩
      generalize hct : Host.checkPeerTimeouts p now = r at e1 e2 e3 e4 e5 e6 e7
      obtain ⟨q, ev⟩ := r
      dsimp only at e1 e2 e3 e4 e5 e6 e7 ⊢
      subst e1
      dsimp only
      unfold Host.checkPeerPing
      split
      · next hping =>
        exfalso
        obtain ⟨helig, hge⟩ := hping
        -- a peer that may ping has its keepalive timer scheduled
        have helig' : Host.pingEligible p = true := by
          unfold Host.pingEligible at helig ⊢
          simp only [Bool.and_eq_true, Array.isEmpty_iff_size_eq_zero] at helig ⊢
          rw [e2, ho] at helig
          refine ⟨⟨e4 ▸ helig.1.1, by rw [← e3]; exact helig.1.2⟩, by rw [ho]; simp⟩
        have ht : p.lastReceiveTime + p.pingInterval ∈ hostTimers h :=
          timers_of_peer hpm (List.mem_append_right _ (by simp [pingEligible, helig']))
        have := elapsed_lt hrecv (hb _ ht).1 (hb _ ht).2
        rw [e6, e7] at hge
        exact absurd hge (UInt32.not_le.mpr this)
      · exact ⟨by rw [e2, ho], by rw [e5, ha], by rw [e4]; exact hl, by rw [e4]; exact had, by rw [e4]; exact hz⟩
  unfold Host.checkTimeoutsAndPings
  rw [mapPeers_eq _ _ _ F (fun p s => s ++ E p) (fun p s => by
    simp only [F, E]; split
    · rfl
    · generalize Host.checkPeerTimeouts p now = c; obtain ⟨q, _ | e⟩ := c <;> rfl)]
  dsimp only
  have hev : h.peers.foldl (fun s p => s ++ E p) #[] = #[] := by
    refine Array.foldl_induction (motive := fun _ (s : Array Event) => s = #[]) rfl ?_
    intro i s hs
    have he := (hstep h.peers[i] (Array.getElem_mem i.2)).1
    rw [hs, he]; rfl
  rw [hev]
  -- then `pollOutgoing` over peers that are all still quiet
  unfold Host.pollOutgoing
  dsimp only
  rw [mapPeers_eq _ _ _ (fun p => (Host.pollPeer p now h.checksumEnabled).1)
    (fun p s => (s.1 ++ (Host.pollPeer p now h.checksumEnabled).2.1, s.2 ++ (Host.pollPeer p now h.checksumEnabled).2.2))
    (fun p s => rfl)]
  dsimp only
  have hpoll := Array.foldl_induction
    (motive := fun _ (s : Array (Address × ByteArray) × Array Event) => s = (#[], #[]))
    (as := h.peers.map F) (init := ((#[], #[]) : Array (Address × ByteArray) × Array Event))
    (f := fun s p => (s.1 ++ (Host.pollPeer p now h.checksumEnabled).2.1, s.2 ++ (Host.pollPeer p now h.checksumEnabled).2.2))
    rfl (fun i s hs => by
      obtain ⟨p, hpm, hpe⟩ := Array.mem_map.mp (Array.getElem_mem (xs := h.peers.map F) i.2)
      have := pollPeer_quiet (hstep p hpm).2 now h.checksumEnabled
      rw [hs]
      show (#[] ++ (Host.pollPeer (h.peers.map F)[i] now h.checksumEnabled).2.1,
        #[] ++ (Host.pollPeer (h.peers.map F)[i] now h.checksumEnabled).2.2) = (#[], #[])
      have hpe' : (h.peers.map F)[i] = F p := hpe.symm
      rw [hpe', this.1, this.2]; rfl)
  rw [hpoll]
  exact ⟨rfl, rfl⟩

/-- **A driver sleeping until `nextDeadline` skips nothing**: on a quiet
host whose recorded times are in the past, a `service` call at any time
before the deadline (with every timer inside the window of `now`) sends
nothing and reports nothing. -/
theorem service_before_deadline {h : Host} {now d : UInt32} (hq : Quiet h) (hp : Past h now)
    (hw : ∀ t ∈ hostTimers h, InWindow now t) (hd : h.nextDeadline = some d) (hbefore : d ≠ now) :
    (h.service now).2.1 = #[] ∧ (h.service now).2.2 = #[] := by
  refine service_before_timers hq hp fun t ht => ⟨hw t ht, fun heq => ?_⟩
  obtain ⟨hle, -⟩ := nextDeadline_earliest h now hw hd t ht
  subst heq
  rw [UInt32.sub_self] at hle
  have hd0 : d - t = 0 := UInt32.le_zero_iff.mp hle
  exact hbefore (by bv_decide)

end Lenet.Proofs
