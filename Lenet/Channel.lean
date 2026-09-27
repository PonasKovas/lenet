import Lenet.Constants
import Lenet.Packet

namespace Lenet

/-- A reliable delivery staged out of order: `seq` is the sequence number it
starts at, `span` the number of sequence numbers it occupies (1 for a plain
reliable packet, the fragment count for a reassembled fragmented packet).
ENet treats a fragment set as one incoming reliable command spanning
`fragmentCount` sequence numbers and advances the dispatch frontier by the
whole span when it dispatches (peer.c `dispatch_incoming_reliable_commands`:
`incomingReliableSequenceNumber += fragmentCount - 1`). -/
structure StagedReliable where
  seq : UInt16
  span : Nat
  packet : Packet
deriving BEq, Inhabited

/-- An unreliable delivery held back until the reliable dispatch frontier
reaches `reliableSeq`, the reliable sequence number it was sent after. -/
structure StagedUnreliable where
  reliableSeq   : UInt16
  unreliableSeq : UInt16
  packet        : Packet
deriving BEq, Inhabited

/-- One channel of a connection: its sequence counters, the send-side
reliable window accounting and the receive-side staging of out-of-order
reliable deliveries. Channels are sequenced independently. -/
structure Channel where
  /-- Last sequence number given to an outgoing reliable command (numbering
  starts at 1). -/
  outgoingReliableSequenceNumber   : UInt16 := 0
  /-- Last sequence number given to an outgoing unreliable command; restarts
  with every reliable command. -/
  outgoingUnreliableSequenceNumber : UInt16 := 0
  /-- The reliable dispatch frontier: everything up to it has been delivered. -/
  incomingReliableSequenceNumber   : UInt16 := 0
  /-- Highest unreliable sequence number received in the current reliable window. -/
  incomingUnreliableSequenceNumber : UInt16 := 0
  /-- In-flight unacknowledged reliable command counts for each of the
  `Constants.reliableWindows` windows. Fixed-size by construction. -/
  reliableWindows                  : Vector UInt16 Constants.reliableWindows := Vector.replicate Constants.reliableWindows 0
  /-- Staged out-of-order reliable deliveries waiting for gaps in sequence
  numbers to be filled. -/
  stagedReliable                   : Array StagedReliable := #[]
  /-- Unreliable deliveries sent after a reliable command that has not been
  delivered yet; at most `maximumStagedUnreliable`, each key at most once. -/
  stagedUnreliable                 : Array StagedUnreliable := #[]
deriving BEq, Inhabited

namespace Channel

/-- Any index reduced mod the window count is a valid window slot. -/
theorem modWindowIndex_lt (i : Nat) :
    i % Constants.reliableWindows < Constants.reliableWindows :=
  Nat.mod_lt _ (by decide)

/-- Computes the window slot index (0..15) for a 16-bit sequence number. -/
@[inline]
def windowIndex (seq : UInt16) : Nat :=
  (seq.toNat / Constants.reliableWindowSize) % Constants.reliableWindows

/-- `windowIndex` is always a valid window slot. -/
theorem windowIndex_lt (seq : UInt16) : windowIndex seq < Constants.reliableWindows :=
  modWindowIndex_lt _

/--
Increments and returns the next outgoing reliable sequence number.
Resets the channel's outgoing unreliable sequence number to 0 (matching ENet semantics).
-/
def nextReliableSequenceNumber (c : Channel) : Channel × UInt16 :=
  let nextSeq := c.outgoingReliableSequenceNumber + 1
  ({ c with
     outgoingReliableSequenceNumber   := nextSeq
     outgoingUnreliableSequenceNumber := 0
  }, nextSeq)

/-- Increments and returns the next outgoing unreliable sequence number. -/
def nextUnreliableSequenceNumber (c : Channel) : Channel × UInt16 :=
  let nextSeq := c.outgoingUnreliableSequenceNumber + 1
  ({ c with outgoingUnreliableSequenceNumber := nextSeq }, nextSeq)

/--
Checks whether an incoming reliable sequence number falls within the acceptable
sliding receive window.
-/
def isIncomingReliableInWindow (c : Channel) (seq : UInt16) : Bool :=
  let winSize  := Constants.reliableWindowSize
  let numWins  := Constants.reliableWindows
  let freeWins := Constants.freeReliableWindows
  let rawWin   := seq.toNat / winSize
  let curWin   := c.incomingReliableSequenceNumber.toNat / winSize
  let win      := if seq < c.incomingReliableSequenceNumber then rawWin + numWins else rawWin
  win ≥ curWin && win < curWin + freeWins - 1

/-- Whether reliable sequence number `seq` is ahead of the dispatch frontier
inside the receive window: what the receive path admits, and what staging
keeps. -/
def isReliableAhead (c : Channel) (seq : UInt16) : Bool :=
  c.isIncomingReliableInWindow seq && seq != c.incomingReliableSequenceNumber

/-- Whether reliable sequence number `seq` lies in the window just past the
receive window, which the receive path drops. A sender may be that far
ahead: it keeps up to seven windows in flight ending at the last one sent
(Proofs/Window.lean), and the oldest of them may be the first after the
frontier, in the window after the frontier's. So such a command is not
acknowledged, or the sender would retire a packet the receiver dropped.
ENet acknowledges it and loses the packet. -/
def isReliableTooFarAhead (c : Channel) (seq : UInt16) : Bool :=
  let winSize := Constants.reliableWindowSize
  let rawWin  := seq.toNat / winSize
  let curWin  := c.incomingReliableSequenceNumber.toNat / winSize
  let win     := if seq < c.incomingReliableSequenceNumber then rawWin + Constants.reliableWindows else rawWin
  win == curWin + Constants.freeReliableWindows - 1

/--
Records that a reliable command has been sent in the sequence window of `seq`.
-/
def acquireReliableWindow (c : Channel) (seq : UInt16) : Channel :=
  let winIdx := windowIndex seq
  let count := c.reliableWindows[winIdx]'(windowIndex_lt seq) + 1
  { c with reliableWindows := c.reliableWindows.set winIdx count (windowIndex_lt seq) }

/--
Releases a reliable command from its window upon receiving an acknowledgment.
-/
def releaseReliableWindow (c : Channel) (seq : UInt16) : Channel :=
  let winIdx := windowIndex seq
  let count := c.reliableWindows[winIdx]'(windowIndex_lt seq)
  if count == 0 then
    c
  else
    { c with reliableWindows := c.reliableWindows.set winIdx (count - 1) (windowIndex_lt seq) }

/--
Checks whether any window slot in the circular range `[startWin, startWin + length)` has in-flight commands.
-/
def isWindowRangeInUse (c : Channel) (startWin : Nat) (length : Nat) : Bool :=
  (List.range length).any fun offset =>
    let idx := (startWin + offset) % Constants.reliableWindows
    c.reliableWindows[idx]'(modWindowIndex_lt (startWin + offset)) > 0

/--
Checks whether an outgoing reliable command with sequence number `seq` can be sent
without colliding with previous unacknowledged windows (window wrap check).
-/
def canSendReliable (c : Channel) (seq : UInt16) : Bool :=
  let winSize  := Constants.reliableWindowSize
  let numWins  := Constants.reliableWindows
  let freeWins := Constants.freeReliableWindows
  let relWin   := (seq.toNat / winSize) % numWins
  if seq.toNat % winSize ≠ 0 then
    true
  else
    let prevWinIdx := (relWin + numWins - 1) % numWins
    let prevCount  := c.reliableWindows[prevWinIdx]'(modWindowIndex_lt (relWin + numWins - 1))
    if prevCount.toNat ≥ winSize then
      false
    else
      !c.isWindowRangeInUse relWin (freeWins + 2)

/--
Recursively drains contiguous staged reliable deliveries starting from
`curSeq + 1`. Each staged delivery occupies `span` sequence numbers: after
delivering it, the frontier continues from its end (ENet peer.c
`dispatch_incoming_reliable_commands`:
`incomingReliableSequenceNumber += fragmentCount - 1`).

Bounded by `fuel` (initial value: `staged.size`) to guarantee structural
termination. Returns delivered entries as `(span, packet)` pairs and the
accumulated total span of the delivered entries.
-/
def drainContiguousLoop (curSeq : UInt16) (staged : Array StagedReliable)
    (delivered : Array (Nat × Packet)) (fuel : Nat) (advance : Nat) :
    UInt16 × Array (Nat × Packet) × Array StagedReliable × Nat :=
  match fuel with
  | 0 => (curSeq, delivered, staged, advance)
  | fuel' + 1 =>
    let targetSeq := curSeq + 1
    match staged.findIdx? (fun (e : StagedReliable) => e.seq == targetSeq) with
    | some idx =>
      if h : idx < staged.size then
        let entry : StagedReliable := staged[idx]
        let remaining := staged.eraseIdx idx h
        drainContiguousLoop (targetSeq + (entry.span - 1).toUInt16) remaining
          (delivered.push (entry.span, entry.packet)) fuel' (advance + entry.span)
      else
        (curSeq, delivered, staged, advance)
    | none =>
      (curSeq, delivered, staged, advance)

/--
Drains contiguous staged reliable deliveries starting from `curSeq + 1`.

Returns the advanced sequence number, the drained `(span, packet)` entries
in order, the remaining staged deliveries, and the total drained span.
-/
def drainContiguous (curSeq : UInt16) (staged : Array StagedReliable) :
    UInt16 × Array (Nat × Packet) × Array StagedReliable × Nat :=
  drainContiguousLoop curSeq staged #[] staged.size 0

/--
Processes an incoming reliable delivery of `span` sequence numbers starting
at `seq` (span 1 for a plain packet, the fragment count for a reassembled
fragmented packet).
- If outside the sliding receive window (ENet peer.c queue_incoming_command:
  discard), drops it. The window test is cyclic - "behind" counts as one full
  cycle "ahead" - which is what keeps plain UInt16 wrap-around delivery safe:
  at `incomingReliableSequenceNumber = 0xFFFF` the legitimately next command
  `0x0000` is still accepted. Without this gate a wrap-naive staleness test
  (`seq <= incoming`) would deadlock the channel after 65536 deliveries, and
  far-future sequence numbers would stage without bound.
- If duplicate of the dispatch frontier (`seq == incomingReliableSequenceNumber`), drops it.
- If in-order (`seq == incomingReliableSequenceNumber + 1`), delivers it,
  advancing the frontier by the whole span (peer.c
  `dispatch_incoming_reliable_commands`), and drains any contiguous staged
  deliveries. Staged deliveries the frontier jumped over are dropped: a
  span covers sequence numbers a hostile sender also used for a plain
  packet, and nothing would ever drain those (ENet keeps them at the head
  of its sorted queue, where they block dispatch until the numbers wrap).
- If ahead within the window, stages it until preceding deliveries arrive.
-/
def receiveReliableSpan (c : Channel) (seq : UInt16) (span : Nat) (packet : Packet) :
    Channel × Array (Nat × Packet) :=
  if !c.isIncomingReliableInWindow seq then
    (c, #[])
  else if seq == c.incomingReliableSequenceNumber then
    (c, #[]) -- duplicate of the dispatch frontier
  else if seq == c.incomingReliableSequenceNumber + 1 then
    let (newSeq, drained, remainingStaged, _) :=
      drainContiguous (seq + (span - 1).toUInt16) c.stagedReliable
    let advanced := { c with
      incomingReliableSequenceNumber   := newSeq
      incomingUnreliableSequenceNumber := 0
    }
    ({ advanced with stagedReliable := remainingStaged.filter (advanced.isReliableAhead ·.seq) },
      #[(span, packet)] ++ drained)
  else
    -- Out-of-order: store in staged list (avoiding duplicate sequence insertions)
    let alreadyStaged := c.stagedReliable.any (fun e => e.seq == seq)
    let newStaged := if alreadyStaged then c.stagedReliable
                     else c.stagedReliable.push { seq, span, packet }
    ({ c with stagedReliable := newStaged }, #[])

/-- Processes an incoming single-sequence reliable packet (span 1). -/
def receiveReliable (c : Channel) (seq : UInt16) (packet : Packet) :
    Channel × Array (Nat × Packet) :=
  receiveReliableSpan c seq 1 packet

/--
Processes an unreliable packet sent after reliable command `reliableSeq`
with unreliable sequence number `seq` (ENet peer.c queue_incoming_command
and dispatch_incoming_unreliable_commands).
- If `reliableSeq` is outside the receive window, drops it: it belongs to a
  reliable command already delivered (the packet is stale) or to one too far
  ahead.
- If `reliableSeq` is the dispatch frontier, delivers it when `seq` is newer
  than `incomingUnreliableSequenceNumber`, and drops it otherwise.
- If `reliableSeq` is ahead within the window, stages it until the frontier
  gets there (`releaseStagedUnreliable`). A full stage or a duplicate drops it.
-/
def receiveUnreliable (c : Channel) (reliableSeq seq : UInt16) (packet : Packet) :
    Channel × Option Packet :=
  if !c.isIncomingReliableInWindow reliableSeq then
    (c, none)
  else if reliableSeq == c.incomingReliableSequenceNumber then
    if seq > c.incomingUnreliableSequenceNumber then
      ({ c with incomingUnreliableSequenceNumber := seq }, some packet)
    else
      (c, none)
  else if c.stagedUnreliable.size ≥ Constants.maximumStagedUnreliable ∨
      c.stagedUnreliable.any (fun e => e.reliableSeq == reliableSeq ∧ e.unreliableSeq == seq) then
    (c, none)
  else
    ({ c with stagedUnreliable := c.stagedUnreliable.push { reliableSeq, unreliableSeq := seq, packet } }, none)

/-- After the dispatch frontier moved: delivers the staged unreliable packets
sent after the new frontier, in unreliable sequence order, and drops the ones
the frontier has passed (ENet dispatch_incoming_unreliable_commands, which
dispatch_incoming_reliable_commands calls). -/
def releaseStagedUnreliable (c : Channel) : Channel × Array Packet :=
  if c.stagedUnreliable.isEmpty then (c, #[])
  else
    let (due, rest) := c.stagedUnreliable.partition (·.reliableSeq == c.incomingReliableSequenceNumber)
    let kept := rest.filter (c.isIncomingReliableInWindow ·.reliableSeq)
    let due := due.qsort (·.unreliableSeq < ·.unreliableSeq)
    due.foldl (init := ({ c with stagedUnreliable := kept }, #[])) fun (c, released) e =>
      if e.unreliableSeq > c.incomingUnreliableSequenceNumber then
        ({ c with incomingUnreliableSequenceNumber := e.unreliableSeq }, released.push e.packet)
      else
        (c, released)

/-- Processes a reliable delivery (`receiveReliableSpan`), then releases the
unreliable packets staged for the new frontier. -/
def receiveReliableAndRelease (c : Channel) (seq : UInt16) (span : Nat) (packet : Packet) :
    Channel × Array Packet :=
  let (c, delivered) := c.receiveReliableSpan seq span packet
  if delivered.isEmpty then (c, #[])
  else
    let (c, released) := c.releaseStagedUnreliable
    (c, delivered.map (·.2) ++ released)

end Channel

end Lenet
