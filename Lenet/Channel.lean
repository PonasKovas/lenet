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
/--
Per-channel sequencing and sliding window state.
Each peer connection in ENet maintains an array of independent channels.
-/
structure Channel where
  /-- Next sequence number to assign to an outgoing reliable command on this channel. -/
  outgoingReliableSequenceNumber   : UInt16 := 0
  /-- Next sequence number to assign to an outgoing unreliable command. Reset to 0 whenever a reliable command is sent. -/
  outgoingUnreliableSequenceNumber : UInt16 := 0
  /-- Highest contiguous reliable sequence number received and dispatched to the application. -/
  incomingReliableSequenceNumber   : UInt16 := 0
  /-- Highest unreliable sequence number received in the current reliable window. -/
  incomingUnreliableSequenceNumber : UInt16 := 0
  /-- In-flight unacknowledged reliable command counts for each of the
  `Constants.reliableWindows` windows. Fixed-size by construction. -/
  reliableWindows                  : Vector UInt16 Constants.reliableWindows := Vector.replicate Constants.reliableWindows 0
  /-- Staged out-of-order reliable deliveries waiting for gaps in sequence
  numbers to be filled. -/
  stagedReliable                   : Array StagedReliable := #[]
deriving BEq, Inhabited

namespace Channel

/-- Creates an initialized, reset channel. -/
def init : Channel := {}

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
    deliveries.
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
      let updatedChannel := { c with
        incomingReliableSequenceNumber   := newSeq
        incomingUnreliableSequenceNumber := 0
        stagedReliable                   := remainingStaged
      }
      (updatedChannel, #[(span, packet)] ++ drained)
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
Processes an incoming unreliable packet on this channel.
- If newer than `incomingUnreliableSequenceNumber`, advances sequence number and accepts.
- If older / out-of-order, discards as stale.
-/
def receiveUnreliable (c : Channel) (seq : UInt16) (packet : Packet) : Channel × Option Packet :=
  if seq > c.incomingUnreliableSequenceNumber then
    ({ c with incomingUnreliableSequenceNumber := seq }, some packet)
  else
    (c, none)

end Channel

end Lenet
