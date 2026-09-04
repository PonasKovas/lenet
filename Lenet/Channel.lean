import Lenet.Constants
import Lenet.Packet

namespace Lenet

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
  /-- Array of in-flight unacknowledged reliable command counts for each of the 16 windows. -/
  reliableWindows                  : Array UInt16 := Array.replicate Constants.reliableWindows 0
  /-- Staged out-of-order reliable packets waiting for gaps in sequence numbers to be filled. -/
  stagedReliable                   : Array (UInt16 × Packet) := #[]
deriving BEq, Inhabited

namespace Channel

/-- Creates an initialized, reset channel. -/
def init : Channel := {}

/-- Computes the window slot index (0..15) for a 16-bit sequence number. -/
@[inline]
def windowIndex (seq : UInt16) : Nat :=
  (seq.toNat / Constants.reliableWindowSize) % Constants.reliableWindows

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
  let count := c.reliableWindows[winIdx]?.getD 0 + 1
  let newWindows :=
    if h : winIdx < c.reliableWindows.size then
      c.reliableWindows.set winIdx count h
    else
      c.reliableWindows
  { c with reliableWindows := newWindows }

/--
Releases a reliable command from its window upon receiving an acknowledgment.
-/
def releaseReliableWindow (c : Channel) (seq : UInt16) : Channel :=
  let winIdx := windowIndex seq
  let count := c.reliableWindows[winIdx]?.getD 0
  if count == 0 then
    c
  else
    let newCount := count - 1
    let newWindows :=
      if h : winIdx < c.reliableWindows.size then
        c.reliableWindows.set winIdx newCount h
      else
        c.reliableWindows
    { c with reliableWindows := newWindows }

/--
Checks whether any window slot in the circular range `[startWin, startWin + length)` has in-flight commands.
-/
def isWindowRangeInUse (c : Channel) (startWin : Nat) (length : Nat) : Bool :=
  (List.range length).any fun offset =>
    let idx := (startWin + offset) % Constants.reliableWindows
    c.reliableWindows[idx]?.getD 0 > 0

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
    let prevCount  := c.reliableWindows[prevWinIdx]?.getD 0
    if prevCount.toNat ≥ winSize then
      false
    else
      !c.isWindowRangeInUse relWin (freeWins + 2)

/--
Recursively drains contiguous staged reliable packets starting from `curSeq + 1`.
Bounded by `fuel` (initial value: `staged.size`) to guarantee structural termination.
-/
def drainContiguousLoop (curSeq : UInt16) (staged : Array (UInt16 × Packet)) (delivered : Array Packet) (fuel : Nat) : UInt16 × Array Packet × Array (UInt16 × Packet) :=
  match fuel with
  | 0 => (curSeq, delivered, staged)
  | fuel' + 1 =>
    let targetSeq := curSeq + 1
    match staged.findIdx? (fun (s, _) => s == targetSeq) with
    | some idx =>
      if h : idx < staged.size then
        let pkt := staged[idx].2
        let remaining := staged.eraseIdx idx h
        drainContiguousLoop targetSeq remaining (delivered.push pkt) fuel'
      else
        (curSeq, delivered, staged)
    | none =>
      (curSeq, delivered, staged)

/--
Drains contiguous staged reliable packets starting from `curSeq + 1`.
Returns the advanced sequence number, the drained packets in order, and the remaining staged packets.
-/
def drainContiguous (curSeq : UInt16) (staged : Array (UInt16 × Packet)) : UInt16 × Array Packet × Array (UInt16 × Packet) :=
  drainContiguousLoop curSeq staged #[] staged.size

/--
Processes an incoming reliable packet with sequence number `seq`.
- If duplicate / already delivered (`seq ≤ incomingReliableSequenceNumber`), drops it.
- If in-order (`seq == incomingReliableSequenceNumber + 1`), delivers it and drains any contiguous staged packets.
- If gap (`seq > incomingReliableSequenceNumber + 1`), stages it until preceding packets arrive.
-/
def receiveReliable (c : Channel) (seq : UInt16) (packet : Packet) : Channel × Array Packet :=
  if seq ≤ c.incomingReliableSequenceNumber then
    (c, #[])
  else if seq == c.incomingReliableSequenceNumber + 1 then
    let (newSeq, drained, remainingStaged) := drainContiguous seq c.stagedReliable
    let updatedChannel := { c with
      incomingReliableSequenceNumber   := newSeq
      incomingUnreliableSequenceNumber := 0
      stagedReliable                   := remainingStaged
    }
    (updatedChannel, #[packet] ++ drained)
  else
    -- Out-of-order: store in staged list (avoiding duplicate sequence insertions)
    let alreadyStaged := c.stagedReliable.any (fun (s, _) => s == seq)
    let newStaged := if alreadyStaged then c.stagedReliable else c.stagedReliable.push (seq, packet)
    ({ c with stagedReliable := newStaged }, #[])

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
