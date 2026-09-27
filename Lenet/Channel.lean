import Std.Data.HashMap
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
  numbers to be filled, by the sequence number each starts at (its `seq`). -/
  stagedReliable                   : Std.HashMap UInt16 StagedReliable := {}
  /-- Unreliable deliveries sent after a reliable command that has not been
  delivered yet: by that command's sequence number, then by their own
  unreliable sequence number. -/
  stagedUnreliable                 : Std.HashMap UInt16 (Std.HashMap UInt16 Packet) := {}
  /-- How many unreliable deliveries are staged: at most
  `maximumStagedUnreliable`. -/
  stagedUnreliableCount            : Nat := 0
  /-- The bytes of the reliable packets staged. -/
  reliableBytes                    : Nat := 0
  /-- The bytes of the unreliable packets staged. -/
  unreliableBytes                  : Nat := 0
deriving BEq, Inhabited

namespace Channel

/-- The bytes of the packets the channel holds back, reliable and
unreliable. -/
def stagedBytes (c : Channel) : Nat := c.reliableBytes + c.unreliableBytes

/-- Whether `key` is one of the `count` sequence numbers after `after`
(at most one wrap's worth). -/
def isAfter (after : UInt16) (count : Nat) (key : UInt16) : Bool :=
  let offset := (key - after).toNat
  1 ≤ offset && offset ≤ count

/-- Two weights added up at once. -/
def addWeight (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- `eraseAfter`, one key at a time, adding up what the erased values
weigh. -/
def eraseAfterLoop (m : Std.HashMap UInt16 β) (after : UInt16) (w : β → Nat × Nat) (weight : Nat × Nat) :
    (count : Nat) → Std.HashMap UInt16 β × (Nat × Nat)
  | 0 => (m, weight)
  | n + 1 =>
    let key := after + (n + 1).toUInt16
    let weight := match m[key]? with
      | some v => addWeight weight (w v)
      | none => weight
    eraseAfterLoop (m.erase key) after w weight n

/-- `m` without the keys among the `count` sequence numbers after `after`,
and what the erased values weigh by `w` (two weights, such as a count and
bytes). Costs the fewer of `count` and `m.size` steps: a map smaller than
the range is filtered instead. -/
def eraseAfter (m : Std.HashMap UInt16 β) (after : UInt16) (count : Nat) (w : β → Nat × Nat) :
    Std.HashMap UInt16 β × (Nat × Nat) :=
  let count := min count 65535
  if m.isEmpty then (m, (0, 0))
  else if m.size ≤ count then
    let weight := m.fold (fun n k v => if isAfter after count k then addWeight n (w v) else n) (0, 0)
    (m.filter fun k _ => !isAfter after count k, weight)
  else eraseAfterLoop m after w (0, 0) count

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
receive window, which the receive path drops. An ENet sender may be that
far ahead: it keeps up to seven windows in flight ending at the last one
sent, and the oldest of them may be the first after the frontier, in the
window after the frontier's. So such a command is not acknowledged, or the
sender would retire a packet the receiver dropped. ENet acknowledges it and
loses the packet. (A Lenet sender keeps six windows, `canSendReliable`.) -/
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
The first command of a window waits until the window six back is empty, so
what is in flight spans at most six windows. ENet waits only for the one
seven back, but then a command may reach a receiver one window past its
receive window, which ENet acknowledges and drops (`isReliableTooFarAhead`).
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
      !c.isWindowRangeInUse relWin (freeWins + 3)

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
def drainContiguousLoop (curSeq : UInt16) (staged : Std.HashMap UInt16 StagedReliable)
    (delivered : Array (Nat × Packet)) (fuel : Nat) (advance : Nat) :
    UInt16 × Array (Nat × Packet) × Std.HashMap UInt16 StagedReliable × Nat :=
  match fuel with
  | 0 => (curSeq, delivered, staged, advance)
  | fuel' + 1 =>
    let targetSeq := curSeq + 1
    match staged[targetSeq]? with
    | some entry =>
      drainContiguousLoop (targetSeq + (entry.span - 1).toUInt16) (staged.erase targetSeq)
        (delivered.push (entry.span, entry.packet)) fuel' (advance + entry.span)
    | none =>
      (curSeq, delivered, staged, advance)

/--
Drains contiguous staged reliable deliveries starting from `curSeq + 1`.

Returns the advanced sequence number, the drained `(span, packet)` entries
in order, the remaining staged deliveries, and the total drained span.
-/
def drainContiguous (curSeq : UInt16) (staged : Std.HashMap UInt16 StagedReliable) :
    UInt16 × Array (Nat × Packet) × Std.HashMap UInt16 StagedReliable × Nat :=
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

A span of 0 counts as 1 (fragment sets have at least one fragment). Each
step costs what it delivers, stages or drops, not what is staged: the
staged deliveries are found by sequence number.
-/
def receiveReliableSpan (c : Channel) (seq : UInt16) (span : Nat) (packet : Packet) :
    Channel × Array (Nat × Packet) :=
  let span := max span 1
  if !c.isIncomingReliableInWindow seq then
    (c, #[])
  else if seq == c.incomingReliableSequenceNumber then
    (c, #[]) -- duplicate of the dispatch frontier
  else if seq == c.incomingReliableSequenceNumber + 1 then
    let old := c.incomingReliableSequenceNumber
    -- the map leaves `c` first, so it is held once and changes in place
    let staged := c.stagedReliable
    let c := { c with stagedReliable := {} }
    let (newSeq, drained, staged, advance) := drainContiguous (seq + (span - 1).toUInt16) staged
    -- what the frontier jumped over: the sequence numbers it moved past
    let (staged, (_, jumped)) := eraseAfter staged old (span + advance) fun e => (1, e.packet.data.size)
    let drainedBytes := drained.foldl (fun n d => n + d.2.data.size) 0
    ({ c with
        incomingReliableSequenceNumber   := newSeq
        incomingUnreliableSequenceNumber := 0
        stagedReliable                   := staged
        reliableBytes                    := c.reliableBytes - drainedBytes - jumped },
      #[(span, packet)] ++ drained)
  else if c.stagedReliable.contains seq then
    (c, #[]) -- staged already
  else
    let staged := c.stagedReliable
    let c := { c with stagedReliable := {} }
    ({ c with
        stagedReliable := staged.insert seq { seq, span, packet }
        reliableBytes  := c.reliableBytes + packet.data.size }, #[])

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
  else if c.stagedUnreliableCount ≥ Constants.maximumStagedUnreliable ∨
      (c.stagedUnreliable[reliableSeq]?).any (·.contains seq) then
    (c, none)
  else
    let staged := c.stagedUnreliable
    let c := { c with stagedUnreliable := {} }
    ({ c with
        stagedUnreliable      := staged.alter reliableSeq fun b => some ((b.getD {}).insert seq packet)
        stagedUnreliableCount := c.stagedUnreliableCount + 1
        unreliableBytes       := c.unreliableBytes + packet.data.size }, none)

/-- After the dispatch frontier moved `advance` sequence numbers past `old`:
delivers the staged unreliable packets sent after the new frontier, in
unreliable sequence order, and drops the ones the frontier has passed
(ENet dispatch_incoming_unreliable_commands, which
dispatch_incoming_reliable_commands calls). -/
def releaseStagedUnreliable (c : Channel) (old : UInt16) (advance : Nat) : Channel × Array Packet :=
  if c.stagedUnreliable.isEmpty then (c, #[])
  else
    let staged := c.stagedUnreliable
    let c := { c with stagedUnreliable := {} }
    let due := (staged[c.incomingReliableSequenceNumber]?).getD {}
    -- the frontier passed or reached the reliable commands of these
    let (staged, (count, bytes)) :=
      eraseAfter staged old advance fun b => (b.size, b.fold (fun n _ p => n + p.data.size) 0)
    let due := due.toArray.qsort (·.1 < ·.1)
    due.foldl (init := ({ c with
        stagedUnreliable      := staged
        stagedUnreliableCount := c.stagedUnreliableCount - count
        unreliableBytes       := c.unreliableBytes - bytes }, #[])) fun (c, released) (unreliableSeq, packet) =>
      if unreliableSeq > c.incomingUnreliableSequenceNumber then
        ({ c with incomingUnreliableSequenceNumber := unreliableSeq }, released.push packet)
      else
        (c, released)

/-- Processes a reliable delivery (`receiveReliableSpan`), then releases the
unreliable packets staged for the new frontier. -/
def receiveReliableAndRelease (c : Channel) (seq : UInt16) (span : Nat) (packet : Packet) :
    Channel × Array Packet :=
  let old := c.incomingReliableSequenceNumber
  let (c, delivered) := c.receiveReliableSpan seq span packet
  if delivered.isEmpty then (c, #[])
  else
    let advance := delivered.foldl (fun n d => n + d.1) 0
    let (c, released) := c.releaseStagedUnreliable old advance
    (c, delivered.map (·.2) ++ released)

end Channel

end Lenet
