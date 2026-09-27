import Lenet.Constants
import Lenet.Codec

namespace Lenet

/-- Where a fragment set was sent: with its start sequence number this
identifies the set. Reliable sets are numbered in their channel's reliable
sequence; unreliable sets in the unreliable sequence after one reliable
command, so two sets can share a start number and still differ. -/
structure FragmentOrigin where
  channelId   : UInt8 := 0
  unreliable  : Bool := false
  /-- For an unreliable set, the reliable command it was sent after; 0 for a
  reliable set. -/
  reliableSeq : UInt16 := 0
deriving DecidableEq, Inhabited
/--
State machine for assembling a fragmented packet from incoming fragment
commands. It holds only what arrived: the packet is built once the last
fragment is in (`assemble`), so a set that claims a large total but sends
little costs little. ENet allocates the whole packet when a set starts.
-/
structure FragmentAssembler where
  origin              : FragmentOrigin := {}
  startSequenceNumber : UInt16
  totalLength         : Nat
  fragmentCount       : Nat
  fragmentsRemaining  : Nat
  /-- One byte per fragment of the set, nonzero once it arrived: a byte, not
  a `Bool`, so the bitset a set claims costs one byte per fragment, not a
  boxed word. -/
  received            : ByteArray
  /-- Data bytes received so far. -/
  receivedBytes       : Nat
  /-- The fragments received so far, as `(offset, data)`, in arrival order. -/
  fragments           : Array (Nat × ByteArray)
deriving BEq, Inhabited

namespace FragmentAssembler

/-- Safely copies `src` bytes into `dst` starting at `dstOffset`: in place
(`ByteArray.copySlice`) when `dst` is not shared. -/
def copyBytes (dst : ByteArray) (dstOffset : Nat) (src : ByteArray) : ByteArray :=
  if dstOffset + src.size > dst.size then
    dst
  else
    src.copySlice 0 dst dstOffset src.size

/-- `n` zero bytes, built by doubling (a handful of memcpy-speed appends):
`ByteArray.mk (Array.replicate n 0)` would first build an array of `n`
boxed bytes, eight times the size, and pushing byte by byte is slow. -/
def zeros (n : Nat) : ByteArray :=
  grow n (ByteArray.empty.push 0)
where
  /-- Doubles the zero bytes `b` until they are at least `n`, then cuts. -/
  grow (n : Nat) (b : ByteArray) : ByteArray :=
    if _h : 0 < b.size ∧ b.size < n then grow n (b ++ b) else b.extract 0 n
  termination_by n - b.size
  decreasing_by simp only [ByteArray.size_append]; omega

/--
Initializes a new `FragmentAssembler` for a fragmented packet.
Performs strict validation on fragment parameters to prevent memory overruns.
-/
def init (startSequenceNumber : UInt16) (totalLength : Nat) (fragmentCount : Nat) (maxPacketSize : Nat := Constants.maximumPacketSize) : Except CodecError FragmentAssembler := do
  if fragmentCount == 0 then
    throw (CodecError.custom "Fragment count must be greater than 0")
  if fragmentCount > Constants.maximumFragmentCount then
    throw (CodecError.custom s!"Fragment count {fragmentCount} exceeds maximum allowed")
  if totalLength > maxPacketSize then
    throw (CodecError.custom s!"Total length {totalLength} exceeds maximum packet size")
  if totalLength < fragmentCount then
    throw (CodecError.custom "Total length cannot be less than fragment count")

  return {
    startSequenceNumber
    totalLength
    fragmentCount
    fragmentsRemaining := fragmentCount
    received           := zeros fragmentCount
    receivedBytes      := 0
    fragments          := #[]
  }

/-- Whether `addFragment` takes fragment `fragmentNumber` of `data` at
`offset`: its number and bytes fit the set. -/
def fits (a : FragmentAssembler) (fragmentNumber : Nat) (offset : Nat) (data : ByteArray) : Bool :=
  fragmentNumber < a.fragmentCount && offset < a.totalLength && offset + data.size ≤ a.totalLength

/-- Whether fragment `fragmentNumber` already arrived. -/
def hasFragment (a : FragmentAssembler) (fragmentNumber : Nat) : Bool :=
  if h : fragmentNumber < a.received.size then a.received[fragmentNumber] != 0 else false

/-- Whether a new fragment of `size` bytes leaves the set able to complete:
it fits in what is still missing, and the last missing fragment brings
exactly the rest. So a set completes only once its fragments carried
`totalLength` bytes. ENet completes a set on its fragment count alone, so
one fragment of one byte can claim a whole packet; no honest sender does
that, since its fragments tile the packet. -/
def bytesFit (a : FragmentAssembler) (size : Nat) : Bool :=
  a.receivedBytes + size ≤ a.totalLength &&
    (a.fragmentsRemaining != 1 || a.receivedBytes + size == a.totalLength)

/-- Whether `addFragment` takes fragment `fragmentNumber` of `data` at
`offset`: it `fits` the set, and it is a duplicate (taken and ignored, so
its lost ACK is sent again) or its bytes fit what is missing. -/
def takes (a : FragmentAssembler) (fragmentNumber : Nat) (offset : Nat) (data : ByteArray) : Bool :=
  a.fits fragmentNumber offset data && (a.hasFragment fragmentNumber || a.bytesFit data.size)

/-- One fragment of `appendInOrder`: appended if it starts where the bytes
so far end. -/
def appendStep (acc : Option ByteArray) (fragment : Nat × ByteArray) : Option ByteArray :=
  match acc with
  | some buf => if fragment.1 == buf.size then some (buf ++ fragment.2) else none
  | none => none

/-- The fragments appended in arrival order, when each starts where the
ones before it ended (they arrived in order, as they usually do). -/
def appendInOrder (fragments : Array (Nat × ByteArray)) (capacity : Nat) : Option ByteArray :=
  fragments.foldl appendStep (some (ByteArray.emptyWithCapacity capacity))

/-- The packet: every fragment copied to its offset. A packet built from
fragments that tile it holds exactly their bytes. Fragments that arrived in
order are appended in one pass; otherwise they are copied into zeros. -/
def assemble (a : FragmentAssembler) : ByteArray :=
  match appendInOrder a.fragments a.totalLength with
  | some buf => if buf.size == a.totalLength then buf else placed
  | none => placed
where
  placed := a.fragments.foldl (fun buf (offset, data) => copyBytes buf offset data) (zeros a.totalLength)

/--
Adds an incoming fragment to the assembler.
- If the fragment is already received, returns the unchanged assembler (idempotent).
- If the fragment's bytes cannot fit the set (`bytesFit`), refuses it.
- If the fragment completes the packet, returns `(updatedAssembler, some assembledData)`.
- If more fragments are still needed, returns `(updatedAssembler, none)`.
-/
def addFragment (a : FragmentAssembler) (fragmentNumber : Nat) (offset : Nat) (data : ByteArray) : Except CodecError (FragmentAssembler × Option ByteArray) := do
  if fragmentNumber ≥ a.fragmentCount then
    throw (CodecError.custom s!"Fragment number {fragmentNumber} out of range [0, {a.fragmentCount})")
  if offset ≥ a.totalLength then
    throw (CodecError.custom s!"Fragment offset {offset} exceeds total length {a.totalLength}")
  if offset + data.size > a.totalLength then
    throw (CodecError.custom "Fragment data extends beyond total packet length")

  if h : fragmentNumber < a.received.size then
    -- If this fragment was already received, ignore duplicate chunk:
    if a.received[fragmentNumber] != 0 then
      return (a, none)
    else if !a.bytesFit data.size then
      throw (CodecError.custom "Fragment bytes do not fit what the set is missing")
    else
      -- the fields leave `a` first, so its arrays are held once and update in
      -- place (reading them while `a` still holds them would copy them)
      match a, h with
      | { origin, startSequenceNumber, totalLength, fragmentCount, fragmentsRemaining, received,
          receivedBytes, fragments }, h =>
      let remaining := fragmentsRemaining - 1
      let updated : FragmentAssembler := {
        origin, startSequenceNumber, totalLength, fragmentCount
        received           := received.set fragmentNumber 1 h
        receivedBytes      := receivedBytes + data.size
        fragments          := fragments.push (offset, data)
        fragmentsRemaining := remaining
      }
      if remaining == 0 then
        return (updated, some updated.assemble)
      else
        return (updated, none)
  else
    -- Unreachable: `fragmentNumber < a.fragmentCount` was checked above and
    -- `received` is allocated with `fragmentCount` slots in `init`.
    throw (CodecError.custom s!"received-bitset out of sync with fragment count {a.fragmentCount}")

end FragmentAssembler

end Lenet
