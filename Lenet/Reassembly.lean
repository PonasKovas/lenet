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
State machine for assembling a fragmented packet from incoming fragment commands.
-/
structure FragmentAssembler where
  origin              : FragmentOrigin := {}
  startSequenceNumber : UInt16
  totalLength         : Nat
  fragmentCount       : Nat
  fragmentsRemaining  : Nat
  received            : Array Bool
  buffer              : ByteArray
deriving BEq, Inhabited

namespace FragmentAssembler

/-- Safely copies `src` bytes into `dst` starting at `dstOffset`: in place
(`ByteArray.copySlice`) when `dst` is not shared. -/
def copyBytes (dst : ByteArray) (dstOffset : Nat) (src : ByteArray) : ByteArray :=
  if dstOffset + src.size > dst.size then
    dst
  else
    src.copySlice 0 dst dstOffset src.size

/-- `n` zero bytes. Built by pushing into a buffer of that capacity:
`ByteArray.mk (Array.replicate n 0)` would first build an array of `n`
boxed bytes, eight times the size. -/
def zeros (n : Nat) : ByteArray :=
  go n (ByteArray.emptyWithCapacity n)
where
  go : Nat → ByteArray → ByteArray
    | 0, b => b
    | k + 1, b => go k (b.push 0)

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

  let received := Array.replicate fragmentCount false
  let buffer := zeros totalLength
  return {
    startSequenceNumber
    totalLength
    fragmentCount
    fragmentsRemaining := fragmentCount
    received
    buffer
  }

/-- Whether `addFragment` takes fragment `fragmentNumber` of `data` at
`offset`: its number and bytes fit the set. -/
def fits (a : FragmentAssembler) (fragmentNumber : Nat) (offset : Nat) (data : ByteArray) : Bool :=
  fragmentNumber < a.fragmentCount && offset < a.totalLength && offset + data.size ≤ a.totalLength

/--
Adds an incoming fragment to the assembler.
- If the fragment is already received, returns the unchanged assembler (idempotent).
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

  -- If this fragment was already received, ignore duplicate chunk:
  match a.received[fragmentNumber]? with
  | none =>
    -- Unreachable: `fragmentNumber < a.fragmentCount` was checked above and
    -- `received` is allocated with `fragmentCount` slots in `init`.
    throw (CodecError.custom s!"received-bitset out of sync with fragment count {a.fragmentCount}")
  | some true =>
    return (a, none)
  | some false =>
    -- the fields leave `a` first, so its arrays are held once and update in
    -- place (reading them while `a` still holds them would copy them)
    let { origin, startSequenceNumber, totalLength, fragmentCount, fragmentsRemaining, received, buffer } := a
    let remaining := fragmentsRemaining - 1
    let updated : FragmentAssembler := {
      origin, startSequenceNumber, totalLength, fragmentCount
      received           := received.setIfInBounds fragmentNumber true
      buffer             := copyBytes buffer offset data
      fragmentsRemaining := remaining
    }

    if remaining == 0 then
      return (updated, some updated.buffer)
    else
      return (updated, none)

end FragmentAssembler

end Lenet
