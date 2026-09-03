import Lenet.Constants
import Lenet.Codec

namespace Lenet

/--
State machine for assembling a fragmented packet from incoming fragment commands.
-/
structure FragmentAssembler where
  startSequenceNumber : UInt16
  totalLength         : Nat
  fragmentCount       : Nat
  fragmentsRemaining  : Nat
  received            : Array Bool
  buffer              : ByteArray
deriving BEq, Inhabited

namespace FragmentAssembler

/-- Safely copies `src` bytes into `dst` starting at `dstOffset`. -/
def copyBytes (dst : ByteArray) (dstOffset : Nat) (src : ByteArray) : ByteArray :=
  if dstOffset + src.size > dst.size then
    dst
  else
    let pre := dst.extract 0 dstOffset
    let suffix := dst.extract (dstOffset + src.size) dst.size
    pre ++ src ++ suffix

/--
Initializes a new `FragmentAssembler` for a fragmented packet.
Performs strict validation on fragment parameters to prevent memory overruns.
-/
def init (startSequenceNumber : UInt16) (totalLength : Nat) (fragmentCount : Nat) (maxPacketSize : Nat := Constants.maximumMtu * 1024) : Except CodecError FragmentAssembler := do
  if fragmentCount == 0 then
    throw (CodecError.custom "Fragment count must be greater than 0")
  if fragmentCount > Constants.maximumFragmentCount then
    throw (CodecError.custom s!"Fragment count {fragmentCount} exceeds maximum allowed")
  if totalLength > maxPacketSize then
    throw (CodecError.custom s!"Total length {totalLength} exceeds maximum packet size")
  if totalLength < fragmentCount then
    throw (CodecError.custom "Total length cannot be less than fragment count")

  let received := Array.replicate fragmentCount false
  let buffer := ByteArray.mk (Array.replicate totalLength 0)
  return {
    startSequenceNumber
    totalLength
    fragmentCount
    fragmentsRemaining := fragmentCount
    received
    buffer
  }

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
  if a.received[fragmentNumber]?.getD false then
    return (a, none)

  let newReceived :=
    if h : fragmentNumber < a.received.size then
      a.received.set fragmentNumber true h
    else
      a.received

  let newBuffer := copyBytes a.buffer offset data
  let remaining := a.fragmentsRemaining - 1

  let updated := { a with
    received           := newReceived
    buffer             := newBuffer
    fragmentsRemaining := remaining
  }

  if remaining == 0 then
    return (updated, some updated.buffer)
  else
    return (updated, none)

end FragmentAssembler

end Lenet
