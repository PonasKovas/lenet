import Lenet.Constants
import Lenet.Codec
import Lenet.Checksum
import Lenet.Protocol.Header
import Lenet.Protocol.Command

namespace Lenet.Protocol

open Lenet
open Lenet.ReaderM
open Lenet.WriterM

/--
A decoded ENet protocol datagram.
The wire format consists of:
1. `Header` (2 or 4 bytes, uncompressed)
2. `checksum` (optional 4 bytes, uncompressed)
3. Commands payload (raw command bytes OR compressed bytes if `header.compressed = true`)
-/
structure Datagram where
  header   : Header
  checksum : Option UInt32 := none
  commands : Array Command := #[]
deriving BEq, Inhabited

namespace Datagram

/--
Decodes a datagram from a reader, optionally decompressing the commands payload
if `header.compressed` is set and a `Compressor` is provided.
-/
def decodeWith (hasChecksum : Bool := false) (compressor : Option Compressor := none) : ReaderM Datagram := do
  let header ← Header.decode
  let checksum ← if hasChecksum then
    let cs ← readUInt32BE
    pure (some cs)
  else
    pure none

  let payloadBytes ← readBytes (← remaining)

  let commandBytes ← if header.compressed then
    match compressor with
    | some comp =>
      match comp.decompress payloadBytes with
      | .ok decompressed => pure decompressed
      | .error err       => throw err
    | none =>
      throw (CodecError.custom "Received compressed datagram but no compressor configured")
  else
    pure payloadBytes

  -- Parse commands from the (decompressed) payload:
  let commands ← match ReaderM.run (do
    let mut cmds : Array Command := #[]
    while (← hasRemaining) do
      let cmd ← Command.decode
      cmds := cmds.push cmd
    if cmds.isEmpty then
      throw (CodecError.custom "Datagram must contain at least one command")
    pure cmds
  ) commandBytes with
  | .ok cmds => pure cmds
  | .error err => throw err

  return { header, checksum, commands }

/-- Decodes an uncompressed datagram from a `ReaderM` stream. -/
def decode (hasChecksum : Bool := false) : ReaderM Datagram :=
  decodeWith hasChecksum none

/--
Serializes a datagram into a `ByteArray`, optionally compressing the commands payload
if a `Compressor` is provided and results in a smaller byte size.
-/
def encodeWith (compressor : Option Compressor := none) : Datagram → ByteArray
  | { header, checksum, commands } =>
    let rawCommandBytes := WriterM.run (for cmd in commands do cmd.encode)
    let (isCompressed, payloadBytes) := match compressor with
      | some comp =>
        let compressed := comp.compress rawCommandBytes
        if compressed.size > 0 ∧ compressed.size < rawCommandBytes.size then
          (true, compressed)
        else
          (false, rawCommandBytes)
      | none =>
        (false, rawCommandBytes)

    let finalHeader := { header with compressed := isCompressed }
    WriterM.run do
      finalHeader.encode
      if let some cs := checksum then
        writeUInt32BE cs
      writeBytes payloadBytes

/-- Serializes a datagram into a `WriterM` stream without payload compression. -/
def encode (d : Datagram) : WriterM Unit := do
  d.header.encode
  if let some cs := d.checksum then
    writeUInt32BE cs
  for cmd in d.commands do
    cmd.encode

/--
Computes the CRC32 checksum for a datagram byte buffer as expected by ENet.
`checksumOffset` is the offset in `rawBytes` where the 4-byte checksum field is located.
Temporarily substitutes the checksum field with `connectId` during calculation.
-/
def computeChecksum (rawBytes : ByteArray) (checksumOffset : Nat) (connectId : UInt32 := 0) : UInt32 :=
  if checksumOffset + 4 > rawBytes.size then
    0
  else
    let pre := rawBytes.extract 0 checksumOffset
    let placeholder := WriterM.run (writeUInt32BE connectId) 4
    let suffix := rawBytes.extract (checksumOffset + 4) rawBytes.size
    Checksum.crc32Buffers #[pre, placeholder, suffix]

/--
Verifies that the CRC32 checksum of a received datagram matches the expected checksum.
-/
def verifyChecksum (rawBytes : ByteArray) (checksumOffset : Nat) (expectedChecksum : UInt32) (connectId : UInt32 := 0) : Bool :=
  computeChecksum rawBytes checksumOffset connectId == expectedChecksum

end Datagram

instance : Decode Datagram where decode := Datagram.decode false
instance : Encode Datagram where encode := Datagram.encode

end Lenet.Protocol
