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
Computes the CRC32 checksum as ENet expects: over the bytes before the
checksum field, the 4-byte field temporarily holding `connectId`, and the
bytes after it.

ENet substitutes the field with a plain `memcpy` of the native
`peer->connectID` and the wire field is `enet_crc32`'s `ENET_HOST_TO_NET_32
(~crc)` result, so the transmitted field is the raw `~crc` big-endian.
Because `connectID` is the one command field ENet passes through the body
*without* byte-order conversion (host.c enet_host_connect, protocol.c
handle_connect), the substitution byte pattern equals the big-endian
serialization of the connectID as parsed from the wire — hence `BE` here.
-/
def computeChecksum (pre : ByteArray) (post : ByteArray) (connectId : UInt32 := 0) : UInt32 :=
  let placeholder := WriterM.run (writeUInt32BE connectId) 4
  Checksum.crc32Buffers #[pre, placeholder, post]

/-- Sequentially decodes commands until the first malformed one (ENet's
receive loop `break`s there; everything before it was already applied).
Every valid command consumes at least 4 wire bytes, so `fuel = payload
size` always suffices. -/
def parseCommands (bytes : ByteArray) : Array Command :=
  go bytes.size bytes #[]
where
  go : Nat → ByteArray → Array Command → Array Command
    | 0, _, acc => acc
    | fuel' + 1, rest, acc =>
      if rest.size == 0 then
        acc
      else
        match ReaderM.run Command.decode rest with
        | .ok cmd => go fuel' (rest.extract (cmd.wireSize) rest.size) (acc.push cmd)
        | .error _ => acc

/--
Decodes a datagram from a reader, optionally decompressing the commands payload
if `header.compressed` is set and a `Compressor` is provided.

`connectIdOf` resolves the checksum key for a datagram's header peer ID when
the host has checksums enabled (ENet: the receiving host substitutes the
peer's `connectID`, or 0 for the broadcast peer `0xFFF`, before verifying).
Passing `none` consumes the checksum field without verifying it.
-/
def decodeWith (hasChecksum : Bool := false) (connectIdOf : Option (UInt16 → UInt32) := none)
    (compressor : Option Compressor := none) : ReaderM Datagram := do
  let header ← Header.decode
  let fieldStart := (← get).offset
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

  -- Verify the checksum (ENet enet_protocol_receive): the CRC32 is computed
  -- over header + checksum field (substituted with the peer's connectID) +
  -- the *decompressed* commands payload, and compared against the field as
  -- transmitted. Failures drop the datagram before any command is parsed.
  let verify : ReaderM Unit :=
    match connectIdOf, checksum with
    | some cidOf, some stored => do
      let raw := (← get).bytes
      let pre := raw.extract 0 fieldStart
      let expected := computeChecksum pre commandBytes (cidOf header.peerId)
      if expected != stored then
        throw (CodecError.custom s!"Checksum mismatch: expected {expected}, got {stored}")
    | _, _ => pure ()
  if hasChecksum then
    verify
  else
    pure ()

  -- Parse commands from the (decompressed) payload, sequentially, ENet-style
  -- (protocol.c receive loop): apply the prefix of well-formed commands and
  -- stop at the first malformed one (unknown command number, truncated body).
  -- ENet does not discard earlier commands when a later one is malformed, and
  -- accepts a payload with zero commands (the loop simply never runs).
  let commands := parseCommands commandBytes

  return { header, checksum, commands }

/-- Decodes an uncompressed datagram from a `ReaderM` stream. -/
def decode (hasChecksum : Bool := false) : ReaderM Datagram :=
  decodeWith hasChecksum none none

/--
Serializes a datagram into a `ByteArray`, optionally compressing the commands payload
if a `Compressor` is provided and results in a smaller byte size.

When the datagram carries a checksum, `connectId` is the checksum key (ENet:
`peer->connectID`, or 0 while the peer's outgoing ID is still unset). ENet
computes the CRC32 over header + checksum field (holding `connectID` in host
byte order, i.e. little-endian on the hosts we interop with) + the
*uncompressed* commands payload, then stores the CRC32 big-endian in the field
(`enet_crc32` returns `ENET_HOST_TO_NET_32 (~crc)`).
-/
def encodeWith (compressor : Option Compressor := none) (connectId : UInt32 := 0) : Datagram → ByteArray
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
    match checksum with
    | none =>
      WriterM.run do
        finalHeader.encode
        writeBytes payloadBytes
    | some _ =>
      let crc := computeChecksum (WriterM.run finalHeader.encode) rawCommandBytes connectId
      WriterM.run do
        finalHeader.encode
        writeUInt32BE crc
        writeBytes payloadBytes

/-- Serializes a datagram into a `WriterM` stream without payload compression. -/
def encode (d : Datagram) : WriterM Unit := do
  d.header.encode
  if let some cs := d.checksum then
    writeUInt32BE cs
  for cmd in d.commands do
    cmd.encode

end Datagram

instance : Decode Datagram where decode := Datagram.decode false
instance : Encode Datagram where encode := Datagram.encode

end Lenet.Protocol
