import Lenet.Constants
import Lenet.Codec
import Lenet.Checksum
import Lenet.Protocol.Header
import Lenet.Protocol.Command

namespace Lenet.Protocol

open ReaderM WriterM

/--
A decoded ENet protocol datagram. Wire layout:
1. `Header` (2 or 4 bytes)
2. `checksum` (4 bytes, only when the hosts have checksums enabled)
3. the commands, back to back

ENet's optional payload compression is not supported: compressed
datagrams are rejected on decode and never produced. It is opt-in in ENet,
and a decoder would have to copy ENet's range coder model exactly.
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
Each command is read where the one before it ended, in place: the bytes
are never copied. Every valid command consumes at least 4 wire bytes, so
`fuel = payload size` always suffices. -/
def parseCommands (bytes : ByteArray) : Array Command :=
  go bytes.size 0 #[]
where
  go : Nat → Nat → Array Command → Array Command
    | 0, _, acc => acc
    | fuel' + 1, offset, acc =>
      if bytes.size ≤ offset then
        acc
      else
        match EStateM.run Command.decode { bytes, offset } with
        | .ok cmd _ => go fuel' (offset + cmd.wireSize) (acc.push cmd)
        | .error _ _ => acc

/--
Decodes a datagram. `hasChecksum` says whether the 4-byte checksum field is
present (the host's checksum setting).

`connectIdOf` resolves the checksum key for a datagram's header peer ID
(ENet: the receiving host substitutes the peer's `connectID`, or 0 for the
broadcast peer `0xFFF`, before verifying). Passing `none` consumes the
checksum field without verifying it.
-/
def decode (hasChecksum : Bool := false) (connectIdOf : Option (UInt16 → UInt32) := none) :
    ReaderM Datagram := do
  let header ← Header.decode
  let fieldStart := (← get).offset
  let checksum ← if hasChecksum then
    let cs ← readUInt32BE
    pure (some cs)
  else
    pure none

  let commandBytes ← readBytes (← remaining)

  if header.compressed then
    throw (CodecError.custom "compressed datagrams are not supported")

  -- Verify the checksum (ENet enet_protocol_receive): the CRC32 is computed
  -- over header + checksum field (substituted with the peer's connectID) +
  -- the commands, and compared against the field as transmitted. Failures
  -- drop the datagram before any command is parsed.
  match connectIdOf, checksum with
  | some cidOf, some stored =>
    let pre := (← get).bytes.extract 0 fieldStart
    let expected := computeChecksum pre commandBytes (cidOf header.peerId)
    if expected != stored then
      throw (CodecError.custom s!"Checksum mismatch: expected {expected}, got {stored}")
  | _, _ => pure ()

  -- ENet applies the prefix of well-formed commands and stops at the first
  -- malformed one (unknown command number, truncated body); a payload with
  -- zero commands is legal.
  return { header, checksum, commands := parseCommands commandBytes }

/--
Serializes a datagram. When it carries a checksum, the stored checksum value
is ignored and recomputed with `connectId` as the key (ENet:
`peer->connectID`, or 0 while the peer's outgoing ID is still unset); see
`computeChecksum`.
-/
def encode (connectId : UInt32 := 0) : Datagram → ByteArray
  | { header, checksum, commands } =>
    let commandBytes := WriterM.run (for cmd in commands do cmd.encode)
    let header := { header with compressed := false }
    match checksum with
    | none =>
      WriterM.run do
        header.encode
        writeBytes commandBytes
    | some _ =>
      let crc := computeChecksum (WriterM.run header.encode) commandBytes connectId
      WriterM.run do
        header.encode
        writeUInt32BE crc
        writeBytes commandBytes

end Datagram

end Lenet.Protocol
