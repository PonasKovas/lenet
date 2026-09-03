import Lenet.Constants
import Lenet.Codec

namespace Lenet.Protocol

open Lenet
open Lenet.ReaderM
open Lenet.WriterM

/-- High-level representation of an ENet protocol packet header. -/
structure Header where
  peerId     : UInt16
  session    : UInt8
  compressed : Bool
  sentTime   : Option UInt16
deriving Repr, BEq, Inhabited

namespace Header

/-- Decodes a protocol header from an incoming binary stream. -/
def decode : ReaderM Header := do
  let rawPeerId ← readUInt16BE

  let session := (
    (rawPeerId &&& Constants.headerSessionMask) >>> Constants.headerSessionShift.toUInt16
  ).toUInt8
  let compressed  := (rawPeerId &&& Constants.headerFlagCompressed) != 0
  let hasSentTime := (rawPeerId &&& Constants.headerFlagSentTime) != 0
  let peerId      := rawPeerId &&& ~~~(Constants.headerFlagMask ||| Constants.headerSessionMask)

  -- Conditionally parse the optional timestamp:
  let sentTime ← if hasSentTime then
    let time ← readUInt16BE
    pure (some time)
  else
    pure none

  return {
    peerId
    session
    compressed
    sentTime
  }

/-- Serializes a protocol header into the binary writer. -/
def encode (h : Header) : WriterM Unit := do
  let flags : UInt16 :=
    (if h.compressed then Constants.headerFlagCompressed else 0) |||
    (if h.sentTime.isSome then Constants.headerFlagSentTime else 0)

  let sessionBits :=
    (h.session.toUInt16 <<< Constants.headerSessionShift.toUInt16) &&& Constants.headerSessionMask

  let rawPeerId :=
    (h.peerId &&& ~~~(Constants.headerFlagMask ||| Constants.headerSessionMask)) |||
    sessionBits |||
    flags

  writeUInt16BE rawPeerId

  -- Write optional timestamp if present:
  if let some time := h.sentTime then
    writeUInt16BE time

end Header

-- Hook into the global Encode/Decode typeclass system:
instance : Decode Header where
  decode := Header.decode

instance : Encode Header where
  encode := Header.encode

end Lenet.Protocol
