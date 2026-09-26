import Lenet.Constants
import Lenet.Codec

namespace Lenet.Protocol

open ReaderM WriterM

/-- ENet protocol header: a 16-bit word packing the target peer ID (low 12
bits), the session ID (2 bits) and the compressed / sent-time flags, followed
by the 16-bit sent time when that flag is set. -/
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

  if let some time := h.sentTime then
    writeUInt16BE time

end Header

end Lenet.Protocol
