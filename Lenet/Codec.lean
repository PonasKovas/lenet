namespace Lenet

/-- Errors that can arise during binary decoding. -/
inductive CodecError where
  | unexpectedEndOfInput (expected : Nat) (available : Nat)
  | invalidEnumValue (type : String) (value : Nat)
  | trailingGarbage (remaining : Nat)
  | custom (msg : String)
deriving Repr, BEq, Inhabited

instance : ToString CodecError where
  toString
    | .unexpectedEndOfInput exp got => s!"Unexpected EOF: expected {exp} bytes, found {got}"
    | .invalidEnumValue ty val      => s!"Invalid enum value for {ty}: {val}"
    | .trailingGarbage rem          => s!"Trailing unparsed bytes remaining: {rem}"
    | .custom msg                   => msg -- misc failures that carry their own message

--------------------------------------------------------------------------------
-- ByteReader (Binary Parser Monad)
--------------------------------------------------------------------------------

/-- Cursor tracking the input buffer and read position. -/
structure ReadCursor where
  bytes  : ByteArray
  offset : Nat := 0
deriving Inhabited

@[inline]
def ReadCursor.remaining (c : ReadCursor) : Nat :=
  c.bytes.size - c.offset

/-- Monad for binary parsing with early-exit failure and state tracking. -/
abbrev ReaderM := EStateM CodecError ReadCursor

namespace ReaderM

@[inline]
def remaining : ReaderM Nat := do
  let c ← get
  return c.remaining

@[inline]
def hasRemaining : ReaderM Bool := do
  let c ← get
  return c.offset < c.bytes.size

def readUInt8 : ReaderM UInt8 := do
  let c ← get
  if h : c.offset < c.bytes.size then
    set { c with offset := c.offset + 1 }
    return c.bytes[c.offset]
  else
    throw (CodecError.unexpectedEndOfInput 1 0)

def readUInt16BE : ReaderM UInt16 := do
  let c ← get
  if h : c.offset + 2 <= c.bytes.size then
    have h0 : c.offset < c.bytes.size := by omega
    have h1 : c.offset + 1 < c.bytes.size := by omega
    let b0 := c.bytes[c.offset]
    let b1 := c.bytes[c.offset + 1]
    set { c with offset := c.offset + 2 }
    return (b0.toUInt16 <<< 8) ||| b1.toUInt16
  else
    throw (CodecError.unexpectedEndOfInput 2 c.remaining)

def readUInt32BE : ReaderM UInt32 := do
  let c ← get
  if h : c.offset + 4 <= c.bytes.size then
    have h0 : c.offset < c.bytes.size := by omega
    have h1 : c.offset + 1 < c.bytes.size := by omega
    have h2 : c.offset + 2 < c.bytes.size := by omega
    have h3 : c.offset + 3 < c.bytes.size := by omega
    let b0 := c.bytes[c.offset]
    let b1 := c.bytes[c.offset + 1]
    let b2 := c.bytes[c.offset + 2]
    let b3 := c.bytes[c.offset + 3]
    set { c with offset := c.offset + 4 }
    return (b0.toUInt32 <<< 24) |||
           (b1.toUInt32 <<< 16) |||
           (b2.toUInt32 <<< 8)  |||
            b3.toUInt32
  else
    throw (CodecError.unexpectedEndOfInput 4 c.remaining)

def readBytes (len : Nat) : ReaderM ByteArray := do
  let c ← get
  if c.offset + len <= c.bytes.size then
    let slice := c.bytes.extract c.offset (c.offset + len)
    set { c with offset := c.offset + len }
    return slice
  else
    throw (CodecError.unexpectedEndOfInput len c.remaining)

/-- Asserts that the entire input has been consumed. -/
def requireEOF : ReaderM Unit := do
  let c ← get
  let rem := c.remaining
  if rem ≠ 0 then
    throw (CodecError.trailingGarbage rem)

/-- Runs the reader over a `ByteArray`. -/
def run (r : ReaderM α) (bytes : ByteArray) : Except CodecError α :=
  match EStateM.run r { bytes := bytes, offset := 0 } with
  | .ok val _ => .ok val
  | .error err _ => .error err

/-- Runs the reader and guarantees all bytes are consumed without trailing garbage. -/
def runFully (r : ReaderM α) (bytes : ByteArray) : Except CodecError α :=
  run (r <* requireEOF) bytes

end ReaderM

--------------------------------------------------------------------------------
-- ByteWriter (Binary Builder Monad)
--------------------------------------------------------------------------------

/--
Monad for binary serialization.
Uses Lean 4's Perceus linear memory model for in-place mutation of the `ByteArray`.
-/
abbrev WriterM := StateM ByteArray

namespace WriterM

@[inline]
def writeUInt8 (v : UInt8) : WriterM Unit :=
  modify (·.push v)

def writeUInt16BE (v : UInt16) : WriterM Unit := do
  writeUInt8 (v >>> 8).toUInt8
  writeUInt8 v.toUInt8

def writeUInt32LE (v : UInt32) : WriterM Unit := do
  writeUInt8 v.toUInt8
  writeUInt8 (v >>> 8).toUInt8
  writeUInt8 (v >>> 16).toUInt8
  writeUInt8 (v >>> 24).toUInt8

def writeUInt32BE (v : UInt32) : WriterM Unit := do
  writeUInt8 (v >>> 24).toUInt8
  writeUInt8 (v >>> 16).toUInt8
  writeUInt8 (v >>> 8).toUInt8
  writeUInt8 v.toUInt8

@[inline]
def writeBytes (src : ByteArray) : WriterM Unit :=
  modify (· ++ src)

/-- Runs the writer and outputs the finished `ByteArray`. -/
def run (w : WriterM Unit) (capacityHint : Nat := 64) : ByteArray :=
  let initial := ByteArray.emptyWithCapacity capacityHint
  (w initial).2

end WriterM

--------------------------------------------------------------------------------
-- Typeclasses & Helpers
--------------------------------------------------------------------------------

/--
A pure packet compressor interface for datagram payload compression/decompression.
Matches ENet's compressor contract without mutable global state.
-/
structure Compressor where
  compress   : ByteArray → ByteArray
  decompress : ByteArray → Except CodecError ByteArray

class Encode (α : Type) where
  encode : α → WriterM Unit

class Decode (α : Type) where
  decode : ReaderM α

/-- Serializes a value into a `ByteArray`. -/
def encode [Encode α] (x : α) (capacityHint : Nat := 64) : ByteArray :=
  WriterM.run (Encode.encode x) capacityHint

/-- Decodes a value from a `ByteArray`. -/
def decode [Decode α] (bytes : ByteArray) : Except CodecError α :=
  ReaderM.run Decode.decode bytes

/-- Decodes a value and ensures no trailing garbage remains. -/
def decodeFully [Decode α] (bytes : ByteArray) : Except CodecError α :=
  ReaderM.runFully Decode.decode bytes

end Lenet
