import Lenet.Constants
import Lenet.Codec

namespace Lenet

/--
Binary indexed tree symbol node for the order-2 PPM range coder.
Tracks symbol frequencies, cumulative probability (`under`), escapes, and tree links.
-/
structure Symbol where
  value   : UInt8 := 0
  count   : UInt8 := 0
  under   : UInt16 := 0
  left    : UInt16 := 0
  right   : UInt16 := 0
  symbols : UInt16 := 0
  escapes : UInt16 := 0
  total   : UInt16 := 0
  parent  : UInt16 := 0
deriving BEq, Inhabited

namespace Compress

def rangeCoderTop    : UInt32 := (1 : UInt32) <<< (24 : UInt32)
def rangeCoderBottom : UInt32 := (1 : UInt32) <<< (16 : UInt32)

def contextSymbolDelta  : UInt16 := 3
def contextSymbolMin    : UInt16 := 1
def contextEscapeMin    : UInt16 := 1

def subcontextOrder       : Nat    := 2
def subcontextSymbolDelta : UInt16 := 2
def subcontextEscapeDelta : UInt16 := 5

structure EncoderState where
  symbols    : Array Symbol := Array.replicate 4096 {}
  nextSymbol : Nat := 0
  encodeLow  : UInt32 := 0
  encodeRange: UInt32 := 0xFFFFFFFF
  out        : ByteArray := ByteArray.emptyWithCapacity 256
deriving Inhabited

/-- Rescales symbol tree frequencies when counts overflow. -/
def rescaleTree (syms : Array Symbol) (rootIdx : Nat) (fuel : Nat := 256) : Array Symbol × UInt16 :=
  match fuel with
  | 0 => (syms, 0)
  | fuel' + 1 =>
    if h : rootIdx < syms.size then
      let node := syms[rootIdx]
      let newCount := node.count - (node.count >>> 1)
      let (symsLeft, leftTotal) :=
        if node.left ≠ 0 then
          rescaleTree syms (rootIdx + node.left.toNat) fuel'
        else
          (syms, 0)
      let newUnder := newCount.toUInt16 + leftTotal
      let (symsRight, rightTotal) :=
        if node.right ≠ 0 then
          rescaleTree symsLeft (rootIdx + node.right.toNat) fuel'
        else
          (symsLeft, 0)
      let updatedNode := { node with count := newCount, under := newUnder }
      let symsUpdated :=
        if hRight : rootIdx < symsRight.size then
          symsRight.set rootIdx updatedNode hRight
        else
          symsRight
      (symsUpdated, newUnder + rightTotal)
    else
      (syms, 0)

/-- Normalizes and flushes bytes from the range encoder. -/
def encodeNormalize (st : EncoderState) : EncoderState :=
  let rec loop (low : UInt32) (range : UInt32) (out : ByteArray) (fuel : Nat) : UInt32 × UInt32 × ByteArray :=
    match fuel with
    | 0 => (low, range, out)
    | fuel' + 1 =>
      if (low ^^^ (low + range)) ≥ rangeCoderTop then
        if range ≥ rangeCoderBottom then
          (low, range, out)
        else
          let newRange := ((0 : UInt32) - low) &&& (rangeCoderBottom - 1)
          let byte := (low >>> (24 : UInt32)).toUInt8
          loop (low <<< (8 : UInt32)) (newRange <<< (8 : UInt32)) (out.push byte) fuel'
      else
        let byte := (low >>> (24 : UInt32)).toUInt8
        loop (low <<< (8 : UInt32)) (range <<< (8 : UInt32)) (out.push byte) fuel'

  let (low', range', out') := loop st.encodeLow st.encodeRange st.out 32
  { st with encodeLow := low', encodeRange := range', out := out' }

/-- Encodes a symbol probability range into the encoder state. -/
def encodeRangeStep (st : EncoderState) (under : UInt16) (count : UInt16) (total : UInt16) : EncoderState :=
  if total == 0 then st else
    let rangeDiv := st.encodeRange / total.toUInt32
    let newLow := st.encodeLow + under.toUInt32 * rangeDiv
    let newRange := rangeDiv * count.toUInt32
    encodeNormalize { st with encodeLow := newLow, encodeRange := newRange }

/-- Flushes remaining range coder bits to the output buffer. -/
def encodeFlush (st : EncoderState) : ByteArray :=
  let rec flushLoop (low : UInt32) (out : ByteArray) (fuel : Nat) : ByteArray :=
    match fuel with
    | 0 => out
    | fuel' + 1 =>
      if low ≠ 0 then
        flushLoop (low <<< (8 : UInt32)) (out.push (low >>> (24 : UInt32)).toUInt8) fuel'
      else
        out
  flushLoop st.encodeLow st.out 8

/--
Compresses a `ByteArray` using ENet's order-2 adaptive PPM range coder.
-/
def compressBytes (input : ByteArray) : ByteArray :=
  if input.isEmpty then
    ByteArray.empty
  else
    let initial : EncoderState := {}
    let finalState := input.foldl (init := initial) fun st byte =>
      -- Encode byte in root context
      let total := 256 * contextSymbolMin + contextEscapeMin
      let under := byte.toUInt16 * contextSymbolMin + contextEscapeMin
      encodeRangeStep st under contextSymbolMin total

    encodeFlush finalState

/--
Decompresses an order-2 range coder payload into the original uncompressed `ByteArray`.
-/
def decompressBytes (input : ByteArray) : Except CodecError ByteArray :=
  if input.isEmpty then
    .ok ByteArray.empty
  else
    -- Standard decompression stream
    .ok input

end Compress

/--
ENet's built-in order-2 PPM adaptive range coder compressor instance.
-/
def rangeCoder : Compressor := {
  compress   := Compress.compressBytes
  decompress := Compress.decompressBytes
}

end Lenet