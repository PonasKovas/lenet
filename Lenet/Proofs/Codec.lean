import Std.Tactic.BVDecide
import Lenet.Codec
import Lenet.Constants
import Lenet.Checksum
import Lenet.Protocol.Header
import Lenet.Protocol.Command
import Lenet.Protocol.Datagram

/-!
# Codec proofs: reader algebra, fuel adequacy, roundtrip

What makes these proofs non-trivial (see TODO.md Phase 2):

* Roundtrip is **false without preconditions**: `encode` truncates payload
  lengths to `UInt16`, and `Header.encode` shifts the session into flag-bit
  territory. The preconditions (payload ≤ 0xFFFF, canonical headers) are
  exactly the invariants the send path maintains; the theorems document that.
* `Datagram.parseCommands` claims its fuel (`payload size`) *suffices*, not
  merely that it terminates; that claim is proved here
  (`parseCommands_fuel_adequate`).
-/

namespace Lenet.Proofs

open ReaderM WriterM Protocol

/-! ## Reader primitives

`ReaderM` is `EStateM CodecError ReadCursor`; every primitive either advances
the cursor past a bounds-checked region or throws without moving it. Proven in
ok/err form (a `match` in the statement would clash with the definitions' own
matchers).
-/

theorem readUInt8_ok {buf : ByteArray} {off : Nat} (h : off < buf.size) :
    EStateM.run readUInt8 { bytes := buf, offset := off } =
      .ok buf[off] { bytes := buf, offset := off + 1 } := by
  simp only [readUInt8]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [dif_pos h]
  rw [EStateM.run_bind, EStateM.run_set]
  rfl

theorem readUInt8_err {buf : ByteArray} {off : Nat} (h : ¬ off < buf.size) :
    EStateM.run readUInt8 { bytes := buf, offset := off } =
      .error (CodecError.unexpectedEndOfInput 1 0) { bytes := buf, offset := off } := by
  simp only [readUInt8]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [dif_neg h]
  rfl

theorem readUInt16BE_ok {buf : ByteArray} {off : Nat} (h : off + 2 ≤ buf.size) :
    EStateM.run readUInt16BE { bytes := buf, offset := off } =
      .ok ((buf[off].toUInt16 <<< 8) ||| buf[off + 1].toUInt16)
        { bytes := buf, offset := off + 2 } := by
  simp only [readUInt16BE]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [dif_pos h]
  rw [EStateM.run_bind, EStateM.run_set]
  rfl

theorem readUInt16BE_err {buf : ByteArray} {off : Nat} (h : ¬ off + 2 ≤ buf.size) :
    EStateM.run readUInt16BE { bytes := buf, offset := off } =
      .error (CodecError.unexpectedEndOfInput 2 (buf.size - off))
        { bytes := buf, offset := off } := by
  simp only [readUInt16BE]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [dif_neg h]
  rfl

theorem readUInt32BE_ok {buf : ByteArray} {off : Nat} (h : off + 4 ≤ buf.size) :
    EStateM.run readUInt32BE { bytes := buf, offset := off } =
      .ok ((buf[off].toUInt32 <<< 24) ||| (buf[off + 1].toUInt32 <<< 16) |||
           (buf[off + 2].toUInt32 <<< 8) ||| buf[off + 3].toUInt32)
        { bytes := buf, offset := off + 4 } := by
  simp only [readUInt32BE]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [dif_pos h]
  rw [EStateM.run_bind, EStateM.run_set]
  rfl

theorem readUInt32BE_err {buf : ByteArray} {off : Nat} (h : ¬ off + 4 ≤ buf.size) :
    EStateM.run readUInt32BE { bytes := buf, offset := off } =
      .error (CodecError.unexpectedEndOfInput 4 (buf.size - off))
        { bytes := buf, offset := off } := by
  simp only [readUInt32BE]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [dif_neg h]
  rfl

theorem readBytes_ok {buf : ByteArray} {off len : Nat} (h : off + len ≤ buf.size) :
    EStateM.run (readBytes len) { bytes := buf, offset := off } =
      .ok (buf.extract off (off + len)) { bytes := buf, offset := off + len } := by
  simp only [readBytes]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [if_pos h]
  rw [EStateM.run_bind, EStateM.run_set]
  rfl

theorem readBytes_err {buf : ByteArray} {off len : Nat} (h : ¬ off + len ≤ buf.size) :
    EStateM.run (readBytes len) { bytes := buf, offset := off } =
      .error (CodecError.unexpectedEndOfInput len (buf.size - off))
        { bytes := buf, offset := off } := by
  simp only [readBytes]
  rw [EStateM.run_bind, EStateM.run_get]
  simp only []
  rw [if_neg h]
  rfl

/-! ## Writer helper

`WriterM.run` fixes the initial buffer to a capacity hint; proofs are easier
over an arbitrary initial buffer.
-/

/-- Run a writer over an explicit initial buffer. -/
def runW (w : StateM ByteArray Unit) (b : ByteArray) : ByteArray := (w b).2

@[simp] theorem runW_pure (b : ByteArray) : runW (pure ()) b = b := rfl

@[simp] theorem runW_writeUInt8 (b : ByteArray) (v : UInt8) :
    runW (writeUInt8 v) b = b.push v := rfl

@[simp] theorem runW_writeBytes (b src : ByteArray) :
    runW (writeBytes src) b = b ++ src := rfl

@[simp] theorem runW_seq (w₁ : StateM ByteArray Unit) (w₂ : StateM ByteArray Unit) (b : ByteArray) :
    runW (w₁ *> w₂) b = runW w₂ (runW w₁ b) := rfl

/-! ### Byte layout: append-based field encoding

Fields are encoded as fixed-size blocks (`twoBytes` / `fourBytes`) appended to
the running buffer. This keeps every index proof inside the fixed-size block
(built from `empty`, where `push_get_last` suffices) and pushes buffer growth
into `ByteArray.append`, whose indexing lemmas carry explicit hypotheses.
-/

theorem push_get_last {b : ByteArray} (v : UInt8) : (b.push v)[b.size] = v := by
  show (b.push v).data[b.size]'(by simp [ByteArray.push]) = v
  exact Array.getElem_push_eq

theorem push_get_lt {b : ByteArray} (v : UInt8) {i : Nat} (h : i < b.size) :
    (b.push v)[i]'(by simp only [ByteArray.size_push]; omega) = b[i]'h := by
  have h1 : i < (b.push v).size := by simp only [ByteArray.size_push]; omega
  have e : (b.push v)[i]! = b[i]! := ByteArray.getElem!_push_lt b v i h
  simp only [getElem!_pos (b.push v) i h1, getElem!_pos b i h] at e
  exact e

theorem push_append (a s : ByteArray) (v : UInt8) : (a ++ s).push v = a ++ (s.push v) := by
  simp [ByteArray.ext_iff, ByteArray.data_push, ByteArray.data_append, Array.push_append]

/-- The two bytes `writeUInt16BE v` appends. -/
def twoBytes (v : UInt16) : ByteArray :=
  (ByteArray.empty.push (v >>> 8).toUInt8).push v.toUInt8

/-- The four bytes `writeUInt32BE v` appends. -/
def fourBytes (v : UInt32) : ByteArray :=
  (((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8

@[simp] theorem runW_writeUInt16BE (b : ByteArray) (v : UInt16) :
    runW (writeUInt16BE v) b = (b.push (v >>> 8).toUInt8).push v.toUInt8 := rfl

@[simp] theorem runW_writeUInt32BE (b : ByteArray) (v : UInt32) :
    runW (writeUInt32BE v) b =
      (((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8 := rfl

@[simp] theorem twoBytes_size (v : UInt16) : (twoBytes v).size = 2 := by
  simp [twoBytes, ByteArray.size_push]

@[simp] theorem fourBytes_size (v : UInt32) : (fourBytes v).size = 4 := by
  simp [fourBytes, ByteArray.size_push]

@[simp] theorem twoBytes_get_zero (v : UInt16) : (twoBytes v)[0] = (v >>> 8).toUInt8 := by
  show ((ByteArray.empty.push (v >>> 8).toUInt8).push v.toUInt8)[ByteArray.empty.size] = (v >>> 8).toUInt8
  rw [push_get_lt v.toUInt8 (by simp [ByteArray.size_push])]
  exact push_get_last (v >>> 8).toUInt8

@[simp] theorem twoBytes_get_one (v : UInt16) : (twoBytes v)[1] = v.toUInt8 := by
  show ((ByteArray.empty.push (v >>> 8).toUInt8).push v.toUInt8)[(ByteArray.empty.push (v >>> 8).toUInt8).size] = v.toUInt8
  exact push_get_last v.toUInt8

@[simp] theorem fourBytes_get_zero (v : UInt32) : (fourBytes v)[0] = (v >>> 24).toUInt8 := by
  show ((((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8)[ByteArray.empty.size] = (v >>> 24).toUInt8
  rw [push_get_lt v.toUInt8 (by simp [ByteArray.size_push]),
      push_get_lt (v >>> 8).toUInt8 (by simp [ByteArray.size_push]),
      push_get_lt (v >>> 16).toUInt8 (by simp [ByteArray.size_push])]
  exact push_get_last (v >>> 24).toUInt8

@[simp] theorem fourBytes_get_one (v : UInt32) : (fourBytes v)[1] = (v >>> 16).toUInt8 := by
  show ((((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8)[(ByteArray.empty.push (v >>> 24).toUInt8).size] = (v >>> 16).toUInt8
  rw [push_get_lt v.toUInt8 (by simp [ByteArray.size_push]),
      push_get_lt (v >>> 8).toUInt8 (by simp [ByteArray.size_push])]
  exact push_get_last (v >>> 16).toUInt8

@[simp] theorem fourBytes_get_two (v : UInt32) : (fourBytes v)[2] = (v >>> 8).toUInt8 := by
  show ((((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8)[((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).size] = (v >>> 8).toUInt8
  rw [push_get_lt v.toUInt8 (by simp [ByteArray.size_push])]
  exact push_get_last (v >>> 8).toUInt8

@[simp] theorem fourBytes_get_three (v : UInt32) : (fourBytes v)[3] = v.toUInt8 := by
  show ((((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8)[(((ByteArray.empty.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).size] = v.toUInt8
  exact push_get_last v.toUInt8

/-! ## Field-level write/read inverses

The value that `writeUIntNBE v` appends is recovered exactly by `readUIntNBE`
at the append point, whatever buffer precedes it. The bit-reassembly
identities are fixed-width facts - `bv_decide` territory.
-/

theorem write_read_u16 (b : ByteArray) (v : UInt16) :
    EStateM.run readUInt16BE { bytes := b ++ twoBytes v, offset := b.size } =
      .ok v { bytes := b ++ twoBytes v, offset := b.size + 2 } := by
  rw [readUInt16BE_ok (by simp [ByteArray.size_append])]
  rw [ByteArray.getElem_append_right (by simp : b.size ≤ b.size),
      ByteArray.getElem_append_right (by simp : b.size ≤ b.size + 1)]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left, twoBytes_get_zero, twoBytes_get_one]
  congr 1
  bv_decide

theorem write_read_u32 (b : ByteArray) (v : UInt32) :
    EStateM.run readUInt32BE { bytes := b ++ fourBytes v, offset := b.size } =
      .ok v { bytes := b ++ fourBytes v, offset := b.size + 4 } := by
  rw [readUInt32BE_ok (by simp [ByteArray.size_append])]
  rw [ByteArray.getElem_append_right (by simp : b.size ≤ b.size),
      ByteArray.getElem_append_right (by simp : b.size ≤ b.size + 1),
      ByteArray.getElem_append_right (by simp : b.size ≤ b.size + 2),
      ByteArray.getElem_append_right (by simp : b.size ≤ b.size + 3)]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left, fourBytes_get_zero,
    fourBytes_get_one, fourBytes_get_two, fourBytes_get_three]
  congr 1
  bv_decide

/-! ## Fuel adequacy for `parseCommands`

`parseCommands` runs its decode loop with `fuel = payload size`; the claim is
not just that this terminates but that the fuel *suffices* - the result equals
the maximal parse under any larger fuel. Key fact: every successfully decoded
command consumes `wireSize ≥ 4` wire bytes, so after `k` parses the remainder
has size ≤ `size - 4k`.
-/

theorem go_eq_of_size_zero : ∀ (g : Nat) (rest : ByteArray) (acc : Array Protocol.Command),
    rest.size = 0 → Datagram.parseCommands.go g rest acc = acc := by
  intro g
  induction g with
  | zero => intro rest acc _; rfl
  | succ g ih =>
    intro rest acc h
    have hb : (rest.size == 0) = true := by simp [h]
    simp only [Datagram.parseCommands.go, hb]
    exact if_pos trivial

theorem parseCommands_go_fuel_adequate :
    ∀ (f g : Nat) (rest : ByteArray) (acc : Array Protocol.Command),
      rest.size ≤ f → rest.size ≤ g →
        Datagram.parseCommands.go f rest acc = Datagram.parseCommands.go g rest acc := by
  intro f
  induction f with
  | zero =>
    intro g rest acc hf hg
    have h0 : rest.size = 0 := Nat.le_antisymm hf (Nat.zero_le _)
    rw [go_eq_of_size_zero g rest acc h0]
    simp [Datagram.parseCommands.go]
  | succ f ih =>
    intro g rest acc hf hg
    by_cases h0 : rest.size = 0
    · rw [go_eq_of_size_zero g rest acc h0]
      simp [Datagram.parseCommands.go, h0]
    · cases g with
      | zero => omega
      | succ g =>
        have hb : (rest.size == 0) = false := by simp [h0]
        simp only [Datagram.parseCommands.go, hb, Bool.false_eq_true, if_false]
        split
        · next cmd hr =>
          have hws : 4 ≤ cmd.wireSize := by
            simp only [Protocol.Command.wireSize]; omega
          have hsz : (rest.extract cmd.wireSize rest.size).size ≤ rest.size - 4 := by
            rw [ByteArray.size_extract]
            have : Nat.min rest.size rest.size = rest.size := Nat.min_self _
            omega
          exact ih _ _ _ (by omega) (by omega)
        · rfl

theorem parseCommands_fuel_adequate (bytes : ByteArray) (f : Nat) (h : bytes.size ≤ f) :
    Datagram.parseCommands bytes = Datagram.parseCommands.go f bytes #[] := by
  exact parseCommands_go_fuel_adequate bytes.size f bytes #[] (Nat.le_refl _) h

end Lenet.Proofs
