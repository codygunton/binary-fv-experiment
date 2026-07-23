import BinaryFv.Binary.ProgramImage
import BinaryFv.RiscV.Model.State

open PreSail
open LeanRV64DExecutable.Functions
open Register

namespace BinaryFv.Binary

/-!
These relate a `BinaryFv.Binary` image to the generated Sail sparse memory, so they are RISC-V-layer
content. They are declared in the image's own namespace, rather than `BinaryFv.RiscV`, only so that
`image.matchesMemory` dot-notation resolves; the architecture-independent `Binary` layer itself does
not depend on them.
-/

/-- The parsed image agrees pointwise with the Sail sparse memory. -/
def LoadSegment.matchesMemory (segment : LoadSegment) (memory : Std.ExtHashMap Nat (BitVec 8)) :
    Prop :=
  ∀ address byte,
    segment.readByte? address = some byte → memory.get? address = some (BitVec.ofNat 8 byte.toNat)

def ProgramImage.matchesMemory (image : ProgramImage) (memory : Std.ExtHashMap Nat (BitVec 8)) :
    Prop :=
  ∀ address byte,
    image.readByte? address = some byte → memory.get? address = some (BitVec.ofNat 8 byte.toNat)

/-- Sparse-memory agreement for bytes actually present in the executable file. -/
def ProgramImage.fileBytesMatchMemory (image : ProgramImage)
    (memory : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ address byte,
    image.readFileByte? address = some byte →
      memory.get? address = some (BitVec.ofNat 8 byte.toNat)

/-- **File-backed agreement is insensitive to writes at non-file-backed (BSS) addresses.** This is
the property that makes `fileBytesMatchMemory` the right notion of "code intact": the decoder's and
host's writes to the mutable BSS globals (heap cursor, arena, decoder globals) do not disturb it,
while a write to a file-backed code/rodata byte would. -/
theorem ProgramImage.fileBytesMatchMemory_insert_non_file {image : ProgramImage}
    {memory : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} {value : BitVec 8}
    (notFileBacked : image.readFileByte? address = none)
    (h : image.fileBytesMatchMemory memory) :
    image.fileBytesMatchMemory (memory.insert address value) := by
  intro a byte hread
  have hne : a ≠ address := by rintro rfl; rw [notFileBacked] at hread; exact absurd hread (by simp)
  have : (memory.insert address value).get? a = memory.get? a := by
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp [hne.symm]
  rw [this]; exact h a byte hread

/-- **A write of the wrong value at a file-backed address breaks file-backed agreement.** The
companion to the lemma above: `fileBytesMatchMemory` genuinely constrains the code and rodata, so a
corrupted code byte is caught. -/
theorem ProgramImage.not_fileBytesMatchMemory_insert_file {image : ProgramImage}
    {memory : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} {byte : UInt8} {value : BitVec 8}
    (fileBacked : image.readFileByte? address = some byte)
    (wrong : value ≠ BitVec.ofNat 8 byte.toNat) :
    ¬ image.fileBytesMatchMemory (memory.insert address value) := by
  intro h
  have hget := h address byte fileBacked
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert] at hget
  simp at hget
  have hconv : (byte.toBitVec : BitVec 8) = BitVec.ofNat 8 byte.toNat :=
    (UInt8.toNat_toBitVec byte ▸ (BitVec.ofNat_toNat 8 byte.toBitVec)).symm
  exact wrong (hget.trans hconv)

end BinaryFv.Binary

namespace BinaryFv.RiscV

open BinaryFv.Binary

def imageUnchanged (image : ProgramImage) (state : State) : Prop :=
  image.matchesMemory state.mem

end BinaryFv.RiscV
