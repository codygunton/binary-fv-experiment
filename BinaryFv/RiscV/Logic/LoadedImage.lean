import BinaryFv.Binary.ProgramImage
import BinaryFv.RiscV.Model.State

open PreSail
open LeanRV64DExecutable.Functions
open Register

namespace BinaryFv.Binary

/-!
These predicates state when bytes from a parsed `ProgramImage` appear at the correct addresses in
the generated Sail sparse memory. They belong to the RISC-V layer because they mention that machine
memory, but they are declared in the image's namespace so dot notation such as
`image.fileBytesLoadedFaithfully memory` works. The architecture-independent `Binary` layer does not
depend on them.
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

/-- Every byte stored in the executable file has been loaded at its specified machine address. -/
def ProgramImage.fileBytesLoadedFaithfully (image : ProgramImage)
    (memory : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ address byte,
    image.readFileByte? address = some byte →
      memory.get? address = some (BitVec.ofNat 8 byte.toNat)

/-- **Writes outside the file-backed image preserve faithful loading.** This makes
`fileBytesLoadedFaithfully` suitable for stating that code and read-only data remain intact: writes
to mutable BSS globals such as the heap cursor, arena, and decoder globals do not affect it. -/
theorem ProgramImage.fileBytesLoadedFaithfully_insert_non_file {image : ProgramImage}
    {memory : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} {value : BitVec 8}
    (notFileBacked : image.readFileByte? address = none)
    (h : image.fileBytesLoadedFaithfully memory) :
    image.fileBytesLoadedFaithfully (memory.insert address value) := by
  intro a byte hread
  have hne : a ≠ address := by rintro rfl; rw [notFileBacked] at hread; exact absurd hread (by simp)
  have : (memory.insert address value).get? a = memory.get? a := by
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]; simp [hne.symm]
  rw [this]; exact h a byte hread

/-- **Writing the wrong value over a file-backed byte violates faithful loading.** This is the
companion to the preservation lemma above and ensures that corrupting code or read-only data is
detected. -/
theorem ProgramImage.not_fileBytesLoadedFaithfully_insert_file {image : ProgramImage}
    {memory : Std.ExtHashMap Nat (BitVec 8)} {address : Nat} {byte : UInt8} {value : BitVec 8}
    (fileBacked : image.readFileByte? address = some byte)
    (wrong : value ≠ BitVec.ofNat 8 byte.toNat) :
    ¬ image.fileBytesLoadedFaithfully (memory.insert address value) := by
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
