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

end BinaryFv.Binary

namespace BinaryFv.RiscV

open BinaryFv.Binary

def imageUnchanged (image : ProgramImage) (state : State) : Prop :=
  image.matchesMemory state.mem

end BinaryFv.RiscV
