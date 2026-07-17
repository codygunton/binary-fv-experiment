import BinaryFv.Keccak.Reth.Artifact.Image
import BinaryFv.RiscV.ELF.Decode

/-!
# The image-byte predicate

`imageByte address value` is a closed decidable statement about the pinned image: the byte at
`address` is `value`. Every per-address byte fact in `Facts/` is an instance of it, discharged by
`native_decide` under the approved fixed-artifact exception.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Closed parser byte fact: the parsed image's byte read at `address` is `value`.  This is a
    decidable fact about the embedded ELF, discharged by `native_decide` per address below. -/
def imageByte (address : Nat) (value : UInt8) : Bool :=
  match Artifact.programImage with
  | .ok image => decide (image.readByte? address = some value)
  | .error _ => false
/-- Lift a closed parser byte fact into a byte read against a concrete parsed image. -/
theorem imageByte_readByte (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (address : Nat) (value : UInt8)
    (h : imageByte address value = true) : image.readByte? address = some value := by
  unfold imageByte at h
  rw [imageEq] at h
  simpa using h

end BinaryFv.Keccak
