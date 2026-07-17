import BinaryFv.Keccak.Reth.Artifact.Image
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.ELF.Decode

/-!
# Closed image facts for the `xor_block` store word
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- The `xor_block` store, as a parser-level encoded word: `sd a3, 0(a0)` at `0x10cdc`. -/
def sdStoreWord : EncodedWord := { address := 0x10cdc, bits := 0x00d53023 }
/-- Closed parser fact: the parsed image's little-endian four-byte read at `0x10cdc` is the store
    encoding.  This is a decidable fact about the embedded ELF, discharged by `native_decide`. -/
def sdStoreWordOwned : Bool :=
  match Artifact.programImage with
  | .ok image => decide (image.readU32LE? sdStoreWord.address = some sdStoreWord.bits.toNat)
  | .error _ => false
theorem sdStoreWordOwned_true : sdStoreWordOwned = true := by native_decide
theorem sdStoreWord_owned_image (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) : image.ownsEncodedWord sdStoreWord := by
  have h := sdStoreWordOwned_true
  unfold sdStoreWordOwned at h
  rw [imageEq] at h
  simp only [decide_eq_true_eq] at h
  exact h
/-- Closed parser byte facts: the image's byte reads at `0x10cdc … 0x10cdf` are `23 30 d5 00`. -/
def sdStoreImageByte (offset : Nat) (value : UInt8) : Bool :=
  match Artifact.programImage with
  | .ok image => decide (image.readByte? (0x10cdc + offset) = some value)
  | .error _ => false
theorem sdStoreImageByte_true :
    sdStoreImageByte 0 0x23 = true ∧ sdStoreImageByte 1 0x30 = true ∧
      sdStoreImageByte 2 0xd5 = true ∧ sdStoreImageByte 3 0x00 = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide
theorem sdStoreImage_readByte (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (offset : Nat) (value : UInt8)
    (h : sdStoreImageByte offset value = true) : image.readByte? (0x10cdc + offset) = some value := by
  unfold sdStoreImageByte at h
  rw [imageEq] at h
  simpa using h

end BinaryFv.Keccak
