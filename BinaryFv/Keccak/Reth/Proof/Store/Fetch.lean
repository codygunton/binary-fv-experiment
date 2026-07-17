import BinaryFv.Keccak.Reth.Artifact.Facts.StoreWord
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Keccak.Reth.Proof.Common.ArtifactFetch
import BinaryFv.RiscV.Platform.Fetch

/-!
# Fetch lift for the `xor_block` store word
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Given the parsed image agrees with sparse memory (the persistent code-image assertion), the
    store word is fetchable from that memory. -/
theorem sdStoreWord_fetchable (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    ArtifactFetchableWord state sdStoreWord :=
  ⟨image, imageEq, loaded, sdStoreWord_owned_image image imageEq, by decide⟩
/-- Derive the exact four fetch bytes at `0x10cdc` directly from the persistent code-image
    assertion (`matchesMemory`), rather than assuming them: given the parsed ELF agrees with sparse
    memory, the generated fetch reads exactly `23 30 d5 00` there. -/
theorem sdStoreWord_fetchBytesAt (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x10cdc) 0x23#8 0x30#8 0xd5#8 0x00#8 := by
  obtain ⟨h0, h1, h2, h3⟩ := sdStoreImageByte_true
  have pcNat : (BitVec.ofNat 64 0x10cdc).toNat = 0x10cdc := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [pcNat]
  · simpa using loaded 0x10cdc 0x23 (sdStoreImage_readByte image imageEq 0 0x23 h0)
  · simpa using loaded (0x10cdc + 1) 0x30 (sdStoreImage_readByte image imageEq 1 0x30 h1)
  · simpa using loaded (0x10cdc + 2) 0xd5 (sdStoreImage_readByte image imageEq 2 0xd5 h2)
  · simpa using loaded (0x10cdc + 3) 0x00 (sdStoreImage_readByte image imageEq 3 0x00 h3)
/-- The parser derives the exact four fetch bytes at `0x10cdc` and confirms their generated fetch
    word is the store encoding `0x00d53023`. -/
theorem sdStoreWord_fetchBytes (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    ∃ (byte0 byte1 byte2 byte3 : UInt8),
      FetchBytesAt state (BitVec.ofNat 64 sdStoreWord.address)
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ∧
      fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) = sdStoreWord.bits :=
  artifactFetchableWord_fetchBytes state sdStoreWord
    (sdStoreWord_fetchable state image imageEq loaded)

end BinaryFv.Keccak
