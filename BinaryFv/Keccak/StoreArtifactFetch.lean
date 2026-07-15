import BinaryFv.Keccak.ArtifactFetch

/-!
# Parser-derived fetch of the `xor_block` store instruction

The `sd a3, 0(a0)` at address `0x10cdc` is `0x00d53023` (little-endian bytes `23 30 d5 00`).  These
bytes are not trusted input: they are derived from the embedded canonical Reth Keccak ELF through
the bounded parser, exactly as the fetch side already does for other instructions.  The only
`native_decide` here is the closed parser fact that the parsed image backs this word — the same
trust policy used by the existing artifact regressions.
-/

namespace BinaryFv.Keccak

open BinaryFv.RISCV

/-- The `xor_block` store, as a parser-level encoded word: `sd a3, 0(a0)` at `0x10cdc`. -/
def sdStoreWord : EncodedWord := { address := 0x10cdc, bits := 0x00d53023 }

/-- Closed parser fact: the parsed image's little-endian four-byte read at `0x10cdc` is the store
    encoding.  This is a decidable fact about the embedded ELF, discharged by `native_decide`. -/
private def sdStoreWordOwned : Bool :=
  match Artifact.programImage with
  | .ok image => decide (image.readU32LE? sdStoreWord.address = some sdStoreWord.bits.toNat)
  | .error _ => false

private theorem sdStoreWordOwned_true : sdStoreWordOwned = true := by native_decide

theorem sdStoreWord_owned_image (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) : image.ownsEncodedWord sdStoreWord := by
  have h := sdStoreWordOwned_true
  unfold sdStoreWordOwned at h
  rw [imageEq] at h
  simp only [decide_eq_true_eq] at h
  exact h

/-- Given the parsed image agrees with sparse memory (the persistent code-image assertion), the
    store word is fetchable from that memory. -/
theorem sdStoreWord_fetchable (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem) :
    ArtifactFetchableWord state sdStoreWord :=
  ⟨image, imageEq, loaded, sdStoreWord_owned_image image imageEq, by decide⟩

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
