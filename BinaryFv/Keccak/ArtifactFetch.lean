import BinaryFv.Keccak.Artifact
import BinaryFv.RISCV.Decode
import BinaryFv.RISCV.FetchContract
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RISCV

private theorem fetchWord_of_image_bytes (byte0 byte1 byte2 byte3 : UInt8) :
    fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) =
      BitVec.ofNat 32 (byte0.toNat + 256 *
        (byte1.toNat + 256 * (byte2.toNat + 256 * byte3.toNat))) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := UInt8.toNat_lt byte0
  have h1 := UInt8.toNat_lt byte1
  have h2 := UInt8.toNat_lt byte2
  have h3 := UInt8.toNat_lt byte3
  have pow8 : 2 ^ 8 = 256 := by decide
  have pow32 : 2 ^ 32 = 4294967296 := by decide
  simp only [fetchWord, BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3]
  rw [← Nat.shiftLeft_add_eq_or_of_lt h0, ← Nat.shiftLeft_add_eq_or_of_lt h1,
    ← Nat.shiftLeft_add_eq_or_of_lt h2]
  simp only [Nat.shiftLeft_eq]
  have wordBound : byte0.toNat + 256 *
      (byte1.toNat + 256 * (byte2.toNat + 256 * byte3.toNat)) < 2 ^ 32 := by
    rw [pow8] at h0 h1 h2 h3
    rw [pow32]
    omega
  rw [Nat.mod_eq_of_lt wordBound]
  rw [pow8]
  omega

namespace ProgramImage

/-- An encoded word is backed by this image's little-endian four-byte read. -/
def ownsEncodedWord (image : ProgramImage) (word : EncodedWord) : Prop :=
  image.readU32LE? word.address = some word.bits.toNat

/-- Decompose an image-backed word into its four source bytes and generated fetch word. -/
theorem ownsEncodedWord_bytes (image : ProgramImage) (word : EncodedWord)
    (owned : image.ownsEncodedWord word) :
    ∃ (byte0 byte1 byte2 byte3 : UInt8),
      image.readByte? word.address = some byte0 ∧
        image.readByte? (word.address + 1) = some byte1 ∧
          image.readByte? (word.address + 2) = some byte2 ∧
            image.readByte? (word.address + 3) = some byte3 ∧
              fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
                (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) = word.bits := by
  simp only [ownsEncodedWord, readU32LE?, readNatLE?] at owned
  cases h0 : image.readByte? word.address with
  | none => simp [h0] at owned
  | some byte0 =>
    cases h1 : image.readByte? (word.address + 1) with
    | none => simp [h0, h1] at owned
    | some byte1 =>
      cases h2 : image.readByte? (word.address + 1 + 1) with
      | none => simp [h0, h1, h2] at owned
      | some byte2 =>
        cases h3 : image.readByte? (word.address + 1 + 1 + 1) with
        | none => simp [h0, h1, h2, h3] at owned
        | some byte3 =>
          simp [h0, h1, h2, h3] at owned
          refine ⟨byte0, byte1, byte2, byte3, rfl, rfl, rfl, rfl, ?_⟩
          calc
            fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
                (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) =
                BitVec.ofNat 32 (byte0.toNat + 256 *
                  (byte1.toNat + 256 * (byte2.toNat + 256 * byte3.toNat))) :=
              fetchWord_of_image_bytes byte0 byte1 byte2 byte3
            _ = BitVec.ofNat 32 word.bits.toNat := by rw [owned]
            _ = word.bits := by simp

/-- Lift four parser-image byte facts into the generated sparse-memory fetch predicate. -/
theorem fetchBytesAt_of_image_bytes (image : ProgramImage) (state : State) (address : Nat)
    (addressFits : address < 2 ^ 64) (loaded : image.matchesMemory state.mem)
    (byte0 byte1 byte2 byte3 : UInt8)
    (read0 : image.readByte? address = some byte0)
    (read1 : image.readByte? (address + 1) = some byte1)
    (read2 : image.readByte? (address + 2) = some byte2)
    (read3 : image.readByte? (address + 3) = some byte3) :
    FetchBytesAt state (BitVec.ofNat 64 address)
      (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
      (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) := by
  unfold FetchBytesAt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressFits]
  exact ⟨loaded address byte0 read0, loaded (address + 1) byte1 read1,
    loaded (address + 2) byte2 read2, loaded (address + 3) byte3 read3⟩

/-- Assemble generated fetch bytes directly from an image-owned encoded word. -/
theorem fetchBytesAt_of_ownedEncodedWord (image : ProgramImage) (state : State)
    (word : EncodedWord) (addressFits : word.address < 2 ^ 64)
    (loaded : image.matchesMemory state.mem) (owned : image.ownsEncodedWord word) :
    ∃ (byte0 byte1 byte2 byte3 : UInt8),
      FetchBytesAt state (BitVec.ofNat 64 word.address)
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ∧
          fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
            (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) = word.bits := by
  obtain ⟨byte0, byte1, byte2, byte3, read0, read1, read2, read3, wordBits⟩ :=
    ownsEncodedWord_bytes image word owned
  refine ⟨byte0, byte1, byte2, byte3, ?_, wordBits⟩
  exact fetchBytesAt_of_image_bytes image state word.address addressFits loaded byte0 byte1 byte2
    byte3 read0 read1 read2 read3

end ProgramImage

end BinaryFv.RISCV

namespace BinaryFv.Keccak

open BinaryFv.RISCV

/--
Conditional parser-image facts sufficient for one generated fetch. This reconstructs bytes only;
it asserts neither a decoder result nor execution or CFG reachability.
-/
def ArtifactFetchableWord (state : State) (word : EncodedWord) : Prop :=
  ∃ image,
    Artifact.programImage = .ok image ∧ image.matchesMemory state.mem ∧
      image.ownsEncodedWord word ∧ word.address < 2 ^ 64

theorem artifactFetchableWord_fetchBytes (state : State) (word : EncodedWord)
    (fetchable : ArtifactFetchableWord state word) :
    ∃ (byte0 byte1 byte2 byte3 : UInt8),
      FetchBytesAt state (BitVec.ofNat 64 word.address)
        (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
        (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) ∧
          fetchWord (BitVec.ofNat 8 byte0.toNat) (BitVec.ofNat 8 byte1.toNat)
            (BitVec.ofNat 8 byte2.toNat) (BitVec.ofNat 8 byte3.toNat) = word.bits := by
  rcases fetchable with ⟨image, _, loaded, owned, addressFits⟩
  exact image.fetchBytesAt_of_ownedEncodedWord state word addressFits loaded owned

end BinaryFv.Keccak
