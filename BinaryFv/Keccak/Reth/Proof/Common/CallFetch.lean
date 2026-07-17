import BinaryFv.Keccak.Reth.Artifact.Facts.CallWords
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Platform.Fetch

/-!
# Fetch lift for the real call sites
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Derive the exact four fetch bytes at `address` directly from the persistent code-image
    assertion (`matchesMemory`): given the parsed ELF agrees with sparse memory and the parser owns
    the four bytes there, the generated fetch reads exactly `b0 b1 b2 b3`. -/
theorem callWord_fetchBytesAt (state : State) (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (loaded : image.matchesMemory state.mem)
    (address : Nat) (addressFits : address < 2 ^ 64) (b0 b1 b2 b3 : UInt8)
    (owned : callBytesOwned address b0 b1 b2 b3 = true) :
    FetchBytesAt state (BitVec.ofNat 64 address)
      (BitVec.ofNat 8 b0.toNat) (BitVec.ofNat 8 b1.toNat)
      (BitVec.ofNat 8 b2.toNat) (BitVec.ofNat 8 b3.toNat) := by
  obtain ⟨r0, r1, r2, r3⟩ := callBytesOwned_readBytes image imageEq address b0 b1 b2 b3 owned
  exact image.fetchBytesAt_of_image_bytes state address addressFits loaded b0 b1 b2 b3 r0 r1 r2 r3

end BinaryFv.Keccak
