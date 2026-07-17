import BinaryFv.Keccak.Reth.Artifact.Image
import BinaryFv.RiscV.ELF.Decode

/-!
# Closed image facts for the real call sites

Which four-byte words the pinned image owns at each call site.
-/

namespace BinaryFv.Keccak

open BinaryFv.Binary
open BinaryFv.RiscV

/-- Closed parser fact: the image's four consecutive little-endian bytes at `address` are
    `b0 b1 b2 b3`.  Decidable over the embedded ELF, discharged by `native_decide`. -/
def callBytesOwned (address : Nat) (b0 b1 b2 b3 : UInt8) : Bool :=
  match Artifact.programImage with
  | .ok image =>
    decide (image.readByte? address = some b0 ∧ image.readByte? (address + 1) = some b1 ∧
      image.readByte? (address + 2) = some b2 ∧ image.readByte? (address + 3) = some b3)
  | .error _ => false
theorem callBytesOwned_readBytes (image : ProgramImage)
    (imageEq : Artifact.programImage = .ok image) (address : Nat) (b0 b1 b2 b3 : UInt8)
    (h : callBytesOwned address b0 b1 b2 b3 = true) :
    image.readByte? address = some b0 ∧ image.readByte? (address + 1) = some b1 ∧
      image.readByte? (address + 2) = some b2 ∧ image.readByte? (address + 3) = some b3 := by
  unfold callBytesOwned at h
  rw [imageEq] at h
  simpa using h
/-- `auipc ra,0x0` at `0x10ad4` (word `0x00000097`, little-endian `97 00 00 00`). -/
theorem xorCallAuipc_owned : callBytesOwned 0x10ad4 0x97 0x00 0x00 0x00 = true := by native_decide
/-- `jalr ra,408(ra)` at `0x10ad8` (word `0x198080e7`, little-endian `e7 80 80 19`). -/
theorem xorCallJalr_owned : callBytesOwned 0x10ad8 0xe7 0x80 0x80 0x19 = true := by native_decide
/-- `auipc ra,0xfffff` at `0x10c64` (word `0xfffff097`, little-endian `97 f0 ff ff`). -/
theorem negCallAuipc_owned : callBytesOwned 0x10c64 0x97 0xf0 0xff 0xff = true := by native_decide
/-- `jalr ra,1164(ra)` at `0x10c68` (word `0x48c080e7`, little-endian `e7 80 c0 48`). -/
theorem negCallJalr_owned : callBytesOwned 0x10c68 0xe7 0x80 0xc0 0x48 = true := by native_decide
/-- `auipc t0,0x0` at `0x10844` (word `0x00000297`, little-endian `97 02 00 00`). -/
theorem t0CallAuipc_owned : callBytesOwned 0x10844 0x97 0x02 0x00 0x00 = true := by native_decide
/-- `jalr t0,1192(t0)` at `0x10848` (word `0x4a8282e7`, little-endian `e7 82 82 4a`). -/
theorem t0CallJalr_owned : callBytesOwned 0x10848 0xe7 0x82 0x82 0x4a = true := by native_decide
/-- `auipc t1,0x0` at `0x10c54` (word `0x00000317`, little-endian `17 03 00 00`). -/
theorem t1TailAuipc_owned : callBytesOwned 0x10c54 0x17 0x03 0x00 0x00 = true := by native_decide
/-- `jr 196(t1)` (`jalr x0,196(t1)`) at `0x10c58` (word `0x0c430067`, little-endian `67 00 43 0c`). -/
theorem t1TailJr_owned : callBytesOwned 0x10c58 0x67 0x00 0x43 0x0c = true := by native_decide
/-- `jal ra,reth_keccak256` at `0x101f8` (word `0x035000ef`, little-endian `ef 00 50 03`). -/
theorem jalCall_owned : callBytesOwned 0x101f8 0xef 0x00 0x50 0x03 = true := by native_decide

end BinaryFv.Keccak
