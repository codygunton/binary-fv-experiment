import BinaryFv.Keccak.Reth.Proof.XorBlock.Registers

/-!
# The little-endian byte-assembly bridge

Assembling eight bytes into the 64-bit lane the machine loads.
-/

namespace BinaryFv.Keccak.XorBlock
open BinaryFv.Binary
open BinaryFv.Keccak.SpecBridge
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open BinaryFv.Keccak
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Deliverable 3: the little-endian byte-assembly bridge

The 8 `lbu` + 6 `slli` + 6 `or` compose the 8 input bytes into the 64-bit little-endian lane, which
is exactly `SepLogic.leWord` of those bytes.  This is a pure `BitVec` identity (`bv_decide`) over the
zero-extended, shifted, and or-ed bytes, structured to match the exact association the machine
produces (`low32 = a4|||a3`, `high32 = a6|||a5`, lane `= (high32 <<< 32) ||| low32`). -/

theorem assemble_leWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((zero_extend (m := 64) b7 <<< 24 ||| zero_extend (m := 64) b6 <<< 16) |||
        (zero_extend (m := 64) b5 <<< 8 ||| zero_extend (m := 64) b4)) <<< 32) |||
      ((zero_extend (m := 64) b3 <<< 24 ||| zero_extend (m := 64) b2 <<< 16) |||
        (zero_extend (m := 64) b1 <<< 8 ||| zero_extend (m := 64) b0)))
      = BitVec.cast (by rfl) (leWord [b0, b1, b2, b3, b4, b5, b6, b7]) := by
  simp only [leWord, List.length_cons, List.length_nil, zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

/-- Concrete shift-by-8. -/
theorem slli_amt8 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (8#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 8 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-- Concrete shift-by-16. -/
theorem slli_amt16 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (16#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 16 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-- Concrete shift-by-24. -/
theorem slli_amt24 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (24#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 24 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

/-- Concrete shift-by-32. -/
theorem slli_amt32 (x : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (32#6)
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0) = x <<< 32 := by
  have hhi : (LeanRV64DExecutable.Functions.log2_xlen -i 1) = 5 := rfl
  rw [hhi]; unfold Sail.shift_bits_left Sail.BitVec.extractLsb; bv_decide

end BinaryFv.Keccak.XorBlock
