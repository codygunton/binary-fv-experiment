import BinaryFv.Zesu.MachineExecution.Level2OutcomeEpilogue

/-! Concrete wrapper saved-register load addresses derived from the entered stack frame. -/
namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register

private def restoreAddressFacts (args : ZesuDecodeRawArgs) (stackBase offset : Nat)
    (machine : ZesuDecodeRawMachinePre args stackBase entry) (offsetEnd : offset + 8 ≤ 0xa20)
    (offsetAligned : offset % 8 = 0) :
    { address : BitVec 64 // stackBase + offset = address.toNat ∧
      is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true ∧
      DecoderAccessRange (DecoderReadableByte (zesuDecodeRawMachineArgs args)) address 8 } := by
  let address := BitVec.ofNat 64 (stackBase + offset)
  have wordSize : 2 ^ 64 = 18446744073709551616 := by native_decide
  have frameFits := machine.stackFrameFits
  rw [wordSize] at frameFits
  have addressNat : address.toNat = stackBase + offset := by
    change (BitVec.ofNat 64 (stackBase + offset)).toNat = stackBase + offset
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨address, addressNat.symm, ?_, ?_⟩
  · simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, addressNat]
    have aligned : (stackBase + offset) % 8 = 0 := by
      have stackAligned := machine.stackAligned
      omega
    simp [Int.tmod, aligned]
  · rw [DecoderAccessRange, addressNat]
    refine ⟨by decide, by omega, ?_⟩
    intro index bound
    right; right; left
    simpa [Nat.add_assoc] using
      machine.stackFrameWritable (offset + index) (by omega)

private theorem restoreAddressEq (stackBase : Nat) (upper lower offset : Nat)
    (upperValue : sign_extend (m := 64) (BitVec.ofNat 12 upper) = BitVec.ofNat 64 upper)
    (lowerValue : sign_extend (m := 64) (BitVec.ofNat 12 lower) = BitVec.ofNat 64 lower)
    (offsetEq : upper + lower = offset) :
    (BitVec.ofNat 64 stackBase + sign_extend (m := 64) (BitVec.ofNat 12 upper)) +
        sign_extend (m := 64) (BitVec.ofNat 12 lower) = BitVec.ofNat 64 (stackBase + offset) := by
  rw [upperValue, lowerValue, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

/-- The entered wrapper frame supplies all four concrete saved-register load addresses. -/
def wrapperRestoreAddresses_of_machinePre (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (entry : State) (machine : ZesuDecodeRawMachinePre args stackBase entry) :
    WrapperRestoreAddresses (zesuDecodeRawMachineArgs args) (BitVec.ofNat 64 stackBase) := by
  let ra := restoreAddressFacts args stackBase 0xa18 machine (by omega) (by decide)
  let s0 := restoreAddressFacts args stackBase 0xa10 machine (by omega) (by decide)
  let s1 := restoreAddressFacts args stackBase 0xa08 machine (by omega) (by decide)
  let s2 := restoreAddressFacts args stackBase 0xa00 machine (by omega) (by decide)
  have stackNat : (BitVec.ofNat 64 stackBase).toNat = stackBase := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have frameFits := machine.stackFrameFits
      omega)]
  refine ⟨ra.val, s0.val, s1.val, s2.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ra.property.2.1,
    s0.property.2.1, s1.property.2.1,
    s2.property.2.1, ra.property.2.2, s0.property.2.2, s1.property.2.2, s2.property.2.2⟩
  · simpa [← ra.property.1] using restoreAddressEq stackBase 0x230 0x7e8 0xa18
      (by decide) (by decide) (by decide)
  · simpa [← s0.property.1] using restoreAddressEq stackBase 0x230 0x7e0 0xa10
      (by decide) (by decide) (by decide)
  · simpa [← s1.property.1] using restoreAddressEq stackBase 0x230 0x7d8 0xa08
      (by decide) (by decide) (by decide)
  · simpa [← s2.property.1] using restoreAddressEq stackBase 0x230 0x7d0 0xa00
      (by decide) (by decide) (by decide)
  · simpa [stackNat] using ra.property.1
  · simpa [stackNat] using s0.property.1
  · simpa [stackNat] using s1.property.1
  · simpa [stackNat] using s2.property.1

/-- The two emitted stack additions restore the wrapper's entered stack pointer. -/
theorem wrapper_final_stack_address (stackBase : Nat) :
    (BitVec.ofNat 64 stackBase + sign_extend (m := 64) (0x230#12)) +
        sign_extend (m := 64) (0x7f0#12) = BitVec.ofNat 64 (stackBase + 0xa20) := by
  simpa using restoreAddressEq stackBase 0x230 0x7f0 0xa20 (by decide) (by decide) (by decide)

end BinaryFv.Zesu.MachineExecution
