import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Exact r7 execution-witness result stores

The pinned production ELF has the six `sd` words below.  This module records their literal
addresses, encodings, source register and stack offset for the succeeding Sail corridor proof. -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register RegisterWriteStep

structure Level4ExecutionWitnessResultStore where
  pc : Nat
  word : UInt32
  source : Register
  offset : Nat

def level4ExecutionWitnessResultStores : List Level4ExecutionWitnessResultStore :=
  [ { pc := 0x12924, word := 0x59613023, source := x22, offset := 0x580 }
  , { pc := 0x12928, word := 0x59513423, source := x21, offset := 0x588 }
  , { pc := 0x1292c, word := 0x59813823, source := x24, offset := 0x590 }
  , { pc := 0x12930, word := 0x59713c23, source := x23, offset := 0x598 }
  , { pc := 0x12944, word := 0x5aa13023, source := x10, offset := 0x5a0 }
  , { pc := 0x12948, word := 0x5ab13423, source := x11, offset := 0x5a8 } ]

theorem level4ExecutionWitnessResultStores_exact :
    level4ExecutionWitnessResultStores.length = 6 := by native_decide

/-- The first r7 descriptor write is the literal production `sd s6,0x580(sp)`.  The caller
supplies the frame-derived writable range and alignment; Sail supplies fetch/decode/execute/retire. -/
theorem level4_executionWitness_store_state_base {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo postStack : Nat)
    {stateBase : BitVec 64}
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12924))
    (sp : state.regs.get? x2 = some (BitVec.ofNat 64 postStack))
    (value : state.regs.get? x22 = some stateBase)
    (targetEq : BitVec.ofNat 64 postStack + sign_extend (m := 64) 0x580#12 =
      BitVec.ofNat 64 (postStack + 0x580))
    (fits : postStack + 0x580 < 2 ^ 64)
    (allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (postStack + 0x580)) 8)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (postStack + 0x580))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x12924) stepRetired (postStack + 0x580)
        (width := 8) stateBase) false := by
  have targetToNat : (BitVec.ofNat 64 (postStack + 0x580)).toNat = postStack + 0x580 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact fits
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x12924 0x23 0x30 0x61 0x59 0x580#12 22#5 2#5 (BitVec.ofNat 64 postStack) stateBase
    (BitVec.ofNat 64 (postStack + 0x580)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? sp))
    (rX_x22_run _ _ (decoderExecuteState_get? value)) targetEq allowed
    ⟨by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- The second r7 descriptor write is the literal production `sd s5,0x588(sp)`. -/
theorem level4_executionWitness_store_state_length {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo postStack : Nat)
    {stateLength : BitVec 64}
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12928))
    (sp : state.regs.get? x2 = some (BitVec.ofNat 64 postStack))
    (value : state.regs.get? x21 = some stateLength)
    (targetEq : BitVec.ofNat 64 postStack + sign_extend (m := 64) 0x588#12 = BitVec.ofNat 64 (postStack + 0x588))
    (fits : postStack + 0x588 < 2 ^ 64)
    (allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (postStack + 0x588)) 8)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (postStack + 0x588))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x12928) stepRetired (postStack + 0x588)
        (width := 8) stateLength) false := by
  have targetToNat : (BitVec.ofNat 64 (postStack + 0x588)).toNat = postStack + 0x588 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact fits
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x12928 0x23 0x34 0x51 0x59 0x588#12 21#5 2#5 (BitVec.ofNat 64 postStack) stateLength
    (BitVec.ofNat 64 (postStack + 0x588)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? sp))
    (rX_x21_run _ _ (decoderExecuteState_get? value)) targetEq allowed
    ⟨by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide, by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

end BinaryFv.Zesu.MachineExecution
