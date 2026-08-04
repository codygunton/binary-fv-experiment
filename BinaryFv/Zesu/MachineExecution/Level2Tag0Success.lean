import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep

/-!
# Tag-zero stored-result continuation

The zero-result route reaches `0x1033c`. This module executes the wrapper instructions that copy
the successful result into `raw_decoder_root.stored_result` before the common status-store entry.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Execute `addi a0, s2, 16` at `0x1033c`, selecting the 832-byte `stored_result` payload. -/
theorem tag0_stored_result_destination_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1033c))
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) retired x10
        (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 0x4215020))) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1033c) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1033c) 0x13#8 0x05#8 0x09#8 0x01#8 :=
    fetchFileInstruction state 0x1033c 0x13 0x05 0x09 0x01 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x1033c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x05#8 0x09#8 0x01#8 = (0x01090513 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x09#8 0x01#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x010#12, .Regidx 18#5, .Regidx 10#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1033c)
  have globalsAtExecute : executeState.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, globals]
  let result := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 0x4215020)
  have execute : Runs (execute (.ITYPE (0x010#12, .Regidx 18#5, .Regidx 10#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x10 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x010#12 (.Regidx 18#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x010#12 (.Regidx 18#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 0x4215020) (rX_bits_run_x18 executeState _ globalsAtExecute)
      (wX_x10_run executeState result)
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1033c) pcIn atPc 0x13#8 0x05#8 0x09#8 0x01#8
    (.ITYPE (0x010#12, .Regidx 18#5, .Regidx 10#5, .ADDI)) x10 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `addi a1, sp, 32` at `0x10340`, selecting the stack-resident result bytes. -/
theorem tag0_stored_result_source_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10340))
    (stack : BitVec 64) (stackRead : state.regs.get? x2 = some stack) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10340) retired x11
        (iTypeResult .ADDI 0x020#12 stack)) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10340) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10340) 0x93#8 0x05#8 0x01#8 0x02#8 :=
    fetchFileInstruction state 0x10340 0x93 0x05 0x01 0x02 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x10340) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x93#8 0x05#8 0x01#8 0x02#8 = (0x02010593 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x01#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10340)
  have stackAtExecute : executeState.regs.get? x2 = some stack := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, stackRead]
  let result := iTypeResult .ADDI 0x020#12 stack
  have execute : Runs (execute (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 11#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x11 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x020#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x020#12 (.Regidx 2#5) (.Regidx 11#5) .ADDI
      stack (rX_bits_run_x2 executeState _ stackAtExecute) (wX_x11_run executeState result)
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10340) pcIn atPc 0x93#8 0x05#8 0x01#8 0x02#8
    (.ITYPE (0x020#12, .Regidx 2#5, .Regidx 11#5, .ADDI)) x11 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

end BinaryFv.Zesu.MachineExecution
