import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.MemcpyInstance
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge

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
set_option maxHeartbeats 4000000

/-- Facts at `0x1033c` required to execute the tag-zero stored-result copy.  The eventual Level 2
capstone must derive this record from the wrapper prologue and the selected `decode` success result;
it is not an ABI assigned to the inlined decoder. -/
structure Tag0StoredResultCopyPre (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry state : State)
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64) : Prop where
  machineEntry : ZesuDecodeRawMachinePre args stackBase entry
  atCopyStart : state.regs.get? PC = some (BitVec.ofNat 64 0x1033c)
  machine : DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (zesuDecodeRawMachineArgs args) state
  retired : RetiredCounterPresent state
  code : canonicalContractParams.env.CodeIntact state
  stack : state.regs.get? x2 = some (BitVec.ofNat 64 stackBase)
  globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)
  savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 state
  sourceBytes : MemoryRepresentation.MemoryBytes state (stackBase + 32) contents
  contentsSize : contents.size = 832

/-- The tag-zero stored-result copy, with its four wrapper-owned setup instructions and the emitted
`memcpy` call kept as a composable Level 2 prefix.  The prefix stops at `0x10350`, which is not
claimed to be a wrapper exit; a later theorem supplies the following owned instructions. -/
structure Tag0StoredResultCopyPhase (args : ZesuDecodeRawArgs) (stackBase : Nat) (entry state : State)
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64) (fromStep used : Nat)
    (callState resumed : State) : Prop where
  setup : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep 4 state callState
  transfer : Nonempty (CallTransfer
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary memcpyStoredResult generatedProgram
    functionInstance_raw_decoder_root_zesu_decode_raw functionInstance_memcpy
    (fromStep + 4) used callState resumed)
  scopedPrefix : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep (6 + used) state resumed
  trace : Trace fromStep (6 + used) state resumed
  atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10350)
  savedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 resumed
  destinationBytes : MemoryRepresentation.MemoryBytes resumed 0x4215030 contents
  code : canonicalContractParams.env.CodeIntact resumed
  retired : RetiredCounterPresent resumed
  stack : resumed.regs.get? x2 = some (BitVec.ofNat 64 stackBase)
  globals : resumed.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)

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

/-- Execute `addi a2, x0, 832` at `0x10344`. -/
theorem tag0_stored_result_length_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10344)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10344) retired x12
        (iTypeResult .ADDI 0x340#12 (0#64))) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10344) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10344) 0x13#8 0x06#8 0x00#8 0x34#8 :=
    fetchFileInstruction state 0x10344 0x13 0x06 0x00 0x34 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x10344) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x13#8 0x06#8 0x00#8 0x34#8 = (0x34000613 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x06#8 0x00#8 0x34#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10344)
  let result := iTypeResult .ADDI 0x340#12 (0#64)
  have execute : Runs (execute (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)))
      executeState { executeState with regs := executeState.regs.insert x12 result }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    exact execute_ITYPE_run executeState _ 0x340#12 (.Regidx 0#5) (.Regidx 12#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x12_run executeState result)
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10344) pcIn atPc 0x13#8 0x06#8 0x00#8 0x34#8
    (.ITYPE (0x340#12, .Regidx 0#5, .Regidx 12#5, .ADDI)) x12 result fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Execute `auipc ra, 4` at `0x10348`, establishing the real `memcpy` call base. -/
theorem tag0_stored_result_call_page_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10348)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10348) retired x1 (BitVec.ofNat 64 0x14348)) false := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10348) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image := hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10348) 0x97#8 0x40#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10348 0x97 0x40 0x00 0x00 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x10348) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  have wordEq : fetchWord 0x97#8 0x40#8 0x00#8 0x00#8 = (0x00004097 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x97#8 0x40#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10348)
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10348) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  have execute : Runs (execute (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC))) executeState
      { executeState with regs := executeState.regs.insert x1 (BitVec.ofNat 64 0x14348) }
      (.Retire_Success ()) := by
    apply execute_UTYPE_auipc_run executeState _ 0x00004#20 (.Regidx 1#5)
      (BitVec.ofNat 64 0x10348)
    · exact readReg_run _ _ _ pcAtExecute
    · simpa using wX_bits_run_x1 executeState (BitVec.ofNat 64 0x14348)
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10348) pcIn atPc 0x97#8 0x40#8 0x00#8 0x00#8
    (.UTYPE (0x00004#20, .Regidx 1#5, .AUIPC)) x1 (BitVec.ofNat 64 0x14348) fetchBytes
    (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- State immediately after the stored-result `jalr` at `0x1034c`. -/
def tag0StoredResultMemcpyCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8) x1
      (BitVec.ofNat 64 0x10350))
    (BitVec.ofNat 64 0x13eb8) retired

/-- Normalize the source setup instruction's modular RV64 result to the bounded stack address. -/
private theorem tag0_stored_result_source_value (stackBase : Nat) :
    iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 stackBase) =
      BitVec.ofNat 64 (stackBase + 32) := by
  rw [show BitVec.ofNat 64 (stackBase + 32) =
      BitVec.ofNat 64 stackBase + BitVec.ofNat 64 32 by rw [← BitVec.ofNat_add]]
  unfold iTypeResult
  rw [show sign_extend (0x020#12) = (0x20#64) by decide]

/-- Normalize the zero-register length setup instruction. -/
private theorem tag0_stored_result_length_value :
    iTypeResult .ADDI 0x340#12 (0#64) = BitVec.ofNat 64 832 := by decide

/-- Execute the actual stored-result `jalr x1, -0x490(x1)`.  Its arguments are the four values
established by the preceding wrapper instructions, rather than an ABI premise. -/
theorem tag0_stored_result_memcpy_call_step
    {args : ZesuDecodeRawArgs} {state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (zesuDecodeRawMachineArgs args) state)
    (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1034c))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x14348)) :
    ∃ retired,
      Runs (try_step stepNo false) state (tag0StoredResultMemcpyCallAfter state retired) false ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? PC = some (BitVec.ofNat 64 0x13eb8) ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x1 = some (BitVec.ofNat 64 0x10350) ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x10 = state.regs.get? x10 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x11 = state.regs.get? x11 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x12 = state.regs.get? x12 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x2 = state.regs.get? x2 ∧
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? x18 = state.regs.get? x18 ∧
      Agree decoderPreserved state (tag0StoredResultMemcpyCallAfter state retired) ∧
      (tag0StoredResultMemcpyCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (tag0StoredResultMemcpyCallAfter state retired) := by
  have pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1034c) := by
    refine ⟨?_, by native_decide⟩
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have image : Artifacts.programImage.fileBytesMatchMemory state.mem :=
    hasExactErePrefix_programImage_of_codeIntact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1034c) 0xe7#8 0x80#8 0x00#8 0xb7#8 :=
    fetchFileInstruction state 0x1034c 0xe7 0x80 0x00 0xb7 image
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine (Agree.refl state)
    (BitVec.ofNat 64 0x1034c) atPc pcIn _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, hartRead, inhibitRead, configRead, notInhibited,
    machineEnabled, retiredRead⟩ :=
    decoderStepCounters_of_decoderAgree machine.normal (Agree.refl state) retiredPresent
  have wordEq : fetchWord 0xe7#8 0x80#8 0x00#8 0xb7#8 = (0xb70080e7 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0xe7#8 0x80#8 0x00#8 0xb7#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JALR (0xb70#12, .Regidx 1#5, .Regidx 1#5)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1034c)
  have executeAgree : Agree decoderPreserved state executeState :=
    Agree.weaken (fun _ preserved => preserved.2)
      (agree_stepPremiseState state (BitVec.ofNat 64 0x1034c))
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    machine.landingPad executeState (.Regidx 1#5) trivial executeAgree
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x10350) := by
    change ((tryStepControlFlowAfterIncrement state).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x1034c) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some (BitVec.ofNat 64 0x14348) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, callBase]
  have targetEq : Sail.BitVec.update
      ((BitVec.ofNat 64 0x14348) + sign_extend (m := 64) (0xb70#12)) 0 0#1 =
      BitVec.ofNat 64 0x13eb8 := by decide
  have hwrite : Runs (wX_bits (.Regidx 1#5) (BitVec.ofNat 64 0x10350))
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8))
      (callLinkState (tryStepControlFlowAfterIncrement state)
        (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x13eb8) x1
        (BitVec.ofNat 64 0x10350)) () := wX_bits_run_x1 _ _
  obtain ⟨misaBits, misaRead, -⟩ : ∃ misaBits,
      state.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match h : state.regs.get? misa with
    | none => simp [h] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [h] using normalMisa⟩
  have misaState : state.regs.get? misa = some misaBits := misaRead
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x1034c)
    misaBits misaState
  have callRun := tryStepJalrCallRetires stepNo state
    (BitVec.ofNat 64 0x1034c) (BitVec.ofNat 64 0x14348) retired
    (BitVec.ofNat 64 0x10350) (0xb70#12) (.Regidx 1#5) (.Regidx 1#5) x1
    (BitVec.ofNat 64 0x10350) inhibit config 0xe7#8 0x80#8 0x00#8 0xb7#8
    (_get_Misa_C misaBits == 1#1)
    (by simpa [targetEq] using hwrite) (by decide) (by decide) (by decide) (by decide)
    fetch noMMIO fetchBytes interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected helpElp (get_next_pc_run executeState _ linkRead)
    (rX_bits_run_x1 executeState _ sourceRead) (by decide) zca hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead
  have run : Runs (try_step stepNo false) state (tag0StoredResultMemcpyCallAfter state retired) false := by
    simpa [tag0StoredResultMemcpyCallAfter, targetEq] using callRun
  have preserveGeneral (register : Register) (notLink : register ≠ x1)
      (notPc : register ≠ PC) (notNextPc : register ≠ nextPC)
      (notIncrement : register ≠ minstret_increment) (notRetired : register ≠ minstret) :
      (tag0StoredResultMemcpyCallAfter state retired).regs.get? register = state.regs.get? register := by
    have preserved := jalrCallAfterRetired_agree_of
      (P := fun candidate => candidate = register) state (BitVec.ofNat 64 0x1034c)
      (BitVec.ofNat 64 0x13eb8) retired x1 (BitVec.ofNat 64 0x10350)
      (Ne.symm notLink) (Ne.symm notPc) (Ne.symm notNextPc)
      (Ne.symm notIncrement) (Ne.symm notRetired)
    exact preserved register rfl
  refine ⟨retired, run, ?_, ?_, preserveGeneral x10 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x11 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x12 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x2 (by decide) (by decide) (by decide)
    (by decide) (by decide), preserveGeneral x18 (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  · simp [tag0StoredResultMemcpyCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x10350)
    · decide
    · decide
  · apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  · exact ⟨Sail.BitVec.addInt retired 1, by
      simp [tag0StoredResultMemcpyCallAfter, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick]⟩

/-- Compose the four wrapper-owned setup words into the real stored-result call boundary. -/
theorem tag0_stored_result_setup
    {args : ZesuDecodeRawArgs} {stackBase : Nat} {entry state : State}
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64)
    (pre : Tag0StoredResultCopyPre args stackBase entry state contents link savedS0 savedS1 savedS2)
    (fromStep : Nat) :
    ∃ r0 r1 r2 r3 callState,
      Trace fromStep 4 state callState ∧
      ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary fromStep 4 state callState ∧
      callState = afterRegisterWrite
        (afterRegisterWrite
          (afterRegisterWrite
            (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
              (BitVec.ofNat 64 0x4215030))
            (BitVec.ofNat 64 0x10340) r1 x11 (BitVec.ofNat 64 (stackBase + 32)))
          (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
        (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348) ∧
      callState.regs.get? PC = some (BitVec.ofNat 64 0x1034c) ∧
      callState.regs.get? x10 = some (BitVec.ofNat 64 0x4215030) ∧
      callState.regs.get? x11 = some (BitVec.ofNat 64 (stackBase + 32)) ∧
      callState.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      callState.regs.get? x1 = some (BitVec.ofNat 64 0x14348) ∧
      callState.regs.get? x2 = some (BitVec.ofNat 64 stackBase) ∧
      Agree decoderPreserved state callState ∧
      RetiredCounterPresent callState ∧
      canonicalContractParams.env.CodeIntact callState ∧
      WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 callState ∧
      MemoryRepresentation.MemoryBytes callState (stackBase + 32) contents := by
  obtain ⟨r0, h0⟩ := tag0_stored_result_destination_step pre.machine (Agree.refl state)
    pre.retired pre.code fromStep pre.atCopyStart pre.globals
  let s0 := afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10 (BitVec.ofNat 64 0x4215030)
  have a0 : Agree platformPreserved state s0 := (Agree.refl state).trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c0 : RetiredCounterPresent s0 := afterRegisterWrite_retired_present _ _ _ _ _
  have code0 : canonicalContractParams.env.CodeIntact s0 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact pre.code
  have pc0 : s0.regs.get? PC = some (BitVec.ofNat 64 0x10340) := by
    simpa [s0] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x1033c) r0 x10
      (BitVec.ofNat 64 0x4215030)
  have stack0 : s0.regs.get? x2 = some (BitVec.ofNat 64 stackBase) := by
    have stack0Preserved : s0.regs.get? x2 = state.regs.get? x2 := by
      simpa [s0] using
        (afterRegisterWrite_register state (BitVec.ofNat 64 0x1033c) r0 x10 x2
          (BitVec.ofNat 64 0x4215030) (by decide) (by decide) (by decide) (by decide) (by decide))
    exact stack0Preserved.trans pre.stack
  obtain ⟨r1, h1⟩ := tag0_stored_result_source_step pre.machine a0 c0 code0
    (fromStep + 1) pc0 _ stack0
  have sourceValue := tag0_stored_result_source_value stackBase
  rw [sourceValue] at h1
  let s1 := afterRegisterWrite s0 (BitVec.ofNat 64 0x10340) r1 x11
    (BitVec.ofNat 64 (stackBase + 32))
  have a1 : Agree platformPreserved state s1 := a0.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c1 : RetiredCounterPresent s1 := afterRegisterWrite_retired_present _ _ _ _ _
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact code0
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10344) := by
    simpa [s1] using afterRegisterWrite_pc s0 (BitVec.ofNat 64 0x10340) r1 x11
      (BitVec.ofNat 64 (stackBase + 32))
  obtain ⟨r2, h2⟩ := tag0_stored_result_length_step pre.machine a1 c1 code1
    (fromStep + 2) pc1
  rw [tag0_stored_result_length_value] at h2
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832)
  have a2 : Agree platformPreserved state s2 := a1.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have c2 : RetiredCounterPresent s2 := afterRegisterWrite_retired_present _ _ _ _ _
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10348) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x10344) r2 x12
      (BitVec.ofNat 64 832)
  obtain ⟨r3, h3⟩ := tag0_stored_result_call_page_step pre.machine a2 c2 code2
    (fromStep + 3) pc2
  let callState := afterRegisterWrite s2 (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348)
  have a2Decoder : Agree decoderPreserved state s2 := fun register preserved =>
    a2 register preserved.2
  have a3 : Agree decoderPreserved state callState := a2Decoder.trans
    (afterRegisterWrite_agree_of (P := decoderPreserved)
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]))
  have c3 : RetiredCounterPresent callState := afterRegisterWrite_retired_present _ _ _ _ _
  have code3 : canonicalContractParams.env.CodeIntact callState := by
    rw [DecoderEnvironment.CodeIntact, afterRegisterWrite_mem]
    exact code2
  refine ⟨r0, r1, r2, r3, callState, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, a3, c3, code3, ?_, ?_⟩
  · simpa [s0, s1, s2, callState, Nat.add_assoc] using
      Trace.append (Trace.one fromStep state s0 (by simpa [s0] using h0))
        (Trace.append (Trace.one (fromStep + 1) s0 s1 (by simpa [s1] using h1))
          (Trace.append (Trace.one (fromStep + 2) s1 s2 (by simpa [s2] using h2))
            (Trace.one (fromStep + 3) s2 callState (by simpa [callState] using h3))))
  · have p0In : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1033c) := by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    have p1In : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10340) := by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    have p2In : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10344) := by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    have p3In : functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10348) := by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide
    have p0NotExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
        (BitVec.ofNat 64 0x1033c) := by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    have p1NotExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
        (BitVec.ofNat 64 0x10340) := by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    have p2NotExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
        (BitVec.ofNat 64 0x10344) := by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    have p3NotExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
        (BitVec.ofNat 64 0x10348) := by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]
    have first := ConfinedPrefix.ownStep (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (exit := functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      (childSummary := Level2ChildSummary) (a := fromStep) (s := state) (s' := s0)
      (pc := BitVec.ofNat 64 0x1033c) pre.atCopyStart p0In p0NotExit
      (by simpa [s0] using h0)
    have second := ConfinedPrefix.ownStep (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (exit := functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      (childSummary := Level2ChildSummary) (a := fromStep + 1) (s := s0) (s' := s1)
      (pc := BitVec.ofNat 64 0x10340) pc0 p1In p1NotExit
      (by simpa [s1] using h1)
    have third := ConfinedPrefix.ownStep (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (exit := functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      (childSummary := Level2ChildSummary) (a := fromStep + 2) (s := s1) (s' := s2)
      (pc := BitVec.ofNat 64 0x10344) pc1 p2In p2NotExit
      (by simpa [s2] using h2)
    have fourth := ConfinedPrefix.ownStep (own := functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (exit := functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      (childSummary := Level2ChildSummary) (a := fromStep + 3) (s := s2) (s' := callState)
      (pc := BitVec.ofNat 64 0x10348) pc2 p3In p3NotExit
      (by simpa [callState] using h3)
    have paired := ConfinedPrefix.trans first second
    have triple := ConfinedPrefix.trans paired third
    have complete := ConfinedPrefix.trans triple fourth
    simpa [Nat.add_assoc] using complete
  · simpa [callState] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10348) r3 x1
      (BitVec.ofNat 64 0x14348)
  · simp [callState, s2, s1, s0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [callState, s2, s1, s0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [callState, s2, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [callState, s2, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [callState, s2, s1, s0, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, pre.stack]
  · apply WrapperSavedRegisterFrame.of_mem_eq pre.savedFrame
    simp [callState, s2, s1, s0, afterRegisterWrite_mem]
  · apply pre.sourceBytes.of_mem_eq
    simp [callState, s2, s1, s0, afterRegisterWrite_mem]

/-- The exact arguments carried by the tag-zero wrapper copy. -/
def tag0StoredResultCopyArgs (stackBase : Nat) (contents : ByteArray) : CopyArgs where
  destination := 0x4215030
  source := stackBase + 32
  length := 832
  contents := contents

/-- Turn the wrapper's typed stored-result boundary into the compiled `memcpy` machine entry.
The source is a proved stack payload and the destination is the checked private decoder BSS range. -/
theorem tag0_stored_result_memcpy_machine_pre
    {args : ZesuDecodeRawArgs} {stackBase : Nat} {entry state childEntry : State}
    (contents : ByteArray) (pre : Tag0StoredResultCopyPre args stackBase entry state
      contents link savedS0 savedS1 savedS2)
    (agree : Agree decoderPreserved state childEntry)
    (retired : RetiredCounterPresent childEntry)
    (atEntry : childEntry.regs.get? PC = some (BitVec.ofNat 64 0x13eb8))
    (returnAddress : childEntry.regs.get? x1 = some (BitVec.ofNat 64 0x10350)) :
    MemcpyMachinePre canonicalContractParams.env (tag0StoredResultCopyArgs stackBase contents) childEntry := by
  let copyArgs := tag0StoredResultCopyArgs stackBase contents
  let machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (zesuDecodeRawMachineArgs args) childEntry :=
    DecoderMachinePre.mono agree retired pre.machine
  have sourceFits : copyArgs.source + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, tag0StoredResultCopyArgs]
    have frameFits := pre.machineEntry.stackFrameFits
    omega
  have destinationFits : copyArgs.destination + copyArgs.length ≤ 2 ^ 64 := by
    dsimp [copyArgs, tag0StoredResultCopyArgs]
    decide
  have destinationNotFile : ∀ index, index < copyArgs.length →
      canonicalContractParams.env.image.readFileByte? (copyArgs.destination + index) = none := by
    intro index bound
    cases read : canonicalContractParams.env.image.readFileByte? (copyArgs.destination + index) with
    | none => rfl
    | some byte =>
      have fileBelow : copyArgs.destination + index < 86028 :=
        Entrypoints.ZesuDecodeRaw.file_addr_lt (by
          simpa [canonicalContractParams, canonicalEnvironment] using read)
      dsimp [copyArgs, tag0StoredResultCopyArgs] at bound fileBelow ⊢
      omega
  have destinationNotAllocator : ∀ address, canonicalContractParams.env.allocatorState address →
      address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address := by
    intro address allocator
    left
    unfold canonicalContractParams canonicalEnvironment at allocator
    unfold Elflings.canonicalAllocatorState at allocator
    rcases allocator with h | h <;>
      have heapPosBound : Elflings.canonicalHeapPosAddr + 8 ≤ Entrypoints.ZesuDecodeRaw.heapCeiling := by native_decide
    all_goals
      have heapTopBound : Elflings.canonicalHeapTopAddr + 8 ≤ Entrypoints.ZesuDecodeRaw.heapCeiling := by native_decide
      have globalBase : Entrypoints.ZesuDecodeRaw.heapCeiling ≤ 0x4215020 := by
        simpa using Entrypoints.ZesuDecodeRaw.arena_disjoint_from_globals
      dsimp [copyArgs, tag0StoredResultCopyArgs]
      omega
  have sourceReadable : ∀ index, index < copyArgs.length →
      DecoderReadableByte (zesuDecodeRawMachineArgs args) (copyArgs.source + index) := by
    intro index bound
    right; right; left
    dsimp [copyArgs, tag0StoredResultCopyArgs] at bound ⊢
    simpa [Nat.add_assoc] using
      pre.machineEntry.stackFrameWritable (32 + index) (by omega)
  have destinationWritable : ∀ index, index < copyArgs.length →
      DecoderWritableByte (copyArgs.destination + index) := by
    intro index bound
    right; left
    unfold DecoderGlobalsByte
    dsimp [copyArgs, tag0StoredResultCopyArgs] at bound ⊢
    have bssBase : Elflings.GeneratedDecoderGlobals.bssBase = 0x4215020 := by native_decide
    have bssSize : Elflings.GeneratedDecoderGlobals.bssSize = 864 := by native_decide
    omega
  apply memcpyMachinePre_of_decoder copyArgs childEntry machine
  · intro pc bodyPc
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    rcases bodyPc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide
  · exact atEntry
  · exact ⟨BitVec.ofNat 64 0x10350, returnAddress, by decide⟩
  · rfl
  · simp [copyArgs, tag0StoredResultCopyArgs]
  · dsimp [copyArgs, tag0StoredResultCopyArgs]
    have frameFits := pre.machineEntry.stackFrameFits
    omega
  · dsimp [copyArgs, tag0StoredResultCopyArgs]
    decide
  · exact sourceFits
  · exact destinationFits
  · exact destinationNotFile
  · exact destinationNotAllocator
  · exact sourceReadable
  · exact destinationWritable

/-- Execute the complete stored-result call phase: four wrapper setup words, the real `jalr`, the
proved emitted `memcpy` body, and its real `ret` to `0x10350`.  The returned frame and payload are
the exact facts consumed by the following three wrapper instructions. -/
theorem tag0_stored_result_copy_phase
    {args : ZesuDecodeRawArgs} {stackBase : Nat} {entry state : State}
    (contents : ByteArray) (link savedS0 savedS1 savedS2 : BitVec 64)
    (pre : Tag0StoredResultCopyPre args stackBase entry state contents link savedS0 savedS1 savedS2)
    (fromStep : Nat) :
    ∃ used callState resumed, Tag0StoredResultCopyPhase args stackBase entry state contents link savedS0
      savedS1 savedS2 fromStep used callState resumed := by
  obtain ⟨r0, r1, r2, r3, callState, setupTrace, setupPrefix, callStateEq, callPc, destination, source,
    length, callBase, stack, setupAgree, setupCounter, setupCode, setupFrame, setupSource⟩ :=
    tag0_stored_result_setup contents link savedS0 savedS1 savedS2 pre fromStep
  have callMachine := DecoderMachinePre.mono setupAgree setupCounter pre.machine
  subst callState
  obtain ⟨callRetired, callRun, childPc, childLink, childDestination, childSource, childLength,
    childStack, childGlobals, callAgree, callMemory, childCounter⟩ :=
    tag0_stored_result_memcpy_call_step callMachine setupCounter setupCode
      (fromStep + 4) callPc callBase
  let childEntry := tag0StoredResultMemcpyCallAfter
    (afterRegisterWrite
      (afterRegisterWrite
        (afterRegisterWrite
          (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
            (BitVec.ofNat 64 0x4215030))
          (BitVec.ofNat 64 0x10340) r1 x11
          (BitVec.ofNat 64 (stackBase + 32)))
        (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
      (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348)) callRetired
  let copyArgs := tag0StoredResultCopyArgs stackBase contents
  have childAgree : Agree decoderPreserved state childEntry := setupAgree.trans callAgree
  have childCode : canonicalContractParams.env.CodeIntact childEntry := by
    rw [DecoderEnvironment.CodeIntact, show childEntry.mem = state.mem by
      simpa [childEntry] using callMemory]
    exact pre.code
  have childSourceMemory : MemoryRepresentation.MemoryBytes childEntry (stackBase + 32) contents := by
    intro index bound
    rw [show childEntry.mem = state.mem by simpa [childEntry] using callMemory]
    exact pre.sourceBytes index bound
  have machinePre : MemcpyMachinePre canonicalContractParams.env copyArgs childEntry := by
    apply tag0_stored_result_memcpy_machine_pre contents pre childAgree childCounter
    · simpa [childEntry] using childPc
    · simpa [childEntry] using childLink
  have sourcePre : (contractMemcpy canonicalContractParams.env).pre copyArgs childEntry := by
    constructor
    · refine ⟨childSourceMemory, ?_, childCode, ?_, ?_, ?_⟩
      · simpa [copyArgs, tag0StoredResultCopyArgs] using pre.contentsSize
      · simpa [copyArgs, tag0StoredResultCopyArgs, childEntry] using childDestination.trans destination
      · simpa [copyArgs, tag0StoredResultCopyArgs, childEntry] using childSource.trans source
      · simpa [copyArgs, tag0StoredResultCopyArgs, childEntry] using childLength.trans length
    · left
      dsimp [copyArgs, tag0StoredResultCopyArgs]
      have separated := Entrypoints.ZesuDecodeRaw.wrapper_stack_after_stored_result pre.machineEntry
      omega
  have compiledEntry : (compiledMemcpyContract canonicalContractParams.env).binding.entry
      copyArgs childEntry := ⟨sourcePre, machinePre⟩
  obtain ⟨used, childExit, bound, childTrace, childPost⟩ :=
    compiledMemcpyInstanceContract_proved copyArgs (fromStep + 5) childEntry compiledEntry
  dsimp [copyArgs] at bound childTrace childPost compiledEntry
  obtain ⟨returnRetired, returnRun, resumePc⟩ :=
    memcpy_return_step (fromStep + 5 + used) (tag0StoredResultCopyArgs stackBase contents)
      (BitVec.ofNat 64 0x10350) childEntry childExit (by decide) (by decide) compiledEntry childTrace
      (by simpa [childEntry] using childLink) childPost
  have fullChildPost := childPost
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) := by
    obtain ⟨retPc, atRet, isExit⟩ := childTrace.trace.final_at_exit
    have retPcEq : retPc = BitVec.ofNat 64 0x13ec0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using isExit
    simpa [retPcEq] using atRet
  rcases childPost with ⟨sourcePost, machinePost⟩
  rcases sourcePost with ⟨exitCode, -, -, copyFrame, -, destinationMemory⟩
  let resumed := memcpyReturnAfter (BitVec.ofNat 64 0x10350) childExit returnRetired
  have callInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1034c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have returnInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10350) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have retInRegion : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x13ec0) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have callNotExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x1034c) := by
    simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  have retNotExit : ¬ functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw
      (BitVec.ofNat 64 0x13ec0) := by
    simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
      functionInstance_raw_decoder_root_zesu_decode_raw]
  have body : Level2ChildSummary functionInstance_memcpyId (fromStep + 5) used childEntry childExit :=
    .memcpy ⟨rfl, tag0StoredResultCopyArgs stackBase contents, compiledEntry, bound, childTrace,
      fullChildPost⟩
  have transfer : CallTransfer
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary memcpyStoredResult generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw functionInstance_memcpy
      (fromStep + 4) used _ resumed :=
    { valid := memcpyStoredResult_valid
      callPc := BitVec.ofNat 64 0x1034c
      atCall := callPc
      callSource := by decide
      callInRegion
      callNotExit
      sCall := childEntry
      doCall := by simpa [childEntry] using callRun
      calleeEntryPc := BitVec.ofNat 64 0x13eb8
      atCalleeEntry := machinePre.entry
      calleeEntryMatches := by decide
      sRet := childExit
      body
      retPc := BitVec.ofNat 64 0x13ec0
      atRet
      retInRegion
      retNotExit
      doReturn := by simpa [resumed, Nat.add_assoc] using returnRun
      returnPc := BitVec.ofNat 64 0x10350
      atResume := by simpa [resumed] using resumePc
      returnMatches := by decide
      resumeInRegion := returnInRegion }
  have callPrefix := ConfinedPrefix.ofCall transfer
  have scopedPrefix := ConfinedPrefix.trans setupPrefix callPrefix
  have resumedFrame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 resumed := by
    apply WrapperSavedRegisterFrame.of_mem_eq
      (WrapperSavedRegisterFrame.of_stored_result_copy pre.machineEntry setupFrame
        (tag0StoredResultCopyArgs stackBase contents) rfl rfl copyFrame)
    simp [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState]
  refine ⟨used,
    afterRegisterWrite
      (afterRegisterWrite
        (afterRegisterWrite
          (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
            (BitVec.ofNat 64 0x4215030))
          (BitVec.ofNat 64 0x10340) r1 x11 (BitVec.ofNat 64 (stackBase + 32)))
        (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
      (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348), resumed, ?_⟩
  refine ⟨setupPrefix, ⟨transfer⟩,
    by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using scopedPrefix,
    ?_, by simpa [resumed] using resumePc, resumedFrame, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.append setupTrace
      (Trace.append (Trace.one (fromStep + 4) _ childEntry (by simpa [childEntry] using callRun))
        (Trace.append childTrace.trace.toTrace
          (Trace.one (fromStep + 5 + used) childExit resumed returnRun)))
  · simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState] using destinationMemory
  · rw [DecoderEnvironment.CodeIntact]
    simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState] using exitCode
  · exact ⟨Sail.BitVec.addInt returnRetired 1, by
      simp [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick]⟩
  · have stable := machinePost.frame x2 (by simp [NonW])
    have childStackValue : childEntry.regs.get? x2 = some (BitVec.ofNat 64 stackBase) :=
      (childStack.trans stack)
    have exitStack := stable.trans childStackValue
    simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert] using exitStack
  · have stable := machinePost.frame x18 (by simp [NonW])
    have setupGlobals :
        (afterRegisterWrite
            (afterRegisterWrite
              (afterRegisterWrite
                (afterRegisterWrite state (BitVec.ofNat 64 0x1033c) r0 x10
                  (BitVec.ofNat 64 0x4215030))
                (BitVec.ofNat 64 0x10340) r1 x11 (BitVec.ofNat 64 (stackBase + 32)))
              (BitVec.ofNat 64 0x10344) r2 x12 (BitVec.ofNat 64 832))
            (BitVec.ofNat 64 0x10348) r3 x1 (BitVec.ofNat 64 0x14348)).regs.get? x18 =
          some (BitVec.ofNat 64 0x4215020) := by
      simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
        pre.globals]
    have childGlobalsValue : childEntry.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) :=
      childGlobals.trans setupGlobals
    have exitGlobals := stable.trans childGlobalsValue
    simpa [resumed, memcpyReturnAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, tryStepControlFlowAfterIncrement,
      coreControlFlowNextState, Std.ExtDHashMap.get?_insert] using exitGlobals

end BinaryFv.Zesu.MachineExecution
