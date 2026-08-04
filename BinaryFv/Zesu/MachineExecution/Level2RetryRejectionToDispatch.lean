import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2WrapperProof

/-!
# Retry rejection handoff to wrapper dispatch

Both retry rejection exits converge at `0x10420`.  This module executes the two
wrapper-owned instructions there: `addi a0, zero, 0` and `jal zero, 0x1035c`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem retry_rejection_constant_step {machineArgs : DecoderMachineArgs}
    {base state : State} {destination : Register} {value : RegisterType destination}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64)
    (pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc)
    (atPc : state.regs.get? PC = some pc) (byte0 byte1 byte2 byte3 : BitVec 8)
    (inst : instruction) (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (execute : Runs (execute inst) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          destination value }
      (.Retire_Success ())) (baseEncoding : BaseInstructionEncoding byte0)
    (destinationNotNextPc : destination ≠ nextPC) (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state pc retired destination value) false :=
  decoderRegisterWriteStep machine agree retiredPresent stepNo pc pcIn atPc
    byte0 byte1 byte2 byte3 inst destination value fetchBytes
    baseEncoding decode destinationNotNextPc destinationNotHart destinationNotIncrement
    destinationNotRetired execute

private theorem retry_rejection_jump_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc target : BitVec 64) (imm : BitVec 21)
    (pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc)
    (atPc : state.regs.get? PC = some pc) (byte0 byte1 byte2 byte3 : BitVec 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) (.JAL (imm, zreg)))
    (targetEq : pc + sign_extend (m := 64) imm = target)
    (targetAligned0 : Sail.BitVec.access target 0 = 0#1)
    (targetAligned1 : Sail.BitVec.access target 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) false := by
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree pc atPc pcIn
    byte0 byte1 byte2 byte3 fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc
  have linkRead : executeState.regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
    simp [executeState, coreControlFlowNextState]
  have pcRead : executeState.regs.get? PC = some pc := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, atPc]
  obtain ⟨misaBits, misaBaseRead, -⟩ : ∃ misaBits,
      base.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : base.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have misaRead : state.regs.get? misa = some misaBits :=
    (agree misa (by simp [platformPreserved])).trans misaBaseRead
  have zca := currentlyEnabledZca_run_atStepPremise state pc misaBits misaRead
  have align0 : Sail.BitVec.access (pc + sign_extend (m := 64) imm) 0 = 0#1 := by
    rw [targetEq]
    exact targetAligned0
  have align1 : Sail.BitVec.access (pc + sign_extend (m := 64) imm) 1 = 0#1 := by
    rw [targetEq]
    exact targetAligned1
  refine ⟨retired, ?_⟩
  simpa [targetEq] using tryStepJRetires stepNo state pc pc retired imm inhibit config
    byte0 byte1 byte2 byte3 (Sail.BitVec.addInt pc 4) (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts baseEncoding decode notExpected
    (get_next_pc_run executeState _ linkRead) (readReg_run executeState PC _ pcRead)
    align0 align1 zca hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

/-- `addi a0, zero, 0` at the common retry-rejection entry. -/
theorem retry_rejection_clear_result_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10420)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10420) retired x10 (BitVec.ofNat 64 0)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10420) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10420) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10420) 0x13#8 0x05#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10420 0x13 0x05 0x00 0x00
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have afterIncrementAgree : Agree platformPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (agree_afterIncrement state)
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [platformPreserved])).trans machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits :=
    (afterIncrementAgree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x13#8 0x05#8 0x00#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by
    change Runs (ext_decode (0x00000513 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10420)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact retry_rejection_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10420) fetchPc atPc 0x13#8 0x05#8 0x00#8 0x00#8
    (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- `jal zero, 0x1035c` joins the shared rejection continuation. -/
theorem retry_rejection_to_rejection_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10424)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10424) (BitVec.ofNat 64 0x1035c))
        (BitVec.ofNat 64 0x1035c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10424) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10424) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10424) 0x6f#8 0xf0#8 0x9f#8 0xf3#8 :=
    fetchFileInstruction state 0x10424 0x6f 0xf0 0x9f 0xf3
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  have afterIncrementAgree : Agree platformPreserved base (tryStepControlFlowAfterIncrement state) :=
    agree.trans (agree_afterIncrement state)
  have privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege =
      some Privilege.Machine :=
    (afterIncrementAgree cur_privilege (by simp [platformPreserved])).trans machine.normal.2.1
  obtain ⟨mseccfgBits, mseccfgRead, -⟩ := machine.mseccfg
  have mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? mseccfg = some mseccfgBits :=
    (afterIncrementAgree mseccfg (by simp [platformPreserved])).trans mseccfgRead
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x9f#8 0xf3#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff38#21, zreg)) := by
    change Runs (ext_decode (0xf39ff06f : BitVec 32)) _ _ _
    decode_run
  have targetEq : BitVec.ofNat 64 0x10424 + sign_extend (m := 64) (0x1fff38#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact retry_rejection_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10424) (BitVec.ofNat 64 0x1035c) (0x1fff38#21) fetchPc atPc
    0x6f#8 0xf0#8 0x9f#8 0xf3#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    targetEq (by decide) (by decide)

/-- The two common retry-rejection instructions, ending at the shared status store. -/
structure RetryRejectionToStatusStore (base before after : State) (machineArgs : DecoderMachineArgs)
    (fromStep : Nat) : Prop where
  trace : Trace fromStep 2 before after
  confined : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep 2 before after
  atStatusStore : after.regs.get? PC = some (BitVec.ofNat 64 0x1035c)
  resultValue : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  statusValue : after.regs.get? x11 = before.regs.get? x11
  platform : Agree platformPreserved base after
  retired : RetiredCounterPresent after
  code : canonicalContractParams.env.CodeIntact after
  memory : after.mem = before.mem
  stackValue : after.regs.get? x2 = before.regs.get? x2
  globalsValue : after.regs.get? x18 = before.regs.get? x18

/-- Retire the common rejection tail from `0x10420` to the status store at `0x1035c`. -/
theorem retry_rejection_to_status_store {machineArgs : DecoderMachineArgs} {base before : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base before) (retired : RetiredCounterPresent before)
    (code : canonicalContractParams.env.CodeIntact before) (fromStep : Nat)
    (atPc : before.regs.get? PC = some (BitVec.ofNat 64 0x10420)) :
    ∃ after, RetryRejectionToStatusStore base before after machineArgs fromStep := by
  obtain ⟨r1, h1⟩ := retry_rejection_clear_result_step machine agree retired code fromStep atPc
  let s1 := afterRegisterWrite before (BitVec.ofNat 64 0x10420) r1 x10 (BitVec.ofNat 64 0)
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10424) := by
    simpa [s1] using afterRegisterWrite_pc before (BitVec.ofNat 64 0x10420) r1 x10
      (BitVec.ofNat 64 0)
  have agree1 : Agree platformPreserved base s1 :=
    agree.trans (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 : RetiredCounterPresent s1 :=
    afterRegisterWrite_retired_present before (BitVec.ofNat 64 0x10420) r1 x10 (BitVec.ofNat 64 0)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
  obtain ⟨r2, h2⟩ := retry_rejection_to_rejection_step machine agree1 retired1 code1
    (fromStep + 1) pc1
  let after := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s1)
      (BitVec.ofNat 64 0x10424) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r2
  have prefix1 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 1 before s1 :=
    ConfinedPrefix.ownStep atPc (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s1] using h1)
  have prefix2 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (fromStep + 1) 1 s1 after :=
    ConfinedPrefix.ownStep pc1 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [after] using h2)
  refine ⟨after, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [s1, after, Nat.add_assoc] using
      Trace.step fromStep 1 before s1 after (by simpa [s1] using h1)
        (Trace.one (fromStep + 1) s1 after (by simpa [after] using h2))
  · simpa [Nat.add_assoc] using ConfinedPrefix.trans prefix1 prefix2
  · simp [after, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [after, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [after, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · intro register preserved
    have notDestination : x10 ≠ register := by
      intro equal; subst register; simp [platformPreserved] at preserved
    have notPc : PC ≠ register := by intro equal; subst register; simp [platformPreserved] at preserved
    have notNextPc : nextPC ≠ register := by
      intro equal; subst register; simp [platformPreserved] at preserved
    have notIncrement : minstret_increment ≠ register := by
      intro equal; subst register; simp [platformPreserved] at preserved
    have notRetired : minstret ≠ register := by
      intro equal; subst register; simp [platformPreserved] at preserved
    simpa [after, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notPc, notNextPc,
      notIncrement, notRetired, notDestination] using agree register preserved
  · refine ⟨Sail.BitVec.addInt r2 1, ?_⟩
    simp [after, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
  · rw [DecoderEnvironment.CodeIntact]
    simp [after, s1, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement]
    exact code
  · simp [after, s1, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement]
  · simp [after, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [after, s1, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
