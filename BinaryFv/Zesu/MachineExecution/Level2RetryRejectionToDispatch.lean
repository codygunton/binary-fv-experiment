import BinaryFv.Zesu.MachineExecution.Seg
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
    fetchInstruction state 0x10420 0x13 0x05 0x00 0x00
      (hasExactErePrefix_programImage_of_codeIntact code)
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
    fetchInstruction state 0x10424 0x6f 0xf0 0x9f 0xf3
      (hasExactErePrefix_programImage_of_codeIntact code)
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

/-- The write set of the whole rejection tail: the `try_step` bookkeeping every retirement performs,
plus the single architectural register the `addi` targets. Fixed once for both steps -- see
`WritesOnlyRegs.trans_same` on why the set must not grow per instruction. -/
@[reducible] private def retryRejectionWrites : RegSet :=
  RegSet.union stepBookkeeping (RegSet.only x10)

/-- Retire the common rejection tail from `0x10420` to the status store at `0x1035c`.

Both instructions are composed through `Seg`, so no post-state of either is ever named: each
combinator hands back an opaque successor, and every clause of the result structure is a field
read or a one-line membership check against `retryRejectionWrites`. -/
theorem retry_rejection_to_status_store {machineArgs : DecoderMachineArgs} {base before : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base before) (retired : RetiredCounterPresent before)
    (code : canonicalContractParams.env.CodeIntact before) (fromStep : Nat)
    (atPc : before.regs.get? PC = some (BitVec.ofNat 64 0x10420)) :
    ∃ after, RetryRejectionToStatusStore base before after machineArgs fromStep := by
  have bookkeeping : ∀ r, stepBookkeeping r → retryRejectionWrites r := fun _ h => Or.inl h
  have disjoint : RegSet.Disjoint platformPreserved retryRejectionWrites :=
    platformPreserved_disjoint.union (RegSet.Disjoint.only (by simp [platformPreserved]))
  have codeOf : ∀ {s : State}, s.mem = before.mem → canonicalContractParams.env.CodeIntact s :=
    fun memory => by rw [DecoderEnvironment.CodeIntact, memory]; exact code
  obtain ⟨_, seg⟩ :=
    (Seg.nil
        (functionInstanceExecutionPcs generatedProgram
          functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary retryRejectionWrites noMemory fromStep retired atPc).step
      (by
        apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide)
      (by
        simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
          functionInstance_raw_decoder_root_zesu_decode_raw])
      x10 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0x10424)
      (retry_rejection_clear_result_step machine agree retired code fromStep atPc)
      (by decide) bookkeeping (Or.inr rfl) (by decide) (by decide) (by decide)
  obtain ⟨after, seg⟩ :=
    seg.stepJump (BitVec.ofNat 64 0x1035c)
      (by
        apply functionInstanceExecutionPcs_iff_ranges.mpr
        apply RegionPcs.iff_inRanges.mpr
        native_decide)
      (by
        simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
          functionInstance_raw_decoder_root_zesu_decode_raw])
      (retry_rejection_to_rejection_step machine (agree.trans (seg.agree disjoint)) seg.retired
        (codeOf (seg.memEq noMemory_empty)) (fromStep + 1) seg.atPc)
      bookkeeping (by decide)
  exact ⟨after,
    { trace := seg.trace
      confined := seg.confined
      atStatusStore := seg.atPc
      resultValue := seg.reg x10 (BitVec.ofNat 64 0) (by simp)
      statusValue := seg.get x11 (by decide)
      platform := agree.trans (seg.agree disjoint)
      retired := seg.retired
      code := codeOf (seg.memEq noMemory_empty)
      memory := seg.memEq noMemory_empty
      stackValue := seg.get x2 (by decide)
      globalsValue := seg.get x18 (by decide) }⟩

end BinaryFv.Zesu.MachineExecution
