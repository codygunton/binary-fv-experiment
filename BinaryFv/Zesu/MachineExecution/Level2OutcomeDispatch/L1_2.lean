import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps

/-!
# Level 2 result-tag dispatch

The wrapper owns the instructions after either inlined `decode` segment reaches `0x103fc`.
These Sail proofs distinguish the internal result tags before entering the shared wrapper tail.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem wrapper_dispatch_branch_not_taken_step {machineArgs : DecoderMachineArgs}
    {base state : State} (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc)
    (atPc : state.regs.get? PC = some pc) (byte0 byte1 byte2 byte3 : BitVec 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (imm, rs2, rs1, op)))
    (condition : Runs (bTypeTaken rs2 rs1 op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) false) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        (Sail.BitVec.addInt pc 4) retired) false := by
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree pc atPc pcIn
    byte0 byte1 byte2 byte3 fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  refine ⟨retired, ?_⟩
  exact tryStepBranchNotTakenRetires stepNo state pc retired imm rs2 rs1 op inhibit config
    byte0 byte1 byte2 byte3 fetch noMMIO fetched interrupts baseEncoding decode notExpected condition
    hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

theorem wrapper_dispatch_branch_taken_step {machineArgs : DecoderMachineArgs}
    {base state : State} (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc target : BitVec 64) (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop)
    (pcIn : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw) pc)
    (atPc : state.regs.get? PC = some pc) (byte0 byte1 byte2 byte3 : BitVec 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (imm, rs2, rs1, op)))
    (condition : Runs (bTypeTaken rs2 rs1 op)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) true)
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
  simpa [targetEq] using tryStepBranchTakenRetires stepNo state pc pc retired imm rs2 rs1 op
    inhibit config byte0 byte1 byte2 byte3 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts baseEncoding decode notExpected condition
    (readReg_run executeState PC _ pcRead) align0 align1 zca hartRead inhibitRead configRead
    notInhibited machineEnabled retiredRead

/-- The first dispatch instruction writes the tag-three comparison constant. -/
theorem wrapper_dispatch_tag3_constant_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103fc) retired x11 (BitVec.ofNat 64 3)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x103fc) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x103fc) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x103fc) 0x93#8 0x05#8 0x30#8 0x00#8 :=
    fetchFileInstruction state 0x103fc 0x93 0x05 0x30 0x00
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
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x30#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00300593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103fc)
  have execute : Runs (execute (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 3) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x003#12 (0#64) = BitVec.ofNat 64 3 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x003#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 3))
  exact decoderRegisterWriteStep machine agree retiredPresent stepNo (BitVec.ofNat 64 0x103fc)
    fetchPc atPc 0x93#8 0x05#8 0x30#8 0x00#8
    (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) x11 (BitVec.ofNat 64 3)
    fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    (by decide) (by decide) (by decide) (by decide) execute

/-- Exact post-state of the tag-three branch at `0x10400`. -/
def wrapperDispatchTag3BranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434))
    (BitVec.ofNat 64 0x10434) retired

theorem wrapperDispatchBranchNotTakenAfter_agree (state : State) (pc retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        (Sail.BitVec.addInt pc 4) retired) := by
  intro register preserved
  have notRetired : minstret ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notPc : PC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
    notNextPc, notIncrement]

theorem wrapperDispatchJumpAfter_agree (state : State) (pc target retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) := by
  intro register preserved
  have notRetired : minstret ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notPc : PC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notNextPc : nextPC ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  have notIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    simp [platformPreserved] at preserved
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notRetired, notPc, notNextPc, notIncrement]

end BinaryFv.Zesu.MachineExecution
