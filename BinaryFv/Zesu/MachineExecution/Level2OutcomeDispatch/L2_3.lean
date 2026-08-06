import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_4
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_5
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_6
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_7
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_8
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_9

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

/-- A tag-three result takes the first comparison branch to its rejection tail. -/
theorem wrapper_dispatch_tag3_branch_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10400))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 3)) :
    ∃ retired, Runs (try_step stepNo false) state
      (wrapperDispatchTag3BranchAfter state retired) false ∧
      (wrapperDispatchTag3BranchAfter state retired).regs.get? PC = some (BitVec.ofNat 64 0x10434) := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10400) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10400) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10400) 0x63#8 0x0a#8 0xb5#8 0x02#8 :=
    fetchFileInstruction state 0x10400 0x63 0x0a 0xb5 0x02
      (hasExactErePrefix_programImage_of_codeIntact code)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x10400) atPc fetchPc _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x0a#8 0xb5#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x34#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    change Runs (ext_decode (0x02b50a63 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10400)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 3) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 3) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BEQ)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
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
  have zca := currentlyEnabledZca_run_atStepPremise state (BitVec.ofNat 64 0x10400)
    misaBits misaRead
  have run := tryStepBranchTakenRetires stepNo state (BitVec.ofNat 64 0x10400)
    (BitVec.ofNat 64 0x10400) retired (0x34#13) (.Regidx 11#5) (.Regidx 10#5) .BEQ
    inhibit config 0x63#8 0x0a#8 0xb5#8 0x02#8 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts (by unfold BaseInstructionEncoding; decide) decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperDispatchTag3BranchAfter] using run
  · simp [wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- Any non-three tag falls through the first comparison to `0x10404`. -/
theorem wrapper_dispatch_tag3_miss_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10400))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 tagValue))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 3))
    (notTag3 : BitVec.ofNat 64 tagValue ≠ BitVec.ofNat 64 3) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10400))
        (BitVec.ofNat 64 0x10404) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10400) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10400) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10400) 0x63#8 0x0a#8 0xb5#8 0x02#8 :=
    fetchFileInstruction state 0x10400 0x63 0x0a 0xb5 0x02
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
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x0a#8 0xb5#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x34#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    change Runs (ext_decode (0x02b50a63 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10400)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 3) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BEQ)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    have comparisonFalse : (BitVec.ofNat 64 tagValue == BitVec.ofNat 64 3) = false := by
      cases equal : (BitVec.ofNat 64 tagValue == BitVec.ofNat 64 3) with
      | false => rfl
      | true => exact False.elim (notTag3 (beq_iff_eq.mp equal))
    rw [comparisonFalse]
    rfl
  exact wrapper_dispatch_branch_not_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10400) (0x34#13) (.Regidx 11#5) (.Regidx 10#5) .BEQ fetchPc atPc
    0x63#8 0x0a#8 0xb5#8 0x02#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode condition

end BinaryFv.Zesu.MachineExecution
