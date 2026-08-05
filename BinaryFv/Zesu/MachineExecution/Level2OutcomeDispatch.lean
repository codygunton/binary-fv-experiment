import BinaryFv.Zesu.MachineExecution.Level2SecondEntryProof
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

/-- Compact concrete evidence for a wrapper result-tag route.  The existential lives inside this
`Prop`-valued record, so route composition exposes its trace and final frame without a tower of
retired-counter/state binders in every theorem statement. -/
private structure DispatchPath (base : State) (fromStep steps : Nat) (entry : State)
    (exit a0 a1 : BitVec 64) : Prop where
  evidence : ∃ final,
    Trace fromStep steps entry final ∧
    final.regs.get? PC = some exit ∧
    final.regs.get? x10 = some a0 ∧
    final.regs.get? x11 = some a1 ∧
    RetiredCounterPresent final ∧
    final.mem = entry.mem ∧
    Agree platformPreserved base final ∧
    canonicalContractParams.env.CodeIntact final ∧
    final.regs.get? x18 = entry.regs.get? x18 ∧
    final.regs.get? x2 = entry.regs.get? x2

/-- The concrete comparison phase of the tag-one route, through the taken branch at `0x10408`. -/
private structure Tag1PrefixPath (base : State) (fromStep : Nat) (entry : State) : Prop where
  evidence : ∃ after,
    Trace fromStep 4 entry after ∧
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 4 entry after ∧
    after.regs.get? PC = some (BitVec.ofNat 64 0x10428) ∧
    after.regs.get? x10 = some (BitVec.ofNat 64 1) ∧
    after.regs.get? x11 = some (BitVec.ofNat 64 1) ∧
    RetiredCounterPresent after ∧
    after.mem = entry.mem ∧
    Agree platformPreserved base after ∧
    canonicalContractParams.env.CodeIntact after ∧
    after.regs.get? x18 = entry.regs.get? x18 ∧
    after.regs.get? x2 = entry.regs.get? x2

/-- The concrete rejection-result phase of the tag-one route, from `0x10428` to `0x1035c`. -/
private structure Tag1SuffixPath (base : State) (fromStep : Nat) (entry : State) : Prop where
  evidence : ∃ final,
    Trace fromStep 3 entry final ∧
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 3 entry final ∧
    final.regs.get? PC = some (BitVec.ofNat 64 0x1035c) ∧
    final.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
    final.regs.get? x11 = some (BitVec.ofNat 64 4) ∧
    RetiredCounterPresent final ∧
    final.mem = entry.mem ∧
    Agree platformPreserved base final ∧
    canonicalContractParams.env.CodeIntact final ∧
    final.regs.get? x18 = entry.regs.get? x18 ∧
    final.regs.get? x2 = entry.regs.get? x2

/-- The public, composable boundary of one result-tag route.  Unlike the local Sail step
proofs, this keeps the exact execution trace together with the state frame needed by the next
wrapper segment. -/
structure WrapperDispatchRouteFrame (base before after : State) (fromStep steps : Nat)
    (terminalPc result status : BitVec 64) : Prop where
  trace : Trace fromStep steps before after
  atTerminal : after.regs.get? PC = some terminalPc
  resultValue : after.regs.get? x10 = some result
  statusValue : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  platform : Agree platformPreserved base after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  savedS2 : after.regs.get? x18 = before.regs.get? x18
  savedStack : after.regs.get? x2 = before.regs.get? x2

/-- Facts shared by every wrapper route arriving at the status store.  Memory framing and live
register values remain separate because the tag-zero route performs a real payload-adjacent store,
while rejection routes leave memory unchanged. -/
structure WrapperTerminalRouteFrame (base before after : State) (fromStep steps : Nat)
    (terminalPc result status : BitVec 64) : Prop where
  trace : Trace fromStep steps before after
  atTerminal : after.regs.get? PC = some terminalPc
  resultValue : after.regs.get? x10 = some result
  statusValue : after.regs.get? x11 = some status
  platform : Agree platformPreserved base after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after

/-- A result-tag route whose flat Sail trace and Level 2 ownership have the same endpoint. -/
structure WrapperOwnedTerminalRouteFrame (base before after : State) (fromStep steps : Nat)
    (terminalPc result status : BitVec 64) : Prop where
  route : WrapperDispatchRouteFrame base before after fromStep steps terminalPc result status
  confined : ConfinedPrefix
    (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
    Level2ChildSummary fromStep steps before after

private structure Tag3OwnedPath (base : State) (fromStep : Nat) (entry : State) : Prop where
  evidence : ∃ after, WrapperDispatchRouteFrame base entry after fromStep 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) ∧
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 5 entry after

def WrapperDispatchRouteFrame.terminal
    (route : WrapperDispatchRouteFrame base before after fromStep steps terminalPc result status) :
    WrapperTerminalRouteFrame base before after fromStep steps terminalPc result status :=
  { trace := route.trace
    atTerminal := route.atTerminal
    resultValue := route.resultValue
    statusValue := route.statusValue
    platform := route.platform
    code := route.code
    retired := route.retired }

private theorem wrapper_dispatch_register_constant_step {machineArgs : DecoderMachineArgs}
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

private theorem wrapper_dispatch_jump_step {machineArgs : DecoderMachineArgs} {base state : State}
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

private theorem wrapper_dispatch_branch_not_taken_step {machineArgs : DecoderMachineArgs}
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

private theorem wrapper_dispatch_branch_taken_step {machineArgs : DecoderMachineArgs}
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

private theorem wrapperDispatchTag3BranchAfter_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag3BranchAfter state retired) := by
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
  simp [wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
    notNextPc, notIncrement]

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

/-- The second dispatch instruction writes the tag-one comparison constant. -/
theorem wrapper_dispatch_tag1_constant_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10404)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10404) retired x11 (BitVec.ofNat 64 1)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10404) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10404) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10404) 0x93#8 0x05#8 0x10#8 0x00#8 :=
    fetchFileInstruction state 0x10404 0x93 0x05 0x10 0x00
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
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x10#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00100593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10404)
  have execute : Runs (execute (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 1) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x001#12 (0#64) = BitVec.ofNat 64 1 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x001#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 1))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10404) fetchPc atPc 0x93#8 0x05#8 0x10#8 0x00#8
    (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- A tag-one result takes the second comparison branch to its rejection tail. -/
theorem wrapper_dispatch_tag1_branch_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10408))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 1)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428))
        (BitVec.ofNat 64 0x10428) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10408) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10408) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10408) 0x63#8 0x00#8 0xb5#8 0x02#8 :=
    fetchFileInstruction state 0x10408 0x63 0x00 0xb5 0x02
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
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x00#8 0xb5#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x20#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    change Runs (ext_decode (0x02b50063 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10408)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 1) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BEQ)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    rfl
  have targetEq : BitVec.ofNat 64 0x10408 + sign_extend (m := 64) (0x20#13) =
      BitVec.ofNat 64 0x10428 := by decide
  exact wrapper_dispatch_branch_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428) (0x20#13)
    (.Regidx 11#5) (.Regidx 10#5) .BEQ fetchPc atPc
    0x63#8 0x00#8 0xb5#8 0x02#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    condition targetEq (by decide) (by decide)

private theorem wrapperDispatchBranchNotTakenAfter_agree (state : State) (pc retired : BitVec 64) :
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

private theorem wrapperDispatchJumpAfter_agree (state : State) (pc target retired : BitVec 64) :
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

/-- Exact post-state of the tag-one branch at `0x10408`. -/
def wrapperDispatchTag1BranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428))
    (BitVec.ofNat 64 0x10428) retired

private theorem wrapperDispatchTag1BranchAfter_mem (state : State) (retired : BitVec 64) :
    (wrapperDispatchTag1BranchAfter state retired).mem = state.mem := rfl

private theorem wrapperDispatchTag1BranchAfter_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag1BranchAfter state retired) := by
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
  simp [wrapperDispatchTag1BranchAfter, tryStepControlFlowAfterRetired,
    tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
    tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, notRetired, notPc,
    notNextPc, notIncrement]

/-- Any tag other than one falls through the second comparison to `0x1040c`. -/
theorem wrapper_dispatch_tag1_miss_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10408))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 tagValue))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 1))
    (notTag1 : BitVec.ofNat 64 tagValue ≠ BitVec.ofNat 64 1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10408))
        (BitVec.ofNat 64 0x1040c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10408) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10408) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10408) 0x63#8 0x00#8 0xb5#8 0x02#8 :=
    fetchFileInstruction state 0x10408 0x63 0x00 0xb5 0x02
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
  have decode : Runs (ext_decode (fetchWord 0x63#8 0x00#8 0xb5#8 0x02#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x20#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    change Runs (ext_decode (0x02b50063 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10408)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BEQ)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    have comparisonFalse : (BitVec.ofNat 64 tagValue == BitVec.ofNat 64 1) = false := by
      cases equal : (BitVec.ofNat 64 tagValue == BitVec.ofNat 64 1) with
      | false => rfl
      | true => exact False.elim (notTag1 (beq_iff_eq.mp equal))
    rw [comparisonFalse]
    rfl
  exact wrapper_dispatch_branch_not_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10408) (0x20#13) (.Regidx 11#5) (.Regidx 10#5) .BEQ fetchPc atPc
    0x63#8 0x00#8 0xb5#8 0x02#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode condition

/-- The third dispatch instruction writes the tag-two comparison constant. -/
theorem wrapper_dispatch_tag2_constant_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1040c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1040c) retired x11 (BitVec.ofNat 64 2)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1040c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1040c) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1040c) 0x93#8 0x05#8 0x20#8 0x00#8 :=
    fetchFileInstruction state 0x1040c 0x93 0x05 0x20 0x00
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
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x20#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00200593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1040c)
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1040c) fetchPc atPc 0x93#8 0x05#8 0x20#8 0x00#8
    (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- A tag-two result falls through the final comparison to its rejection tail. -/
theorem wrapper_dispatch_tag2_branch_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10410))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 2))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 2)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10410))
        (BitVec.ofNat 64 0x10414) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10410) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10410) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10410) 0xe3#8 0x16#8 0xb5#8 0xf2#8 :=
    fetchFileInstruction state 0x10410 0xe3 0x16 0xb5 0xf2
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
  have decode : Runs (ext_decode (fetchWord 0xe3#8 0x16#8 0xb5#8 0xf2#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f2c#13, .Regidx 11#5, .Regidx 10#5, .BNE)) := by
    change Runs (ext_decode (0xf2b516e3 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10410)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 2) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BNE)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    rfl
  exact wrapper_dispatch_branch_not_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10410) (0x1f2c#13) (.Regidx 11#5) (.Regidx 10#5) .BNE fetchPc atPc
    0xe3#8 0x16#8 0xb5#8 0xf2#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode condition

/-- The tag-two rejection tail clears the wrapper return value. -/
theorem wrapper_dispatch_tag2_clear_result_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10414)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10414) retired x10 (BitVec.ofNat 64 0)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10414) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10414) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10414) 0x13#8 0x05#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10414 0x13 0x05 0x00 0x00
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
    (BitVec.ofNat 64 0x10414)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10414) fetchPc atPc 0x13#8 0x05#8 0x00#8 0x00#8
    (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-two rejection tail records status `2`. -/
theorem wrapper_dispatch_tag2_status_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10418)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10418) retired x11 (BitVec.ofNat 64 2)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10418) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10418) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10418) 0x93#8 0x05#8 0x20#8 0x00#8 :=
    fetchFileInstruction state 0x10418 0x93 0x05 0x20 0x00
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
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x20#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00200593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10418)
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10418) fetchPc atPc 0x93#8 0x05#8 0x20#8 0x00#8
    (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-two tail jumps into the shared wrapper rejection continuation at `0x1035c`. -/
theorem wrapper_dispatch_tag2_to_rejection_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1041c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c))
        (BitVec.ofNat 64 0x1035c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1041c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1041c) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1041c) 0x6f#8 0xf0#8 0x1f#8 0xf4#8 :=
    fetchFileInstruction state 0x1041c 0x6f 0xf0 0x1f 0xf4
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
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x1f#8 0xf4#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff40#21, zreg)) := by
    change Runs (ext_decode (0xf41ff06f : BitVec 32)) _ _ _
    decode_run
  have targetEq : BitVec.ofNat 64 0x1041c + sign_extend (m := 64) (0x1fff40#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c) (0x1fff40#21) fetchPc atPc
    0x6f#8 0xf0#8 0x1f#8 0xf4#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    targetEq (by decide) (by decide)

/-- A zero result takes the final comparison to the success continuation at `0x1033c`. -/
theorem wrapper_dispatch_tag0_success_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10410))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 0))
    (comparison : state.regs.get? x11 = some (BitVec.ofNat 64 2)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10410) (BitVec.ofNat 64 0x1033c))
        (BitVec.ofNat 64 0x1033c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10410) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10410) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10410) 0xe3#8 0x16#8 0xb5#8 0xf2#8 :=
    fetchFileInstruction state 0x10410 0xe3 0x16 0xb5 0xf2
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
  have decode : Runs (ext_decode (fetchWord 0xe3#8 0x16#8 0xb5#8 0xf2#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f2c#13, .Regidx 11#5, .Regidx 10#5, .BNE)) := by
    change Runs (ext_decode (0xf2b516e3 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10410)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 0) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, tag]
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, comparison]
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BNE)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    rfl
  have targetEq : BitVec.ofNat 64 0x10410 + sign_extend (m := 64) (0x1f2c#13) =
      BitVec.ofNat 64 0x1033c := by decide
  exact wrapper_dispatch_branch_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10410) (BitVec.ofNat 64 0x1033c) (0x1f2c#13)
    (.Regidx 11#5) (.Regidx 10#5) .BNE fetchPc atPc
    0xe3#8 0x16#8 0xb5#8 0xf2#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    condition targetEq (by decide) (by decide)

/-- The shared prefix for result tags that are neither three nor one. -/
theorem wrapper_dispatch_non_three_non_one_prefix {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo tagValue : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 tagValue))
    (notTag3 : BitVec.ofNat 64 tagValue ≠ BitVec.ofNat 64 3)
    (notTag1 : BitVec.ofNat 64 tagValue ≠ BitVec.ofNat 64 1) :
    ∃ r1 r2 r3 r4 r5,
      let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
      let s2 := tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
        (BitVec.ofNat 64 0x10404) r2
      let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
      let s4 := tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
        (BitVec.ofNat 64 0x1040c) r4
      let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
      Runs (try_step stepNo false) state s1 false ∧
      Runs (try_step (stepNo + 1) false) s1 s2 false ∧
      Runs (try_step (stepNo + 2) false) s2 s3 false ∧
      Runs (try_step (stepNo + 3) false) s3 s4 false ∧
      Runs (try_step (stepNo + 4) false) s4 s5 false ∧
      s5.regs.get? PC = some (BitVec.ofNat 64 0x10410) ∧
      s5.regs.get? x10 = some (BitVec.ofNat 64 tagValue) ∧
      s5.regs.get? x11 = some (BitVec.ofNat 64 2) := by
  obtain ⟨r1, run1⟩ := wrapper_dispatch_tag3_constant_step machine agree retiredPresent code stepNo atPc
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r1 x11
    (BitVec.ofNat 64 3)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    grind
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    simpa [s1] using (afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r1 x11 x10
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r2, run2⟩ := wrapper_dispatch_tag3_miss_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1 notTag3
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have retired2 : RetiredCounterPresent s2 := ⟨Sail.BitVec.addInt r2 1, by
    simp [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    grind
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10404) := by
    simp [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag1_constant_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10404) r3 x11
    (BitVec.ofNat 64 1)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    grind
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10408) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have tag3 : s3.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    have tag2 : s2.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
      simp [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, tag1]
    simpa [s3] using (afterRegisterWrite_register s2 (BitVec.ofNat 64 0x10404) r3 x11 x10
      (BitVec.ofNat 64 1) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag2
  have comparison3 : s3.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag1_miss_step machine agree3 retired3 code3
    (stepNo + 3) pc3 tag3 comparison3 notTag1
  let s4 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
    (BitVec.ofNat 64 0x1040c) r4
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchBranchNotTakenAfter_agree s3 (BitVec.ofNat 64 0x10408) r4)
  have retired4 : RetiredCounterPresent s4 := ⟨Sail.BitVec.addInt r4 1, by
    simp [s4, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code4 : canonicalContractParams.env.CodeIntact s4 := by
    grind
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1040c) := by
    simp [s4, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag2_constant_step machine agree4 retired4 code4
    (stepNo + 4) pc4
  let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
  refine ⟨r1, r2, r3, r4, r5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [s1] using run1
  · simpa [s1, s2] using run2
  · simpa [s2, s3] using run3
  · simpa [s3, s4] using run4
  · simpa [s4, s5] using run5
  · simpa [s5] using afterRegisterWrite_pc s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
  · have tag4 : s4.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
      simp [s4, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, tag3]
    simpa [s5] using (afterRegisterWrite_register s4 (BitVec.ofNat 64 0x1040c) r5 x11 x10
      (BitVec.ofNat 64 2) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag4
  · simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- The tag-three rejection tail clears the wrapper return value. -/
theorem wrapper_dispatch_tag3_clear_result_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10434)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10434) retired x10 (BitVec.ofNat 64 0)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10434) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10434) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10434) 0x13#8 0x05#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10434 0x13 0x05 0x00 0x00
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
    (BitVec.ofNat 64 0x10434)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10434) fetchPc atPc 0x13#8 0x05#8 0x00#8 0x00#8
    (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-three rejection tail records status `3`. -/
theorem wrapper_dispatch_tag3_status_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10438)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10438) retired x11 (BitVec.ofNat 64 3)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10438) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10438) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10438) 0x93#8 0x05#8 0x30#8 0x00#8 :=
    fetchFileInstruction state 0x10438 0x93 0x05 0x30 0x00
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
    (BitVec.ofNat 64 0x10438)
  have execute : Runs (execute (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 3) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x003#12 (0#64) = BitVec.ofNat 64 3 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x003#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 3))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10438) fetchPc atPc 0x93#8 0x05#8 0x30#8 0x00#8
    (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-three tail jumps into the shared wrapper rejection continuation at `0x1035c`. -/
theorem wrapper_dispatch_tag3_to_rejection_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1043c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c))
        (BitVec.ofNat 64 0x1035c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1043c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1043c) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1043c) 0x6f#8 0xf0#8 0x1f#8 0xf2#8 :=
    fetchFileInstruction state 0x1043c 0x6f 0xf0 0x1f 0xf2
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
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0x1f#8 0xf2#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff20#21, zreg)) := by
    change Runs (ext_decode (0xf21ff06f : BitVec 32)) _ _ _
    decode_run
  have targetEq : BitVec.ofNat 64 0x1043c + sign_extend (m := 64) (0x1fff20#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) (0x1fff20#21) fetchPc atPc
    0x6f#8 0xf0#8 0x1f#8 0xf2#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    targetEq (by decide) (by decide)

/-- The tag-one rejection tail clears the wrapper return value. -/
theorem wrapper_dispatch_tag1_clear_result_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10428)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10428) retired x10 (BitVec.ofNat 64 0)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10428) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10428) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10428) 0x13#8 0x05#8 0x00#8 0x00#8 :=
    fetchFileInstruction state 0x10428 0x13 0x05 0x00 0x00
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
    (BitVec.ofNat 64 0x10428)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10428) fetchPc atPc 0x13#8 0x05#8 0x00#8 0x00#8
    (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-one rejection tail records status `4`. -/
theorem wrapper_dispatch_tag1_status_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1042c)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1042c) retired x11 (BitVec.ofNat 64 4)) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x1042c) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x1042c) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1042c) 0x93#8 0x05#8 0x40#8 0x00#8 :=
    fetchFileInstruction state 0x1042c 0x93 0x05 0x40 0x00
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
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x05#8 0x40#8 0x00#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x004#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by
    change Runs (ext_decode (0x00400593 : BitVec 32)) _ _ _
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1042c)
  have execute : Runs (execute (.ITYPE (0x004#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 4) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x004#12 (0#64) = BitVec.ofNat 64 4 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x004#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 4))
  exact wrapper_dispatch_register_constant_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1042c) fetchPc atPc 0x93#8 0x05#8 0x40#8 0x00#8
    (.ITYPE (0x004#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) fetchBytes decode execute
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide) (by decide)

/-- The tag-one tail jumps into the shared wrapper rejection continuation at `0x1035c`. -/
theorem wrapper_dispatch_tag1_to_rejection_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10430)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c))
        (BitVec.ofNat 64 0x1035c) retired) false := by
  have pcIn : functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw (BitVec.ofNat 64 0x10430) := by
    apply functionInstanceExecutionPcs_iff_ranges.mpr
    apply RegionPcs.iff_inRanges.mpr
    native_decide
  have fetchPc : DecoderFetchPc
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (BitVec.ofNat 64 0x10430) := ⟨pcIn, by native_decide⟩
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10430) 0x6f#8 0xf0#8 0xdf#8 0xf2#8 :=
    fetchFileInstruction state 0x10430 0x6f 0xf0 0xdf 0xf2
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
  have decode : Runs (ext_decode (fetchWord 0x6f#8 0xf0#8 0xdf#8 0xf2#8))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff2c#21, zreg)) := by
    change Runs (ext_decode (0xf2dff06f : BitVec 32)) _ _ _
    decode_run
  have targetEq : BitVec.ofNat 64 0x10430 + sign_extend (m := 64) (0x1fff2c#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c) (0x1fff2c#21) fetchPc atPc
    0x6f#8 0xf0#8 0xdf#8 0xf2#8 fetchBytes (by unfold BaseInstructionEncoding; decide) decode
    targetEq (by decide) (by decide)

/-- The zero-result route reaches the success continuation with `(a0, a1) = (0, 2)`. -/
theorem wrapper_dispatch_tag0_success_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 0)) :
    DispatchPath base stepNo 6 state (BitVec.ofNat 64 0x1033c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 2) := by
  obtain ⟨r1, r2, r3, r4, r5, run1, run2, run3, run4, run5, pc5, tag5, comparison5⟩ :=
    wrapper_dispatch_non_three_non_one_prefix machine agree retiredPresent code stepNo 0 atPc tag
      (by decide) (by decide)
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  let s4 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
    (BitVec.ofNat 64 0x1040c) r4
  let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchBranchNotTakenAfter_agree s3 (BitVec.ofNat 64 0x10408) r4)
  have agree5 : Agree platformPreserved base s5 := agree4.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired5 : RetiredCounterPresent s5 := ⟨Sail.BitVec.addInt r5 1, by
    simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    grind
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag0_success_step machine agree5 retired5 code5
    (stepNo + 5) (by simpa [s1, s2, s3, s4, s5] using pc5)
    (by simpa [s1, s2, s3, s4, s5] using tag5)
    (by simpa [s1, s2, s3, s4, s5] using comparison5)
  let s6 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s5)
      (BitVec.ofNat 64 0x10410) (BitVec.ofNat 64 0x1033c))
    (BitVec.ofNat 64 0x1033c) r6
  refine ⟨⟨s6,
    Trace.step stepNo 5 state s1 s6 run1
      (Trace.step (stepNo + 1) 4 s1 s2 s6 run2
        (Trace.step (stepNo + 2) 3 s2 s3 s6 run3
          (Trace.step (stepNo + 3) 2 s3 s4 s6 run4
            (Trace.step (stepNo + 4) 1 s4 s5 s6 run5
              (Trace.step (stepNo + 5) 0 s5 s6 s6 (by simpa [s6] using run6)
                (Trace.refl (stepNo + 6) s6)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · apply tryStepControlFlowAfterRetired_preserves_register
    · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using tag5
    · decide
    · decide
  · apply tryStepControlFlowAfterRetired_preserves_register
    · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using comparison5
    · decide
    · decide
  · exact ⟨Sail.BitVec.addInt r6 1, by
      simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · simp [s1, s2, s3, s4, s5, s6, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement]
  · exact agree5.trans (wrapperDispatchJumpAfter_agree s5 (BitVec.ofNat 64 0x10410)
      (BitVec.ofNat 64 0x1033c) r6)
  · grind
  · simp [s1, s2, s3, s4, s5, s6, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- The tag-two route reaches the shared rejection continuation with `(a0, a1) = (0, 2)`. -/
theorem wrapper_dispatch_tag2_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 2)) :
    DispatchPath base stepNo 9 state (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 2) := by
  obtain ⟨r1, r2, r3, r4, r5, run1, run2, run3, run4, run5, pc5, tag5, comparison5⟩ :=
    wrapper_dispatch_non_three_non_one_prefix machine agree retiredPresent code stepNo 2 atPc tag
      (by decide) (by decide)
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  let s4 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
    (BitVec.ofNat 64 0x1040c) r4
  let s5 := afterRegisterWrite s4 (BitVec.ofNat 64 0x1040c) r5 x11 (BitVec.ofNat 64 2)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchBranchNotTakenAfter_agree s3 (BitVec.ofNat 64 0x10408) r4)
  have agree5 : Agree platformPreserved base s5 := agree4.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired5 : RetiredCounterPresent s5 := ⟨Sail.BitVec.addInt r5 1, by
    simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    grind
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag2_branch_step machine agree5 retired5 code5
    (stepNo + 5) (by simpa [s1, s2, s3, s4, s5] using pc5)
    (by simpa [s1, s2, s3, s4, s5] using tag5)
    (by simpa [s1, s2, s3, s4, s5] using comparison5)
  let s6 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10410))
    (BitVec.ofNat 64 0x10414) r6
  have agree6 : Agree platformPreserved base s6 := agree5.trans
    (wrapperDispatchBranchNotTakenAfter_agree s5 (BitVec.ofNat 64 0x10410) r6)
  have retired6 : RetiredCounterPresent s6 := ⟨Sail.BitVec.addInt r6 1, by
    simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code6 : canonicalContractParams.env.CodeIntact s6 := by
    grind
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x10414) := by
    simp [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r7, run7⟩ := wrapper_dispatch_tag2_clear_result_step machine agree6 retired6 code6
    (stepNo + 6) pc6
  let s7 := afterRegisterWrite s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)
  have agree7 : Agree platformPreserved base s7 := agree6.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired7 := afterRegisterWrite_retired_present s6 (BitVec.ofNat 64 0x10414) r7 x10
    (BitVec.ofNat 64 0)
  have code7 : canonicalContractParams.env.CodeIntact s7 := by
    grind
  have pc7 : s7.regs.get? PC = some (BitVec.ofNat 64 0x10418) := by
    simpa [s7] using afterRegisterWrite_pc s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)
  obtain ⟨r8, run8⟩ := wrapper_dispatch_tag2_status_step machine agree7 retired7 code7
    (stepNo + 7) pc7
  let s8 := afterRegisterWrite s7 (BitVec.ofNat 64 0x10418) r8 x11 (BitVec.ofNat 64 2)
  have agree8 : Agree platformPreserved base s8 := agree7.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired8 := afterRegisterWrite_retired_present s7 (BitVec.ofNat 64 0x10418) r8 x11
    (BitVec.ofNat 64 2)
  have code8 : canonicalContractParams.env.CodeIntact s8 := by
    change canonicalContractParams.env.image.fileBytesMatchMemory s8.mem
    change canonicalContractParams.env.image.fileBytesMatchMemory s7.mem at code7
    rw [show s8.mem = s7.mem from rfl]
    exact code7
  have pc8 : s8.regs.get? PC = some (BitVec.ofNat 64 0x1041c) := by
    simpa [s8] using afterRegisterWrite_pc s7 (BitVec.ofNat 64 0x10418) r8 x11 (BitVec.ofNat 64 2)
  obtain ⟨r9, run9⟩ := wrapper_dispatch_tag2_to_rejection_step machine agree8 retired8 code8
    (stepNo + 8) pc8
  let s9 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s8)
      (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r9
  refine ⟨⟨s9, Trace.step stepNo 8 state s1 s9 run1
    (Trace.step (stepNo + 1) 7 s1 s2 s9 run2
    (Trace.step (stepNo + 2) 6 s2 s3 s9 run3
    (Trace.step (stepNo + 3) 5 s3 s4 s9 run4
    (Trace.step (stepNo + 4) 4 s4 s5 s9 run5
    (Trace.step (stepNo + 5) 3 s5 s6 s9 (by simpa [s6] using run6)
    (Trace.step (stepNo + 6) 2 s6 s7 s9 (by simpa [s6, s7] using run7)
    (Trace.step (stepNo + 7) 1 s7 s8 s9 (by simpa [s7, s8] using run8)
    (Trace.step (stepNo + 8) 0 s8 s9 s9 (by simpa [s8] using run9)
      (Trace.refl (stepNo + 9) s9))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [s9, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · have x10s7 : s7.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simp [s7, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    have x10s8 : s8.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s8] using (afterRegisterWrite_register s7 (BitVec.ofNat 64 0x10418) r8 x11 x10
        (BitVec.ofNat 64 2) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x10s7
    exact tryStepControlFlowAfterRetired_preserves_register
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x1041c)
        (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r9 x10 (BitVec.ofNat 64 0)
      (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x10s8) (by decide) (by decide)
  · have x11s8 : s8.regs.get? x11 = some (BitVec.ofNat 64 2) := by
      simp [s8, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    exact tryStepControlFlowAfterRetired_preserves_register
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s8) (BitVec.ofNat 64 0x1041c)
        (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r9 x11 (BitVec.ofNat 64 2)
      (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x11s8) (by decide) (by decide)
  · exact ⟨Sail.BitVec.addInt r9 1, by
      simp [s9, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, afterRegisterWrite_mem,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
  · exact agree8.trans (wrapperDispatchJumpAfter_agree s8 (BitVec.ofNat 64 0x1041c)
      (BitVec.ofNat 64 0x1035c) r9)
  · grind
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- Executes the tag-one comparison phase through its taken branch. -/
private theorem wrapper_dispatch_tag1_prefix {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    Tag1PrefixPath base stepNo state := by
  obtain ⟨r1, run1⟩ := wrapper_dispatch_tag3_constant_step machine agree retiredPresent code stepNo atPc
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r1 x11
    (BitVec.ofNat 64 3)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    grind
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 1) := by
    simpa [s1] using (afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r1 x11 x10
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r2, run2⟩ := wrapper_dispatch_tag3_miss_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1 (by decide)
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have retired2 : RetiredCounterPresent s2 := ⟨Sail.BitVec.addInt r2 1, by
    simp [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    grind
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10404) := by
    simp [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag1_constant_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10404) r3 x11
    (BitVec.ofNat 64 1)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    grind
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10408) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have tag3 : s3.regs.get? x10 = some (BitVec.ofNat 64 1) := by
    have tag2 : s2.regs.get? x10 = some (BitVec.ofNat 64 1) := by
      simp [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, tag1]
    simpa [s3] using (afterRegisterWrite_register s2 (BitVec.ofNat 64 0x10404) r3 x11 x10
      (BitVec.ofNat 64 1) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag2
  have comparison3 : s3.regs.get? x11 = some (BitVec.ofNat 64 1) := by
    simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag1_branch_step machine agree3 retired3 code3
    (stepNo + 3) pc3 tag3 comparison3
  let s4 := wrapperDispatchTag1BranchAfter s3 r4
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchTag1BranchAfter_agree s3 r4)
  have retired4 : RetiredCounterPresent s4 := ⟨Sail.BitVec.addInt r4 1, by
    simp [s4, wrapperDispatchTag1BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩
  have code4 : canonicalContractParams.env.CodeIntact s4 := by
    simpa [s4, wrapperDispatchTag1BranchAfter] using code3
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10428) := by
    simp [s4, wrapperDispatchTag1BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have prefixConfined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 4 state s4 := by
    have p1 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 1 state s1 := ConfinedPrefix.ownStep atPc (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s1] using run1)
    have p2 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 1) 1 s1 s2 := ConfinedPrefix.ownStep pc1 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s1, s2] using run2)
    have p3 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 2) 1 s2 s3 := ConfinedPrefix.ownStep pc2 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s2, s3] using run3)
    have p4 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 3) 1 s3 s4 := ConfinedPrefix.ownStep pc3 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s3, s4, wrapperDispatchTag1BranchAfter] using run4)
    simpa [Nat.add_assoc] using ConfinedPrefix.trans (ConfinedPrefix.trans
      (ConfinedPrefix.trans p1 p2) p3) p4
  refine ⟨⟨s4, Trace.step stepNo 3 state s1 s4 (by simpa [s1] using run1)
    (Trace.step (stepNo + 1) 2 s1 s2 s4 (by simpa [s1, s2] using run2)
    (Trace.step (stepNo + 2) 1 s2 s3 s4 (by simpa [s2, s3] using run3)
    (Trace.step (stepNo + 3) 0 s3 s4 s4
      (by simpa [s3, s4, wrapperDispatchTag1BranchAfter] using run4)
      (Trace.refl (stepNo + 4) s4)))), prefixConfined, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact pc4
  · simp [s4, wrapperDispatchTag1BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, tag3]
  · simp [s4, wrapperDispatchTag1BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, comparison3]
  · exact retired4
  · calc
      s4.mem = s3.mem := wrapperDispatchTag1BranchAfter_mem s3 r4
      _ = s2.mem := rfl
      _ = s1.mem := rfl
      _ = state.mem := rfl
  · exact agree4
  · exact code4
  · simp [s1, s2, s3, s4, wrapperDispatchTag1BranchAfter, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- Executes the tag-one rejection-result phase after the comparison branch. -/
private theorem wrapper_dispatch_tag1_suffix {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10428)) :
    Tag1SuffixPath base stepNo state := by
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag1_clear_result_step machine agree retiredPresent code
    stepNo atPc
  let s5 := afterRegisterWrite state (BitVec.ofNat 64 0x10428) r5 x10 (BitVec.ofNat 64 0)
  have agree5 : Agree platformPreserved base s5 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired5 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10428) r5 x10
    (BitVec.ofNat 64 0)
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    grind
  have pc5 : s5.regs.get? PC = some (BitVec.ofNat 64 0x1042c) := by
    simpa [s5] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10428) r5 x10 (BitVec.ofNat 64 0)
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag1_status_step machine agree5 retired5 code5
    (stepNo + 1) pc5
  let s6 := afterRegisterWrite s5 (BitVec.ofNat 64 0x1042c) r6 x11 (BitVec.ofNat 64 4)
  have agree6 : Agree platformPreserved base s6 := agree5.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired6 := afterRegisterWrite_retired_present s5 (BitVec.ofNat 64 0x1042c) r6 x11
    (BitVec.ofNat 64 4)
  have code6 : canonicalContractParams.env.CodeIntact s6 := by
    change canonicalContractParams.env.image.fileBytesMatchMemory s6.mem
    change canonicalContractParams.env.image.fileBytesMatchMemory s5.mem at code5
    rw [show s6.mem = s5.mem from rfl]
    exact code5
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x10430) := by
    simpa [s6] using afterRegisterWrite_pc s5 (BitVec.ofNat 64 0x1042c) r6 x11 (BitVec.ofNat 64 4)
  obtain ⟨r7, run7⟩ := wrapper_dispatch_tag1_to_rejection_step machine agree6 retired6 code6
    (stepNo + 2) pc6
  let s7 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s6)
      (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r7
  have p5 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 1 state s5 :=
    ConfinedPrefix.ownStep atPc (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s5] using run5)
  have p6 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 1) 1 s5 s6 :=
    ConfinedPrefix.ownStep pc5 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s5, s6] using run6)
  have p7 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 2) 1 s6 s7 :=
    ConfinedPrefix.ownStep pc6 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by
      simp [functionInstanceExitPred, BinaryFv.Binary.Elfling.FunctionInstance.isExit,
        functionInstance_raw_decoder_root_zesu_decode_raw]) (by simpa [s6] using run7)
  have suffixPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 3 state s7 := by
    simpa using ConfinedPrefix.trans (ConfinedPrefix.trans p5 p6) p7
  refine ⟨⟨s7, Trace.step stepNo 2 state s5 s7 (by simpa [s5] using run5)
    (Trace.step (stepNo + 1) 1 s5 s6 s7 (by simpa [s5, s6] using run6)
    (Trace.step (stepNo + 2) 0 s6 s7 s7 (by simpa [s6] using run7)
      (Trace.refl (stepNo + 3) s7))), suffixPrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [s7, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · have x10s5 : s5.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simp [s5, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        wrapperDispatchTag1BranchAfter, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]
    have x10s6 : s6.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s6] using (afterRegisterWrite_register s5 (BitVec.ofNat 64 0x1042c) r6 x11 x10
        (BitVec.ofNat 64 4) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x10s5
    exact tryStepControlFlowAfterRetired_preserves_register
      (controlFlowJumpState (tryStepControlFlowAfterIncrement s6) (BitVec.ofNat 64 0x10430)
        (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r7 x10 (BitVec.ofNat 64 0)
      (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x10s6) (by decide) (by decide)
  · have x11s6 : s6.regs.get? x11 = some (BitVec.ofNat 64 4) := by
      simp [s6, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert]
    apply tryStepControlFlowAfterRetired_preserves_register
    · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
        Std.ExtDHashMap.get?_insert] using x11s6
    · decide
    · decide
  · exact ⟨Sail.BitVec.addInt r7 1, by
      simp [s7, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
  · calc
      s7.mem = s6.mem := rfl
      _ = s5.mem := rfl
      _ = state.mem := rfl
  · exact agree6.trans (wrapperDispatchJumpAfter_agree s6 (BitVec.ofNat 64 0x10430)
      (BitVec.ofNat 64 0x1035c) r7)
  · grind
  · simp [s5, s6, s7, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- Public lossless frame of the three-instruction tag-one rejection tail. -/
theorem wrapper_dispatch_tag1_suffix_frame {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base) (agree : Agree platformPreserved base state)
    (retired : RetiredCounterPresent state) (code : canonicalContractParams.env.CodeIntact state)
    (stepNo : Nat) (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10428)) :
    ∃ after, Trace stepNo 3 state after ∧ ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 3 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x1035c) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 0) ∧ after.regs.get? x11 = some (BitVec.ofNat 64 4) ∧
      RetiredCounterPresent after ∧ after.mem = state.mem ∧ Agree platformPreserved base after ∧
      canonicalContractParams.env.CodeIntact after ∧ after.regs.get? x18 = state.regs.get? x18 ∧
      after.regs.get? x2 = state.regs.get? x2 := by
  obtain ⟨⟨after, trace, tailPrefix, pc, result, status, retired, memory, platform, code, x18,
    x2⟩⟩ :=
    wrapper_dispatch_tag1_suffix machine agree retired code stepNo atPc
  exact ⟨after, trace, tailPrefix, pc, result, status, retired, memory, platform, code, x18, x2⟩

/-- The tag-one route reaches the shared rejection continuation with `(a0, a1) = (0, 4)`. -/
theorem wrapper_dispatch_tag1_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    DispatchPath base stepNo 7 state (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 4) := by
  obtain ⟨⟨s4, prefixTrace, _prefixConfined, pc4, tag4, status4, retired4, memory4, agree4, code4, x18_4,
    x2_4⟩⟩ :=
    wrapper_dispatch_tag1_prefix machine agree retiredPresent code stepNo atPc tag
  obtain ⟨⟨s7, suffixTrace, _suffixPrefix, pc7, result7, status7, retired7, memory7, agree7,
    code7, x18_7, x2_7⟩⟩ :=
    wrapper_dispatch_tag1_suffix machine agree4 retired4 code4 (stepNo + 4) pc4
  refine ⟨⟨s7, Trace.append prefixTrace suffixTrace, pc7, result7, status7, retired7, ?_, agree7,
    code7, ?_, ?_⟩⟩
  · exact memory7.trans memory4
  · exact x18_7.trans x18_4
  · exact x2_7.trans x2_4

/-- Tag one supplies one terminal state carrying both its seven-step Sail trace and wrapper ownership. -/
theorem wrapper_dispatch_tag1_owned_terminal_route {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperOwnedTerminalRouteFrame base state after stepNo 7
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) := by
  obtain ⟨⟨s4, prefixTrace, prefixConfined, pc4, _tag4, _status4, retired4, memory4, agree4,
    code4, x18_4, x2_4⟩⟩ := wrapper_dispatch_tag1_prefix machine agree retiredPresent code stepNo atPc tag
  obtain ⟨⟨after, suffixTrace, suffixConfined, pc, result, status, retired, memory, platform,
    finalCode, x18, x2⟩⟩ := wrapper_dispatch_tag1_suffix machine agree4 retired4 code4 (stepNo + 4) pc4
  let route : WrapperDispatchRouteFrame base state after stepNo 7
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) :=
    { trace := Trace.append prefixTrace suffixTrace
      atTerminal := pc
      resultValue := result
      statusValue := status
      platform := platform
      code := finalCode
      retired := retired
      memory := memory.trans memory4
      savedS2 := x18.trans x18_4
      savedStack := x2.trans x2_4 }
  refine ⟨after, ⟨route, ?_⟩⟩
  simpa [Nat.add_assoc] using ConfinedPrefix.trans prefixConfined suffixConfined

/-- The tag-three route reaches the shared rejection continuation with `(a0, a1) = (0, 3)`. -/
private theorem wrapper_dispatch_tag3_owned_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    Tag3OwnedPath base stepNo state := by
  obtain ⟨r1, run1⟩ := wrapper_dispatch_tag3_constant_step machine agree retiredPresent code stepNo atPc
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r1 x11
    (BitVec.ofNat 64 3)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    grind
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 3) := by
    simpa [s1] using (afterRegisterWrite_register state (BitVec.ofNat 64 0x103fc) r1 x11 x10
      (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) := by
    simp [s1, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r2, run2, -⟩ := wrapper_dispatch_tag3_branch_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1
  let s2 := wrapperDispatchTag3BranchAfter s1 r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchTag3BranchAfter_agree s1 r2)
  have retired2 : RetiredCounterPresent s2 := ⟨Sail.BitVec.addInt r2 1, by
    simp [s2, wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, wrapperDispatchTag3BranchAfter] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10434) := by
    simp [s2, wrapperDispatchTag3BranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag3_clear_result_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10434) r3 x10
    (BitVec.ofNat 64 0)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    grind
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10438) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag3_status_step machine agree3 retired3 code3
    (stepNo + 3) pc3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired4 := afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10438) r4 x11
    (BitVec.ofNat 64 3)
  have code4 : canonicalContractParams.env.CodeIntact s4 := by
    grind
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1043c) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag3_to_rejection_step machine agree4 retired4 code4
    (stepNo + 4) pc4
  let s5 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r5
  have confined : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 5 state s5 := by
    have p1 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary stepNo 1 state s1 := ConfinedPrefix.ownStep atPc (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s1] using run1)
    have p2 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 1) 1 s1 s2 := ConfinedPrefix.ownStep pc1 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s1, s2] using run2)
    have p3 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 2) 1 s2 s3 := ConfinedPrefix.ownStep pc2 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s2, s3] using run3)
    have p4 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 3) 1 s3 s4 := ConfinedPrefix.ownStep pc3 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simp [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s3, s4] using run4)
    have p5 : ConfinedPrefix
        (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
        (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
        Level2ChildSummary (stepNo + 4) 1 s4 s5 := ConfinedPrefix.ownStep pc4 (by
      apply functionInstanceExecutionPcs_iff_ranges.mpr
      apply RegionPcs.iff_inRanges.mpr
      native_decide) (by simpa [functionInstanceExitPred,
      BinaryFv.Binary.Elfling.FunctionInstance.isExit, functionInstance_raw_decoder_root_zesu_decode_raw])
      (by simpa [s4] using run5)
    simpa [Nat.add_assoc] using ConfinedPrefix.trans (ConfinedPrefix.trans
      (ConfinedPrefix.trans (ConfinedPrefix.trans p1 p2) p3) p4) p5
  let trace : Trace stepNo 5 state s5 := Trace.step stepNo 4 state s1 s5 (by simpa [s1] using run1)
    (Trace.step (stepNo + 1) 3 s1 s2 s5 (by simpa [s1, s2] using run2)
    (Trace.step (stepNo + 2) 2 s2 s3 s5 (by simpa [s2, s3] using run3)
    (Trace.step (stepNo + 3) 1 s3 s4 s5 (by simpa [s3, s4] using run4)
    (Trace.step (stepNo + 4) 0 s4 s5 s5 (by simpa [s4] using run5)
      (Trace.refl (stepNo + 5) s5)))))
  let terminal : WrapperDispatchRouteFrame base state s5 stepNo 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
    refine
      { trace := trace
        atTerminal := ?_
        resultValue := ?_
        statusValue := ?_
        memory := ?_
        platform := ?_
        code := ?_
        retired := ?_
        savedS2 := ?_
        savedStack := ?_ }
    · simp [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
    · have x10s3 : s3.regs.get? x10 = some (BitVec.ofNat 64 0) := by
        simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
          wrapperDispatchTag3BranchAfter, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert]
      have x10s4 : s4.regs.get? x10 = some (BitVec.ofNat 64 0) := by
        simpa [s4] using (afterRegisterWrite_register s3 (BitVec.ofNat 64 0x10438) r4 x11 x10
          (BitVec.ofNat 64 3) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x10s3
      exact tryStepControlFlowAfterRetired_preserves_register
        (controlFlowJumpState (tryStepControlFlowAfterIncrement s4) (BitVec.ofNat 64 0x1043c)
          (BitVec.ofNat 64 0x1035c)) (BitVec.ofNat 64 0x1035c) r5 x10 (BitVec.ofNat 64 0)
        (by simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert] using x10s4) (by decide) (by decide)
    · have x11s4 : s4.regs.get? x11 = some (BitVec.ofNat 64 3) := by
        simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
          coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
      apply tryStepControlFlowAfterRetired_preserves_register
      · simpa [controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
          Std.ExtDHashMap.get?_insert] using x11s4
      · decide
      · decide
    · simp [s1, s2, s3, s4, s5, afterRegisterWrite_mem, wrapperDispatchTag3BranchAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
    · exact agree4.trans (wrapperDispatchJumpAfter_agree s4 (BitVec.ofNat 64 0x1043c)
      (BitVec.ofNat 64 0x1035c) r5)
    · grind
    · exact ⟨Sail.BitVec.addInt r5 1, by
      simp [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
    · simp [s1, s2, s3, s4, s5, wrapperDispatchTag3BranchAfter, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
    · simp [s1, s2, s3, s4, s5, wrapperDispatchTag3BranchAfter, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  exact ⟨s5, terminal, confined⟩

/-- The original tag-three route frame projected from its richer shared-state proof. -/
theorem wrapper_dispatch_tag3_path {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    DispatchPath base stepNo 5 state (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 3) := by
  obtain ⟨⟨after, route, -⟩⟩ := wrapper_dispatch_tag3_owned_path machine agree retiredPresent code
    stepNo atPc tag
  exact ⟨⟨after, route.trace, route.atTerminal, route.resultValue, route.statusValue, route.retired,
    route.memory, route.platform, route.code, route.savedS2, route.savedStack⟩⟩

/-- Tag three supplies one terminal state carrying both its five-step Sail trace and wrapper ownership. -/
theorem wrapper_dispatch_tag3_owned_terminal_route {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    ∃ after, WrapperOwnedTerminalRouteFrame base state after stepNo 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
  obtain ⟨⟨after, terminal, confined⟩⟩ := wrapper_dispatch_tag3_owned_path machine agree retiredPresent
    code stepNo atPc tag
  exact ⟨after, ⟨terminal, confined⟩⟩

/-- The short prefix of the tag-one route, kept separate from its result-tail frame. -/
theorem wrapper_dispatch_tag1_trace_prefix {state s1 s2 s3 s4 : State} (stepNo : Nat)
    (run1 : Runs (try_step stepNo false) state s1 false)
    (run2 : Runs (try_step (stepNo + 1) false) s1 s2 false)
    (run3 : Runs (try_step (stepNo + 2) false) s2 s3 false)
    (run4 : Runs (try_step (stepNo + 3) false) s3 s4 false) :
    Trace stepNo 4 state s4 := by
  exact Trace.step _ _ _ _ _ run1 <| Trace.step _ _ _ _ _ run2 <|
    Trace.step _ _ _ _ _ run3 <| Trace.one (stepNo + 3) _ _ run4

/-- The short result-tail of the tag-one route. -/
theorem wrapper_dispatch_tag1_trace_suffix {s4 s5 s6 s7 : State} (stepNo : Nat)
    (run5 : Runs (try_step (stepNo + 4) false) s4 s5 false)
    (run6 : Runs (try_step (stepNo + 5) false) s5 s6 false)
    (run7 : Runs (try_step (stepNo + 6) false) s6 s7 false) :
    Trace (stepNo + 4) 3 s4 s7 := by
  exact Trace.step _ _ _ _ _ run5 <| Trace.step _ _ _ _ _ run6 <|
    Trace.one (stepNo + 6) _ _ run7

/-- The short prefix of the tag-two route, before it writes the rejection result. -/
theorem wrapper_dispatch_tag2_trace_prefix {state s1 s2 s3 s4 s5 : State} (stepNo : Nat)
    (run1 : Runs (try_step stepNo false) state s1 false)
    (run2 : Runs (try_step (stepNo + 1) false) s1 s2 false)
    (run3 : Runs (try_step (stepNo + 2) false) s2 s3 false)
    (run4 : Runs (try_step (stepNo + 3) false) s3 s4 false)
    (run5 : Runs (try_step (stepNo + 4) false) s4 s5 false) :
    Trace stepNo 5 state s5 := by
  exact Trace.step _ _ _ _ _ run1 <| Trace.step _ _ _ _ _ run2 <|
    Trace.step _ _ _ _ _ run3 <| Trace.step _ _ _ _ _ run4 <|
    Trace.one (stepNo + 4) _ _ run5

/-- The short rejection tail of the tag-two route. -/
theorem wrapper_dispatch_tag2_trace_suffix {s5 s6 s7 s8 s9 : State} (stepNo : Nat)
    (run6 : Runs (try_step (stepNo + 5) false) s5 s6 false)
    (run7 : Runs (try_step (stepNo + 6) false) s6 s7 false)
    (run8 : Runs (try_step (stepNo + 7) false) s7 s8 false)
    (run9 : Runs (try_step (stepNo + 8) false) s8 s9 false) :
    Trace (stepNo + 5) 4 s5 s9 := by
  exact Trace.step _ _ _ _ _ run6 <| Trace.step _ _ _ _ _ run7 <|
    Trace.step _ _ _ _ _ run8 <| Trace.one (stepNo + 8) _ _ run9

/-- The tag-three route as a trace plus the frame required by its continuation. -/
theorem wrapper_dispatch_tag3_route_frame {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 3)) :
    ∃ after, WrapperDispatchRouteFrame base state after stepNo 5
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 3) := by
  obtain ⟨⟨after, trace, atTerminal, result, status, retired, memory, platform, codeFinal,
    savedS2, savedStack⟩⟩ :=
    wrapper_dispatch_tag3_path machine agree retiredPresent code stepNo atPc tag
  exact ⟨after, ⟨trace, atTerminal, result, status, memory, platform, codeFinal, retired, savedS2,
    savedStack⟩⟩

/-- The tag-one route as a composable prefix plus rejection-tail frame. -/
theorem wrapper_dispatch_tag1_route_frame {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 1)) :
    ∃ after, WrapperDispatchRouteFrame base state after stepNo 7
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 4) := by
  obtain ⟨⟨after, trace, atTerminal, result, status, retired, memory, platform, codeFinal,
    savedS2, savedStack⟩⟩ :=
    wrapper_dispatch_tag1_path machine agree retiredPresent code stepNo atPc tag
  exact ⟨after, ⟨trace, atTerminal, result, status, memory, platform, codeFinal, retired, savedS2,
    savedStack⟩⟩

/-- The tag-two route as a composable prefix plus rejection-tail frame. -/
theorem wrapper_dispatch_tag2_route_frame {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 2)) :
    ∃ after, WrapperDispatchRouteFrame base state after stepNo 9
      (BitVec.ofNat 64 0x1035c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 2) := by
  obtain ⟨⟨after, trace, atTerminal, result, status, retired, memory, platform, codeFinal,
    savedS2, savedStack⟩⟩ :=
    wrapper_dispatch_tag2_path machine agree retiredPresent code stepNo atPc tag
  exact ⟨after, ⟨trace, atTerminal, result, status, memory, platform, codeFinal, retired, savedS2,
    savedStack⟩⟩

/-- The zero-result route as the success-continuation frame. -/
theorem wrapper_dispatch_tag0_route_frame {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103fc))
    (tag : state.regs.get? x10 = some (BitVec.ofNat 64 0)) :
    ∃ after, WrapperDispatchRouteFrame base state after stepNo 6
      (BitVec.ofNat 64 0x1033c) (BitVec.ofNat 64 0) (BitVec.ofNat 64 2) := by
  obtain ⟨⟨after, trace, atTerminal, result, status, retired, memory, platform, codeFinal,
    savedS2, savedStack⟩⟩ :=
    wrapper_dispatch_tag0_success_path machine agree retiredPresent code stepNo atPc tag
  exact ⟨after, ⟨trace, atTerminal, result, status, memory, platform, codeFinal, retired, savedS2,
    savedStack⟩⟩

end BinaryFv.Zesu.MachineExecution
