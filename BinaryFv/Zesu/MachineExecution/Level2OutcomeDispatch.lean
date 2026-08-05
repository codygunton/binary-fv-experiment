import BinaryFv.Zesu.MachineExecution.GeneratedWordStep
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
open RegisterWriteStep GeneratedWordStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- **Pin for `RiscV.callRetirement_writes`.** That lemma writes the link-writing post-execute state
out by hand, because it lives in `RiscV/Step/ControlFlow.lean` and `RiscV/Step/Call.lean` -- where
`callLinkState` is defined -- imports it, so it cannot name `callLinkState`. This is the check that
the hand-written state is still the same one, stated in the lowest module here that sees both. If
`callLinkState` ever changes shape this fails, rather than `callRetirement_writes` quietly ceasing
to apply to anything. -/
theorem callRetirement_writes_callLinkState (state : State) (pc target retired : BitVec 64)
    (linkReg : Register) (linkVal : RegisterType linkReg) :
    WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only linkReg)) state
      (tryStepControlFlowAfterRetired
        (callLinkState (tryStepControlFlowAfterIncrement state) pc target linkReg linkVal)
        target retired) :=
  callRetirement_writes state pc target retired linkReg linkVal

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
  have pcRead : executeState.regs.get? PC = some pc :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      pc).get PC (by decide)).trans
        (pc_afterIncrement state pc atPc)
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
  have pcRead : executeState.regs.get? PC = some pc :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      pc).get PC (by decide)).trans
        (pc_afterIncrement state pc atPc)
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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00300593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x103fc)
  have execute : Runs (execute (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 3) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x003#12 (0#64) = BitVec.ofNat 64 3 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x003#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 3))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x103fc 0x00300593 atPc
    decode execute

/-- Exact post-state of the tag-three branch at `0x10400`. -/
def wrapperDispatchTag3BranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434))
    (BitVec.ofNat 64 0x10434) retired

/-- A jump writes no architectural register beyond the bookkeeping -- the target goes to `nextPC`,
which the bookkeeping already contains -- so this is `jumpRetirement_writes` read at
`platformPreserved`, and the disjointness is the repository-wide one. -/
private theorem wrapperDispatchTag3BranchAfter_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag3BranchAfter state retired) :=
  (jumpRetirement_writes state (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10434) retired).agree
    platformPreserved_disjoint

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10400 0x02b50a63 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree
    (BitVec.ofNat 64 0x10400) atPc (fetchPc _) _ _ _ _ fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x34#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10400)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 3) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10400)).get x10 (by decide)).trans tag
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 3) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10400)).get x11 (by decide)).trans comparison
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BEQ)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    rfl
  have pcAtExecute : executeState.regs.get? PC = some (BitVec.ofNat 64 0x10400) :=
    ((coreControlFlowNextState_writes (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10400)).get PC (by decide)).trans
        (pc_afterIncrement state (BitVec.ofNat 64 0x10400) atPc)
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
    inhibit config byte0 byte1 byte2 byte3 (_get_Misa_C misaBits == 1#1)
    fetch noMMIO fetched interrupts baseEncoding decode
    notExpected condition (readReg_run executeState PC _ pcAtExecute)
    (by decide) (by decide) zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead
  refine ⟨retired, ?_, ?_⟩
  · simpa [wrapperDispatchTag3BranchAfter] using run
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10400 0x02b50a63 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x34#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10400)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 tagValue) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10400)).get x10 (by decide)).trans tag
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 3) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10400)).get x11 (by decide)).trans comparison
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
    (BitVec.ofNat 64 0x10400) (0x34#13) (.Regidx 11#5) (.Regidx 10#5) .BEQ (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode condition

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00100593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10404)
  have execute : Runs (execute (.ITYPE (0x001#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 1) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x001#12 (0#64) = BitVec.ofNat 64 1 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x001#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 1))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10404 0x00100593 atPc
    decode execute

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10408 0x02b50063 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x20#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10408)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 1) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10408)).get x10 (by decide)).trans tag
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 1) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10408)).get x11 (by decide)).trans comparison
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
    (.Regidx 11#5) (.Regidx 10#5) .BEQ (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode
    condition targetEq (by decide) (by decide)

private theorem wrapperDispatchBranchNotTakenAfter_agree (state : State) (pc retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
        (Sail.BitVec.addInt pc 4) retired) :=
  (fallThroughRetirement_writes state pc (Sail.BitVec.addInt pc 4) retired).agree
    platformPreserved_disjoint

private theorem wrapperDispatchJumpAfter_agree (state : State) (pc target retired : BitVec 64) :
    Agree platformPreserved state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) :=
  (jumpRetirement_writes state pc target retired).agree platformPreserved_disjoint

/-- Exact post-state of the tag-one branch at `0x10408`. -/
def wrapperDispatchTag1BranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428))
    (BitVec.ofNat 64 0x10428) retired

private theorem wrapperDispatchTag1BranchAfter_mem (state : State) (retired : BitVec 64) :
    (wrapperDispatchTag1BranchAfter state retired).mem = state.mem := rfl

private theorem wrapperDispatchTag1BranchAfter_agree (state : State) (retired : BitVec 64) :
    Agree platformPreserved state (wrapperDispatchTag1BranchAfter state retired) :=
  (jumpRetirement_writes state (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428) retired).agree
    platformPreserved_disjoint

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10408 0x02b50063 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x20#13, .Regidx 11#5, .Regidx 10#5, .BEQ)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10408)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 tagValue) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10408)).get x10 (by decide)).trans tag
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 1) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10408)).get x11 (by decide)).trans comparison
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
    (BitVec.ofNat 64 0x10408) (0x20#13) (.Regidx 11#5) (.Regidx 10#5) .BEQ (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode condition

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00200593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1040c)
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x1040c 0x00200593 atPc
    decode execute

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10410 0xf2b516e3 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f2c#13, .Regidx 11#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10410)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 2) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10410)).get x10 (by decide)).trans tag
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10410)).get x11 (by decide)).trans comparison
  have condition : Runs (bTypeTaken (.Regidx 11#5) (.Regidx 10#5) .BNE)
      executeState executeState false := by
    unfold bTypeTaken
    refine Runs.bind (rX_bits_run_x10 executeState _ x10AtExecute) ?_
    refine Runs.bind (rX_bits_run_x11 executeState _ x11AtExecute) ?_
    rfl
  exact wrapper_dispatch_branch_not_taken_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10410) (0x1f2c#13) (.Regidx 11#5) (.Regidx 10#5) .BNE (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode condition

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00000513 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10414)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10414 0x00000513 atPc
    decode execute

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00200593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10418)
  have execute : Runs (execute (.ITYPE (0x002#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 2) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x002#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 2))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10418 0x00200593 atPc
    decode execute

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x1041c 0xf41ff06f (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff40#21, zreg)) := by
    rw [wordEq]
    decode_run
  have targetEq : BitVec.ofNat 64 0x1041c + sign_extend (m := 64) (0x1fff40#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c) (0x1fff40#21) (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode
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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10410 0xf2b516e3 (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.BTYPE (0x1f2c#13, .Regidx 11#5, .Regidx 10#5, .BNE)) := by
    rw [wordEq]
    decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10410)
  have x10AtExecute : executeState.regs.get? x10 = some (BitVec.ofNat 64 0) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10410)).get x10 (by decide)).trans tag
  have x11AtExecute : executeState.regs.get? x11 = some (BitVec.ofNat 64 2) :=
    ((stepPremiseState_writes state (BitVec.ofNat 64 0x10410)).get x11 (by decide)).trans comparison
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
    (.Regidx 11#5) (.Regidx 10#5) .BNE (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode
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
    simpa [s1, afterRegisterWrite_mem] using code
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    simpa [s1] using ((afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r1 x11
      (BitVec.ofNat 64 3)).get x10 (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) :=
    afterRegisterWrite_destination state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
      (by decide) (by decide)
  obtain ⟨r2, run2⟩ := wrapper_dispatch_tag3_miss_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1 notTag3
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have retired2 : RetiredCounterPresent s2 := tryStepControlFlowAfterRetired_retired_present _ _ r2
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10404) :=
    Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag1_constant_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10404) r3 x11
    (BitVec.ofNat 64 1)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10408) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have tag3 : s3.regs.get? x10 = some (BitVec.ofNat 64 tagValue) := by
    have tag2 : s2.regs.get? x10 = some (BitVec.ofNat 64 tagValue) :=
      ((fallThroughRetirement_writes s1 (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10404) r2).get
        x10 (by decide)).trans tag1
    simpa [s3] using ((afterRegisterWrite_writes s2 (BitVec.ofNat 64 0x10404) r3 x11
      (BitVec.ofNat 64 1)).get x10 (by decide)).trans tag2
  have comparison3 : s3.regs.get? x11 = some (BitVec.ofNat 64 1) :=
    afterRegisterWrite_destination s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
      (by decide) (by decide)
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag1_miss_step machine agree3 retired3 code3
    (stepNo + 3) pc3 tag3 comparison3 notTag1
  let s4 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s3) (BitVec.ofNat 64 0x10408))
    (BitVec.ofNat 64 0x1040c) r4
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchBranchNotTakenAfter_agree s3 (BitVec.ofNat 64 0x10408) r4)
  have retired4 : RetiredCounterPresent s4 := tryStepControlFlowAfterRetired_retired_present _ _ r4
  have code4 : canonicalContractParams.env.CodeIntact s4 := by
    simpa [s4, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code3
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1040c) :=
    Elfling.tryStepControlFlowAfterRetired_pc _ _ _
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
  · have tag4 : s4.regs.get? x10 = some (BitVec.ofNat 64 tagValue) :=
      ((fallThroughRetirement_writes s3 (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x1040c) r4).get
        x10 (by decide)).trans tag3
    simpa [s5] using ((afterRegisterWrite_writes s4 (BitVec.ofNat 64 0x1040c) r5 x11
      (BitVec.ofNat 64 2)).get x10 (by decide)).trans tag4
  · simpa [s5] using afterRegisterWrite_destination s4 (BitVec.ofNat 64 0x1040c) r5 x11
      (BitVec.ofNat 64 2) (by decide) (by decide)

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00000513 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10434)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10434 0x00000513 atPc
    decode execute

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00300593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10438)
  have execute : Runs (execute (.ITYPE (0x003#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 3) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x003#12 (0#64) = BitVec.ofNat 64 3 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x003#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 3))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10438 0x00300593 atPc
    decode execute

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x1043c 0xf21ff06f (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff20#21, zreg)) := by
    rw [wordEq]
    decode_run
  have targetEq : BitVec.ofNat 64 0x1043c + sign_extend (m := 64) (0x1fff20#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) (0x1fff20#21) (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode
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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00000513 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10428)
  have execute : Runs (execute (.ITYPE (0#12, .Regidx 0#5, .Regidx 10#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x10 (BitVec.ofNat 64 0) }
      (.Retire_Success ()) := by
    simpa using execute_ITYPE_run executeState _ 0#12 (.Regidx 0#5) (.Regidx 10#5) .ADDI
      (0#64) (rX_x0_run executeState) (wX_x10_run executeState (0#64))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10428 0x00000513 atPc
    decode execute

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
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (0x00400593 : BitVec 32))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.ITYPE (0x004#12, .Regidx 0#5, .Regidx 11#5, .ADDI)) := by decode_run
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x1042c)
  have execute : Runs (execute (.ITYPE (0x004#12, .Regidx 0#5, .Regidx 11#5, .ADDI))) executeState
      { executeState with regs := executeState.regs.insert x11 (BitVec.ofNat 64 4) }
      (.Retire_Success ()) := by
    have resultEq : iTypeResult .ADDI 0x004#12 (0#64) = BitVec.ofNat 64 4 := by decide
    simpa [resultEq] using execute_ITYPE_run executeState _ 0x004#12 (.Regidx 0#5) (.Regidx 11#5)
      .ADDI (0#64) (rX_x0_run executeState) (wX_x11_run executeState (BitVec.ofNat 64 4))
  exact generatedRegisterWriteStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x1042c 0x00400593 atPc
    decode execute

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
  obtain ⟨byte0, byte1, byte2, byte3, fetchBytes, wordEq, baseEncoding⟩ :=
    generatedFetch state 0x10430 0xf2dff06f (hasExactErePrefix_programImage_of_codeIntact code)
  obtain ⟨mseccfgBits, privilege, mseccfg⟩ := decodeReads machine agree
  have decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
      (.JAL (0x1fff2c#21, zreg)) := by
    rw [wordEq]
    decode_run
  have targetEq : BitVec.ofNat 64 0x10430 + sign_extend (m := 64) (0x1fff2c#21) =
      BitVec.ofNat 64 0x1035c := by decide
  exact wrapper_dispatch_jump_step machine agree retiredPresent stepNo
    (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c) (0x1fff2c#21) (fetchPc _) atPc
    byte0 byte1 byte2 byte3 fetchBytes baseEncoding decode
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
  have retired5 : RetiredCounterPresent s5 := tryStepControlFlowAfterRetired_retired_present _ _ r5
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    simpa [s1, s2, s3, s4, s5, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code
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
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  · exact ((jumpRetirement_writes s5 (BitVec.ofNat 64 0x10410) (BitVec.ofNat 64 0x1033c) r6).get
      x10 (by decide)).trans tag5
  · exact ((jumpRetirement_writes s5 (BitVec.ofNat 64 0x10410) (BitVec.ofNat 64 0x1033c) r6).get
      x11 (by decide)).trans comparison5
  · exact tryStepControlFlowAfterRetired_retired_present _ _ r6
  · simp [s1, s2, s3, s4, s5, s6, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement]
  · exact agree5.trans (wrapperDispatchJumpAfter_agree s5 (BitVec.ofNat 64 0x10410)
      (BitVec.ofNat 64 0x1033c) r6)
  · simpa [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code5
  · have writes := (afterRegisterWrite_writes state (0x103fc#64) r1 x11 (3#64)).trans
      ((fallThroughRetirement_writes s1 (0x10400#64) (0x10404#64) r2).trans
        ((afterRegisterWrite_writes s2 (0x10404#64) r3 x11 (1#64)).trans
          ((fallThroughRetirement_writes s3 (0x10408#64) (0x1040c#64) r4).trans
            ((afterRegisterWrite_writes s4 (0x1040c#64) r5 x11 (2#64)).trans
              (jumpRetirement_writes s5 (0x10410#64) (0x1033c#64) r6)))))
    exact ⟨writes.get x18 (by decide), writes.get x2 (by decide)⟩

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
  have retired5 : RetiredCounterPresent s5 := tryStepControlFlowAfterRetired_retired_present _ _ r5
  have code5 : canonicalContractParams.env.CodeIntact s5 := by
    simpa [s1, s2, s3, s4, s5, afterRegisterWrite_mem, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code
  obtain ⟨r6, run6⟩ := wrapper_dispatch_tag2_branch_step machine agree5 retired5 code5
    (stepNo + 5) (by simpa [s1, s2, s3, s4, s5] using pc5)
    (by simpa [s1, s2, s3, s4, s5] using tag5)
    (by simpa [s1, s2, s3, s4, s5] using comparison5)
  let s6 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s5) (BitVec.ofNat 64 0x10410))
    (BitVec.ofNat 64 0x10414) r6
  have agree6 : Agree platformPreserved base s6 := agree5.trans
    (wrapperDispatchBranchNotTakenAfter_agree s5 (BitVec.ofNat 64 0x10410) r6)
  have retired6 : RetiredCounterPresent s6 := tryStepControlFlowAfterRetired_retired_present _ _ r6
  have code6 : canonicalContractParams.env.CodeIntact s6 := by
    simpa [s6, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code5
  have pc6 : s6.regs.get? PC = some (BitVec.ofNat 64 0x10414) :=
    Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  obtain ⟨r7, run7⟩ := wrapper_dispatch_tag2_clear_result_step machine agree6 retired6 code6
    (stepNo + 6) pc6
  let s7 := afterRegisterWrite s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)
  have agree7 : Agree platformPreserved base s7 := agree6.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired7 := afterRegisterWrite_retired_present s6 (BitVec.ofNat 64 0x10414) r7 x10
    (BitVec.ofNat 64 0)
  have code7 : canonicalContractParams.env.CodeIntact s7 := by
    simpa [s7, afterRegisterWrite_mem] using code6
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
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  · have x10s7 : s7.regs.get? x10 = some (BitVec.ofNat 64 0) :=
      afterRegisterWrite_destination s6 (BitVec.ofNat 64 0x10414) r7 x10 (BitVec.ofNat 64 0)
        (by decide) (by decide)
    have x10s8 : s8.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s8] using ((afterRegisterWrite_writes s7 (BitVec.ofNat 64 0x10418) r8 x11
        (BitVec.ofNat 64 2)).get x10 (by decide)).trans x10s7
    exact ((jumpRetirement_writes s8 (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c) r9).get
      x10 (by decide)).trans x10s8
  · have x11s8 : s8.regs.get? x11 = some (BitVec.ofNat 64 2) :=
      afterRegisterWrite_destination s7 (BitVec.ofNat 64 0x10418) r8 x11 (BitVec.ofNat 64 2)
        (by decide) (by decide)
    exact ((jumpRetirement_writes s8 (BitVec.ofNat 64 0x1041c) (BitVec.ofNat 64 0x1035c) r9).get
      x11 (by decide)).trans x11s8
  · exact tryStepControlFlowAfterRetired_retired_present _ _ r9
  · simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, afterRegisterWrite_mem,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
  · exact agree8.trans (wrapperDispatchJumpAfter_agree s8 (BitVec.ofNat 64 0x1041c)
      (BitVec.ofNat 64 0x1035c) r9)
  · simpa [s9, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code8
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
    simpa [s1, afterRegisterWrite_mem] using code
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 1) := by
    simpa [s1] using ((afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r1 x11
      (BitVec.ofNat 64 3)).get x10 (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) :=
    afterRegisterWrite_destination state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
      (by decide) (by decide)
  obtain ⟨r2, run2⟩ := wrapper_dispatch_tag3_miss_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1 (by decide)
  let s2 := tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement s1) (BitVec.ofNat 64 0x10400))
    (BitVec.ofNat 64 0x10404) r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchBranchNotTakenAfter_agree s1 (BitVec.ofNat 64 0x10400) r2)
  have retired2 : RetiredCounterPresent s2 := tryStepControlFlowAfterRetired_retired_present _ _ r2
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10404) :=
    Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag1_constant_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10404) r3 x11
    (BitVec.ofNat 64 1)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10408) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
  have tag3 : s3.regs.get? x10 = some (BitVec.ofNat 64 1) := by
    have tag2 : s2.regs.get? x10 = some (BitVec.ofNat 64 1) :=
      ((fallThroughRetirement_writes s1 (BitVec.ofNat 64 0x10400) (BitVec.ofNat 64 0x10404) r2).get
        x10 (by decide)).trans tag1
    simpa [s3] using ((afterRegisterWrite_writes s2 (BitVec.ofNat 64 0x10404) r3 x11
      (BitVec.ofNat 64 1)).get x10 (by decide)).trans tag2
  have comparison3 : s3.regs.get? x11 = some (BitVec.ofNat 64 1) :=
    afterRegisterWrite_destination s2 (BitVec.ofNat 64 0x10404) r3 x11 (BitVec.ofNat 64 1)
      (by decide) (by decide)
  obtain ⟨r4, run4⟩ := wrapper_dispatch_tag1_branch_step machine agree3 retired3 code3
    (stepNo + 3) pc3 tag3 comparison3
  let s4 := wrapperDispatchTag1BranchAfter s3 r4
  have agree4 : Agree platformPreserved base s4 := agree3.trans
    (wrapperDispatchTag1BranchAfter_agree s3 r4)
  have retired4 : RetiredCounterPresent s4 := tryStepControlFlowAfterRetired_retired_present _ _ r4
  have code4 : canonicalContractParams.env.CodeIntact s4 := by
    simpa [s4, wrapperDispatchTag1BranchAfter] using code3
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10428) :=
    Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  refine ⟨⟨s4, Trace.step stepNo 3 state s1 s4 (by simpa [s1] using run1)
    (Trace.step (stepNo + 1) 2 s1 s2 s4 (by simpa [s1, s2] using run2)
    (Trace.step (stepNo + 2) 1 s2 s3 s4 (by simpa [s2, s3] using run3)
    (Trace.step (stepNo + 3) 0 s3 s4 s4
      (by simpa [s3, s4, wrapperDispatchTag1BranchAfter] using run4)
      (Trace.refl (stepNo + 4) s4)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact pc4
  · exact ((jumpRetirement_writes s3 (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428) r4).get
      x10 (by decide)).trans tag3
  · exact ((jumpRetirement_writes s3 (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428) r4).get
      x11 (by decide)).trans comparison3
  · exact retired4
  · calc
      s4.mem = s3.mem := wrapperDispatchTag1BranchAfter_mem s3 r4
      _ = s2.mem := rfl
      _ = s1.mem := rfl
      _ = state.mem := rfl
  · exact agree4
  · exact code4
  · have writes := (afterRegisterWrite_writes state (0x103fc#64) r1 x11 (3#64)).trans
      ((fallThroughRetirement_writes s1 (0x10400#64) (0x10404#64) r2).trans
        ((afterRegisterWrite_writes s2 (0x10404#64) r3 x11 (1#64)).trans
          (jumpRetirement_writes s3 (0x10408#64) (0x10428#64) r4)))
    exact ⟨writes.get x18 (by decide), writes.get x2 (by decide)⟩

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
    simpa [s5, afterRegisterWrite_mem] using code
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
    ConfinedPrefix.ownStep' atPc (by simpa [s5] using run5)
  have p6 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 1) 1 s5 s6 :=
    ConfinedPrefix.ownStep' pc5 (by simpa [s5, s6] using run6)
  have p7 : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary (stepNo + 2) 1 s6 s7 :=
    ConfinedPrefix.ownStep' pc6 (by simpa [s6] using run7)
  have suffixPrefix : ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary stepNo 3 state s7 := by
    confined_steps [p5, p6, p7]
  refine ⟨⟨s7, Trace.step stepNo 2 state s5 s7 (by simpa [s5] using run5)
    (Trace.step (stepNo + 1) 1 s5 s6 s7 (by simpa [s5, s6] using run6)
    (Trace.step (stepNo + 2) 0 s6 s7 s7 (by simpa [s6] using run7)
      (Trace.refl (stepNo + 3) s7))), suffixPrefix, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  · have x10s5 : s5.regs.get? x10 = some (BitVec.ofNat 64 0) :=
      afterRegisterWrite_destination state (BitVec.ofNat 64 0x10428) r5 x10 (BitVec.ofNat 64 0)
        (by decide) (by decide)
    have x10s6 : s6.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s6] using ((afterRegisterWrite_writes s5 (BitVec.ofNat 64 0x1042c) r6 x11
        (BitVec.ofNat 64 4)).get x10 (by decide)).trans x10s5
    exact ((jumpRetirement_writes s6 (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c) r7).get
      x10 (by decide)).trans x10s6
  · have x11s6 : s6.regs.get? x11 = some (BitVec.ofNat 64 4) :=
      afterRegisterWrite_destination s5 (BitVec.ofNat 64 0x1042c) r6 x11 (BitVec.ofNat 64 4)
        (by decide) (by decide)
    exact ((jumpRetirement_writes s6 (BitVec.ofNat 64 0x10430) (BitVec.ofNat 64 0x1035c) r7).get
      x11 (by decide)).trans x11s6
  · exact tryStepControlFlowAfterRetired_retired_present _ _ r7
  · calc
      s7.mem = s6.mem := rfl
      _ = s5.mem := rfl
      _ = state.mem := rfl
  · exact agree6.trans (wrapperDispatchJumpAfter_agree s6 (BitVec.ofNat 64 0x10430)
      (BitVec.ofNat 64 0x1035c) r7)
  · simpa [s7, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code6
  · have writes := (afterRegisterWrite_writes state (0x10428#64) r5 x10 (0#64)).trans
      ((afterRegisterWrite_writes s5 (0x1042c#64) r6 x11 (4#64)).trans
        (jumpRetirement_writes s6 (0x10430#64) (0x1035c#64) r7))
    exact ⟨writes.get x18 (by decide), writes.get x2 (by decide)⟩

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
  obtain ⟨⟨s4, prefixTrace, pc4, tag4, status4, retired4, memory4, agree4, code4, x18_4,
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

/-- The tag-three route reaches the shared rejection continuation with `(a0, a1) = (0, 3)`. -/
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
  obtain ⟨r1, run1⟩ := wrapper_dispatch_tag3_constant_step machine agree retiredPresent code stepNo atPc
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have agree1 : Agree platformPreserved base s1 := agree.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired1 := afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103fc) r1 x11
    (BitVec.ofNat 64 3)
  have code1 : canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x10400) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
  have tag1 : s1.regs.get? x10 = some (BitVec.ofNat 64 3) := by
    simpa [s1] using ((afterRegisterWrite_writes state (BitVec.ofNat 64 0x103fc) r1 x11
      (BitVec.ofNat 64 3)).get x10 (by decide)).trans tag
  have comparison1 : s1.regs.get? x11 = some (BitVec.ofNat 64 3) :=
    afterRegisterWrite_destination state (BitVec.ofNat 64 0x103fc) r1 x11 (BitVec.ofNat 64 3)
      (by decide) (by decide)
  obtain ⟨r2, run2, -⟩ := wrapper_dispatch_tag3_branch_step machine agree1 retired1 code1
    (stepNo + 1) pc1 tag1 comparison1
  let s2 := wrapperDispatchTag3BranchAfter s1 r2
  have agree2 : Agree platformPreserved base s2 := agree1.trans
    (wrapperDispatchTag3BranchAfter_agree s1 r2)
  have retired2 : RetiredCounterPresent s2 := tryStepControlFlowAfterRetired_retired_present _ _ r2
  have code2 : canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, wrapperDispatchTag3BranchAfter] using code1
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10434) :=
    Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  obtain ⟨r3, run3⟩ := wrapper_dispatch_tag3_clear_result_step machine agree2 retired2 code2
    (stepNo + 2) pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
  have agree3 : Agree platformPreserved base s3 := agree2.trans
    (afterRegisterWrite_agree (by simp [platformPreserved]))
  have retired3 := afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10434) r3 x10
    (BitVec.ofNat 64 0)
  have code3 : canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
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
    simpa [s4, afterRegisterWrite_mem] using code3
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x1043c) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
  obtain ⟨r5, run5⟩ := wrapper_dispatch_tag3_to_rejection_step machine agree4 retired4 code4
    (stepNo + 4) pc4
  let s5 := tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement s4)
      (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c))
    (BitVec.ofNat 64 0x1035c) r5
  refine ⟨⟨s5, Trace.step stepNo 4 state s1 s5 (by simpa [s1] using run1)
    (Trace.step (stepNo + 1) 3 s1 s2 s5 (by simpa [s1, s2] using run2)
    (Trace.step (stepNo + 2) 2 s2 s3 s5 (by simpa [s2, s3] using run3)
    (Trace.step (stepNo + 3) 1 s3 s4 s5 (by simpa [s3, s4] using run4)
    (Trace.step (stepNo + 4) 0 s4 s5 s5 (by simpa [s4] using run5)
      (Trace.refl (stepNo + 5) s5))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Elfling.tryStepControlFlowAfterRetired_pc _ _ _
  · have x10s3 : s3.regs.get? x10 = some (BitVec.ofNat 64 0) :=
      afterRegisterWrite_destination s2 (BitVec.ofNat 64 0x10434) r3 x10 (BitVec.ofNat 64 0)
        (by decide) (by decide)
    have x10s4 : s4.regs.get? x10 = some (BitVec.ofNat 64 0) := by
      simpa [s4] using ((afterRegisterWrite_writes s3 (BitVec.ofNat 64 0x10438) r4 x11
        (BitVec.ofNat 64 3)).get x10 (by decide)).trans x10s3
    exact ((jumpRetirement_writes s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5).get
      x10 (by decide)).trans x10s4
  · have x11s4 : s4.regs.get? x11 = some (BitVec.ofNat 64 3) :=
      afterRegisterWrite_destination s3 (BitVec.ofNat 64 0x10438) r4 x11 (BitVec.ofNat 64 3)
        (by decide) (by decide)
    exact ((jumpRetirement_writes s4 (BitVec.ofNat 64 0x1043c) (BitVec.ofNat 64 0x1035c) r5).get
      x11 (by decide)).trans x11s4
  · exact tryStepControlFlowAfterRetired_retired_present _ _ r5
  · simp [s1, s2, s3, s4, s5, afterRegisterWrite_mem, wrapperDispatchTag3BranchAfter,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, controlFlowJumpState,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement]
  · exact agree4.trans (wrapperDispatchJumpAfter_agree s4 (BitVec.ofNat 64 0x1043c)
      (BitVec.ofNat 64 0x1035c) r5)
  · simpa [s5, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      controlFlowJumpState, coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code4
  · have writes := (afterRegisterWrite_writes state (0x103fc#64) r1 x11 (3#64)).trans
      ((jumpRetirement_writes s1 (0x10400#64) (0x10434#64) r2).trans
        ((afterRegisterWrite_writes s2 (0x10434#64) r3 x10 (0#64)).trans
          ((afterRegisterWrite_writes s3 (0x10438#64) r4 x11 (3#64)).trans
            (jumpRetirement_writes s4 (0x1043c#64) (0x1035c#64) r5))))
    exact ⟨writes.get x18 (by decide), writes.get x2 (by decide)⟩

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
