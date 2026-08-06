import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_3

/-!
# Sail proof for the inlined `decode` scope

This file executes the 31 instructions owned directly by the compiler's inlined `decode` instance
and composes them with the three Level 3 child summaries. The inventory below is the reviewable
starting point: every owned word is checked against the pinned program image before any path proof
uses it.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem decodeInline_first_before_decodeRaw_call (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ beforeCall, Trace fromStep 5 state beforeCall ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x10318) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) ∧
      beforeCall.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      beforeCall.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state beforeCall ∧ beforeCall.mem = state.mem ∧
      RetiredCounterPresent beforeCall := by
  obtain ⟨afterArgs, argsTrace, argsPrefix, argsPc, resultArgs, allocatorArgs, inputArgs,
    lengthArgs, stackArgs, inputBaseArgs, inputLengthArgs, globalsArgs, argsAgree, argsMemory, argsRetired⟩ :=
    decodeInline_first_argument_setup fromStep args state pre phase
  obtain ⟨retired, callPageStep⟩ := decodeInline_first_call_page_step (fromStep + 4) args
    state afterArgs pre argsAgree argsMemory argsRetired argsPc
  let beforeCall := afterRegisterWrite afterArgs (BitVec.ofNat 64 0x10318) retired x1
    (BitVec.ofNat 64 0x10318)
  have callPc : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c) := by
    simpa [beforeCall] using afterRegisterWrite_pc afterArgs (BitVec.ofNat 64 0x10318)
      retired x1 (BitVec.ofNat 64 0x10318)
  have returnBase : beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x10318) := by
    simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have callPageWrites : WritesOnlyRegs _ afterArgs beforeCall := afterRegisterWrite_writes _ _ _ _ _
  have callPageAgree : Agree decoderPreserved afterArgs beforeCall := by
    apply afterRegisterWrite_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have memoryUnchanged : beforeCall.mem = state.mem := by
    change (afterRegisterWrite afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).mem = state.mem
    exact (afterRegisterWrite_mem afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)).trans argsMemory
  have callPageNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10318) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have callPagePrefix : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args)
      Level3ChildSummary (fromStep + 4) 1 afterArgs beforeCall :=
    ConfinedPrefix.ownStep' argsPc (by simpa [beforeCall] using callPageStep)
      (notExit := callPageNotExit)
  have combinedPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 5 state beforeCall := by
    confined_steps [argsPrefix, callPagePrefix]
  refine ⟨beforeCall, ?_, combinedPrefix, callPc, returnBase, by grind, by grind, by grind,
    by grind, by grind, by grind, by grind, by grind,
    Agree.trans (Agree.weaken (fun _ preserved => preserved.2) argsAgree) callPageAgree,
    memoryUnchanged,
    afterRegisterWrite_retired_present afterArgs (BitVec.ofNat 64 0x10318) retired x1
      (BitVec.ofNat 64 0x10318)⟩
  exact Trace.snoc argsTrace (by simpa [beforeCall] using callPageStep)

def decodeRawFirstCallTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (phase : args.phase = .first) (beforeCall childEntry childExit resumed : State)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x1031c))
    (callRun : Runs (try_step fromStep false) beforeCall childEntry false)
    (childPre : compiledDecodeRawContract.binding.entry args.firstRawArgs childEntry)
    (bound : used ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      (fromStep + 1) used childEntry childExit)
    (childPost : compiledDecodeRawContract.binding.exit args.firstRawArgs
      (compiledDecodeRawContract.spec.meaning args.firstRawArgs) childEntry childExit)
    (returnRun : Runs (try_step (fromStep + 1 + used) false) childExit resumed false)
    (atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x10320)) :
    CallTransfer decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary decodeRawFirstAttemptCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw fromStep used beforeCall resumed := by
  have atRet := decodeRaw_trace_exit_pc childTrace
  have callInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x1031c) :=
    decodeInline_owned_in_execution_region (0x1031c, 0x12c080e7)
      (by simp [decodeInlineOwnedInstructionWords])
  have returnInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x10320) :=
    decodeInline_owned_in_execution_region (0x10320, 0x6a015503)
      (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x10530) := by owned_pc
  have callNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1031c) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have retNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10530) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have body : Level3ChildSummary functionInstance_ssz_raw_decodeRawId
      (fromStep + 1) used childEntry childExit :=
    Level3ChildSummary.decodeRaw
      ⟨rfl, args.firstRawArgs, childPre, bound, childTrace, childPost⟩
  exact
    { valid := decodeRawFirstAttemptCall_valid
      callPc := BitVec.ofNat 64 0x1031c
      atCall := atCall
      callSource := by decide
      callInRegion := callInRegion
      callNotExit := callNotExit
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x10444
      atCalleeEntry := childPre.2.1
      calleeEntryMatches := by decide
      sRet := childExit
      body := body
      retPc := BitVec.ofNat 64 0x10530
      atRet := atRet
      retInRegion := retInRegion
      retNotExit := retNotExit
      doReturn := returnRun
      returnPc := BitVec.ofNat 64 0x10320
      atResume := atResume
      returnMatches := by decide
      resumeInRegion := returnInRegion }

/-- The four successful-result copy arguments are not an assumed ABI boundary. They are the exact
Sail execution of the parent-owned words at `0x10328..0x10334`, stopping on the selected emitted
`memcpy` call instruction at `0x10338`. -/
theorem decodeInline_first_success_copy_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (phase : args.phase = .first) (value : BinaryFv.Specs.SSZ.RawV4)
    (success : Contracts.meaningDecodeRaw args.bytes = .ok value)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10328))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (globals : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (post : Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
      Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
      baseState state) :
    ∃ after,
      Trace fromStep 4 state after ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10338) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      after.regs.get? x1 = some (BitVec.ofNat 64 0x14334) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      Agree decoderPreserved baseState after ∧
      RetiredCounterPresent after ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      Contracts.postEntry Contracts.canonicalContractParams.env args.firstRawArgs
        Contracts.canonicalContractParams.repRawV4 (Contracts.meaningDecodeRaw args.bytes)
        baseState after ∧
      after.mem = state.mem := by
  let destination := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_first_success_copy_destination_step fromStep args
    baseState state pre agree retiredPresent code atPc stackRead
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10328) retired1 x10 destination
  have w1 : WritesOnlyRegs _ state s1 := afterRegisterWrite_writes _ _ _ _ _
  have agree1 : Agree decoderPreserved baseState s1 :=
    Agree.trans agree (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1032c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10328) retired1 x10 destination
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have code1 : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
  let source := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_first_success_copy_source_step (fromStep + 1) args
    baseState s1 pre agree1
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10328) retired1 x10 destination)
    code1 pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  have agree2 : Agree decoderPreserved baseState s2 :=
    Agree.trans agree1 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10330) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, afterRegisterWrite_mem] using code1
  let length := iTypeResult .ADDI 0x340#12 (0#64)
  obtain ⟨retired3, run3⟩ := decodeInline_first_success_copy_length_step (fromStep + 2) args
    baseState s2 pre agree2
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1032c) retired2 x11 source)
    code2 pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10330) retired3 x12 length
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree decoderPreserved baseState s3 :=
    Agree.trans agree2 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10334) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10330) retired3 x12 length
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  obtain ⟨retired4, run4⟩ := decodeInline_first_success_copy_call_page_step
    (fromStep + 3) args baseState s3 pre agree3
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10330) retired3 x12 length)
    code3 pc3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10334) retired4 x1
    (BitVec.ofNat 64 0x14334)
  have w4 : WritesOnlyRegs _ s3 s4 := afterRegisterWrite_writes _ _ _ _ _
  have destinationEq : destination = BitVec.ofNat 64 args.finalResultBase := by
    simp only [destination, iTypeResult, DecodeInlineArgs.finalResultBase]
    rw [show sign_extend (0x020#12) = (BitVec.ofNat 64 0x20) by decide,
      ← BitVec.ofNat_add]
  have sourceEq : source = BitVec.ofNat 64 args.firstTemporaryResultBase := by
    simp only [source, iTypeResult, DecodeInlineArgs.firstTemporaryResultBase]
    rw [show sign_extend (0x360#12) = (BitVec.ofNat 64 0x360) by decide,
      ← BitVec.ofNat_add]
  have lengthEq : length = BitVec.ofNat 64 832 := by
    simp [length, iTypeResult]
    decide
  have memory4 : s4.mem = state.mem := by
    simp [s4, s3, s2, s1, afterRegisterWrite_mem]
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have stack4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have notExit1 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10328) := by
    simp [DecodeInlineExit, phase, success]
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1032c) := by
    simp [DecodeInlineExit, phase, success]
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10330) := by
    simp [DecodeInlineExit, phase, success]
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10334) := by
    simp [DecodeInlineExit, phase, success]
  have prefix1 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' atPc (by simpa [s1, destination] using run1) (notExit := notExit1)
  have prefix2 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s2, source] using run2) (notExit := notExit2)
  have prefix3 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3, length] using run3) (notExit := notExit3)
  have prefix4 : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s4] using run4) (notExit := notExit4)
  have completePrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 4 state s4 := by
    confined_steps [prefix1, prefix2, prefix3, prefix4]
  refine ⟨s4, ?_, completePrefix, ?_, ?_, ?_, ?_, ?_, ?_, stack4, ?_, ?_, ?_, ?_, ?_⟩
  · refine Trace.step fromStep 3 state s1 s4 (by simpa [s1, destination] using run1) ?_
    refine Trace.step (fromStep + 1) 2 s1 s2 s4 (by simpa [s2, source] using run2) ?_
    refine Trace.step (fromStep + 2) 1 s2 s3 s4 (by simpa [s3, length] using run3) ?_
    exact Trace.one (fromStep + 3) s3 s4 (by simpa [s4] using run4)
  · simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10334) retired4 x1
      (BitVec.ofNat 64 0x14334)
  · simp [s4, s3, s2, s1, destinationEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [s4, s3, s2, sourceEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [s4, s3, lengthEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]
  · exact globals4
  · exact Agree.trans agree3
      (afterRegisterWrite_agree_of (by simp [decoderPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved])
        (by simp [decoderPreserved, platformPreserved]))
  · exact afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10334) retired4 x1
      (BitVec.ofNat 64 0x14334)
  · simpa [memory4] using code
  · apply canonicalPostEntry_of_mem_eq args.firstRawArgs
      (Contracts.meaningDecodeRaw args.bytes) rfl memory4
    exact post
  · simp [s4, s3, s2, s1, afterRegisterWrite_mem]

/-- Execute the retry-entry branch and all three parent-owned constant instructions, stopping at
the selected prefix helper's length-segment entry. -/
theorem decodeInline_retry_reaches_length_gate (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ after,
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10390) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) ∧
      Agree decoderPreserved state after ∧
      RetiredCounterPresent after ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 2) ∧
      Contracts.canonicalContractParams.env.CodeIntact after ∧
      after.mem = state.mem ∧
      HasExactErePrefixInlinePre
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } after := by
  obtain ⟨branchRetired, branchRun, branchPc⟩ :=
    decodeInline_retry_entry_branch_step fromStep args state pre phase
  let s1 := decodeInlineRetryEntryAfter state branchRetired
  have w1 : WritesOnlyRegs _ state s1 := fallThroughRetirement_writes _ _ _ _
  have preStack := pre.stackValue
  have preInput := pre.inputValue
  have preLength := pre.lengthValue
  have preGlobals := pre.globalsValue
  have branchAgree : Agree decoderPreserved state s1 :=
    Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  have branchCounter : RetiredCounterPresent s1 := by
    refine ⟨Sail.BitVec.addInt branchRetired 1, ?_⟩
    simp [s1, decodeInlineRetryEntryAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]
  have branchMemory : s1.mem = state.mem := rfl
  have branchCode : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    rw [Contracts.DecoderEnvironment.CodeIntact, branchMemory]
    exact pre.code
  obtain ⟨minusOneRetired, minusOneRun⟩ := decodeInline_retry_minus_one_step
    (fromStep + 1) args state s1 pre branchAgree branchCounter branchCode branchPc
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
    (BitVec.ofNat 64 (2 ^ 64 - 1))
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  -- Regression for the write-set carry below: `grind` must refuse the register this step writes.
  fail_if_success (have : s2.regs.get? x10 = s1.regs.get? x10 := by grind)
  have agree2 : Agree decoderPreserved state s2 :=
    Agree.trans branchAgree (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10388) := by
    change (afterRegisterWrite s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 1))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At2 : s2.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 1)) := by
    simp [s2, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, afterRegisterWrite_mem] using branchCode
  obtain ⟨shiftRetired, shiftRun⟩ := decodeInline_retry_shift_constant_step
    (fromStep + 2) args state s2 pre agree2
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x10384) minusOneRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 1))) code2 pc2 x10At2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree decoderPreserved state s3 :=
    Agree.trans agree2 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x1038c) := by
    change (afterRegisterWrite s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At3 : s3.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by
    simp [s3, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  obtain ⟨minusFourRetired, minusFourRun⟩ := decodeInline_retry_minus_four_step
    (fromStep + 3) args state s3 pre agree3
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10388) shiftRetired x10
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) code3 pc3 x10At3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
    (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  have w4 : WritesOnlyRegs _ s3 s4 := afterRegisterWrite_writes _ _ _ _ _
  fail_if_success (have : s4.regs.get? x12 = s3.regs.get? x12 := by grind)
  have agree4 : Agree decoderPreserved state s4 :=
    Agree.trans agree3 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10390) := by
    change (afterRegisterWrite s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))).regs.get? PC = _
    rw [afterRegisterWrite_pc]
    decide
  have x10At4 : s4.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) := by grind
  have x12At4 : s4.regs.get? x12 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4)) := by
    simp [s4, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have code4 : Contracts.canonicalContractParams.env.CodeIntact s4 :=
    codeIntact_of_mem_eq (afterRegisterWrite_mem s3 (BitVec.ofNat 64 0x1038c) minusFourRetired x12
      (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))) code3
  have counter4 := afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x1038c)
    minusFourRetired x12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))
  let childArgs : HasExactErePrefixInlineArgs :=
    { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes }
  have memory4 : s4.mem = state.mem := rfl
  have inputPointer4 : s4.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have inputLength4 : s4.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have stackPointer4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have status4 : s4.regs.get? x11 = some (BitVec.ofNat 64 2) := by
    obtain ⟨-, -, statusAtEntry⟩ := pre.retryReason phase
    grind
  have inputMemory4 : BinaryFv.Zesu.MemoryRepresentation.MemoryBytes s4 args.inputBase args.bytes := by
    intro index bound
    rw [memory4]
    exact pre.inputMemory index bound
  have parentMachine4 : DecodeInlineMachinePre args s4 :=
    pre.machine.mono agree4 counter4
  have childMachine4 : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35)
      childArgs.machineArgs s4 := by
    simpa [childArgs, HasExactErePrefixInlineArgs.machineArgs, DecodeInlineArgs.machineArgs] using
      parentMachine4.restrict hasExactErePrefix_executionPcs_subset_decode
  have childPre : HasExactErePrefixInlinePre childArgs s4 := by
    refine ⟨?_, inputPointer4, inputLength4, globals4, inputMemory4, code4, pre.inputFits,
      pre.rootInputBound, ?_, ?_, childMachine4⟩
    · simpa [childArgs, HasExactErePrefixInlineArgs.entryPc] using pc4
    · intro _
      exact ⟨x10At4, x12At4⟩
    · simp [childArgs]
  have notExit1 := decodeInline_retry_entry_not_selected_exit args phase
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10384) := by
    simp [DecodeInlineExit, phase]
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10388) := by
    simp [DecodeInlineExit, phase]
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1038c) := by
    simp [DecodeInlineExit, phase]
  have p1 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' (by simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry)
      (by simpa [s1] using branchRun) (notExit := notExit1)
  have p2 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' branchPc (by simpa [s2] using minusOneRun) (notExit := notExit2)
  have p3 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3] using shiftRun) (notExit := notExit3)
  have p4 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s4] using minusFourRun) (notExit := notExit4)
  refine ⟨s4, ?_, pc4, x10At4, x12At4, agree4, counter4, stackPointer4, status4, code4,
    memory4, ?_⟩
  · confined_steps [p1, p2, p3, p4]
  · simpa [childArgs] using childPre

def decodeRawRetryCallTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (beforeCall childEntry childExit resumed : State)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103d8))
    (callRun : Runs (try_step fromStep false) beforeCall childEntry false)
    (childPre : compiledDecodeRawContract.binding.entry args.retryRawArgs childEntry)
    (bound : used ≤ compiledDecodeRawContract.binding.stepBound args.retryRawArgs)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      (fromStep + 1) used childEntry childExit)
    (childPost : compiledDecodeRawContract.binding.exit args.retryRawArgs
      (compiledDecodeRawContract.spec.meaning args.retryRawArgs) childEntry childExit)
    (returnRun : Runs (try_step (fromStep + 1 + used) false) childExit resumed false)
    (atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x103dc)) :
    CallTransfer decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary decodeRawRetryCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_ssz_raw_decodeRaw fromStep used beforeCall resumed := by
  have atRet := decodeRaw_trace_exit_pc childTrace
  have callInRegion := decodeInline_owned_in_execution_region (0x103d8, 0x070080e7)
    (by simp [decodeInlineOwnedInstructionWords])
  have returnInRegion := decodeInline_owned_in_execution_region (0x103dc, 0x02010513)
    (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x10530) := by owned_pc
  have callNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103d8) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have retNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10530) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have body : Level3ChildSummary functionInstance_ssz_raw_decodeRawId
      (fromStep + 1) used childEntry childExit :=
    Level3ChildSummary.decodeRaw
      ⟨rfl, args.retryRawArgs, childPre, bound, childTrace, childPost⟩
  exact
    { valid := decodeRawRetryCall_valid
      callPc := BitVec.ofNat 64 0x103d8
      atCall := atCall
      callSource := by decide
      callInRegion := callInRegion
      callNotExit := callNotExit
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x10444
      atCalleeEntry := childPre.2.1
      calleeEntryMatches := by decide
      sRet := childExit
      body := body
      retPc := BitVec.ofNat 64 0x10530
      atRet := atRet
      retInRegion := retInRegion
      retNotExit := retNotExit
      doReturn := returnRun
      returnPc := BitVec.ofNat 64 0x103dc
      atResume := atResume
      returnMatches := by decide
      resumeInRegion := returnInRegion }

/-- Execute the retry call and consume the already-proved compiled `memcpy` contract on the exact
832-byte payload retained from the second `decodeRaw` result. -/
theorem decodeInline_retry_uses_memcpy (fromStep : Nat) (args : DecodeInlineArgs)
    (contents : ByteArray) (baseState beforeCall : State) (pre : DecodeInlinePre args baseState)
    (contentsSize : contents.size = 832)
    (sourceMemory : MemoryRepresentation.MemoryBytes beforeCall
      args.retryRawArgs.resultBase contents)
    (agree : Agree decoderPreserved baseState beforeCall)
    (counter : RetiredCounterPresent beforeCall)
    (code : Contracts.canonicalContractParams.env.CodeIntact beforeCall)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec))
    (callBase : beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x143e8))
    (destination : beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase))
    (source : beforeCall.regs.get? x11 = some
      (BitVec.ofNat 64 args.retryRawArgs.resultBase))
    (length : beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832)) :
    ∃ callRetired childUsed childEntry childExit,
      childEntry = decodeInlineMemcpyCallAfter beforeCall callRetired ∧
      childEntry.regs.get? x18 = beforeCall.regs.get? x18 ∧
      Runs (try_step fromStep false) beforeCall childEntry false ∧
      (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.entry
        (decodeInlineRetryCopyArgs args contents) childEntry ∧
      childUsed ≤ (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.stepBound
        (decodeInlineRetryCopyArgs args contents) ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
        (functionInstanceExitPred functionInstance_memcpy)
        (Contracts.functionInstanceEntryWord functionInstance_memcpy)
        (fromStep + 1) childUsed childEntry childExit ∧
      (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.exit
        (decodeInlineRetryCopyArgs args contents)
        ((compiledMemcpyContract Contracts.canonicalContractParams.env).spec.meaning
          (decodeInlineRetryCopyArgs args contents)) childEntry childExit := by
  obtain ⟨callRetired, callRun, childPc, childLink, childDestination, childSource,
    childLength, childStack, callAgree, callMemory, childCounter⟩ :=
    decodeInline_retry_memcpy_call_step fromStep args baseState beforeCall pre agree
      code counter atCall callBase
  let childEntry := decodeInlineMemcpyCallAfter beforeCall callRetired
  have callWrites : WritesOnlyRegs _ beforeCall childEntry := callRetirement_writes _ _ _ _ _ _
  let copyArgs := decodeInlineRetryCopyArgs args contents
  have childAgree : Agree decoderPreserved baseState childEntry := Agree.trans agree callAgree
  have childCode : Contracts.canonicalContractParams.env.CodeIntact childEntry := by
    rw [Contracts.DecoderEnvironment.CodeIntact, show childEntry.mem = beforeCall.mem by
      simpa [childEntry] using callMemory]
    exact code
  have childSourceMemory : MemoryRepresentation.MemoryBytes childEntry
      args.retryRawArgs.resultBase contents := by
    intro index bound
    rw [show childEntry.mem = beforeCall.mem by simpa [childEntry] using callMemory]
    exact sourceMemory index bound
  have machinePre : MemcpyMachinePre Contracts.canonicalContractParams.env copyArgs childEntry := by
    apply decodeInline_retry_memcpy_machine_pre args contents baseState childEntry pre childAgree
      childCounter
    · simpa [childEntry] using childPc
    · simpa [childEntry] using childLink
  have sourcePre : (Contracts.contractMemcpy Contracts.canonicalContractParams.env).pre
      copyArgs childEntry := by
    constructor
    · refine ⟨childSourceMemory, ?_, childCode, ?_, ?_, ?_⟩
      · simpa [copyArgs, decodeInlineRetryCopyArgs] using contentsSize
      · simpa [copyArgs, decodeInlineRetryCopyArgs, childEntry] using childDestination.trans destination
      · simpa [copyArgs, decodeInlineRetryCopyArgs, childEntry] using childSource.trans source
      · simpa [copyArgs, decodeInlineRetryCopyArgs, childEntry] using childLength.trans length
    · left
      dsimp [copyArgs, decodeInlineRetryCopyArgs, DecodeInlineArgs.finalResultBase,
        DecodeInlineArgs.retryRawArgs]
      omega
  have compiledEntry :
      (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.entry
        copyArgs childEntry := ⟨sourcePre, machinePre⟩
  obtain ⟨childUsed, childExit, childBound, childTrace, childPost⟩ :=
    compiledMemcpyInstanceContract_proved copyArgs (fromStep + 1) childEntry compiledEntry
  exact ⟨callRetired, childUsed, childEntry, childExit, rfl, by grind,
    by simpa [childEntry] using callRun,
    compiledEntry, childBound, childTrace, childPost⟩

/-- Package the retry `memcpy` call, proved child execution, and real return as the checked call
boundary consumed by the enclosing Level 3 trace. -/
def memcpyRetryCallTransfer (fromStep used : Nat) (args : DecodeInlineArgs)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (contents : ByteArray) (beforeCall childEntry childExit resumed : State)
    (atCall : beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec))
    (callRun : Runs (try_step fromStep false) beforeCall childEntry false)
    (childPre : (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.entry
      (decodeInlineRetryCopyArgs args contents) childEntry)
    (bound : used ≤ (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.stepBound
      (decodeInlineRetryCopyArgs args contents))
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
      (functionInstanceExitPred functionInstance_memcpy)
      (Contracts.functionInstanceEntryWord functionInstance_memcpy)
      (fromStep + 1) used childEntry childExit)
    (childPost : (compiledMemcpyContract Contracts.canonicalContractParams.env).binding.exit
      (decodeInlineRetryCopyArgs args contents)
      ((compiledMemcpyContract Contracts.canonicalContractParams.env).spec.meaning
        (decodeInlineRetryCopyArgs args contents)) childEntry childExit)
    (returnRun : Runs (try_step (fromStep + 1 + used) false) childExit resumed false)
    (atResume : resumed.regs.get? PC = some (BitVec.ofNat 64 0x103f0)) :
    CallTransfer decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary memcpyRetryCall generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
      functionInstance_memcpy fromStep used beforeCall resumed := by
  have atRet : childExit.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) := by
    obtain ⟨retPc, atRet, retIsExit⟩ := childTrace.trace.final_at_exit
    have retPcEq : retPc = BitVec.ofNat 64 0x13ec0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using retIsExit
    simpa [retPcEq] using atRet
  have callInRegion := decodeInline_owned_in_execution_region (0x103ec, 0xad0080e7)
    (by simp [decodeInlineOwnedInstructionWords])
  have resumeInRegion := decodeInline_owned_in_execution_region (0x103f0, 0x00001537)
    (by simp [decodeInlineOwnedInstructionWords])
  have retInRegion : decodeInlineOwnPcs (BitVec.ofNat 64 0x13ec0) := by owned_pc
  have callNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x103ec) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have retNotExit : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x13ec0) := by
    simp [DecodeInlineExit, phase, exactPrefix]
  have body : Level3ChildSummary functionInstance_memcpyId
      (fromStep + 1) used childEntry childExit :=
    Level3ChildSummary.memcpy
      ⟨rfl, decodeInlineRetryCopyArgs args contents, childPre, bound, childTrace, childPost⟩
  exact
    { valid := memcpyRetryCall_valid
      callPc := BitVec.ofNat 64 0x103ec
      atCall
      callSource := by decide
      callInRegion
      callNotExit
      sCall := childEntry
      doCall := callRun
      calleeEntryPc := BitVec.ofNat 64 0x13eb8
      atCalleeEntry := childPre.2.entry
      calleeEntryMatches := by decide
      sRet := childExit
      body
      retPc := BitVec.ofNat 64 0x13ec0
      atRet
      retInRegion
      retNotExit
      doReturn := returnRun
      returnPc := BitVec.ofNat 64 0x103f0
      atResume
      returnMatches := by decide
      resumeInRegion }

end BinaryFv.Zesu.MachineExecution
