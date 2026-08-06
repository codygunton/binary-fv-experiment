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

theorem decodeInline_owned_instruction_words_pinned :
    ∀ entry ∈ decodeInlineOwnedInstructionWords,
      decodeInlineImageWord? entry.1 = some entry.2 := by
  native_decide

theorem decodeInline_owned_instruction_count :
    decodeInlineOwnedInstructionWords.length = 31 := by
  decide

/-- Every listed instruction lies in the generated execution extent of this compiled instance.
This checks completeness against the proof's confinement predicate independently of DWARF labels. -/
theorem decodeInline_owned_in_execution_region :
    ∀ entry ∈ decodeInlineOwnedInstructionWords, decodeInlineOwnPcs (BitVec.ofNat 64 entry.1) := by
  intro entry member
  simp only [decodeInlineOwnedInstructionWords, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals owned_pc

/-- `postEntry` is memory-only at the canonical `RawV4` representation. This rebases its relative
write frame and transports its result representation when surrounding instructions change only
registers. -/
theorem canonicalPostEntry_of_mem_eq (args : Contracts.EntryArgs)
    (result : Except Contracts.DecodeError BinaryFv.Specs.SSZ.RawV4)
    {before after before' after' : State}
    (beforeMemory : before'.mem = before.mem) (afterMemory : after'.mem = after.mem)
    (post : Contracts.postEntry Contracts.canonicalContractParams.env args
      Contracts.canonicalContractParams.repRawV4 result before after) :
    Contracts.postEntry Contracts.canonicalContractParams.env args
      Contracts.canonicalContractParams.repRawV4 result before' after' := by
  rcases post with ⟨input, code, writes, status, outcome⟩
  refine ⟨?_, ?_, writesOnlyWithinOwnAllocation_of_mem_eq _ _ _ beforeMemory afterMemory writes,
    ?_, ?_⟩
  · intro index bound
    rw [afterMemory]
    exact input index bound
  · change Contracts.canonicalContractParams.env.image.fileBytesMatchMemory after'.mem
    rw [afterMemory]
    exact code
  · rcases status with ⟨tagBound, low, high⟩
    exact ⟨tagBound, by simpa [afterMemory] using low, by simpa [afterMemory] using high⟩
  · cases result with
    | ok value =>
        exact rawV4Rep_of_mem_eq afterMemory outcome
    | error error => exact outcome

/-! ## First segment: preparing the initial `decodeRaw` call -/

theorem decodeInline_first_argument_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state) (phase : args.phase = .first) :
    ∃ after, Trace fromStep 4 state after ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state after ∧
      after.regs.get? PC = some (BitVec.ofNat 64 0x10318) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      after.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      after.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) ∧
      after.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Agree platformPreserved state after ∧ after.mem = state.mem ∧
      RetiredCounterPresent after := by
  let firstResult := iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_first_result_pointer_step fromStep args state pre phase
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x10308) retired1 x10 firstResult
  have w1 : WritesOnlyRegs _ state s1 := afterRegisterWrite_writes _ _ _ _ _
  have preStack := pre.stackValue
  have preInput := pre.inputValue
  have preLength := pre.lengthValue
  have preGlobals := pre.globalsValue
  have agree1 : Agree platformPreserved state s1 :=
    afterRegisterWrite_agree (by simp [platformPreserved])
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x1030c) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x10308) retired1 x10
      firstResult
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  let allocator := iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_first_allocator_pointer_step (fromStep + 1) args
    state s1 pre agree1 rfl
    (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x10308) retired1 x10 firstResult)
    pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  have agree2 : Agree platformPreserved state s2 :=
    Agree.trans agree1 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x10310) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator
  have input2 : s2.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  let input := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.inputBase)
  obtain ⟨retired3, run3⟩ := decodeInline_first_input_pointer_step (fromStep + 2) args
    state s2 pre agree2 rfl
    (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x1030c) retired2 x11 allocator)
    pc2 input2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x10310) retired3 x12 input
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree platformPreserved state s3 :=
    Agree.trans agree2 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x10314) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x10310) retired3 x12 input
  have length3 : s3.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size) := by grind
  let length := iTypeResult .ADDI 0x000#12 (BitVec.ofNat 64 args.bytes.size)
  obtain ⟨retired4, run4⟩ := decodeInline_first_input_length_step (fromStep + 3) args
    state s3 pre agree3 rfl
    (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x10310) retired3 x12 input)
    pc3 length3
  let s4 := afterRegisterWrite s3 (BitVec.ofNat 64 0x10314) retired4 x13 length
  have w4 : WritesOnlyRegs _ s3 s4 := afterRegisterWrite_writes _ _ _ _ _
  have agree4 : Agree platformPreserved state s4 :=
    Agree.trans agree3 (afterRegisterWrite_agree (by simp [platformPreserved]))
  have pc4 : s4.regs.get? PC = some (BitVec.ofNat 64 0x10318) := by
    simpa [s4] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x10314) retired4 x13 length
  have firstResultEq : firstResult =
      BitVec.ofNat 64 args.firstTemporaryResultBase := by
    simp only [firstResult, iTypeResult, DecodeInlineArgs.firstTemporaryResultBase]
    rw [show sign_extend (0x360#12) = (BitVec.ofNat 64 0x360) by decide,
      ← BitVec.ofNat_add]
  have allocatorEq : allocator = BitVec.ofNat 64 args.allocatorBase := by
    simp only [allocator, iTypeResult, DecodeInlineArgs.allocatorBase]
    rw [show sign_extend (0x010#12) = (BitVec.ofNat 64 0x10) by decide,
      ← BitVec.ofNat_add]
  have inputEq : input = BitVec.ofNat 64 args.inputBase := by
    simp [input, iTypeResult]
    decide
  have lengthEq : length = BitVec.ofNat 64 args.bytes.size := by
    simp [length, iTypeResult]
    decide
  have result4 : s4.regs.get? x10 =
      some (BitVec.ofNat 64 args.firstTemporaryResultBase) := by
    simp [s4, s3, s2, s1, firstResultEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have allocator4 : s4.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) := by
    simp [s4, s3, s2, allocatorEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  have input4 : s4.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase) := by
    simp [s4, s3, inputEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have length4 : s4.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) := by
    simp [s4, lengthEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  have stack4 : s4.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have globals4 : s4.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  have notExit1 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10308) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have notExit2 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x1030c) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have notExit3 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10310) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have notExit4 : ¬ DecodeInlineExit args (BitVec.ofNat 64 0x10314) := by
    simp [DecodeInlineExit, phase]
    split <;> decide
  have atFirstEntry : state.regs.get? PC = some (BitVec.ofNat 64 0x10308) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  have prefix1 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' atFirstEntry (by simpa [s1, firstResult] using run1)
      (notExit := notExit1)
  have prefix2 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s2, allocator] using run2) (notExit := notExit2)
  have prefix3 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3, input] using run3) (notExit := notExit3)
  have prefix4 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 3) 1 s3 s4 :=
    ConfinedPrefix.ownStep' pc3 (by simpa [s4, length] using run4) (notExit := notExit4)
  have combinedPrefix : ConfinedPrefix decodeInlineOwnPcs
      (DecodeInlineExit args) Level3ChildSummary fromStep 4 state s4 := by
    confined_steps [prefix1, prefix2, prefix3, prefix4]
  refine ⟨s4, ?_, combinedPrefix, pc4, result4, allocator4, input4, length4, stack4, ?_, ?_, ?_,
    agree4, rfl, afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x10314) retired4 x13 length⟩
  · refine Trace.step fromStep 3 state s1 s4 (by simpa [s1, firstResult] using run1) ?_
    refine Trace.step (fromStep + 1) 2 s1 s2 s4 (by simpa [s2, allocator] using run2) ?_
    refine Trace.step (fromStep + 2) 1 s2 s3 s4 (by simpa [s3, input] using run3) ?_
    exact Trace.one (fromStep + 3) s3 s4 (by simpa [s4, length] using run4)
  · grind
  · grind
  · exact globals4

theorem decodeInline_first_decodeRaw_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1031c))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x10318))
    (resultPointer : state.regs.get? x10 =
      some (BitVec.ofNat 64 args.firstTemporaryResultBase))
    (allocatorPointer : state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase))
    (inputPointer : state.regs.get? x12 = some (BitVec.ofNat 64 args.inputBase))
    (inputLength : state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size))
    (inputBase : state.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase))
    (lengthBase : state.regs.get? x9 = some (BitVec.ofNat 64 args.bytes.size))
    (globalsBase : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020)) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineFirstCallAfter state retired) false ∧
      (decodeInlineFirstCallAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10444) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x1 =
        some (BitVec.ofNat 64 0x10320) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x10 =
        some (BitVec.ofNat 64 args.firstTemporaryResultBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x11 =
        some (BitVec.ofNat 64 args.allocatorBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x12 =
        some (BitVec.ofNat 64 args.inputBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x13 =
        some (BitVec.ofNat 64 args.bytes.size) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x8 =
        some (BitVec.ofNat 64 args.inputBase) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x9 =
        some (BitVec.ofNat 64 args.bytes.size) ∧
      (decodeInlineFirstCallAfter state retired).regs.get? x18 =
        some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state (decodeInlineFirstCallAfter state retired) ∧
      (decodeInlineFirstCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineFirstCallAfter state retired) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree pre.machine agree
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (decodeInlineFirstCallAfter state retired) false :=
    decoderJalrCallStep pre.machine agree retiredPresent
      (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
      stepNo 0x1031c 0xe7 0x80 0xc0 0x12 0x12c#12 1#5 1#5 (BitVec.ofNat 64 0x10318)
      (BitVec.ofNat 64 0x10320) (BitVec.ofNat 64 0x10444) atPc
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? callBase)) (wX_bits_run_x1 _ _)
  have callWrites : WritesOnlyRegs _ state (decodeInlineFirstCallAfter state retired) :=
    callRetirement_writes _ _ _ _ _ _
  -- Regression for the seven carries below: `grind` must refuse what the call writes.
  fail_if_success (have : (decodeInlineFirstCallAfter state retired).regs.get? x1 =
    state.regs.get? x1 := by grind)
  fail_if_success (have : (decodeInlineFirstCallAfter state retired).regs.get? PC =
    state.regs.get? PC := by grind)
  have pcAfter : (decodeInlineFirstCallAfter state retired).regs.get? PC =
      some (BitVec.ofNat 64 0x10444) := by
    simp [decodeInlineFirstCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have linkAfter : (decodeInlineFirstCallAfter state retired).regs.get? x1 =
      some (BitVec.ofNat 64 0x10320) := by
    apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x10320)
    · decide
    · decide
  have callAgree : Agree decoderPreserved state (decodeInlineFirstCallAfter state retired) := by
    apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  have callMemory : (decodeInlineFirstCallAfter state retired).mem = state.mem :=
    jalrCallAfterRetired_mem _ _ _ _ _ _
  refine ⟨retired, run, pcAfter, linkAfter, by grind, by grind, by grind, by grind, by grind,
    by grind, by grind, callAgree, callMemory, ?_⟩
  exact ⟨Sail.BitVec.addInt retired 1, by
    simp [decodeInlineFirstCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩

end BinaryFv.Zesu.MachineExecution
