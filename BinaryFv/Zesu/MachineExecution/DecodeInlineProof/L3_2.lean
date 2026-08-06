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
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_10
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_11
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_12
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_13
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_14
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_15
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_16
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_17
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_18
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_19
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_20
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_21
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_9

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

end BinaryFv.Zesu.MachineExecution
