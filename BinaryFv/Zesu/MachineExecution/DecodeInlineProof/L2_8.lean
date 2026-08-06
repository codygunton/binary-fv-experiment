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

/-- Execute the second emitted `decodeRaw` call at `0x103d8` through Sail. -/
theorem decodeInline_retry_decodeRaw_call_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state) (memory : state.mem = baseState.mem)
    (retiredPresent : RetiredCounterPresent state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103d8))
    (callBase : state.regs.get? x1 = some (BitVec.ofNat 64 0x103d4))
    (resultPointer : state.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x6b0)))
    (allocatorPointer : state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase))
    (inputPointer : state.regs.get? x12 = some (BitVec.ofNat 64 (args.inputBase + 4)))
    (inputLength : state.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4))) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineRetryCallAfter state retired) false ∧
      (decodeInlineRetryCallAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10444) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x1 =
        some (BitVec.ofNat 64 0x103dc) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x10 =
        some (BitVec.ofNat 64 (args.stackBase + 0x6b0)) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x11 =
        some (BitVec.ofNat 64 args.allocatorBase) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x12 =
        some (BitVec.ofNat 64 (args.inputBase + 4)) ∧
      (decodeInlineRetryCallAfter state retired).regs.get? x13 =
        some (BitVec.ofNat 64 (args.bytes.size - 4)) ∧
      Agree decoderPreserved state (decodeInlineRetryCallAfter state retired) ∧
      (decodeInlineRetryCallAfter state retired).mem = state.mem ∧
      RetiredCounterPresent (decodeInlineRetryCallAfter state retired) := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree pre.machine agree
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (decodeInlineRetryCallAfter state retired) false :=
    decoderJalrCallStep pre.machine agree retiredPresent
      (by rw [memory]; exact hasExactErePrefix_programImage_of_codeIntact pre.code)
      stepNo 0x103d8 0xe7 0x80 0x00 0x07 0x070#12 1#5 1#5 (BitVec.ofNat 64 0x103d4)
      (BitVec.ofNat 64 0x103dc) (BitVec.ofNat 64 0x10444) atPc
      (rX_bits_run_x1 _ _ (decoderExecuteState_get? callBase)) (wX_bits_run_x1 _ _)
  have callWrites : WritesOnlyRegs _ state (decodeInlineRetryCallAfter state retired) :=
    callRetirement_writes _ _ _ _ _ _
  fail_if_success (have : (decodeInlineRetryCallAfter state retired).regs.get? x1 =
    state.regs.get? x1 := by grind)
  have pcAfter : (decodeInlineRetryCallAfter state retired).regs.get? PC =
      some (BitVec.ofNat 64 0x10444) := by
    simp [decodeInlineRetryCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  have linkAfter : (decodeInlineRetryCallAfter state retired).regs.get? x1 =
      some (BitVec.ofNat 64 0x103dc) := by
    apply tryStepControlFlowAfterRetired_preserves_register
    · exact callLinkState_link _ _ _ x1 (BitVec.ofNat 64 0x103dc)
    · decide
    · decide
  have callAgree : Agree decoderPreserved state (decodeInlineRetryCallAfter state retired) := by
    apply jalrCallAfterRetired_agree_of
    all_goals simp [decoderPreserved, platformPreserved]
  refine ⟨retired, run, pcAfter, linkAfter, by grind, by grind, by grind, by grind,
    callAgree, jalrCallAfterRetired_mem _ _ _ _ _ _, ?_⟩
  exact ⟨Sail.BitVec.addInt retired 1, by
    simp [decodeInlineRetryCallAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]⟩

/-- Execute the four retry-copy setup words and establish the exact compiled `memcpy` arguments. -/
theorem decodeInline_retry_copy_setup (fromStep : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (globalsRead : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103dc))
    (payload : DecodeRawResultPayloadInitialized args.retryRawArgs state) :
    ∃ contents beforeCall,
      contents.size = 832 ∧
      ConfinedPrefix decodeInlineOwnPcs
        (DecodeInlineExit args) Level3ChildSummary fromStep 4 state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103ec) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x143e8) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 args.finalResultBase) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.retryRawArgs.resultBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 832) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      MemoryRepresentation.MemoryBytes beforeCall args.retryRawArgs.resultBase contents ∧
      Agree decoderPreserved baseState beforeCall ∧
      RetiredCounterPresent beforeCall ∧
      Contracts.canonicalContractParams.env.CodeIntact beforeCall ∧
      beforeCall.mem = state.mem := by
  obtain ⟨contents, contentsSize, contentsMemory⟩ := payload
  let destination := iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired1, run1⟩ := decodeInline_retry_copy_destination_step fromStep args
    baseState state pre agree retiredPresent code atPc stackRead
  let s1 := afterRegisterWrite state (BitVec.ofNat 64 0x103dc) retired1 x10 destination
  have w1 : WritesOnlyRegs _ state s1 := afterRegisterWrite_writes _ _ _ _ _
  have agree1 : Agree decoderPreserved baseState s1 := Agree.trans agree (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc1 : s1.regs.get? PC = some (BitVec.ofNat 64 0x103e0) := by
    simpa [s1] using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103dc) retired1 x10 destination
  have stack1 : s1.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have code1 : Contracts.canonicalContractParams.env.CodeIntact s1 := by
    simpa [s1, afterRegisterWrite_mem] using code
  let source := iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase)
  obtain ⟨retired2, run2⟩ := decodeInline_retry_copy_source_step (fromStep + 1) args
    baseState s1 pre agree1
      (afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103dc) retired1 x10 destination)
      code1 pc1 stack1
  let s2 := afterRegisterWrite s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source
  have w2 : WritesOnlyRegs _ s1 s2 := afterRegisterWrite_writes _ _ _ _ _
  have agree2 : Agree decoderPreserved baseState s2 := Agree.trans agree1 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc2 : s2.regs.get? PC = some (BitVec.ofNat 64 0x103e4) := by
    simpa [s2] using afterRegisterWrite_pc s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source
  have code2 : Contracts.canonicalContractParams.env.CodeIntact s2 := by
    simpa [s2, afterRegisterWrite_mem] using code1
  let length := iTypeResult .ADDI 0x340#12 (0#64)
  obtain ⟨retired3, run3⟩ := decodeInline_retry_copy_length_step (fromStep + 2) args
    baseState s2 pre agree2
      (afterRegisterWrite_retired_present s1 (BitVec.ofNat 64 0x103e0) retired2 x11 source)
      code2 pc2
  let s3 := afterRegisterWrite s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length
  have w3 : WritesOnlyRegs _ s2 s3 := afterRegisterWrite_writes _ _ _ _ _
  have agree3 : Agree decoderPreserved baseState s3 := Agree.trans agree2 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have pc3 : s3.regs.get? PC = some (BitVec.ofNat 64 0x103e8) := by
    simpa [s3] using afterRegisterWrite_pc s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length
  have code3 : Contracts.canonicalContractParams.env.CodeIntact s3 := by
    simpa [s3, afterRegisterWrite_mem] using code2
  obtain ⟨retired4, run4⟩ := decodeInline_retry_copy_call_page_step (fromStep + 3) args
    baseState s3 pre agree3
      (afterRegisterWrite_retired_present s2 (BitVec.ofNat 64 0x103e4) retired3 x12 length)
      code3 pc3
  let beforeCall := afterRegisterWrite s3 (BitVec.ofNat 64 0x103e8) retired4 x1
    (BitVec.ofNat 64 0x143e8)
  have w4 : WritesOnlyRegs _ s3 beforeCall := afterRegisterWrite_writes _ _ _ _ _
  have notExit (pc : Nat) (pcFits : pc < 2 ^ 64) (different : pc ≠ 0x103f8) :
      ¬ DecodeInlineExit args (BitVec.ofNat 64 pc) := by
    simp only [DecodeInlineExit, phase, exactPrefix, ↓reduceIte]
    intro equal
    apply different
    have sameNat := congrArg BitVec.toNat equal
    simpa [Nat.mod_eq_of_lt pcFits] using sameNat
  have p1 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 1 state s1 :=
    ConfinedPrefix.ownStep' atPc (by simpa [s1, destination] using run1)
      (notExit := notExit 0x103dc (by decide) (by decide))
  have p2 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 1) 1 s1 s2 :=
    ConfinedPrefix.ownStep' pc1 (by simpa [s2, source] using run2)
      (notExit := notExit 0x103e0 (by decide) (by decide))
  have p3 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 2) 1 s2 s3 :=
    ConfinedPrefix.ownStep' pc2 (by simpa [s3, length] using run3)
      (notExit := notExit 0x103e4 (by decide) (by decide))
  have p4 : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + 3) 1 s3 beforeCall :=
    ConfinedPrefix.ownStep' pc3 (by simpa [beforeCall] using run4)
      (notExit := notExit 0x103e8 (by decide) (by decide))
  have complete : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep 4 state beforeCall := by
    confined_steps [p1, p2, p3, p4]
  have destinationEq : destination = BitVec.ofNat 64 args.finalResultBase := by
    simp only [destination, iTypeResult, DecodeInlineArgs.finalResultBase]
    rw [show sign_extend (0x020#12) = (BitVec.ofNat 64 0x20) by decide,
      ← BitVec.ofNat_add]
  have sourceEq : source = BitVec.ofNat 64 args.retryRawArgs.resultBase := by
    simp only [source, iTypeResult, DecodeInlineArgs.retryRawArgs]
    rw [show sign_extend (0x6b0#12) = (BitVec.ofNat 64 0x6b0) by decide,
      ← BitVec.ofNat_add]
  have lengthEq : length = BitVec.ofNat 64 832 := by simp [length, iTypeResult]; decide
  have globalsBeforeCall : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  refine ⟨contents, beforeCall, contentsSize, complete, ?_, ?_, ?_, ?_, ?_, ?_,
    globalsBeforeCall, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [beforeCall] using afterRegisterWrite_pc s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)
  · simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, s2, s1, destinationEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, s2, sourceEq, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, s3, lengthEq, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · grind
  · intro index bound
    have memoryEq : beforeCall.mem = state.mem := by
      simp [beforeCall, s3, s2, s1, afterRegisterWrite_mem]
    rw [memoryEq]
    exact contentsMemory index bound
  · exact Agree.trans agree3 (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  · exact afterRegisterWrite_retired_present s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)
  · exact codeIntact_of_mem_eq (afterRegisterWrite_mem s3 (BitVec.ofNat 64 0x103e8) retired4 x1
      (BitVec.ofNat 64 0x143e8)) code3
  · simp [beforeCall, s3, s2, s1, afterRegisterWrite_mem]

end BinaryFv.Zesu.MachineExecution
