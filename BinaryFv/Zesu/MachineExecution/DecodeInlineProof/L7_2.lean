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
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_2

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

set_option maxHeartbeats 8000000 in
/-- Execute every `decode`-owned instruction from retry entry through the second `decodeRaw` call
site. The two prefix-helper segments are consumed as child summaries; the branch, framing-word
assembly, and four call-argument instructions are executed directly through Sail. -/
theorem decodeInline_retry_before_second_decodeRaw_call (fromStep : Nat)
    (args : DecodeInlineArgs) (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz)
    (exactPrefix : Contracts.meaningHasExactErePrefix args.bytes = true) :
    ∃ lengthUsed prefixUsed beforeCall,
      lengthUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .lengthGate, inputBase := args.inputBase, bytes := args.bytes } ∧
      prefixUsed ≤ hasExactErePrefixInlineStepBound
        { phase := .prefixBytes, inputBase := args.inputBase, bytes := args.bytes } ∧
      ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary fromStep
          (11 + lengthUsed + prefixUsed) state beforeCall ∧
      beforeCall.regs.get? PC = some (BitVec.ofNat 64 0x103d8) ∧
      beforeCall.regs.get? x1 = some (BitVec.ofNat 64 0x103d4) ∧
      beforeCall.regs.get? x10 = some (BitVec.ofNat 64 (args.stackBase + 0x6b0)) ∧
      beforeCall.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
      beforeCall.regs.get? x12 = some (BitVec.ofNat 64 (args.inputBase + 4)) ∧
      beforeCall.regs.get? x13 = some (BitVec.ofNat 64 (args.bytes.size - 4)) ∧
      beforeCall.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) ∧
      beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) ∧
      Agree decoderPreserved state beforeCall ∧
      RetiredCounterPresent beforeCall ∧
      Contracts.canonicalContractParams.env.CodeIntact beforeCall ∧
      beforeCall.mem = state.mem := by
  have fourBytes : 4 ≤ args.bytes.size := by
    rw [Contracts.meaningHasExactErePrefix] at exactPrefix
    split at exactPrefix <;> simp_all
  obtain ⟨lengthUsed, prefixUsed, beforeOr, lengthBound, prefixBound, prefixTrace,
    prefixPost, agreeBeforeOr, counterBeforeOr, stackBeforeOr, inputBeforeOr, lengthBeforeOr,
    globalsBeforeOr, codeBeforeOr, memoryBeforeOr⟩ :=
    decodeInline_retry_uses_prefix_bytes fromStep args state pre phase fourBytes
  obtain ⟨declared, declaredRead, assembled, declaredBound⟩ :=
    prefix_halves_or_eq_readU32LE args.bytes fourBytes
  have declaredEq := prefix_declared_eq_of_meaning_true args.bytes declared declaredRead exactPrefix
  obtain ⟨orRetired, orRun, orPc, orAgree, orCounter, orMemory⟩ :=
    decodeInline_retry_prefix_or_step (fromStep + (5 + lengthUsed + prefixUsed)) args state
      beforeOr pre agreeBeforeOr counterBeforeOr codeBeforeOr prefixPost.1
      (BitVec.ofNat 64 (prefixLow16 args.bytes))
      (BitVec.ofNat 64 (prefixHigh16 args.bytes)) prefixPost.2.1 prefixPost.2.2.1
  let sOr := afterRegisterWrite beforeOr (BitVec.ofNat 64 0x103c0) orRetired x10
    (BitVec.ofNat 64 (prefixHigh16 args.bytes) |||
      BitVec.ofNat 64 (prefixLow16 args.bytes))
  have declaredAtOr : sOr.regs.get? x10 = some (BitVec.ofNat 64 declared) := by
    simp [sOr, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
      assembled]
  have wOr : WritesOnlyRegs _ beforeOr sOr := afterRegisterWrite_writes _ _ _ _ _
  have lengthAtOr : sOr.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) :=
    ((afterRegisterWrite_writes _ _ _ _ _).get x13 (by decide)).trans prefixPost.2.2.2
  have agreeOr := Agree.trans agreeBeforeOr orAgree
  have codeOr : Contracts.canonicalContractParams.env.CodeIntact sOr := by
    rw [Contracts.DecoderEnvironment.CodeIntact, orMemory, memoryBeforeOr]
    exact pre.code
  obtain ⟨branchRetired, branchRun, branchPc, branchAgree, branchCounter, branchMemory⟩ :=
    decodeInline_retry_prefix_branch_not_taken
      (fromStep + (6 + lengthUsed + prefixUsed)) args state sOr pre agreeOr orCounter codeOr
      orPc declared declaredAtOr lengthAtOr declaredEq
  let sBranch := decodeInlineRetryPrefixBranchFallThrough sOr branchRetired
  have wBranch : WritesOnlyRegs _ sOr sBranch := fallThroughRetirement_writes _ _ _ _
  have agreeBranch : Agree decoderPreserved state sBranch :=
    Agree.trans agreeOr (by simpa [sBranch] using branchAgree)
  have memoryBranch : sBranch.mem = state.mem := by
    calc
      sBranch.mem = sOr.mem := by simpa [sBranch] using branchMemory
      _ = beforeOr.mem := orMemory
      _ = state.mem := memoryBeforeOr
  have codeBranch : Contracts.canonicalContractParams.env.CodeIntact sBranch := by
    rw [Contracts.DecoderEnvironment.CodeIntact, memoryBranch]
    exact pre.code
  have inputAtBranch : sBranch.regs.get? x8 = some (BitVec.ofNat 64 args.inputBase) := by grind
  have stackAtBranch : sBranch.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  obtain ⟨tailRetired, tailRun⟩ := decodeInline_retry_tail_pointer_step
    (fromStep + (7 + lengthUsed + prefixUsed)) args state sBranch pre agreeBranch
      (by simpa [sBranch] using branchCounter) codeBranch branchPc inputAtBranch
  let sTail := afterRegisterWrite sBranch (BitVec.ofNat 64 0x103c8) tailRetired x12
    (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have wTail : WritesOnlyRegs _ sBranch sTail := afterRegisterWrite_writes _ _ _ _ _
  have agreeTail : Agree decoderPreserved state sTail := Agree.trans agreeBranch (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have counterTail := afterRegisterWrite_retired_present sBranch
    (BitVec.ofNat 64 0x103c8) tailRetired x12
      (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have pcTail : sTail.regs.get? PC = some (BitVec.ofNat 64 0x103cc) := by
    simpa [sTail] using afterRegisterWrite_pc sBranch (BitVec.ofNat 64 0x103c8) tailRetired
      x12 (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))
  have stackTail : sTail.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have codeTail : Contracts.canonicalContractParams.env.CodeIntact sTail :=
    codeIntact_of_mem_eq (afterRegisterWrite_mem sBranch (BitVec.ofNat 64 0x103c8) tailRetired x12
      (iTypeResult .ADDI 0x004#12 (BitVec.ofNat 64 args.inputBase))) codeBranch
  obtain ⟨resultRetired, resultRun⟩ := decodeInline_retry_result_pointer_step
    (fromStep + (8 + lengthUsed + prefixUsed)) args state sTail pre agreeTail counterTail codeTail
      pcTail stackTail
  let sResult := afterRegisterWrite sTail (BitVec.ofNat 64 0x103cc) resultRetired x10
    (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have wResult : WritesOnlyRegs _ sTail sResult := afterRegisterWrite_writes _ _ _ _ _
  have agreeResult : Agree decoderPreserved state sResult := Agree.trans agreeTail (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have counterResult := afterRegisterWrite_retired_present sTail
    (BitVec.ofNat 64 0x103cc) resultRetired x10
      (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have pcResult : sResult.regs.get? PC = some (BitVec.ofNat 64 0x103d0) := by
    simpa [sResult] using afterRegisterWrite_pc sTail (BitVec.ofNat 64 0x103cc) resultRetired
      x10 (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))
  have stackResult : sResult.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase) := by grind
  have codeResult : Contracts.canonicalContractParams.env.CodeIntact sResult :=
    codeIntact_of_mem_eq (afterRegisterWrite_mem sTail (BitVec.ofNat 64 0x103cc) resultRetired x10
      (iTypeResult .ADDI 0x6b0#12 (BitVec.ofNat 64 args.stackBase))) codeTail
  obtain ⟨allocatorRetired, allocatorRun⟩ := decodeInline_retry_allocator_pointer_step
    (fromStep + (9 + lengthUsed + prefixUsed)) args state sResult pre agreeResult counterResult
      codeResult pcResult stackResult
  let sAllocator := afterRegisterWrite sResult (BitVec.ofNat 64 0x103d0) allocatorRetired x11
    (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have wAllocator : WritesOnlyRegs _ sResult sAllocator := afterRegisterWrite_writes _ _ _ _ _
  have agreeAllocator : Agree decoderPreserved state sAllocator := Agree.trans agreeResult (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have counterAllocator := afterRegisterWrite_retired_present sResult
    (BitVec.ofNat 64 0x103d0) allocatorRetired x11
      (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have pcAllocator : sAllocator.regs.get? PC = some (BitVec.ofNat 64 0x103d4) := by
    simpa [sAllocator] using afterRegisterWrite_pc sResult (BitVec.ofNat 64 0x103d0)
      allocatorRetired x11 (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))
  have codeAllocator : Contracts.canonicalContractParams.env.CodeIntact sAllocator :=
    codeIntact_of_mem_eq (afterRegisterWrite_mem sResult (BitVec.ofNat 64 0x103d0) allocatorRetired
      x11 (iTypeResult .ADDI 0x010#12 (BitVec.ofNat 64 args.stackBase))) codeResult
  obtain ⟨pageRetired, pageRun⟩ := decodeInline_retry_call_page_step
    (fromStep + (10 + lengthUsed + prefixUsed)) args state sAllocator pre agreeAllocator
      counterAllocator codeAllocator pcAllocator
  let beforeCall := afterRegisterWrite sAllocator (BitVec.ofNat 64 0x103d4) pageRetired x1
    (BitVec.ofNat 64 0x103d4)
  have wPage : WritesOnlyRegs _ sAllocator beforeCall := afterRegisterWrite_writes _ _ _ _ _
  have agreeBeforeCall : Agree decoderPreserved state beforeCall := Agree.trans agreeAllocator (by
      apply afterRegisterWrite_agree_of <;> simp [decoderPreserved, platformPreserved])
  have counterBeforeCall := afterRegisterWrite_retired_present sAllocator
    (BitVec.ofNat 64 0x103d4) pageRetired x1 (BitVec.ofNat 64 0x103d4)
  have codeBeforeCall : Contracts.canonicalContractParams.env.CodeIntact beforeCall :=
    codeIntact_of_mem_eq (afterRegisterWrite_mem sAllocator (BitVec.ofNat 64 0x103d4) pageRetired x1
      (BitVec.ofNat 64 0x103d4)) codeAllocator
  have memoryBeforeCall : beforeCall.mem = state.mem := by
    simpa [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite_mem] using memoryBranch
  have notExit (pc : Nat) (pcFits : pc < 2 ^ 64) (notFinal : pc ≠ 0x103f8) :
      ¬ DecodeInlineExit args (BitVec.ofNat 64 pc) := by
    simp only [DecodeInlineExit, phase, exactPrefix, ↓reduceIte]
    intro equal
    apply notFinal
    have sameNat := congrArg BitVec.toNat equal
    simpa [Nat.mod_eq_of_lt pcFits] using sameNat
  have pOr : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (5 + lengthUsed + prefixUsed)) 1 beforeOr sOr :=
    ConfinedPrefix.ownStep' prefixPost.1 (by simpa [sOr] using orRun)
      (notExit := notExit 0x103c0 (by decide) (by decide))
  have pBranch : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (6 + lengthUsed + prefixUsed)) 1 sOr sBranch :=
    ConfinedPrefix.ownStep' orPc (by simpa [sBranch] using branchRun)
      (notExit := notExit 0x103c4 (by decide) (by decide))
  have pTail : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (7 + lengthUsed + prefixUsed)) 1 sBranch sTail :=
    ConfinedPrefix.ownStep' branchPc (by simpa [sTail] using tailRun)
      (notExit := notExit 0x103c8 (by decide) (by decide))
  have pResult : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (8 + lengthUsed + prefixUsed)) 1 sTail sResult :=
    ConfinedPrefix.ownStep' pcTail (by simpa [sResult] using resultRun)
      (notExit := notExit 0x103cc (by decide) (by decide))
  have pAllocator : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (9 + lengthUsed + prefixUsed)) 1 sResult sAllocator :=
    ConfinedPrefix.ownStep' pcResult (by simpa [sAllocator] using allocatorRun)
      (notExit := notExit 0x103d0 (by decide) (by decide))
  have pPage : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      (fromStep + (10 + lengthUsed + prefixUsed)) 1 sAllocator beforeCall :=
    ConfinedPrefix.ownStep' pcAllocator (by simpa [beforeCall] using pageRun)
      (notExit := notExit 0x103d4 (by decide) (by decide))
  have prefixOr : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (6 + lengthUsed + prefixUsed) state sOr :=
    ConfinedPrefix.trans' _ prefixTrace pOr
  have prefixBranch : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (7 + lengthUsed + prefixUsed) state sBranch :=
    ConfinedPrefix.trans' _ prefixOr pBranch
  have prefixTail : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (8 + lengthUsed + prefixUsed) state sTail :=
    ConfinedPrefix.trans' _ prefixBranch pTail
  have prefixResult : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (9 + lengthUsed + prefixUsed) state sResult :=
    ConfinedPrefix.trans' _ prefixTail pResult
  have prefixAllocator : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args)
      Level3ChildSummary fromStep (10 + lengthUsed + prefixUsed) state sAllocator :=
    ConfinedPrefix.trans' _ prefixResult pAllocator
  have complete : ConfinedPrefix decodeInlineOwnPcs (DecodeInlineExit args) Level3ChildSummary
      fromStep (11 + lengthUsed + prefixUsed) state beforeCall :=
    ConfinedPrefix.trans' _ prefixAllocator pPage
  have resultValue : iTypeResult .ADDI (0x6b0#12) (BitVec.ofNat 64 args.stackBase) =
      BitVec.ofNat 64 (args.stackBase + 0x6b0) := by
    simp only [iTypeResult]
    rw [show sign_extend (0x6b0#12) = (BitVec.ofNat 64 0x6b0) by decide,
      ← BitVec.ofNat_add]
  have allocatorValue : iTypeResult .ADDI (0x010#12) (BitVec.ofNat 64 args.stackBase) =
      BitVec.ofNat 64 args.allocatorBase := by
    simp only [iTypeResult, DecodeInlineArgs.allocatorBase]
    rw [show sign_extend (0x010#12) = (BitVec.ofNat 64 0x10) by decide,
      ← BitVec.ofNat_add]
  have inputValue : iTypeResult .ADDI (0x004#12) (BitVec.ofNat 64 args.inputBase) =
      BitVec.ofNat 64 (args.inputBase + 4) := by
    simp only [iTypeResult]
    rw [show sign_extend (0x004#12) = (BitVec.ofNat 64 4) by decide,
      ← BitVec.ofNat_add]
  have lengthAtBranch : sBranch.regs.get? x13 =
      some (BitVec.ofNat 64 (args.bytes.size - 4)) := by grind
  have globalsBeforeCall : beforeCall.regs.get? x18 = some (BitVec.ofNat 64 0x4215020) := by grind
  refine ⟨lengthUsed, prefixUsed, beforeCall, lengthBound, prefixBound, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, globalsBeforeCall, agreeBeforeCall, counterBeforeCall, codeBeforeCall, memoryBeforeCall⟩
  · exact complete
  · simpa [beforeCall] using afterRegisterWrite_pc sAllocator (BitVec.ofNat 64 0x103d4)
      pageRetired x1 (BitVec.ofNat 64 0x103d4)
  · simp [beforeCall, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert]
  · simp [beforeCall, sAllocator, sResult, afterRegisterWrite, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, resultValue]
  · simp [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, allocatorValue]
  · simp [beforeCall, sAllocator, sResult, sTail, afterRegisterWrite,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert, inputValue]
  · grind
  · grind

end BinaryFv.Zesu.MachineExecution
