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

end BinaryFv.Zesu.MachineExecution
