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

end BinaryFv.Zesu.MachineExecution
