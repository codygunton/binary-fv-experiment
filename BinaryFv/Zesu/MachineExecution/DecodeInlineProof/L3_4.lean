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
