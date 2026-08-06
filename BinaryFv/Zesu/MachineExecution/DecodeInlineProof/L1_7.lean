import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc

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

def decodeInlineFirstCallAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (callLinkState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x1031c) (BitVec.ofNat 64 0x10444) x1
      (BitVec.ofNat 64 0x10320))
    (BitVec.ofNat 64 0x10444) retired

/-- Read off the generated exit address of the selected emitted `decodeRaw` from its own trace. -/
theorem decodeRaw_trace_exit_pc {childFrom childUsed : Nat} {childEntry childExit : State}
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
      (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)
      (Contracts.functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
      childFrom childUsed childEntry childExit) :
    childExit.regs.get? PC = some (BitVec.ofNat 64 0x10530) := by
  obtain ⟨retPc, atRet, retIsExit⟩ := childTrace.trace.final_at_exit
  have retPcEq : retPc = BitVec.ofNat 64 0x10530 := by
    apply BitVec.eq_of_toNat_eq
    simpa [functionInstanceExitPred, FunctionInstance.isExit,
      functionInstance_ssz_raw_decodeRaw] using retIsExit
  simpa [retPcEq] using atRet

end BinaryFv.Zesu.MachineExecution
