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

/-- The retry precondition fixes both compared tags to `2`, so the generated
`bne a0, a1, 0x103fc` must fall through into the retry body. -/
theorem decodeInline_retry_entry_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (state : State) (pre : DecodeInlinePre args state)
    (phase : args.phase = .retryAfterInvalidSsz) :
    ∃ retired,
      Runs (try_step stepNo false) state (decodeInlineRetryEntryAfter state retired) false ∧
      (decodeInlineRetryEntryAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10384) := by
  have atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10380) := by
    simpa [DecodeInlineArgs.entryPc, phase] using pre.atEntry
  obtain ⟨-, tagA0, tagA1⟩ := pre.retryReason phase
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContext pre.machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep pre.machine (Agree.refl state)
    pre.machine.retiredCounter (hasExactErePrefix_programImage_of_codeIntact pre.code)
    stepNo 0x10380 0x63 0x1e 0xb5 0x06 0x7c#13 11#5 10#5 .BNE atPc
    (by unfold bTypeTaken
        refine Runs.bind
          (rX_bits_run_x10 _ (BitVec.ofNat 64 2) (decoderExecuteState_get? tagA0)) ?_
        refine Runs.bind
          (rX_bits_run_x11 _ (BitVec.ofNat 64 2) (decoderExecuteState_get? tagA1)) ?_
        rfl)
  refine ⟨retired, ?_, ?_⟩
  · simpa [decodeInlineRetryEntryAfter] using run
  · simp [decodeInlineRetryEntryAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]

/-- When four framing bytes exist, execute `bltu a2, a0, 0x10420` at `0x10394` as not taken.
The constants prepared by the parent turn the unsigned comparison into `bytes.size < 4`. -/
theorem decodeInline_retry_length_branch_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10394))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)))
    (adjustedLength : state.regs.get? x12 = some
      (BitVec.ofNat 64 (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4))))
    (fourBytes : 4 ≤ args.bytes.size) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (decodeInlineRetryLengthBranchAfter state retired) false ∧
      (decodeInlineRetryLengthBranchAfter state retired).regs.get? PC =
        some (BitVec.ofNat 64 0x10398) ∧
      Agree decoderPreserved state (decodeInlineRetryLengthBranchAfter state retired) ∧
      RetiredCounterPresent (decodeInlineRetryLengthBranchAfter state retired) ∧
      (decodeInlineRetryLengthBranchAfter state retired).mem = state.mem := by
  have machine := pre.machine.mono agree retiredPresent
  have sizeBound : args.bytes.size < 2 ^ 32 := by
    have := pre.rootInputBound
    omega
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ := decoderBranchNotTakenStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10394 0x63 0x66 0xa6 0x08 0x8c#13 10#5 12#5 .BLTU atPc
    (by unfold bTypeTaken
        refine Runs.bind (rX_x12_run _ _ (decoderExecuteState_get? adjustedLength)) ?_
        refine Runs.bind (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant)) ?_
        have leftFits : args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4) < 2 ^ 64 := by omega
        have rightFits : 2 ^ 64 - 2 ^ 32 < 2 ^ 64 := by omega
        simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt leftFits, Nat.mod_eq_of_lt rightFits]
        rw [show (Int.ofNat (args.bytes.size + (2 ^ 64 - 2 ^ 32 - 4)) <b
            Int.ofNat (2 ^ 64 - 2 ^ 32)) = false from by
          simp only [decide_eq_false_iff_not]
          exact Int.not_lt.mpr (Int.ofNat_le.mpr (by omega))]
        rfl)
  refine ⟨retired, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [decodeInlineRetryLengthBranchAfter] using run
  · simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, Std.ExtDHashMap.get?_insert]
  · exact Agree.weaken (fun _ preserved => preserved.2)
      ((fallThroughRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  · refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
    simp [decodeInlineRetryLengthBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick]

end BinaryFv.Zesu.MachineExecution
