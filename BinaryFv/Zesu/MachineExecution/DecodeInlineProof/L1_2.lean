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

/-- The declared `decode` budget leaves room for the selected `decodeRaw` budget plus the thirteen
parent-owned instructions of the first phase. -/
theorem decodeInline_first_stepBound_le {args : DecodeInlineArgs} {childUsed own : Nat}
    (childBound : childUsed ≤ compiledDecodeRawContract.binding.stepBound args.firstRawArgs)
    (ownBound : own ≤ 13) : childUsed + own ≤ decodeInlineStepBound args := by
  unfold decodeInlineStepBound
  have stepBoundEq : compiledDecodeRawContract.binding.stepBound args.firstRawArgs =
      16384 + 512 * args.bytes.size := rfl
  rw [stepBoundEq] at childBound
  omega

def decodeRawReturnAfter (returnPc : BitVec 64) (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10530) returnPc)
    returnPc retired

/-- Execute the actual `lhu a0, 0x6a0(sp)` that reads the first `decodeRaw` result tag. The bytes
come from the strengthened child postcondition; no result value is assumed by the machine step. -/
theorem decodeInline_first_result_tag_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (status : BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep state
      (args.firstTemporaryResultBase +
        Contracts.canonicalContractParams.env.record.entryResultTagOffset)
      (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase))
    (globalsRead : state.regs.get? x18 = some (BitVec.ofNat 64 0x4215020))
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10320)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10320) retired x10
        (BitVec.ofNat 64
          (Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)))) false := by
  let tag := Contracts.decodeInternalResultTag (Contracts.meaningDecodeRaw args.bytes)
  have tagCases : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 := by
    simp only [tag]
    cases rawResult : Contracts.meaningDecodeRaw args.bytes with
    | ok value => simp [Contracts.decodeInternalResultTag]
    | error error => cases error <;> simp [Contracts.decodeInternalResultTag]
  have tagOffset : Contracts.canonicalContractParams.env.record.entryResultTagOffset = 832 := by
    have pinned := congrArg (fun record => record.entryResultTagOffset)
      Contracts.canonicalRecordSizes_pinned
    simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
  let address := BitVec.ofNat 64 (args.stackBase + 0x6a0)
  have addressFits : args.stackBase + 0x6a0 + 2 ≤ 2 ^ 64 := by
    have fit := pre.stackObjectsFit
    omega
  have addressNat : address.toNat = args.stackBase + 0x6a0 := by
    simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : args.stackBase + 0x6a0 < 2 ^ 64)]
  have machine := pre.machine.mono agree retiredPresent
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10320)
  have executeAgree : Agree decoderPreserved baseState executeState :=
    Agree.trans agree
      (Agree.weaken (fun _ preserved => preserved.2)
        (agree_stepPremiseState state (BitVec.ofNat 64 0x10320)))
  have stackAtExecute : executeState.regs.get? x2 =
      some (BitVec.ofNat 64 args.stackBase) := decoderExecuteState_get? stackRead
  obtain ⟨mstatusBits, mstatusReadBase, mprvZero⟩ := pre.machine.mstatus
  obtain ⟨mseccfgBase, mseccfgReadBase, pmmDisabled⟩ := pre.machine.mseccfg
  have mstatusRead : executeState.regs.get? mstatus = some mstatusBits :=
    (executeAgree mstatus (by simp [decoderPreserved, platformPreserved])).trans mstatusReadBase
  have privilegeRead : executeState.regs.get? cur_privilege = some Privilege.Machine :=
    (executeAgree cur_privilege (by simp [decoderPreserved, platformPreserved])).trans
      pre.machine.normal.2.1
  have mseccfgReadExecute : executeState.regs.get? mseccfg = some mseccfgBase :=
    (executeAgree mseccfg (by simp [decoderPreserved, platformPreserved])).trans mseccfgReadBase
  have addressEq : BitVec.ofNat 64 args.stackBase + sign_extend (m := 64) (0x6a0#12) =
      address := by
    rw [show sign_extend (m := 64) (0x6a0#12) = BitVec.ofNat 64 0x6a0 by decide,
      ← BitVec.ofNat_add]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 2#5) (sign_extend (m := 64) (0x6a0#12))
        (MemoryAccessType.Load mem_payload.Data) 2)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 2#5)
      (BitVec.ofNat 64 args.stackBase) (sign_extend (m := 64) (0x6a0#12)) mstatusBits
      mseccfgBase (rX_bits_run_x2 executeState _ stackAtExecute) mstatusRead privilegeRead
      mprvZero mseccfgReadExecute pmmDisabled
  have allowed : DecoderAccessRange (DecoderReadableByte args.machineArgs) address 2 := by
    refine ⟨by decide, ?_, ?_⟩
    · simpa [addressNat] using addressFits
    intro index indexLt
    right
    right
    left
    rw [addressNat]
    have stackByte := pre.stackObjectsReadable (0x6a0 + index) (by
      have positive : 0 < Contracts.canonicalContractParams.env.record.entryResult := by
        have pinned := congrArg (fun record => record.entryResult)
          Contracts.canonicalRecordSizes_pinned
        have sizeEq : Contracts.canonicalContractParams.env.record.entryResult = 848 := by
          simpa [Contracts.canonicalContractParams, Contracts.canonicalEnvironment] using pinned
        omega
      omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using stackByte
  have aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 2 = true := by
    have addressMod : address.toNat % 2 = 0 := by
      rw [addressNat]
      have stackAligned := pre.stackAligned
      omega
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, ← Int.ofNat_tmod,
      addressMod]
    rfl
  have physicalAligned : is_aligned_paddr (physaddr.Physaddr address) 2 = true := by
    simpa [is_aligned_paddr, is_aligned_vaddr] using aligned
  obtain ⟨physAccess, loadNoMMIO⟩ :=
    pre.machine.dataAccess.load executeState address 2 executeAgree allowed physicalAligned
  have statusAtAddress : BinaryFv.Zesu.MemoryRepresentation.ResultStatusLERep state
      address.toNat tag := by
    simpa [addressNat, DecodeInlineArgs.firstTemporaryResultBase, tagOffset, tag,
      Nat.add_assoc] using status
  rcases statusAtAddress with ⟨-, lowByte, highByte⟩
  have memoryBytes : ∀ (index : Nat) (indexLt : index < (leBytes 2 (BitVec.ofNat 16 tag)).length),
      executeState.mem.get? (address.toNat + index) =
        some (leBytes 2 (BitVec.ofNat 16 tag))[index] := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have executeMemory : executeState.mem = state.mem := rfl
    rw [executeMemory]
    have indexCases : index = 0 ∨ index = 1 := by omega
    rcases indexCases with rfl | rfl
    · rcases tagCases with h | h | h | h <;> simpa [h, leBytes] using lowByte
    · rcases tagCases with h | h | h | h <;> simpa [h, leBytes] using highByte
  have hread := vmem_read_half_from_bytes_run executeState (.Regidx 2#5)
    (sign_extend (m := 64) (0x6a0#12)) address mstatusBits (BitVec.ofNat 16 tag)
    mstatusRead privilegeRead mprvZero addressRun aligned physAccess loadNoMMIO memoryBytes
  have extended : extend_value true (BitVec.ofNat 16 tag) = BitVec.ofNat 64 tag := by
    rcases tagCases with h | h | h | h <;>
      simp [h, extend_value, zero_extend, Sail.BitVec.zeroExtend]
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderLhuStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10320 0x03 0x55 0x01 0x6a 0x6a0#12 2#5 10#5 atPc hread
    (by simpa [extended] using wX_x10_run executeState (BitVec.ofNat 64 tag))

def decodeInlineFirstSuccessBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10324))
    (BitVec.ofNat 64 0x10328) retired

/-- Execute `addi a0, sp, 0x20`, the first argument setup instruction for the successful-result
copy. -/
theorem decodeInline_first_success_copy_destination_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10328))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10328) retired x10
          (iTypeResult .ADDI 0x020#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10328 0x13 0x05 0x01 0x02 0x020#12 2#5 10#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x10_run _ _)

/-- Execute `addi a1, sp, 0x360`, selecting the successful temporary result as the copy source. -/
theorem decodeInline_first_success_copy_source_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1032c))
    (stackRead : state.regs.get? x2 = some (BitVec.ofNat 64 args.stackBase)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1032c) retired x11
          (iTypeResult .ADDI 0x360#12 (BitVec.ofNat 64 args.stackBase))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1032c 0x93 0x05 0x01 0x36 0x360#12 2#5 11#5 .ADDI atPc
    (rX_bits_run_x2 _ _ (decoderExecuteState_get? stackRead)) (wX_x11_run _ _)

/-- Execute `addi a2, x0, 0x340`, fixing the successful-result copy length at 832 bytes. -/
theorem decodeInline_first_success_copy_length_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10330)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10330) retired x12
          (iTypeResult .ADDI 0x340#12 (0#64))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10330 0x13 0x06 0x00 0x34 0x340#12 0#5 12#5 .ADDI atPc
    (rX_x0_run _) (wX_x12_run _ _)

/-- Execute `auipc ra, 4`, the final parent-owned instruction before the emitted `memcpy` call. -/
theorem decodeInline_first_success_copy_call_page_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10334)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10334) retired x1
          (BitVec.ofNat 64 0x14334)) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderAuipcStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10334 0x97 0x40 0x00 0x00 0x00004#20 1#5 atPc
    (by simpa using wX_bits_run_x1 _ (BitVec.ofNat 64 0x14334))

def decodeInlineRetryEntryAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10380))
    (BitVec.ofNat 64 0x10384) retired

/-- Execute `li a0, -1`, the first parent-owned constant preparation instruction. -/
theorem decodeInline_retry_minus_one_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10384)) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10384) retired x10
          (BitVec.ofNat 64 (2 ^ 64 - 1))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10384 0x13 0x05 0xf0 0xff 0xfff#12 0#5 10#5 .ADDI atPc (rX_x0_run _)
    (by rw [show iTypeResult .ADDI 0xfff#12 (0#64) = BitVec.ofNat 64 (2 ^ 64 - 1) from by
          native_decide]
        exact wX_x10_run _ _)

/-- Execute `slli a0, a0, 32`, producing `2^64 - 2^32`. -/
theorem decodeInline_retry_shift_constant_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10388))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 1))) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x10388) retired x10
          (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderShiftIopStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10388 0x13 0x15 0x05 0x02 32#6 10#5 10#5 .SLLI atPc
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant))
    (by rw [show shiftIopResult .SLLI 32#6 (BitVec.ofNat 64 (2 ^ 64 - 1)) =
              BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32) from by native_decide]
        exact wX_x10_run _ _)

/-- Execute `addi a2, a0, -4`, completing the constants consumed by the prefix length gate. -/
theorem decodeInline_retry_minus_four_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1038c))
    (constant : state.regs.get? x10 = some (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32))) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x1038c) retired x12
          (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4))) false := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  exact decoderITypeStep machine (Agree.refl state) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x1038c 0x13 0x06 0xc5 0xff 0xffc#12 10#5 12#5 .ADDI atPc
    (rX_bits_run_x10 _ _ (decoderExecuteState_get? constant))
    (by rw [show iTypeResult .ADDI 0xffc#12 (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32)) =
              BitVec.ofNat 64 (2 ^ 64 - 2 ^ 32 - 4) from by native_decide]
        exact wX_x12_run _ _)

def decodeInlineRetryLengthBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10394))
    (BitVec.ofNat 64 0x10398) retired

/-- Execute the parent-owned `or a0, a4, a0` at `0x103c0`, assembling the complete little-endian
prefix value and reaching the result branch at `0x103c4`. -/
theorem decodeInline_retry_prefix_or_step (stepNo : Nat) (args : DecodeInlineArgs)
    (baseState state : State) (pre : DecodeInlinePre args baseState)
    (agree : Agree decoderPreserved baseState state)
    (retiredPresent : RetiredCounterPresent state)
    (code : Contracts.canonicalContractParams.env.CodeIntact state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x103c0))
    (low high : BitVec 64) (lowRead : state.regs.get? x10 = some low)
    (highRead : state.regs.get? x14 = some high) :
    ∃ retired,
      Runs (try_step stepNo false) state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) false ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10
        (high ||| low)).regs.get? PC = some (BitVec.ofNat 64 0x103c4) ∧
      Agree decoderPreserved state
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) ∧
      RetiredCounterPresent
        (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) ∧
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10
        (high ||| low)).mem = state.mem := by
  have machine := pre.machine.mono agree retiredPresent
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine (Agree.refl state)
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x103c0) retired x10 (high ||| low)) false :=
    decoderRTypeStep machine (Agree.refl state) retiredPresent
      (hasExactErePrefix_programImage_of_codeIntact code)
      stepNo 0x103c0 0x33 0x65 0xa7 0x00 10#5 14#5 10#5 .OR atPc
      (rX_x14_run _ _ (decoderExecuteState_get? highRead))
      (rX_x10_run _ _ (decoderExecuteState_get? lowRead)) (wX_x10_run _ _)
  refine ⟨retired, run, ?_, ?_, ?_, rfl⟩
  · simpa using afterRegisterWrite_pc state (BitVec.ofNat 64 0x103c0) retired x10
      (high ||| low)
  · exact afterRegisterWrite_agree_of
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved])
  · exact afterRegisterWrite_retired_present state (BitVec.ofNat 64 0x103c0) retired x10
      (high ||| low)

end BinaryFv.Zesu.MachineExecution
