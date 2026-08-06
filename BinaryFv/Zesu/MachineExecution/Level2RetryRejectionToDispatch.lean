import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps
import BinaryFv.Zesu.MachineExecution.Level2WrapperProof

/-!
# Retry rejection handoff to wrapper dispatch

Both retry rejection exits converge at `0x10420`.  This module executes the two
wrapper-owned instructions there: `addi a0, zero, 0` and `jal zero, 0x1035c`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem retry_rejection_constant_step {machineArgs : DecoderMachineArgs}
    {base state : State} {destination : Register} {value : RegisterType destination}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc : BitVec 64)
    (pcIn : DecoderFetchPc decodeRawExecutionPcs pc)
    (atPc : state.regs.get? PC = some pc) (byte0 byte1 byte2 byte3 : BitVec 8)
    (inst : instruction) (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc
      byte0 byte1 byte2 byte3)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (execute : Runs (execute inst) (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          destination value }
      (.Retire_Success ())) (baseEncoding : BaseInstructionEncoding byte0)
    (destinationNotNextPc : destination ≠ nextPC) (destinationNotHart : destination ≠ hart_state)
    (destinationNotIncrement : destination ≠ minstret_increment)
    (destinationNotRetired : destination ≠ minstret) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state pc retired destination value) false :=
  decoderRegisterWriteStep machine agree retiredPresent stepNo pc pcIn atPc
    byte0 byte1 byte2 byte3 inst destination value fetchBytes
    baseEncoding decode destinationNotNextPc destinationNotHart destinationNotIncrement
    destinationNotRetired execute

private theorem retry_rejection_jump_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (stepNo : Nat) (pc target : BitVec 64) (imm : BitVec 21)
    (pcIn : DecoderFetchPc decodeRawExecutionPcs pc)
    (atPc : state.regs.get? PC = some pc) (byte0 byte1 byte2 byte3 : BitVec 8)
    (fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (baseEncoding : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) (.JAL (imm, zreg)))
    (targetEq : pc + sign_extend (m := 64) imm = target)
    (targetAligned0 : Sail.BitVec.access target 0 = 0#1)
    (targetAligned1 : Sail.BitVec.access target 1 = 0#1) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) false := by
  subst targetEq
  obtain ⟨mseccfgBits, platform⟩ := decoderStepPlatform machine agree pc atPc pcIn
    byte0 byte1 byte2 byte3 fetchBytes
  obtain ⟨fetch, noMMIO, fetched, interrupts, notExpected, privilege, mseccfgRead⟩ := platform
  obtain ⟨retired, inhibit, config, counters⟩ :=
    decoderStepCounters machine.normal agree retiredPresent
  obtain ⟨hartRead, inhibitRead, configRead, notInhibited, machineEnabled, retiredRead⟩ := counters
  obtain ⟨zcaEnabled, zca⟩ :=
    decoderZcaEnabled machine (Agree.weaken (fun _ preserved => preserved.2) agree) pc
  exact ⟨retired, tryStepJRetires stepNo state pc pc retired imm inhibit config
    byte0 byte1 byte2 byte3 (Sail.BitVec.addInt pc 4) zcaEnabled
    fetch noMMIO fetched interrupts baseEncoding decode notExpected
    (decoderReturnAddress state pc) (readReg_run _ PC _ (decoderExecuteState_get? atPc))
    targetAligned0 targetAligned1 zca hartRead inhibitRead configRead notInhibited machineEnabled
    retiredRead⟩

/-- `addi a0, zero, 0` at the common retry-rejection entry. -/
theorem retry_rejection_clear_result_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10420)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10420) retired x10 (BitVec.ofNat 64 0)) false := by
  have resultEq : iTypeResult .ADDI (0#12) (0#64) = BitVec.ofNat 64 0 := by decide
  exact decoderITypeStep machine agree retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code)
    stepNo 0x10420 0x13 0x05 0x00 0x00 0#12 0#5 10#5 .ADDI atPc
    (rX_x0_run _) (by rw [resultEq]; exact wX_x10_run _ _)

/-- `jal zero, 0x1035c` joins the shared rejection continuation. -/
theorem retry_rejection_to_rejection_step {machineArgs : DecoderMachineArgs} {base state : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10424)) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x10424) (BitVec.ofNat 64 0x1035c))
        (BitVec.ofNat 64 0x1035c) retired) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContext machine agree
  exact decoderJalStep machine (Agree.weaken (fun _ preserved => preserved.2) agree) retiredPresent
    (hasExactErePrefix_programImage_of_codeIntact code) stepNo 0x10424 0x6f 0xf0 0x9f 0xf3
    (0x1fff38#21) (BitVec.ofNat 64 0x1035c) atPc

/-- The two common retry-rejection instructions, ending at the shared status store. -/
structure RetryRejectionToStatusStore (base before after : State) (machineArgs : DecoderMachineArgs)
    (fromStep : Nat) : Prop where
  trace : Trace fromStep 2 before after
  confined : ConfinedPrefix decodeRawExecutionPcs decodeRawExit Level2ChildSummary
    fromStep 2 before after
  atStatusStore : after.regs.get? PC = some (BitVec.ofNat 64 0x1035c)
  resultValue : after.regs.get? x10 = some (BitVec.ofNat 64 0)
  statusValue : after.regs.get? x11 = before.regs.get? x11
  platform : Agree platformPreserved base after
  retired : RetiredCounterPresent after
  code : canonicalContractParams.env.CodeIntact after
  memory : after.mem = before.mem
  stackValue : after.regs.get? x2 = before.regs.get? x2
  globalsValue : after.regs.get? x18 = before.regs.get? x18

/-- The write set of the whole rejection tail: the `try_step` bookkeeping every retirement performs,
plus the single architectural register the `addi` targets. Fixed once for both steps -- see
`WritesOnlyRegs.trans_same` on why the set must not grow per instruction. -/
@[reducible] private def retryRejectionWrites : RegSet :=
  RegSet.union stepBookkeeping (RegSet.only x10)

/-- Retire the common rejection tail from `0x10420` to the status store at `0x1035c`.

Both instructions are composed through `Seg`, so no post-state of either is ever named: each
combinator hands back an opaque successor, and every clause of the result structure is a field
read or a one-line membership check against `retryRejectionWrites`. -/
theorem retry_rejection_to_status_store {machineArgs : DecoderMachineArgs} {base before : State}
    (machine : DecoderMachinePre decodeRawExecutionPcs machineArgs base)
    (agree : Agree platformPreserved base before) (retired : RetiredCounterPresent before)
    (code : canonicalContractParams.env.CodeIntact before) (fromStep : Nat)
    (atPc : before.regs.get? PC = some (BitVec.ofNat 64 0x10420)) :
    ∃ after, RetryRejectionToStatusStore base before after machineArgs fromStep := by
  have bookkeeping : ∀ r, stepBookkeeping r → retryRejectionWrites r := fun _ h => Or.inl h
  have disjoint : RegSet.Disjoint platformPreserved retryRejectionWrites :=
    platformPreserved_disjoint.union (RegSet.Disjoint.only (by simp [platformPreserved]))
  have codeOf : ∀ {s : State}, s.mem = before.mem → canonicalContractParams.env.CodeIntact s :=
    fun memory => by rw [DecoderEnvironment.CodeIntact, memory]; exact code
  obtain ⟨_, seg⟩ :=
    (Seg.nil decodeRawExecutionPcs decodeRawExit
        Level2ChildSummary retryRejectionWrites noMemory fromStep retired atPc).step
      (GeneratedWordStep.regionPc _) (GeneratedWordStep.notExitPc _)
      x10 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0x10424)
      (retry_rejection_clear_result_step machine agree retired code fromStep atPc)
      (by decide) bookkeeping (Or.inr rfl) (by decide) (by decide) (by decide)
  obtain ⟨after, seg⟩ :=
    seg.stepJump (BitVec.ofNat 64 0x1035c)
      (GeneratedWordStep.regionPc _) (GeneratedWordStep.notExitPc _)
      (retry_rejection_to_rejection_step machine (agree.trans (seg.agree disjoint)) seg.retired
        (codeOf (seg.memEq noMemory_empty)) (fromStep + 1) seg.atPc)
      bookkeeping (by decide)
  exact ⟨after,
    { trace := seg.trace
      confined := seg.confined
      atStatusStore := seg.atPc
      resultValue := seg.reg x10 (BitVec.ofNat 64 0) (by simp)
      statusValue := seg.get x11 (by decide)
      platform := agree.trans (seg.agree disjoint)
      retired := seg.retired
      code := codeOf (seg.memEq noMemory_empty)
      memory := seg.memEq noMemory_empty
      stackValue := seg.get x2 (by decide)
      globalsValue := seg.get x18 (by decide) }⟩

end BinaryFv.Zesu.MachineExecution
