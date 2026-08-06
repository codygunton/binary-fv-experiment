import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L1_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L1_2
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L2_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L2_2

/-!
# Shared `zesu_decode_raw` epilogue

The wrapper paths meet at `0x1035c`.  This module proves that common instruction sequence; callers
supply the value already selected for `a0`, the normalized status in `a1`, and the ordinary
machine frame carried from their own path.  No source-function ABI is assigned to an inline child.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The first typed tail phase restores the stack window and then the saved return address. -/
theorem wrapper_epilogue_first_restore_and_ra {base state : State} {machineArgs : DecoderMachineArgs}
    (machine : DecoderMachinePre
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      machineArgs base)
    (agree : Agree decoderPreserved base state) (retiredPresent : RetiredCounterPresent state)
    (code : canonicalContractParams.env.CodeIntact state) (fromStep : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10360))
    (stackBase link savedS0 savedS1 savedS2 stack address : BitVec 64)
    (frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 state)
    (stackValue : state.regs.get? x2 = some stack)
    (addressEq : (stack + sign_extend (m := 64) (0x230#12)) +
      sign_extend (m := 64) (0x7e8#12) = address)
    (addressNat : stackBase.toNat + 0xa18 = address.toNat)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr address) 8 = true)
    (allowed : DecoderAccessRange (DecoderReadableByte machineArgs) address 8) :
    ∃ retired1 retired2,
      let afterFirst := wrapperAfterFirstStackRestore state retired1 stack
      let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retired2 x1 link
      Runs (try_step fromStep false) state afterFirst false ∧
      Runs (try_step (fromStep + 1) false) afterFirst afterRa false ∧
      Trace fromStep 2 state afterRa ∧ afterRa.regs.get? x1 = some link ∧
      WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterRa ∧
      RetiredCounterPresent afterRa := by
  obtain ⟨retired1, firstRun⟩ := wrapper_epilogue_first_stack_restore_step machine agree retiredPresent
    code fromStep atPc stack stackValue
  let afterFirst := wrapperAfterFirstStackRestore state retired1 stack
  have w1 : WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x2)) state afterFirst :=
    stackAddiRetirement_writes state (BitVec.ofNat 64 0x10360) 0x230#12 stack retired1
  have stepAgree : Agree decoderPreserved state afterFirst :=
    w1.agree ((platformPreserved_disjoint.weaken (fun _ h => h.2)).union
      (RegSet.Disjoint.only (by simp [decoderPreserved, platformPreserved])))
  have agreeFirst : Agree decoderPreserved base afterFirst := agree.trans stepAgree
  have counterFirst : RetiredCounterPresent afterFirst := by
    refine ⟨Sail.BitVec.addInt retired1 1, ?_⟩
    simp [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick]
  have machineFirst := machine.mono agreeFirst counterFirst
  have stackFirst : afterFirst.regs.get? x2 = some (stack + sign_extend (m := 64) (0x230#12)) := by
    simpa [afterFirst] using tryStepStackAddiAfterRetired_stackPointer state
      (BitVec.ofNat 64 0x10360) 0x230#12 stack retired1
  have frameFirst : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 afterFirst :=
    WrapperSavedRegisterFrame.of_mem_eq frame (by rfl)
  have atRa : afterFirst.regs.get? PC = some (BitVec.ofNat 64 0x10364) := by
    simp [afterFirst, wrapperAfterFirstStackRestore, tryStepStackAddiAfterRetired,
      tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState,
      stackAddiNextState, tryStepStackAddiAfterIncrement, Std.ExtDHashMap.get?_insert]
    decide
  obtain ⟨retired2, raRun⟩ := wrapper_epilogue_load_ra_step machineFirst (Agree.refl afterFirst) counterFirst code
    (fromStep + 1) atRa (stack + sign_extend (m := 64) (0x230#12)) link address stackFirst addressEq
    (stackBase.toNat + 0xa18) addressNat frameFirst.1 aligned allowed
  let afterRa := afterRegisterWrite afterFirst (BitVec.ofNat 64 0x10364) retired2 x1 link
  refine ⟨retired1, retired2, firstRun, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [afterFirst, afterRa] using raRun
  · trace_steps [(by simpa [afterFirst] using firstRun), (by simpa [afterFirst, afterRa] using raRun)]
  · simp [afterRa, afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact WrapperSavedRegisterFrame.of_mem_eq frameFirst (afterRegisterWrite_mem _ _ _ _ _)
  · exact afterRegisterWrite_retired_present _ _ _ _ _

end BinaryFv.Zesu.MachineExecution
