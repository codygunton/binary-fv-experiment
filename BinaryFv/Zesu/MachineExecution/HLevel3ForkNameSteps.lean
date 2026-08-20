import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Elfling.Seg

/-!
# Exact steps for the Level 3 fork-name dispatcher

The inlined dispatcher starts at `0x1221c`. This module first proves its two `ADDI` steps.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

def forkNameSchemaIndex (schema : Nat) : BitVec 64 :=
  iTypeResult .ADDI (0xfff#12) (BitVec.ofNat 64 schema)

/-- Exact `0x1221c: addi a0,a0,-1`. -/
theorem forkNameSubtractOneStep (stepNo schema : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1221c))
    (schemaAt : state.regs.get? x10 = some (BitVec.ofNat 64 schema))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1221c retired x10 (forkNameSchemaIndex schema)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1221c
  have sourceAtPremise : premise.regs.get? x10 = some (BitVec.ofNat 64 schema) :=
    (stepPremiseState_writes state 0x1221c).get x10 (by decide) |>.trans schemaAt
  have execute : Runs (execute (.ITYPE (0xfff, .Regidx 10#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (forkNameSchemaIndex schema) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xfff (.Regidx 10#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run premise _ 0xfff (.Regidx 10#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 schema) (rX_x10_run premise _ sourceAtPremise)
      (wX_x10_run premise _)
  exact configuredRegisterWriteStep stepNo 0x1221c state x10 (forkNameSchemaIndex schema)
    (.ITYPE (0xfff, .Regidx 10#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0xf5 0xff
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12220: li a2,20`. -/
theorem forkNameLoadLimitStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12220))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12220 retired x12 20) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12220
  have execute : Runs (execute (.ITYPE (20, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 20 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 20 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 20 0 = 20#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 20 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12220 state x12 20
    (.ITYPE (20, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x40 0x01
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

private theorem forkNameBltuCondition (state : State) (index limit : BitVec 64)
    (indexAt : state.regs.get? x10 = some index)
    (limitAt : state.regs.get? x12 = some limit) :
    Runs (bTypeTaken (.Regidx 10#5) (.Regidx 12#5) .BLTU) state state
      (zopz0zI_u limit index) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run state limit limitAt) ?_
  refine Runs.bind (rX_x10_run state index indexAt) ?_
  rfl

/-- Exact not-taken `0x12224: bltu a2,a0,0x12638`. -/
theorem forkNameBoundsAcceptedStep (stepNo : Nat) (state : State) (index : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12224))
    (indexAt : state.regs.get? x10 = some index)
    (limitAt : state.regs.get? x12 = some 20)
    (accepted : zopz0zI_u 20 index = false)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12224)
        0x12228 retired) false := by
  apply configuredBranchNotTakenStep stepNo 0x12224 state 0x414 (.Regidx 10#5)
    (.Regidx 12#5) .BLTU 0x63 0x6a 0xa6 0x40 configured atPc loaded
  · configured_decode configured
  · simpa only [accepted] using forkNameBltuCondition
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12224)
      index 20
      ((stepPremiseState_writes state 0x12224).get x10 (by decide) |>.trans indexAt)
      ((stepPremiseState_writes state 0x12224).get x12 (by decide) |>.trans limitAt)
  · native_decide
  · rfl

/-- Exact taken `0x12224: bltu a2,a0,0x12638`. -/
theorem forkNameBoundsRejectedStep (stepNo : Nat) (state : State) (index : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12224))
    (indexAt : state.regs.get? x10 = some index)
    (limitAt : state.regs.get? x12 = some 20)
    (rejected : zopz0zI_u 20 index = true)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x12224 0x12638)
        0x12638 retired) false := by
  apply configuredBranchTakenStep stepNo 0x12224 0x12638 state 0x414 (.Regidx 10#5)
    (.Regidx 12#5) .BLTU 0x63 0x6a 0xa6 0x40 configured atPc loaded
  · configured_decode configured
  · simpa only [rejected] using forkNameBltuCondition
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12224)
      index 20
      ((stepPremiseState_writes state 0x12224).get x10 (by decide) |>.trans indexAt)
      ((stepPremiseState_writes state 0x12224).get x12 (by decide) |>.trans limitAt)
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl

end BinaryFv.Zesu.MachineExecution
