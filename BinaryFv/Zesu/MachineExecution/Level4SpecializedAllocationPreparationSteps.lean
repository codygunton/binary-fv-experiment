import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Parent allocation preparation before a Level 4 dynamic boundary -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The one direct parent word immediately before the dynamic boundary at `0x1290c`. -/
def level4SpecializedAllocationPreparationPcs : List Nat := [0x12908]

abbrev Level4SpecializedAllocationPreparationPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4SpecializedAllocationPreparationPcs

theorem level4SpecializedAllocationPreparationPcs_subset_phase :
    level4SpecializedAllocationPreparationPcs.all
      decodeRawSpecializedDispatchReturnsSuccessPcs.contains = true := by
  native_decide

theorem level4SpecializedAllocationPreparationPcs_subset_direct :
    level4SpecializedAllocationPreparationPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

private theorem level4_specialized_allocation_preparation_parent :
    Level4SpecializedAllocationPreparationPcs (BitVec.ofNat 64 0x12908) := by
  simp [Level4SpecializedAllocationPreparationPcs, level4SpecializedAllocationPreparationPcs]

private theorem level4_specialized_allocation_preparation_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x12908) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

private theorem level4_wX_x20_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 20#5) value) state
      { state with regs := state.regs.insert x20 value } () := by
  have index : (Sail.BitVec.toNatInt 20#5).toNat = 20 := by decide
  unfold Runs
  simp [wX_bits, wX, PreSail.writeReg, index, EStateM.run, EStateM.bind, EStateM.modifyGet,
    EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]

private theorem level4_specialized_allocation_preparation_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    {spBits : BitVec 64} (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12908))
    (stackPointerValue : state.regs.get? x2 = some spBits) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x12908) stepRetired x20
        (iTypeResult .ADDI 0x580#12 spBits)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x12908 0x13 0x0a 0x01 0x58 0x580#12 2#5 20#5 .ADDI atPc
    (rX_x2_run _ _ (decoderExecuteState_get? stackPointerValue)) (level4_wX_x20_run _ _)
    (pcIn := ⟨level4_specialized_allocation_preparation_owned, by native_decide⟩)

def level4SpecializedAllocationPreparationWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x20

private theorem decoderPreserved_level4SpecializedAllocationPreparationWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4SpecializedAllocationPreparationWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with book | rfl
  · exact platformPreserved_disjoint r platform book
  · simp [platformPreserved] at platform

structure Level4SpecializedAllocationPreparationPre (margs : DecoderMachineArgs) (state : State) where
  machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12908)
  stackPointer : BitVec 64
  stackPointerValue : state.regs.get? x2 = some stackPointer
  retired : RetiredCounterPresent state

structure Level4SpecializedAllocationPreparationHandoff (fromStep : Nat) (before after : State)
    (pre : Level4SpecializedAllocationPreparationPre margs before) : Prop where
  trace : Trace fromStep 1 before after
  confined : ConfinedPrefix Level4SpecializedAllocationPreparationPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 1 before after
  writes : WritesOnlyRegs level4SpecializedAllocationPreparationWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x1290c)
  allocationBase : after.regs.get? x20 = some (iTypeResult .ADDI 0x580#12 pre.stackPointer)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs after
  retired : RetiredCounterPresent after

/-- Sail executes the maximal direct parent segment before the `0x1290c` dynamic H boundary. -/
theorem level4_specialized_allocation_preparation
    (pre : Level4SpecializedAllocationPreparationPre margs state) (fromStep : Nat) :
    ∃ after, Level4SpecializedAllocationPreparationHandoff fromStep state after pre := by
  let seg0 := Seg.nil Level4SpecializedAllocationPreparationPcs (fun _ => False)
    (fun _ _ _ _ _ => False) level4SpecializedAllocationPreparationWrites noMemory fromStep pre.retired
    pre.atPc
  obtain ⟨after, seg1⟩ := seg0.step level4_specialized_allocation_preparation_parent (by simp) x20
    (iTypeResult .ADDI 0x580#12 pre.stackPointer) (BitVec.ofNat 64 0x1290c)
    (level4_specialized_allocation_preparation_step pre.machine (Agree.refl state) seg0.retired
      pre.code fromStep seg0.atPc pre.stackPointerValue)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedAllocationPreparationWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  refine ⟨after, ⟨seg1.trace, seg1.confined, seg1.writes, seg1.memEq noMemory_empty, seg1.atPc,
    seg1.reg x20 (iTypeResult .ADDI 0x580#12 pre.stackPointer) (by simp), ?_, ?_, seg1.retired⟩⟩
  · rw [seg1.memEq noMemory_empty]
    exact pre.code
  · exact pre.machine.mono
      (seg1.agree decoderPreserved_level4SpecializedAllocationPreparationWrites_disjoint) seg1.retired

end BinaryFv.Zesu.MachineExecution
