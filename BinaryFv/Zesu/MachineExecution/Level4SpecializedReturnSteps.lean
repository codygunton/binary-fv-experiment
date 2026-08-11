import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Register-only return preparation in Level 4 `decodeRaw`

The two parent-owned words before the dynamic decoder reached from `0x12728` are executed here
directly through Sail.  They do not rely on the route provider that later resumes the decoder.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

def level4SpecializedReturnPreparationPcs : List Nat := [0x12720, 0x12724]

abbrev Level4SpecializedReturnPreparationPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4SpecializedReturnPreparationPcs

theorem level4SpecializedReturnPreparationPcs_count :
    level4SpecializedReturnPreparationPcs.length = 2 := rfl

theorem level4SpecializedReturnPreparationPcs_subset_phase :
    level4SpecializedReturnPreparationPcs.all
      decodeRawSpecializedDispatchReturnsSuccessPcs.contains = true := by
  native_decide

theorem level4SpecializedReturnPreparationPcs_subset_direct :
    level4SpecializedReturnPreparationPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

private theorem level4_specialized_return_sub_parent :
    Level4SpecializedReturnPreparationPcs (BitVec.ofNat 64 0x12720) := by
  simp [Level4SpecializedReturnPreparationPcs, level4SpecializedReturnPreparationPcs]

private theorem level4_specialized_return_length_parent :
    Level4SpecializedReturnPreparationPcs (BitVec.ofNat 64 0x12724) := by
  simp [Level4SpecializedReturnPreparationPcs, level4SpecializedReturnPreparationPcs]

private theorem level4_specialized_return_sub_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x12720) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

private theorem level4_specialized_return_length_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x12724) := by
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

private theorem level4_specialized_return_sub_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12720))
    (a2Value : state.regs.get? x12 = some a2)
    (a3Value : state.regs.get? x13 = some a3) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x12720) stepRetired x20
        (rTypeResult .SUB a2 a3)) false := by
  exact decoderRTypeStepOfDecoderAgree machine agree retired code stepNo
    0x12720 0x33 0x0a 0xd6 0x40 13#5 12#5 20#5 .SUB atPc
    (rX_x12_run _ _ (decoderExecuteState_get? a2Value))
    (rX_x13_run _ _ (decoderExecuteState_get? a3Value)) (level4_wX_x20_run _ _)
    (pcIn := ⟨level4_specialized_return_sub_owned, by native_decide⟩)

private theorem level4_specialized_return_length_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12724)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x12724) stepRetired x12
        (BitVec.ofNat 64 12)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x12724 0x13 0x06 0xc0 0x00 0x00c#12 0#5 12#5 .ADDI atPc (rX_x0_run _)
    (by
      rw [show iTypeResult .ADDI 0x00c#12 0#64 = BitVec.ofNat 64 12 by decide]
      exact wX_x12_run _ _)
    (pcIn := ⟨level4_specialized_return_length_owned, by native_decide⟩)

def level4SpecializedReturnPreparationWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x20 ∨ r = x12

private theorem decoderPreserved_level4SpecializedReturnPreparationWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4SpecializedReturnPreparationWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with book | rfl | rfl
  · exact platformPreserved_disjoint r platform book
  all_goals simp [platformPreserved] at platform

structure Level4SpecializedReturnPreparationPre (margs : DecoderMachineArgs) (state : State) where
  machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12720)
  a2 : BitVec 64
  a2Value : state.regs.get? x12 = some a2
  a3 : BitVec 64
  a3Value : state.regs.get? x13 = some a3
  retired : RetiredCounterPresent state

structure Level4SpecializedReturnPreparationHandoff (fromStep : Nat) (before after : State)
    (pre : Level4SpecializedReturnPreparationPre margs before) : Prop where
  trace : Trace fromStep 2 before after
  confined : ConfinedPrefix Level4SpecializedReturnPreparationPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 2 before after
  writes : WritesOnlyRegs level4SpecializedReturnPreparationWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x12728)
  byteLength : after.regs.get? x20 = some (rTypeResult .SUB pre.a2 pre.a3)
  fixedLength : after.regs.get? x12 = some (BitVec.ofNat 64 12)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs after
  retired : RetiredCounterPresent after

/-- Sail executes the exact parent return-preparation segment before the next dynamic H boundary. -/
theorem level4_specialized_return_preparation
    (pre : Level4SpecializedReturnPreparationPre margs state) (fromStep : Nat) :
    ∃ after, Level4SpecializedReturnPreparationHandoff fromStep state after pre := by
  let seg0 := Seg.nil Level4SpecializedReturnPreparationPcs (fun _ => False)
    (fun _ _ _ _ _ => False) level4SpecializedReturnPreparationWrites noMemory fromStep pre.retired
    pre.atPc
  let seg0' := (seg0.know x12 pre.a2 pre.a2Value).know x13 pre.a3 pre.a3Value
  obtain ⟨afterSub, seg1⟩ := seg0'.step level4_specialized_return_sub_parent (by simp) x20
    (rTypeResult .SUB pre.a2 pre.a3) (BitVec.ofNat 64 0x12724)
    (level4_specialized_return_sub_step pre.machine (Agree.refl state) seg0'.retired pre.code
      fromStep seg0'.atPc pre.a2Value pre.a3Value)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedReturnPreparationWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterSub.mem := by
    rw [seg1.memEq noMemory_empty]
    exact pre.code
  have machine1 : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs afterSub :=
    pre.machine.mono (seg1.agree decoderPreserved_level4SpecializedReturnPreparationWrites_disjoint)
      seg1.retired
  let seg1' := seg1.forget (kv' := [⟨x20, rTypeResult .SUB pre.a2 pre.a3⟩, ⟨x13, pre.a3⟩]) (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp))
  obtain ⟨after, seg2⟩ := seg1'.step level4_specialized_return_length_parent (by simp) x12
    (BitVec.ofNat 64 12) (BitVec.ofNat 64 0x12728)
    (level4_specialized_return_length_step machine1 (Agree.refl afterSub) seg1'.retired code1
      (fromStep + 1) seg1'.atPc)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedReturnPreparationWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  refine ⟨after, ⟨seg2.trace, seg2.confined, seg2.writes, seg2.memEq noMemory_empty, seg2.atPc,
    seg2.reg x20 (rTypeResult .SUB pre.a2 pre.a3) (by simp),
    seg2.reg x12 (BitVec.ofNat 64 12) (by simp), ?_, ?_, seg2.retired⟩⟩
  · rw [seg2.memEq noMemory_empty]
    exact pre.code
  · exact pre.machine.mono
      (seg2.agree decoderPreserved_level4SpecializedReturnPreparationWrites_disjoint) seg2.retired

end BinaryFv.Zesu.MachineExecution
