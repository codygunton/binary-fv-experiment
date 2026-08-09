import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Initial parent instructions before the first Level 4 specialized dispatch

These two `fi:6` words precede the first selected dynamic decoder boundary at `0x1061c`.
They are proved directly through Sail and do not depend on the dynamic route-provider interface.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The first two direct `fi:6` words leading to the first specialized decoder re-entry. -/
def level4SpecializedDispatchInitialPcs : List Nat := [0x10614, 0x10618]

theorem level4SpecializedDispatchInitialPcs_subset_phase :
    level4SpecializedDispatchInitialPcs.all
      decodeRawSpecializedDispatchReturnsSuccessPcs.contains = true := by
  native_decide

theorem level4SpecializedDispatchInitialPcs_subset_direct :
    level4SpecializedDispatchInitialPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

private theorem level4_specialized_dispatch_sub_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x10614) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

private theorem level4_specialized_dispatch_length_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x10618) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

private theorem level4_rX_x23_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x23 = some value) :
    Runs (rX_bits (.Regidx 23#5)) state state value := by
  have index : (Sail.BitVec.toNatInt 23#5).toNat = 23 := by decide
  unfold Runs rX_bits rX
  simp [index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

private theorem level4_rX_x25_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x25 = some value) :
    Runs (rX_bits (.Regidx 25#5)) state state value := by
  have index : (Sail.BitVec.toNatInt 25#5).toNat = 25 := by decide
  unfold Runs rX_bits rX
  simp [index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

/-- Sail executes `sub a0, s9, s7` at the first direct parent PC after entry-offset setup. -/
theorem level4_specialized_dispatch_sub_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10614))
    (s9Value : state.regs.get? x25 = some s9)
    (s7Value : state.regs.get? x23 = some s7) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10614) stepRetired x10
        (rTypeResult .SUB s9 s7)) false := by
  exact decoderRTypeStepOfDecoderAgree machine agree retired code stepNo
    0x10614 0x33 0x85 0x7c 0x41 23#5 25#5 10#5 .SUB atPc
    (level4_rX_x25_run _ _ (decoderExecuteState_get? s9Value))
    (level4_rX_x23_run _ _ (decoderExecuteState_get? s7Value)) (wX_x10_run _ _)
    (pcIn := ⟨level4_specialized_dispatch_sub_owned, by native_decide⟩)

/-- Sail executes `li a2, 44` before control reaches the first specialized decoder re-entry. -/
theorem level4_specialized_dispatch_length_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10618)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10618) stepRetired x12
        (BitVec.ofNat 64 44)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x10618 0x13 0x06 0xc0 0x02 0x02c#12 0#5 12#5 .ADDI atPc (rX_x0_run _)
    (by
      rw [show iTypeResult .ADDI 0x02c#12 0#64 = BitVec.ofNat 64 44 by decide]
      exact wX_x12_run _ _)
    (pcIn := ⟨level4_specialized_dispatch_length_owned, by native_decide⟩)

def level4SpecializedDispatchInitialWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x10 ∨ r = x12

private theorem decoderPreserved_level4SpecializedDispatchInitialWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4SpecializedDispatchInitialWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with book | rfl | rfl
  · exact platformPreserved_disjoint r platform book
  all_goals simp [platformPreserved] at platform

structure Level4SpecializedDispatchInitialPre (margs : DecoderMachineArgs) (state : State) where
  machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10614)
  s9 : BitVec 64
  s9Value : state.regs.get? x25 = some s9
  s7 : BitVec 64
  s7Value : state.regs.get? x23 = some s7
  retired : RetiredCounterPresent state

structure Level4SpecializedDispatchInitialHandoff (fromStep : Nat) (before after : State)
    (pre : Level4SpecializedDispatchInitialPre margs before) : Prop where
  trace : Trace fromStep 2 before after
  confined : ConfinedPrefix RegisterWriteStep.decodeRawExecutionPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 2 before after
  writes : WritesOnlyRegs level4SpecializedDispatchInitialWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x1061c)
  offset : after.regs.get? x10 = some (rTypeResult .SUB pre.s9 pre.s7)
  fixedLength : after.regs.get? x12 = some (BitVec.ofNat 64 44)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs after
  retired : RetiredCounterPresent after

/-- The maximal straight-line `fi:6` segment before the first dynamic H boundary at `0x1061c`. -/
theorem level4_specialized_dispatch_initial
    (pre : Level4SpecializedDispatchInitialPre margs state) (fromStep : Nat) :
    ∃ after, Level4SpecializedDispatchInitialHandoff fromStep state after pre := by
  let seg0 := Seg.nil RegisterWriteStep.decodeRawExecutionPcs (fun _ => False)
    (fun _ _ _ _ _ => False) level4SpecializedDispatchInitialWrites noMemory fromStep pre.retired
    pre.atPc
  let seg0' := (seg0.know x25 pre.s9 pre.s9Value).know x23 pre.s7 pre.s7Value
  obtain ⟨afterSub, seg1⟩ := seg0'.step level4_specialized_dispatch_sub_owned (by simp) x10
    (rTypeResult .SUB pre.s9 pre.s7) (BitVec.ofNat 64 0x10618)
    (level4_specialized_dispatch_sub_step pre.machine (Agree.refl state) seg0'.retired pre.code
      fromStep seg0'.atPc pre.s9Value pre.s7Value)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedDispatchInitialWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterSub.mem := by
    rw [seg1.memEq noMemory_empty]
    exact pre.code
  have machine1 : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs afterSub :=
    pre.machine.mono (seg1.agree decoderPreserved_level4SpecializedDispatchInitialWrites_disjoint)
      seg1.retired
  obtain ⟨after, seg2⟩ := seg1.step level4_specialized_dispatch_length_owned (by simp) x12
    (BitVec.ofNat 64 44) (BitVec.ofNat 64 0x1061c)
    (level4_specialized_dispatch_length_step machine1 (Agree.refl afterSub) seg1.retired code1
      (fromStep + 1) seg1.atPc)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedDispatchInitialWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  refine ⟨after, ⟨seg2.trace, seg2.confined, seg2.writes, seg2.memEq noMemory_empty, seg2.atPc,
    seg2.reg x10 (rTypeResult .SUB pre.s9 pre.s7) (by simp),
    seg2.reg x12 (BitVec.ofNat 64 44) (by simp), ?_, ?_, seg2.retired⟩⟩
  · rw [seg2.memEq noMemory_empty]
    exact pre.code
  · exact pre.machine.mono
      (seg2.agree decoderPreserved_level4SpecializedDispatchInitialWrites_disjoint) seg2.retired

end BinaryFv.Zesu.MachineExecution
