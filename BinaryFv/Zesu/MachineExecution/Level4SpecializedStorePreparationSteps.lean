import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level4DecodeRawParentInvariant
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Parent store preparation before the next specialized decoder re-entry -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The exact direct `fi:6` corridor whose middle word stores a temporary raw-frame value. -/
def level4SpecializedStorePreparationPcs : List Nat := [0x10638, 0x1063c, 0x10640]

abbrev Level4SpecializedStorePreparationPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4SpecializedStorePreparationPcs

theorem level4SpecializedStorePreparationPcs_subset_phase :
    level4SpecializedStorePreparationPcs.all
      decodeRawSpecializedDispatchReturnsSuccessPcs.contains = true := by
  native_decide

theorem level4SpecializedStorePreparationPcs_subset_direct :
    level4SpecializedStorePreparationPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

private theorem level4_specialized_store_preparation_10638_parent :
    Level4SpecializedStorePreparationPcs (BitVec.ofNat 64 0x10638) := by
  simp [Level4SpecializedStorePreparationPcs, level4SpecializedStorePreparationPcs]

private theorem level4_specialized_store_preparation_1063c_parent :
    Level4SpecializedStorePreparationPcs (BitVec.ofNat 64 0x1063c) := by
  simp [Level4SpecializedStorePreparationPcs, level4SpecializedStorePreparationPcs]

private theorem level4_specialized_store_preparation_10640_parent :
    Level4SpecializedStorePreparationPcs (BitVec.ofNat 64 0x10640) := by
  simp [Level4SpecializedStorePreparationPcs, level4SpecializedStorePreparationPcs]

private theorem level4_specialized_store_preparation_owned (pc : Nat)
    (inCorridor : pc = 0x10638 ∨ pc = 0x1063c ∨ pc = 0x10640) :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 pc) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  rcases inCorridor with rfl | rfl | rfl <;> native_decide

private theorem level4_rX_x20_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x20 = some value) :
    Runs (rX_bits (.Regidx 20#5)) state state value := by
  have index : (Sail.BitVec.toNatInt 20#5).toNat = 20 := by decide
  unfold Runs rX_bits rX
  simp [index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

private theorem level4_rX_x22_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x22 = some value) :
    Runs (rX_bits (.Regidx 22#5)) state state value := by
  have index : (Sail.BitVec.toNatInt 22#5).toNat = 22 := by decide
  unfold Runs rX_bits rX
  simp [index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

private theorem level4_rX_x23_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x23 = some value) :
    Runs (rX_bits (.Regidx 23#5)) state state value := by
  have index : (Sail.BitVec.toNatInt 23#5).toNat = 23 := by decide
  unfold Runs rX_bits rX
  simp [index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

/-- Sail executes `addi s6, s4, 2` at the corridor's first parent PC. -/
theorem level4_specialized_store_preparation_addi_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10638))
    (s4Value : state.regs.get? x20 = some s4) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10638) stepRetired x22
        (iTypeResult .ADDI 0x002#12 s4)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x10638 0x13 0x0b 0x2a 0x00 0x002#12 20#5 22#5 .ADDI atPc
    (level4_rX_x20_run _ _ (decoderExecuteState_get? s4Value)) (wX_x22_run _ _)
    (pcIn := ⟨level4_specialized_store_preparation_owned _ (Or.inl rfl), by native_decide⟩)

/-- Sail executes `sd s7, 0x2a0(sp)` into the explicitly caller-authorized raw frame.  The
separate input-frame fact is consumed later when this concrete post-state is shown to retain the
parent frame. -/
theorem level4_specialized_store_preparation_store_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo postStack : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1063c))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 postStack))
    (s7Value : state.regs.get? x23 = some s7)
    (fits : postStack + 0x2a8 ≤ 2 ^ 64)
    (writable : ∀ index, index < 8 →
      canonicalContractParams.env.stack (postStack + 0x2a0 + index))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (postStack + 0x2a0))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x1063c) stepRetired (postStack + 0x2a0)
        (width := 8) s7) false := by
  have targetToNat : (BitVec.ofNat 64 (postStack + 0x2a0)).toNat = postStack + 0x2a0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have targetEq : BitVec.ofNat 64 postStack + sign_extend (m := 64) 0x2a0#12 =
      BitVec.ofNat 64 (postStack + 0x2a0) := by
    rw [show sign_extend (m := 64) 0x2a0#12 = BitVec.ofNat 64 0x2a0 by decide, ← BitVec.ofNat_add]
  have allowed : DecoderAccessRange DecoderWritableByte
      (BitVec.ofNat 64 (postStack + 0x2a0)) 8 := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [targetToNat]
      exact fits
    · intro index indexBound
      rw [targetToNat]
      exact Or.inl (writable index indexBound)
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x1063c 0x23 0x30 0x71 0x2b 0x2a0#12 23#5 2#5 (BitVec.ofNat 64 postStack) s7
    (BitVec.ofNat 64 (postStack + 0x2a0)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? spValue))
    (level4_rX_x23_run _ _ (decoderExecuteState_get? s7Value)) targetEq allowed
    ⟨level4_specialized_store_preparation_owned _ (Or.inr (Or.inl rfl)), by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- Sail executes `add t1, s6, s7` after the exact raw-frame store. -/
theorem level4_specialized_store_preparation_add_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10640))
    (s6Value : state.regs.get? x22 = some s6) (s7Value : state.regs.get? x23 = some s7) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10640) stepRetired x6
        (rTypeResult .ADD s6 s7)) false := by
  exact decoderRTypeStepOfDecoderAgree machine agree retired code stepNo
    0x10640 0x33 0x03 0x7b 0x01 23#5 22#5 6#5 .ADD atPc
    (level4_rX_x22_run _ _ (decoderExecuteState_get? s6Value))
    (level4_rX_x23_run _ _ (decoderExecuteState_get? s7Value)) (wX_x6_run _ _)
    (pcIn := ⟨level4_specialized_store_preparation_owned _ (Or.inr (Or.inr rfl)), by native_decide⟩)

/-- A store frame transports one saved word when its eight bytes lie outside the precise write
region.  The corridor proof applies this once per concrete raw prologue slot. -/
private theorem level4_saved_word_preserved {before after : State} {M : Region}
    {base : Nat} {value : BitVec 64} (saved : SavedWordBytes before base value)
    (writes : WritesOnlyWithin M before after)
    (outside : ∀ index, index < (BinaryFv.RiscV.Sep.leBytes 8 value).length → ¬ M (base + index)) :
    SavedWordBytes after base value := by
  intro index bound
  exact (writes _ (outside index bound)).trans (saved index bound)

private theorem level4_specialized_store_alignment {margs : DecoderMachineArgs} {origin state : State}
    (frame : Level4DecodeRawParentFrame margs origin state) :
    ∃ entry : Level4DecodeRawEntryProloguePre margs origin,
      is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (entry.postStack + 0x2a0))) 8 = true := by
  rcases frame.invariant with ⟨entry, stackEq, raEq, saved, sp, inputMemory, inputSeparated,
    stackWritable, rawWritable, rawSeparated, aligned, code, machine, retired⟩
  refine ⟨entry, ?_⟩
  have targetFits : entry.postStack + 0x2a0 < 2 ^ 64 := by
    have fits := entry.stackFits
    rw [entry.postStackEq] at fits
    omega
  have targetAligned : (entry.postStack + 0x2a0) % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Nat.dvd_add
    · exact Nat.dvd_trans (by decide) (Nat.dvd_of_mod_eq_zero aligned)
    · decide
  simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt targetFits]
  simp [Int.tmod, targetAligned]

end BinaryFv.Zesu.MachineExecution
