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

/-- The corridor's two register writes and ordinary retirement bookkeeping. -/
def level4SpecializedStorePreparationWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x22 ∨ r = x6

/-- The only bytes this three-word corridor may modify. -/
def level4SpecializedStorePreparationMemory (postStack : Nat) : Region := fun address =>
  postStack + 0x2a0 ≤ address ∧ address < postStack + 0x2a8

private theorem decoderPreserved_level4SpecializedStorePreparationWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4SpecializedStorePreparationWrites := by
  intro r preserved written
  rcases preserved with ⟨notLink, platform⟩
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint r platform bookkeeping
  all_goals simp [platformPreserved] at platform

/-- Parent facts at the first word of the raw-frame store corridor.  The protected frame comes
from the concrete raw prologue; the two live operands are machine bindings at this PC. -/
structure Level4SpecializedStorePreparationPre (margs : DecoderMachineArgs) (origin state : State)
    where
  frame : Level4DecodeRawParentFrame margs origin state
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10638)
  s4 : BitVec 64
  s4Value : state.regs.get? x20 = some s4
  s7 : BitVec 64
  s7Value : state.regs.get? x23 = some s7

/-- Exact parent handoff after `addi; sd; add`.  Its `preserved` field is the concrete raw
prologue frame needed by every later decoder/rejection/epilogue route. -/
structure Level4SpecializedStorePreparationHandoff (postStack fromStep : Nat) (before after : State)
    (pre : Level4SpecializedStorePreparationPre margs origin before) : Prop where
  trace : Trace fromStep 3 before after
  confined : ConfinedPrefix Level4SpecializedStorePreparationPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 3 before after
  writes : WritesOnlyRegs level4SpecializedStorePreparationWrites before after
  memory : WritesOnlyWithin (level4SpecializedStorePreparationMemory postStack) before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10644)
  s6 : after.regs.get? x22 = some (iTypeResult .ADDI 0x002#12 pre.s4)
  sum : after.regs.get? x6 = some (rTypeResult .ADD (iTypeResult .ADDI 0x002#12 pre.s4) pre.s7)
  preserved : pre.frame.PreservedTo after

private theorem level4_specialized_store_preparation_saved_frame
    {margs : DecoderMachineArgs} {origin before after : State}
    (frame : Level4DecodeRawParentFrame margs origin before)
    (entry : Level4DecodeRawEntryProloguePre margs origin)
    (stackEq : entry.stack = frame.stack)
    (saved : Level4DecodeRawPrologueSavedFrame before frame.stack frame.savedRa frame.savedS0
      frame.savedS1 frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6
      frame.savedS7 frame.savedS8 frame.savedS9 frame.savedS10 frame.savedS11)
    (writes : WritesOnlyWithin (level4SpecializedStorePreparationMemory entry.postStack) before after) :
    Level4DecodeRawPrologueSavedFrame after frame.stack frame.savedRa frame.savedS0 frame.savedS1
      frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6 frame.savedS7
      frame.savedS8 frame.savedS9 frame.savedS10 frame.savedS11 := by
  have outside (offset : Nat) (lower : 0x788 ≤ offset) (upper : offset + 8 ≤ 0x7f0) : ∀ index,
      index < (BinaryFv.RiscV.Sep.leBytes 8 frame.savedRa).length →
      ¬ level4SpecializedStorePreparationMemory entry.postStack (frame.stack + offset + index) := by
    intro index bound inStore
    rw [BinaryFv.RiscV.Sep.leBytes_length] at bound
    simp only [level4SpecializedStorePreparationMemory] at inStore
    rw [← stackEq, entry.postStackEq] at inStore
    omega
  rcases saved with ⟨ra, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact level4_saved_word_preserved ra writes (outside 0x7e8 (by omega) (by omega))
  · exact level4_saved_word_preserved s0 writes (outside 0x7e0 (by omega) (by omega))
  · exact level4_saved_word_preserved s1 writes (outside 0x7d8 (by omega) (by omega))
  · exact level4_saved_word_preserved s2 writes (outside 0x7d0 (by omega) (by omega))
  · exact level4_saved_word_preserved s3 writes (outside 0x7c8 (by omega) (by omega))
  · exact level4_saved_word_preserved s4 writes (outside 0x7c0 (by omega) (by omega))
  · exact level4_saved_word_preserved s5 writes (outside 0x7b8 (by omega) (by omega))
  · exact level4_saved_word_preserved s6 writes (outside 0x7b0 (by omega) (by omega))
  · exact level4_saved_word_preserved s7 writes (outside 0x7a8 (by omega) (by omega))
  · exact level4_saved_word_preserved s8 writes (outside 0x7a0 (by omega) (by omega))
  · exact level4_saved_word_preserved s9 writes (outside 0x798 (by omega) (by omega))
  · exact level4_saved_word_preserved s10 writes (outside 0x790 (by omega) (by omega))
  · exact level4_saved_word_preserved s11 writes (outside 0x788 (by omega) (by omega))

/-- Sail executes the complete direct raw-frame corridor and retains the concrete parent frame. -/
theorem level4_specialized_store_preparation
    (pre : Level4SpecializedStorePreparationPre margs origin state) (fromStep : Nat) :
    ∃ after postStack, Level4SpecializedStorePreparationHandoff postStack fromStep state after pre := by
  rcases pre.frame.invariant with ⟨entry, stackEq, raEq, saved, sp, inputMemory, inputSeparated,
    stackWritable, rawWritable, rawSeparated, postStackAligned, code, machine, retired⟩
  have stackFits : entry.postStack + 0x2a8 ≤ 2 ^ 64 := by
    have fits := entry.stackFits
    rw [entry.postStackEq] at fits
    omega
  have writable : ∀ index, index < 8 →
      canonicalContractParams.env.stack (entry.postStack + 0x2a0 + index) := by
    intro index bound
    have targetIndex : 0x2a0 + index < 0x7f0 := by omega
    simpa [Nat.add_assoc] using rawWritable (0x2a0 + index) targetIndex
  have aligned : is_aligned_vaddr
      (virtaddr.Virtaddr (BitVec.ofNat 64 (entry.postStack + 0x2a0))) 8 = true := by
    have targetFits : entry.postStack + 0x2a0 < 2 ^ 64 := by omega
    have targetAligned : (entry.postStack + 0x2a0) % 8 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      apply Nat.dvd_add
      · exact Nat.dvd_trans (by decide) (Nat.dvd_of_mod_eq_zero postStackAligned)
      · decide
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt targetFits]
    simp [Int.tmod, targetAligned]
  let seg0 := Seg.nil Level4SpecializedStorePreparationPcs (fun _ => False)
    (fun _ _ _ _ _ => False) level4SpecializedStorePreparationWrites
    (level4SpecializedStorePreparationMemory entry.postStack) fromStep retired pre.atPc
  let seg0 := (seg0.know x20 pre.s4 pre.s4Value).know x23 pre.s7 pre.s7Value
  let seg0 := seg0.know x2 (BitVec.ofNat 64 entry.postStack) sp
  obtain ⟨retired1, afterAddi, hAddi, seg1⟩ := seg0.stepWitness
    level4_specialized_store_preparation_10638_parent (by simp) x22
    (iTypeResult .ADDI 0x002#12 pre.s4) (BitVec.ofNat 64 0x1063c)
    (level4_specialized_store_preparation_addi_step machine (Agree.refl state) seg0.retired code
      fromStep seg0.atPc pre.s4Value)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedStorePreparationWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterAddi.mem := by
    rw [hAddi, afterRegisterWrite_mem]
    exact code
  have machine1 : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs afterAddi :=
    machine.mono (seg1.agree decoderPreserved_level4SpecializedStorePreparationWrites_disjoint)
      seg1.retired
  have sp1 := seg1.reg x2 (BitVec.ofNat 64 entry.postStack) (by simp)
  have s7At1 := seg1.reg x23 pre.s7 (by simp)
  obtain ⟨retired2, afterStore, hStore, seg2⟩ := seg1.stepStoreWitness
    (entry.postStack + 0x2a0) pre.s7 (BitVec.ofNat 64 0x10640)
    level4_specialized_store_preparation_1063c_parent (by simp)
    (level4_specialized_store_preparation_store_step machine1 (Agree.refl afterAddi) seg1.retired
      code1 (fromStep + 1) entry.postStack seg1.atPc sp1 s7At1 stackFits writable aligned)
    (by decide) (by intro other low high; exact ⟨low, high⟩)
    (by intro r h; exact Or.inl h) (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully afterStore.mem := by
    rw [hStore]
    have notFile : ∀ index : Fin 8,
        Artifacts.programImage.readFileByte? (entry.postStack + 0x2a0 + index.val) = none :=
      fun index => canonicalStack_not_fileByte (writable index.val index.isLt)
    have written := fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement afterAddi)
        (BitVec.ofNat 64 0x1063c)) (entry.postStack + 0x2a0) pre.s7 notFile
      (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code1)
    simpa [afterMemoryWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using written
  have machine2 : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs afterStore :=
    machine.mono (seg2.agree decoderPreserved_level4SpecializedStorePreparationWrites_disjoint)
      seg2.retired
  have s6At2 := seg2.reg x22 (iTypeResult .ADDI 0x002#12 pre.s4) (by simp)
  have s7At2 := seg2.reg x23 pre.s7 (by simp)
  obtain ⟨retired3, after, hAdd, seg3⟩ := seg2.stepWitness
    level4_specialized_store_preparation_10640_parent (by simp) x6
    (rTypeResult .ADD (iTypeResult .ADDI 0x002#12 pre.s4) pre.s7) (BitVec.ofNat 64 0x10644)
    (level4_specialized_store_preparation_add_step machine2 (Agree.refl afterStore) seg2.retired code2
      (fromStep + 2) seg2.atPc s6At2 s7At2)
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4SpecializedStorePreparationWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code3 : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hAdd, afterRegisterWrite_mem]
    exact code2
  have inputAfter : DecodedValue.MemoryBytes after margs.inputBase margs.bytes := by
    apply inputMemory.of_mem_eq
    intro index bound
    exact seg3.mem _ (by
      intro inStore
      simp only [level4SpecializedStorePreparationMemory] at inStore
      rcases rawSeparated (margs.inputBase + index) (by omega) (by omega) with separated | separated
      · omega
      · omega)
  have savedAfter := level4_specialized_store_preparation_saved_frame pre.frame entry stackEq saved
    seg3.mem
  have preserved : pre.frame.PreservedTo after := by
    refine ⟨entry, stackEq, raEq, savedAfter,
      seg3.reg x2 (BitVec.ofNat 64 entry.postStack) (by simp), inputAfter, inputSeparated,
      stackWritable, rawWritable, rawSeparated, postStackAligned, code3, ?_, seg3.retired⟩
    exact machine.mono (seg3.agree decoderPreserved_level4SpecializedStorePreparationWrites_disjoint)
      seg3.retired
  exact ⟨after, entry.postStack, ⟨seg3.trace, seg3.confined, seg3.writes, seg3.mem, seg3.atPc,
    seg3.reg x22 (iTypeResult .ADDI 0x002#12 pre.s4) (by simp),
    seg3.reg x6 (rTypeResult .ADD (iTypeResult .ADDI 0x002#12 pre.s4) pre.s7) (by simp),
    preserved⟩⟩

end BinaryFv.Zesu.MachineExecution
