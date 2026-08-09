import BinaryFv.Zesu.MachineExecution.Level4DecodeRawParentInvariant

/-! # Exact parent continuation for excluded `RawNewPayloadRequest.deinit` -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The exact 45 generated PCs of excluded `RawNewPayloadRequest.deinit`. -/
abbrev Level4RawNewPayloadRequestDeinitPcs : BitVec 64 → Prop :=
  RegionPcs excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions

private theorem level4_rawNewPayloadRequestDeinit_entry_owned :
    Level4RawNewPayloadRequestDeinitPcs (BitVec.ofNat 64 0x131ec) := by
  change ∃ range : BinaryFv.Binary.AddressRange,
    range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
      range.start ≤ 78316 ∧ 78316 < range.stop
  refine ⟨{ start := 78316, size := 180 }, ?_, by decide, by decide⟩
  native_decide

/-- Current parent facts at the selected excluded-region entry. -/
structure Level4RawNewPayloadRequestDeinitPre {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current) : Prop where
  pc : current.regs.get? PC = some (BitVec.ofNat 64 0x131ec)
  sp : current.regs.get? x2 = some (BitVec.ofNat 64 (frame.stack - 0x690))
  /-- The parent `jalr` return address consumed by the selected deinit call. -/
  ra : current.regs.get? x1 = some (BitVec.ofNat 64 0x129ec)
  /-- `s0` is live through this inline continuation and is saved/restored by the child. -/
  s0 : ∃ value, current.regs.get? x8 = some value
  /-- The accepted rejection route establishes its literal tag value before this child. -/
  s1 : current.regs.get? x9 = some (BitVec.ofNat 64 2)
  /-- Parent call setup supplies the two argument registers consumed after the initial saves. -/
  a0 : ∃ value, current.regs.get? x10 = some value
  a1 : ∃ value, current.regs.get? x11 = some value
  preservation : frame.PreservedTo current

/-- Exact union of the three eight-byte child-save slots. -/
def level4RawNewPayloadRequestDeinitSaveMemory (postStack : Nat) : Region := fun address =>
  (postStack - 0x50 + 0x48 ≤ address ∧ address < postStack - 0x50 + 0x50) ∨
  (postStack - 0x50 + 0x40 ≤ address ∧ address < postStack - 0x50 + 0x48) ∨
  (postStack - 0x50 + 0x38 ≤ address ∧ address < postStack - 0x50 + 0x40)

abbrev Level4RawNewPayloadRequestDeinitExit : BitVec 64 → Prop := fun _ => False
abbrev Level4RawNewPayloadRequestDeinitChildSummary : FunctionInstanceId → Nat → Nat → State → State → Prop :=
  fun _ _ _ _ _ => False

def level4RawNewPayloadRequestDeinitWrites : RegSet := fun r => stepBookkeeping r ∨ r = x2

private theorem decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4RawNewPayloadRequestDeinitWrites := by
  intro r preserved written
  rcases preserved with ⟨notLink, platform⟩
  rcases written with bookkeeping | rfl
  · exact platformPreserved_disjoint r platform bookkeeping
  · simp [platformPreserved] at platform

private theorem level4_rawNewPayloadRequestDeinit_slot_writable
    (entry : Level4DecodeRawEntryProloguePre margs origin) {offset index : Nat}
    (slot : offset + 8 ≤ 0x50) (indexBound : index < 8) :
    canonicalContractParams.env.stack (entry.postStack - 0x50 + offset + index) := by
  rw [show entry.postStack - 0x50 + offset + index =
    entry.postStack - 0x50 + (offset + index) by omega]
  apply entry.nestedCallFrameWritable
  omega

private theorem level4_rawNewPayloadRequestDeinit_slot_fits
    (entry : Level4DecodeRawEntryProloguePre margs origin) {offset : Nat}
    (slot : offset + 8 ≤ 0x50) : entry.postStack - 0x50 + offset + 8 ≤ 2 ^ 64 := by
  have stackFits := entry.stackFits
  have postStackFits := entry.nestedCallFrameFits
  rw [entry.postStackEq] at stackFits
  have childFits : entry.postStack - 0x50 + 0x50 = entry.postStack := by
    omega
  omega

private theorem level4_rawNewPayloadRequestDeinit_slot_aligned
    (entry : Level4DecodeRawEntryProloguePre margs origin) {offset : Nat}
    (slot : offset + 8 ≤ 0x50) (offsetAligned : offset % 8 = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr
      (BitVec.ofNat 64 (entry.postStack - 0x50 + offset))) 8 = true := by
  have addressFits : entry.postStack - 0x50 + offset < 2 ^ 64 := by
    have stackFits := entry.stackFits
    have postStackFits := entry.nestedCallFrameFits
    rw [entry.postStackEq] at stackFits
    omega
  have baseAligned : (entry.postStack - 0x50) % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_sub
      (Nat.dvd_trans (by decide) (Nat.dvd_of_mod_eq_zero entry.postStackAligned)) (by decide)
  have addressAligned : (entry.postStack - 0x50 + offset) % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Nat.dvd_add
    · exact Nat.dvd_of_mod_eq_zero baseAligned
    · exact Nat.dvd_of_mod_eq_zero offsetAligned
  simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt addressFits]
  simp [Int.tmod, addressAligned]

private theorem level4_rawNewPayloadRequestDeinit_stack_value (postStack : Nat)
    (fits : 0x50 ≤ postStack) :
    iTypeResult .ADDI 0xfb0#12 (BitVec.ofNat 64 postStack) =
      BitVec.ofNat 64 (postStack - 0x50) := by
  unfold iTypeResult
  simp only
  rw [show sign_extend (m := 64) 0xfb0#12 = BitVec.ofNat 64 (2 ^ 64 - 0x50) by decide]
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show postStack = (postStack - 0x50) + 0x50 by omega]
  rw [show (postStack - 0x50 + 0x50 + (2 ^ 64 - 0x50)) =
    (postStack - 0x50) + 2 ^ 64 by omega]
  exact Nat.add_mod_right _ _

/-- Sail executes the literal `addi sp, sp, -0x50` at excluded:3's entry.  The result is left in
instruction-class form here; the following save steps consume it as their concrete stack base. -/
theorem level4_rawNewPayloadRequestDeinit_stack_step
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ retired, Runs (try_step fromStep false) current
      (afterRegisterWrite current (BitVec.ofNat 64 0x131ec) retired x2
        (iTypeResult .ADDI 0xfb0#12 (BitVec.ofNat 64 (frame.stack - 0x690)))) false := by
  rcases pre.preservation with ⟨entry, -, -, -, stackValue, -, -, -, -, -, -, code, outerMachine, retired⟩
  let machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs current :=
    outerMachine.restrict rawNewPayloadRequestDeinitPcs_subset_decodeRaw
  exact decoderITypeStepOfDecoderAgree machine (Agree.refl current) retired code fromStep
    0x131ec 0x13 0x01 0x01 0xfb 0xfb0#12 2#5 2#5 .ADDI pre.pc
    (rX_x2_run _ _ (decoderExecuteState_get? pre.sp)) (wX_x2_run _ _)
    (pcIn := ⟨level4_rawNewPayloadRequestDeinit_entry_owned, by native_decide⟩)

/-- The child-frame allocation is one exact straight-line step, retaining its concrete successor
shape for the three immediately following stores. -/
private theorem level4_rawNewPayloadRequestDeinit_stack_seg_witness
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ after, Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
      Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
      (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
      [⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x9, BitVec.ofNat 64 2⟩,
        ⟨x8, Classical.choose pre.s0⟩, ⟨x1, BitVec.ofNat 64 0x129ec⟩]
      fromStep 1 current after (BitVec.ofNat 64 0x131f0) ∧
      ∃ retired, after = afterRegisterWrite current (BitVec.ofNat 64 0x131ec) retired x2
        (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) := by
  rcases pre.preservation with ⟨entry, stackEq, -, -, -, -, -, -, -, -, -, -, -, retired⟩
  have postStack : frame.stack - 0x690 = entry.postStack := by rw [← stackEq, entry.postStackEq]; omega
  have s0Value : current.regs.get? x8 = some (Classical.choose pre.s0) := Classical.choose_spec pre.s0
  let seg0 := Seg.nil Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
    Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
    (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
    fromStep retired pre.pc
  let seg0 := seg0.know x1 (BitVec.ofNat 64 0x129ec) pre.ra
  let seg0 := seg0.know x8 (Classical.choose pre.s0) s0Value
  let seg0 := seg0.know x9 (BitVec.ofNat 64 2) pre.s1
  have run : ∃ stepRetired, Runs (try_step fromStep false) current
      (afterRegisterWrite current (BitVec.ofNat 64 0x131ec) stepRetired x2
        (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50))) false := by
    obtain ⟨stepRetired, hrun⟩ := level4_rawNewPayloadRequestDeinit_stack_step frame pre fromStep
    rw [level4_rawNewPayloadRequestDeinit_stack_value (frame.stack - 0x690) (by rw [postStack]; exact entry.nestedCallFrameFits)] at hrun
    exact ⟨stepRetired, hrun⟩
  obtain ⟨stepRetired, after, hAfter, seg1⟩ := seg0.stepWitness level4_rawNewPayloadRequestDeinit_entry_owned
    (by simp [Level4RawNewPayloadRequestDeinitExit]) x2
    (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (BitVec.ofNat 64 0x131f0) run
    (by decide) (fun _ h => Or.inl h) (Or.inr rfl) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  exact ⟨after, by simpa [seg0] using seg1, ⟨stepRetired, hAfter⟩⟩

/-- The child-frame allocation is one exact straight-line step. -/
theorem level4_rawNewPayloadRequestDeinit_stack_seg
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ after, Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
      Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
      (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
      [⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x9, BitVec.ofNat 64 2⟩,
        ⟨x8, Classical.choose pre.s0⟩, ⟨x1, BitVec.ofNat 64 0x129ec⟩]
      fromStep 1 current after (BitVec.ofNat 64 0x131f0) := by
  obtain ⟨after, seg, -⟩ := level4_rawNewPayloadRequestDeinit_stack_seg_witness frame pre fromStep
  exact ⟨after, seg⟩

/-- The first child save is the literal `sd ra, 0x48(sp)`.  Its permission is explicit so the
continuation theorem can discharge it from `ParentFrame.entry.nestedCallFrameWritable`. -/
theorem level4_rawNewPayloadRequestDeinit_save_ra_step {margs : DecoderMachineArgs}
    {base state : State} {ra : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo childBase : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x131f0))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 childBase))
    (raValue : state.regs.get? x1 = some ra) (fits : childBase + 0x50 ≤ 2 ^ 64)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (childBase + 0x48 + index))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (childBase + 0x48))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x131f0) stepRetired (childBase + 0x48)
        (width := 8) ra) false := by
  have targetToNat : (BitVec.ofNat 64 (childBase + 0x48)).toNat = childBase + 0x48 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have targetEq : BitVec.ofNat 64 childBase + sign_extend (m := 64) 0x048#12 =
      BitVec.ofNat 64 (childBase + 0x48) := by
    rw [show sign_extend (m := 64) 0x048#12 = BitVec.ofNat 64 0x48 by decide, ← BitVec.ofNat_add]
  have allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (childBase + 0x48)) 8 := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [targetToNat]
      omega
    · intro index indexBound
      rw [targetToNat]
      exact Or.inl (writable index indexBound)
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x131f0 0x23 0x34 0x11 0x04 0x048#12 1#5 2#5 (BitVec.ofNat 64 childBase) ra
    (BitVec.ofNat 64 (childBase + 0x48)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? spValue))
    (rX_x1_run _ _ (decoderExecuteState_get? raValue)) targetEq allowed
    ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78320 ∧ 78320 < range.stop
      refine ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- The second child save is the literal `sd s0, 0x40(sp)`. -/
theorem level4_rawNewPayloadRequestDeinit_save_s0_step {margs : DecoderMachineArgs}
    {base state : State} {s0 : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo childBase : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x131f4))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 childBase))
    (s0Value : state.regs.get? x8 = some s0) (fits : childBase + 0x48 ≤ 2 ^ 64)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (childBase + 0x40 + index))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (childBase + 0x40))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x131f4) stepRetired (childBase + 0x40)
        (width := 8) s0) false := by
  have targetToNat : (BitVec.ofNat 64 (childBase + 0x40)).toNat = childBase + 0x40 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have targetEq : BitVec.ofNat 64 childBase + sign_extend (m := 64) 0x040#12 =
      BitVec.ofNat 64 (childBase + 0x40) := by
    rw [show sign_extend (m := 64) 0x040#12 = BitVec.ofNat 64 0x40 by decide, ← BitVec.ofNat_add]
  have allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (childBase + 0x40)) 8 := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [targetToNat]
      omega
    · intro index indexBound
      rw [targetToNat]
      exact Or.inl (writable index indexBound)
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x131f4 0x23 0x30 0x81 0x04 0x040#12 8#5 2#5 (BitVec.ofNat 64 childBase) s0
    (BitVec.ofNat 64 (childBase + 0x40)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? spValue))
    (rX_x8_run _ _ (decoderExecuteState_get? s0Value)) targetEq allowed
    ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78324 ∧ 78324 < range.stop
      refine ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- The third child save is the literal `sd s1, 0x38(sp)`. -/
theorem level4_rawNewPayloadRequestDeinit_save_s1_step {margs : DecoderMachineArgs}
    {base state : State} {s1 : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo childBase : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x131f8))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 childBase))
    (s1Value : state.regs.get? x9 = some s1) (fits : childBase + 0x40 ≤ 2 ^ 64)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (childBase + 0x38 + index))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (childBase + 0x38))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x131f8) stepRetired (childBase + 0x38)
        (width := 8) s1) false := by
  have targetToNat : (BitVec.ofNat 64 (childBase + 0x38)).toNat = childBase + 0x38 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have targetEq : BitVec.ofNat 64 childBase + sign_extend (m := 64) 0x038#12 =
      BitVec.ofNat 64 (childBase + 0x38) := by
    rw [show sign_extend (m := 64) 0x038#12 = BitVec.ofNat 64 0x38 by decide, ← BitVec.ofNat_add]
  have allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (childBase + 0x38)) 8 := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [targetToNat]
      omega
    · intro index indexBound
      rw [targetToNat]
      exact Or.inl (writable index indexBound)
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x131f8 0x23 0x3c 0x91 0x02 0x038#12 9#5 2#5 (BitVec.ofNat 64 childBase) s1
    (BitVec.ofNat 64 (childBase + 0x38)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? spValue))
    (rX_x9_run _ _ (decoderExecuteState_get? s1Value)) targetEq allowed
    ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78328 ∧ 78328 < range.stop
      refine ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- The initial child-frame allocation and three saves form a four-word corridor.  It retains the
exact three-slot write region and the live `ra`, `s0`, and rejection-tag `s1` bindings needed by
the remaining excluded instructions. -/
structure Level4RawNewPayloadRequestDeinitInitialSavesHandoff
    {margs : DecoderMachineArgs} {origin before : State}
    (frame : Level4DecodeRawParentFrame margs origin before)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) (after : State) : Prop where
  trace : Trace fromStep 4 before after
  confined : ConfinedPrefix Level4RawNewPayloadRequestDeinitPcs
    Level4RawNewPayloadRequestDeinitExit Level4RawNewPayloadRequestDeinitChildSummary fromStep 4
    before after
  writes : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites before after
  memory : WritesOnlyWithin (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
    before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x131fc)
  childSp : after.regs.get? x2 = some (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50))
  ra : after.regs.get? x1 = some (BitVec.ofNat 64 0x129ec)
  s0 : after.regs.get? x8 = some (Classical.choose pre.s0)
  s1 : after.regs.get? x9 = some (BitVec.ofNat 64 2)
  a0 : after.regs.get? x10 = some (Classical.choose pre.a0)
  a1 : after.regs.get? x11 = some (Classical.choose pre.a1)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs after
  retired : RetiredCounterPresent after

/-- Compose `addi sp, -0x50` with the literal `sd ra`, `sd s0`, and `sd s1` saves. -/
theorem level4_rawNewPayloadRequestDeinit_initial_saves_handoff
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ after, Level4RawNewPayloadRequestDeinitInitialSavesHandoff frame pre fromStep after := by
  rcases pre.preservation with ⟨entry, stackEq, -, -, -, -, -, -, -, -, -, code, outerMachine, -⟩
  have postStack : frame.stack - 0x690 = entry.postStack := by
    rw [← stackEq, entry.postStackEq]
    omega
  have childBase : frame.stack - 0x690 - 0x50 = entry.postStack - 0x50 := by rw [postStack]
  let machine0 : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs current :=
    outerMachine.restrict rawNewPayloadRequestDeinitPcs_subset_decodeRaw
  obtain ⟨afterStack, seg1, stepRetired, hStack⟩ :=
    level4_rawNewPayloadRequestDeinit_stack_seg_witness frame pre fromStep
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterStack.mem := by
    rw [hStack, afterRegisterWrite_mem]
    exact code
  have machine1 : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs afterStack :=
    machine0.mono (seg1.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
      seg1.retired
  have sp1 := seg1.reg x2 (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (by simp)
  have ra1 := seg1.reg x1 (BitVec.ofNat 64 0x129ec) (by simp)
  obtain ⟨retired2, afterRa, hRa, seg2⟩ := seg1.stepStoreWitness
    (frame.stack - 0x690 - 0x50 + 0x48) (BitVec.ofNat 64 0x129ec) (BitVec.ofNat 64 0x131f4)
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78320 ∧ 78320 < range.stop
      refine ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp)
    (by
      have fits : frame.stack - 0x690 - 0x50 + 0x50 ≤ 2 ^ 64 := by
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_fits entry (offset := 0x48) (by omega)
      have writable : ∀ index, index < 8 → canonicalContractParams.env.stack
          (frame.stack - 0x690 - 0x50 + 0x48 + index) := by
        intro index bound
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 0x48) (by omega) bound
      have aligned : is_aligned_vaddr (virtaddr.Virtaddr
          (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50 + 0x48))) 8 = true := by
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_aligned entry (offset := 0x48) (by omega)
          (by decide)
      exact level4_rawNewPayloadRequestDeinit_save_ra_step machine1 (Agree.refl afterStack)
        seg1.retired code1 (fromStep + 1) (frame.stack - 0x690 - 0x50) seg1.atPc
        sp1 ra1 fits writable aligned)
    (by decide)
    (by
      intro other lower upper
      simp only [level4RawNewPayloadRequestDeinitSaveMemory]
      exact Or.inl ⟨by omega, by omega⟩)
    (fun r h => Or.inl h) (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully afterRa.mem := by
    rw [hRa]
    have writable : ∀ index : Fin 8,
        canonicalContractParams.env.stack (frame.stack - 0x690 - 0x50 + 0x48 + index.val) := by
      intro index
      rw [childBase]
      exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 0x48) (by omega)
        index.isLt
    have written := fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement afterStack) (BitVec.ofNat 64 0x131f0))
      (frame.stack - 0x690 - 0x50 + 0x48) (BitVec.ofNat 64 0x129ec)
      (fun index => canonicalStack_not_fileByte (writable index))
      (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code1)
    simpa [afterMemoryWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using written
  have machine2 : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs afterRa :=
    machine0.mono (seg2.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
      seg2.retired
  have sp2 := seg2.reg x2 (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (by simp)
  have s0_2 := seg2.reg x8 (Classical.choose pre.s0) (by simp)
  obtain ⟨retired3, afterS0, hS0, seg3⟩ := seg2.stepStoreWitness
    (frame.stack - 0x690 - 0x50 + 0x40) (Classical.choose pre.s0) (BitVec.ofNat 64 0x131f8)
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78324 ∧ 78324 < range.stop
      refine ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp)
    (by
      have fits : frame.stack - 0x690 - 0x50 + 0x48 ≤ 2 ^ 64 := by
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_fits entry (offset := 0x40) (by omega)
      have writable : ∀ index, index < 8 → canonicalContractParams.env.stack
          (frame.stack - 0x690 - 0x50 + 0x40 + index) := by
        intro index bound
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 0x40) (by omega) bound
      have aligned : is_aligned_vaddr (virtaddr.Virtaddr
          (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50 + 0x40))) 8 = true := by
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_aligned entry (offset := 0x40) (by omega)
          (by decide)
      exact level4_rawNewPayloadRequestDeinit_save_s0_step machine2 (Agree.refl afterRa)
        seg2.retired code2 (fromStep + 2) (frame.stack - 0x690 - 0x50) seg2.atPc
        sp2 s0_2 fits writable aligned)
    (by decide)
    (by
      intro other lower upper
      simp only [level4RawNewPayloadRequestDeinitSaveMemory]
      exact Or.inr (Or.inl ⟨by omega, by omega⟩))
    (fun r h => Or.inl h) (by exact of_decide_eq_true rfl)
  have code3 : Artifacts.programImage.fileBytesLoadedFaithfully afterS0.mem := by
    rw [hS0]
    have writable : ∀ index : Fin 8,
        canonicalContractParams.env.stack (frame.stack - 0x690 - 0x50 + 0x40 + index.val) := by
      intro index
      rw [childBase]
      exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 0x40) (by omega)
        index.isLt
    have written := fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement afterRa) (BitVec.ofNat 64 0x131f4))
      (frame.stack - 0x690 - 0x50 + 0x40) (Classical.choose pre.s0)
      (fun index => canonicalStack_not_fileByte (writable index))
      (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code2)
    simpa [afterMemoryWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using written
  have machine3 : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs afterS0 :=
    machine0.mono (seg3.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
      seg3.retired
  have sp3 := seg3.reg x2 (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (by simp)
  have s1_3 := seg3.reg x9 (BitVec.ofNat 64 2) (by simp)
  obtain ⟨retired4, after, hS1, seg4⟩ := seg3.stepStoreWitness
    (frame.stack - 0x690 - 0x50 + 0x38) (BitVec.ofNat 64 2) (BitVec.ofNat 64 0x131fc)
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78328 ∧ 78328 < range.stop
      refine ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp)
    (by
      have fits : frame.stack - 0x690 - 0x50 + 0x40 ≤ 2 ^ 64 := by
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_fits entry (offset := 0x38) (by omega)
      have writable : ∀ index, index < 8 → canonicalContractParams.env.stack
          (frame.stack - 0x690 - 0x50 + 0x38 + index) := by
        intro index bound
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 0x38) (by omega) bound
      have aligned : is_aligned_vaddr (virtaddr.Virtaddr
          (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50 + 0x38))) 8 = true := by
        rw [childBase]
        exact level4_rawNewPayloadRequestDeinit_slot_aligned entry (offset := 0x38) (by omega)
          (by decide)
      exact level4_rawNewPayloadRequestDeinit_save_s1_step machine3 (Agree.refl afterS0)
        seg3.retired code3 (fromStep + 3) (frame.stack - 0x690 - 0x50) seg3.atPc
        sp3 s1_3 fits writable aligned)
    (by decide)
    (by
      intro other lower upper
      simp only [level4RawNewPayloadRequestDeinitSaveMemory]
      exact Or.inr (Or.inr ⟨by omega, by omega⟩))
    (fun r h => Or.inl h) (by exact of_decide_eq_true rfl)
  have code4 : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hS1]
    have writable : ∀ index : Fin 8,
        canonicalContractParams.env.stack (frame.stack - 0x690 - 0x50 + 0x38 + index.val) := by
      intro index
      rw [childBase]
      exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 0x38) (by omega)
        index.isLt
    have written := fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement afterS0) (BitVec.ofNat 64 0x131f8))
      (frame.stack - 0x690 - 0x50 + 0x38) (BitVec.ofNat 64 2)
      (fun index => canonicalStack_not_fileByte (writable index))
      (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code3)
    simpa [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using written
  refine ⟨after, ⟨seg4.trace, seg4.confined, seg4.writes, seg4.mem, seg4.atPc,
    seg4.reg x2 (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (by simp),
    seg4.reg x1 (BitVec.ofNat 64 0x129ec) (by simp),
    seg4.reg x8 (Classical.choose pre.s0) (by simp),
    seg4.reg x9 (BitVec.ofNat 64 2) (by simp),
    (seg4.get x10 (by simp [level4RawNewPayloadRequestDeinitWrites])).trans
      (Classical.choose_spec pre.a0),
    (seg4.get x11 (by simp [level4RawNewPayloadRequestDeinitWrites])).trans
      (Classical.choose_spec pre.a1), code4, ?_, seg4.retired⟩⟩
  exact machine0.mono (seg4.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
    seg4.retired

/-- Sail executes the literal `mv s0, a1` at `0x131fc`. -/
theorem level4_rawNewPayloadRequestDeinit_move_s0_step {margs : DecoderMachineArgs}
    {base state : State} {a1 : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x131fc))
    (a1Value : state.regs.get? x11 = some a1) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x131fc) stepRetired x8
        (iTypeResult .ADDI 0x000#12 a1)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x131fc 0x13 0x84 0x05 0x00 0x000#12 11#5 8#5 .ADDI atPc
    (rX_x11_run _ _ (decoderExecuteState_get? a1Value)) (wX_x8_run _ _)
    (pcIn := ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78332 ∧ 78332 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩)

end BinaryFv.Zesu.MachineExecution
