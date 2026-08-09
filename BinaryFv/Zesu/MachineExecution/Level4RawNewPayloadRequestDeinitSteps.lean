import BinaryFv.Zesu.MachineExecution.Level4DecodeRawParentInvariant
import BinaryFv.Zesu.MachineExecution.DecoderBitVectorLoad

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

/-- Exact union of the three eight-byte child-save slots. -/
def level4RawNewPayloadRequestDeinitSaveMemory (postStack : Nat) : Region := fun address =>
  (postStack - 0x50 + 0x48 ≤ address ∧ address < postStack - 0x50 + 0x50) ∨
  (postStack - 0x50 + 0x40 ≤ address ∧ address < postStack - 0x50 + 0x48) ∨
  (postStack - 0x50 + 0x38 ≤ address ∧ address < postStack - 0x50 + 0x40)

/-- The child-save slots together with the two argument slots written before the first nested call. -/
def level4RawNewPayloadRequestDeinitCallMemory (postStack : Nat) : Region := fun address =>
  level4RawNewPayloadRequestDeinitSaveMemory postStack address ∨
    (postStack - 0x50 + 8 ≤ address ∧ address < postStack - 0x50 + 0x18)

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
  /-- The live allocator pointer names the two machine words loaded at `0x13204` and `0x13208`.
  The rejection parent must derive this from its canonical allocator representation. -/
  allocatorPair : ∃ first second,
    DecodedValue.Word64LERep current (Classical.choose a1).toNat first ∧
      DecodedValue.Word64LERep current ((Classical.choose a1).toNat + 8) second ∧
        first < 2 ^ 64 ∧ second < 2 ^ 64 ∧ (Classical.choose a1).toNat + 16 ≤ 2 ^ 64
  allocatorReadable : DecoderAccessRange (DecoderReadableByte margs)
    (BitVec.ofNat 64 (Classical.choose a1).toNat) 16
  allocatorAligned : is_aligned_vaddr
    (virtaddr.Virtaddr (BitVec.ofNat 64 (Classical.choose a1).toNat)) 8 = true
  allocatorSecondAligned : is_aligned_vaddr
    (virtaddr.Virtaddr (BitVec.ofNat 64 (Classical.choose a1).toNat + 8)) 8 = true
  /-- The preceding child saves cannot overwrite either allocator word before the two loads. -/
  allocatorOutsideSave : ∀ address,
    (Classical.choose a1).toNat ≤ address → address < (Classical.choose a1).toNat + 16 →
      ¬ level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690) address
  preservation : frame.PreservedTo current

abbrev Level4RawNewPayloadRequestDeinitExit : BitVec 64 → Prop := fun _ => False
abbrev Level4RawNewPayloadRequestDeinitChildSummary : FunctionInstanceId → Nat → Nat → State → State → Prop :=
  fun _ _ _ _ _ => False

def level4RawNewPayloadRequestDeinitWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x2 ∨ r = x8 ∨ r = x9 ∨ r = x10 ∨ r = x11

private theorem decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4RawNewPayloadRequestDeinitWrites := by
  intro r preserved written
  rcases preserved with ⟨notLink, platform⟩
  rcases written with bookkeeping | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint r platform bookkeeping
  all_goals simp [platformPreserved] at platform

private theorem level4_rawNewPayloadRequestDeinit_widen_seg_memory
    {M wider : Region} {kv : List RegVal} {fromStep length : Nat} {before after : State}
    {pc : BitVec 64}
    (sub : ∀ address, M address → wider address)
    (seg : Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
      Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites M kv
      fromStep length before after pc) :
    Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
      Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites wider kv
      fromStep length before after pc :=
  { seg with mem := fun address outside => seg.mem address (fun owned => outside (sub address owned)) }

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
      [⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x11, Classical.choose pre.a1⟩,
        ⟨x10, Classical.choose pre.a0⟩, ⟨x9, BitVec.ofNat 64 2⟩,
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
  let seg0 := seg0.know x10 (Classical.choose pre.a0) (Classical.choose_spec pre.a0)
  let seg0 := seg0.know x11 (Classical.choose pre.a1) (Classical.choose_spec pre.a1)
  have run : ∃ stepRetired, Runs (try_step fromStep false) current
      (afterRegisterWrite current (BitVec.ofNat 64 0x131ec) stepRetired x2
        (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50))) false := by
    obtain ⟨stepRetired, hrun⟩ := level4_rawNewPayloadRequestDeinit_stack_step frame pre fromStep
    rw [level4_rawNewPayloadRequestDeinit_stack_value (frame.stack - 0x690) (by rw [postStack]; exact entry.nestedCallFrameFits)] at hrun
    exact ⟨stepRetired, hrun⟩
  obtain ⟨stepRetired, after, hAfter, seg1⟩ := seg0.stepWitness level4_rawNewPayloadRequestDeinit_entry_owned
    (by simp [Level4RawNewPayloadRequestDeinitExit]) x2
    (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (BitVec.ofNat 64 0x131f0) run
    (by decide) (fun _ h => Or.inl h) (Or.inr (Or.inl rfl)) (by decide) (by decide)
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
      [⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x11, Classical.choose pre.a1⟩,
        ⟨x10, Classical.choose pre.a0⟩, ⟨x9, BitVec.ofNat 64 2⟩,
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
  seg : Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
    Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
    (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
    [⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x11, Classical.choose pre.a1⟩,
      ⟨x10, Classical.choose pre.a0⟩, ⟨x9, BitVec.ofNat 64 2⟩,
      ⟨x8, Classical.choose pre.s0⟩, ⟨x1, BitVec.ofNat 64 0x129ec⟩]
    fromStep 4 before after (BitVec.ofNat 64 0x131fc)
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
  refine ⟨after, ⟨seg4.trace, seg4.confined, seg4.writes, seg4.mem, seg4, seg4.atPc,
    seg4.reg x2 (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (by simp),
    seg4.reg x1 (BitVec.ofNat 64 0x129ec) (by simp),
    seg4.reg x8 (Classical.choose pre.s0) (by simp),
    seg4.reg x9 (BitVec.ofNat 64 2) (by simp),
    seg4.reg x10 (Classical.choose pre.a0) (by simp),
    seg4.reg x11 (Classical.choose pre.a1) (by simp), code4, ?_, seg4.retired⟩⟩
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

/-- Sail executes the literal `mv s1, a0` at `0x13200`. -/
theorem level4_rawNewPayloadRequestDeinit_move_s1_step {margs : DecoderMachineArgs}
    {base state : State} {a0 : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13200))
    (a0Value : state.regs.get? x10 = some a0) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x13200) stepRetired x9
        (iTypeResult .ADDI 0x000#12 a0)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x13200 0x93 0x04 0x05 0x00 0x000#12 10#5 9#5 .ADDI atPc
    (rX_x10_run _ _ (decoderExecuteState_get? a0Value)) (wX_x9_run _ _)
    (pcIn := ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78336 ∧ 78336 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩)

private theorem level4_rawNewPayloadRequestDeinit_extend_value_dword (value : BitVec (8 * 8)) :
    extend_value false value = value := by
  unfold extend_value
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

/-- Sail executes `ld a0, 0(a1)` from the typed allocator pair at `0x13204`. -/
private theorem level4_rawNewPayloadRequestDeinit_load_a0_step {margs : DecoderMachineArgs}
    {base state : State} {pointer first : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13204))
    (pointerValue : state.regs.get? x11 = some pointer)
    (word : DecodedValue.Word64LERep state pointer.toNat first.toNat)
    (readable : DecoderAccessRange (DecoderReadableByte margs) pointer 8)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr pointer) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x13204) stepRetired x10 first) false := by
  have targetEq : pointer + sign_extend (m := 64) 0x000#12 = pointer := by
    rw [show sign_extend (m := 64) 0x000#12 = BitVec.ofNat 64 0 by decide]
    simp
  change DecodedValue.BitVectorLERep state pointer.toNat first at word
  exact decoderLoadStepOfDecoderAgree (dest := x10) (value := first) machine agree retired code stepNo
    0x13204 0x03 0xb5 0x05 0x00 0x000#12 11#5 10#5 false 8 first atPc
    (pcIn := ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78340 ∧ 78340 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x13204) 0x000#12
      (.Regidx 11#5) first pointer pointer
      (rX_x11_run _ _ (decoderExecuteState_get? pointerValue)) targetEq pointer.toNat rfl word aligned
      readable)
    (by rw [level4_rawNewPayloadRequestDeinit_extend_value_dword]; exact wX_x10_run _ _)

/-- Sail executes `ld a1, 8(a1)` from the typed allocator pair at `0x13208`. -/
private theorem level4_rawNewPayloadRequestDeinit_load_a1_step {margs : DecoderMachineArgs}
    {base state : State} {pointer second : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13208))
    (pointerValue : state.regs.get? x11 = some pointer)
    (word : DecodedValue.Word64LERep state (pointer.toNat + 8) second.toNat)
    (fits : pointer.toNat + 8 < 2 ^ 64)
    (readable : DecoderAccessRange (DecoderReadableByte margs) (pointer + 8) 8)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (pointer + 8)) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x13208) stepRetired x11 second) false := by
  have targetEq : pointer + sign_extend (m := 64) 0x008#12 = pointer + 8 := by
    rw [show sign_extend (m := 64) 0x008#12 = BitVec.ofNat 64 8 by decide]
    simp
  have targetToNat : (pointer + 8).toNat = pointer.toNat + 8 := by
    simp only [BitVec.toNat_add]
    change (pointer.toNat + 8) % 2 ^ 64 = pointer.toNat + 8
    omega
  change DecodedValue.BitVectorLERep state (pointer.toNat + 8) second at word
  exact decoderLoadStepOfDecoderAgree (dest := x11) (value := second) machine agree retired code stepNo
    0x13208 0x83 0xb5 0x85 0x00 0x008#12 11#5 11#5 false 8 second atPc
    (pcIn := ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78344 ∧ 78344 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x13208) 0x008#12
      (.Regidx 11#5) second pointer (pointer + 8)
      (rX_x11_run _ _ (decoderExecuteState_get? pointerValue)) targetEq (pointer.toNat + 8)
      targetToNat.symm word aligned readable)
    (by rw [level4_rawNewPayloadRequestDeinit_extend_value_dword]; exact wX_x11_run _ _)

/-- Sail executes the literal `sd a0, 8(sp)` at `0x1320c`. -/
theorem level4_rawNewPayloadRequestDeinit_store_a0_step {margs : DecoderMachineArgs}
    {base state : State} {value : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo childBase : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1320c))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 childBase))
    (a0Value : state.regs.get? x10 = some value) (fits : childBase + 0x10 ≤ 2 ^ 64)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (childBase + 8 + index))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (childBase + 8))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x1320c) stepRetired (childBase + 8)
        (width := 8) value) false := by
  have targetToNat : (BitVec.ofNat 64 (childBase + 8)).toNat = childBase + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have targetEq : BitVec.ofNat 64 childBase + sign_extend (m := 64) 0x008#12 =
      BitVec.ofNat 64 (childBase + 8) := by
    rw [show sign_extend (m := 64) 0x008#12 = BitVec.ofNat 64 8 by decide,
      ← BitVec.ofNat_add]
  have allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (childBase + 8)) 8 := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [targetToNat]
      omega
    · intro index indexBound
      rw [targetToNat]
      exact Or.inl (writable index indexBound)
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x1320c 0x23 0x34 0xa1 0x00 0x008#12 10#5 2#5 (BitVec.ofNat 64 childBase) value
    (BitVec.ofNat 64 (childBase + 8)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? spValue))
    (rX_x10_run _ _ (decoderExecuteState_get? a0Value)) targetEq allowed
    ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78348 ∧ 78348 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- Sail executes the literal `sd a1, 16(sp)` at `0x13210`. -/
theorem level4_rawNewPayloadRequestDeinit_store_a1_step {margs : DecoderMachineArgs}
    {base state : State} {value : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo childBase : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13210))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 childBase))
    (a1Value : state.regs.get? x11 = some value) (fits : childBase + 0x18 ≤ 2 ^ 64)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (childBase + 16 + index))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (childBase + 16))) 8 = true) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x13210) stepRetired (childBase + 16)
        (width := 8) value) false := by
  have targetToNat : (BitVec.ofNat 64 (childBase + 16)).toNat = childBase + 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have targetEq : BitVec.ofNat 64 childBase + sign_extend (m := 64) 0x010#12 =
      BitVec.ofNat 64 (childBase + 16) := by
    rw [show sign_extend (m := 64) 0x010#12 = BitVec.ofNat 64 16 by decide,
      ← BitVec.ofNat_add]
  have allowed : DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (childBase + 16)) 8 := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [targetToNat]
      omega
    · intro index indexBound
      rw [targetToNat]
      exact Or.inl (writable index indexBound)
  obtain ⟨stepRetired, run⟩ := decoderStoreDwordStep machine agree retired code stepNo
    0x13210 0x23 0x38 0xb1 0x00 0x010#12 11#5 2#5 (BitVec.ofNat 64 childBase) value
    (BitVec.ofNat 64 (childBase + 16)) atPc
    (rX_x2_run _ _ (decoderExecuteState_get? spValue))
    (rX_x11_run _ _ (decoderExecuteState_get? a1Value)) targetEq allowed
    ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78352 ∧ 78352 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide)
    (by decoder_decode) (by unfold BaseInstructionEncoding; decide) aligned
  exact ⟨stepRetired, by simpa [afterMemoryWrite, targetToNat] using run⟩

/-- Sail executes the literal `mv a0, s1` at `0x13214`. -/
theorem level4_rawNewPayloadRequestDeinit_restore_a0_step {margs : DecoderMachineArgs}
    {base state : State} {s1 : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13214))
    (s1Value : state.regs.get? x9 = some s1) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x13214) stepRetired x10
        (iTypeResult .ADDI 0x000#12 s1)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x13214 0x13 0x85 0x04 0x00 0x000#12 9#5 10#5 .ADDI atPc
    (rX_x9_run _ _ (decoderExecuteState_get? s1Value)) (wX_x10_run _ _)
    (pcIn := ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78356 ∧ 78356 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩)

/-- Sail executes the literal `mv a1, s0` at `0x13218`. -/
theorem level4_rawNewPayloadRequestDeinit_restore_a1_step {margs : DecoderMachineArgs}
    {base state : State} {s0 : BitVec 64}
    (machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x13218))
    (s0Value : state.regs.get? x8 = some s0) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x13218) stepRetired x11
        (iTypeResult .ADDI 0x000#12 s0)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x13218 0x93 0x05 0x04 0x00 0x000#12 8#5 11#5 .ADDI atPc
    (rX_x8_run _ _ (decoderExecuteState_get? s0Value)) (wX_x11_run _ _)
    (pcIn := ⟨by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78360 ∧ 78360 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩,
      by native_decide⟩)

private theorem level4_rawNewPayloadRequestDeinit_allocator_pair_through_saves
    {before after : State} {postStack pointer first second : Nat}
    (memory : WritesOnlyWithin (level4RawNewPayloadRequestDeinitSaveMemory postStack) before after)
    (outside : ∀ address, pointer ≤ address → address < pointer + 16 →
      ¬ level4RawNewPayloadRequestDeinitSaveMemory postStack address)
    (pair : DecodedValue.Word64LERep before pointer first ∧
      DecodedValue.Word64LERep before (pointer + 8) second) :
    DecodedValue.Word64LERep after pointer first ∧
      DecodedValue.Word64LERep after (pointer + 8) second := by
  have relocation : DecodedValue.ByteWindowRelocation before after pointer pointer 16 := by
    intro index bound
    exact memory (pointer + index) (outside _ (by omega) (by omega))
  refine ⟨pair.1.rebase (DecodedValue.ByteWindowRelocation.atOffset relocation 0 8 (by omega)), ?_⟩
  exact pair.2.rebase (DecodedValue.ByteWindowRelocation.atOffset relocation 8 8 (by omega))

private theorem level4_rawNewPayloadRequestDeinit_allocator_first_readable
    {margs : DecoderMachineArgs} {pointer : BitVec 64}
    (readable : DecoderAccessRange (DecoderReadableByte margs) pointer 16) :
    DecoderAccessRange (DecoderReadableByte margs) pointer 8 := by
  refine ⟨by decide, ?_, ?_⟩
  · exact Nat.le_trans (by omega) readable.2.1
  · intro index bound
    exact readable.2.2 index (by omega)

private theorem level4_rawNewPayloadRequestDeinit_allocator_second_readable
    {margs : DecoderMachineArgs} {pointer : BitVec 64}
    (readable : DecoderAccessRange (DecoderReadableByte margs) pointer 16)
    (fits : pointer.toNat + 16 ≤ 2 ^ 64) :
    DecoderAccessRange (DecoderReadableByte margs) (pointer + 8) 8 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [BitVec.toNat_add]
    change (pointer.toNat + 8) % 2 ^ 64 + 8 ≤ 2 ^ 64
    have : pointer.toNat + 8 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  · intro index bound
    rw [BitVec.toNat_add]
    change DecoderReadableByte margs ((pointer.toNat + 8) % 2 ^ 64 + index)
    have : pointer.toNat + 8 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]
    simpa [Nat.add_assoc] using readable.2.2 (8 + index) (by omega)

/-- Handoff after the two argument moves, with the saved child frame and both live arguments still
available to the remaining deinit corridor. -/
structure Level4RawNewPayloadRequestDeinitArgumentMovesHandoff
    {margs : DecoderMachineArgs} {origin before : State}
    (frame : Level4DecodeRawParentFrame margs origin before)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) (after : State) : Prop where
  trace : Trace fromStep 6 before after
  confined : ConfinedPrefix Level4RawNewPayloadRequestDeinitPcs
    Level4RawNewPayloadRequestDeinitExit Level4RawNewPayloadRequestDeinitChildSummary fromStep 6
    before after
  writes : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites before after
  memory : WritesOnlyWithin (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
    before after
  seg : Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
    Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
    (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
    [⟨x9, Classical.choose pre.a0⟩, ⟨x8, Classical.choose pre.a1⟩,
      ⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x1, BitVec.ofNat 64 0x129ec⟩,
      ⟨x10, Classical.choose pre.a0⟩, ⟨x11, Classical.choose pre.a1⟩]
    fromStep 6 before after (BitVec.ofNat 64 0x13204)
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x13204)
  childSp : after.regs.get? x2 = some (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50))
  ra : after.regs.get? x1 = some (BitVec.ofNat 64 0x129ec)
  s0 : after.regs.get? x8 = some (Classical.choose pre.a1)
  s1 : after.regs.get? x9 = some (Classical.choose pre.a0)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs after
  retired : RetiredCounterPresent after

/-- Append `mv s0, a1; mv s1, a0` to the four-save segment.  Each destination overwrites its
saved pre-move value, so `Seg.forget` removes that stale binding before the next `Seg.stepWitness`. -/
theorem level4_rawNewPayloadRequestDeinit_argument_moves_handoff
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ after, Level4RawNewPayloadRequestDeinitArgumentMovesHandoff frame pre fromStep after := by
  obtain ⟨initial, handoff⟩ := level4_rawNewPayloadRequestDeinit_initial_saves_handoff frame pre fromStep
  have zeroAdd (value : BitVec 64) : iTypeResult .ADDI 0x000#12 value = value := by
    unfold iTypeResult
    rw [show sign_extend 0x000#12 = (0x0000000000000000#64) by decide]
    simp
  let seg0 := handoff.seg.forget
    (kv' := [⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x9, BitVec.ofNat 64 2⟩,
      ⟨x1, BitVec.ofNat 64 0x129ec⟩, ⟨x10, Classical.choose pre.a0⟩,
      ⟨x11, Classical.choose pre.a1⟩]) (by simp)
  obtain ⟨retired5, afterS0, hS0, seg1⟩ := seg0.stepWitness
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78332 ∧ 78332 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp) x8 (Classical.choose pre.a1) (BitVec.ofNat 64 0x13200)
    (by
      simpa only [zeroAdd] using
        (level4_rawNewPayloadRequestDeinit_move_s0_step handoff.machine (Agree.refl initial)
          seg0.retired handoff.code (fromStep + 4) seg0.atPc handoff.a1))
    (by decide) (fun r h => Or.inl h) (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterS0.mem := by
    rw [hS0, afterRegisterWrite_mem]
    exact handoff.code
  have writes1 : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites initial afterS0 := by
    rw [hS0]
    exact (afterRegisterWrite_writes initial (BitVec.ofNat 64 0x131fc) retired5 x8
      (Classical.choose pre.a1)).mono (fun r h => h.elim Or.inl (fun h => h ▸ Or.inr (Or.inr (Or.inl rfl))))
  have machine1 : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs afterS0 := by
    rw [hS0] at writes1 ⊢
    exact handoff.machine.mono
      (writes1.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
      (afterRegisterWrite_retired_present initial (BitVec.ofNat 64 0x131fc) retired5 x8 (Classical.choose pre.a1))
  have a0AfterS0 : afterS0.regs.get? x10 = some (Classical.choose pre.a0) := by
    rw [hS0]
    exact (afterRegisterWrite_writes initial (BitVec.ofNat 64 0x131fc) retired5 x8
      (Classical.choose pre.a1)) x10 (by decide) |>.trans handoff.a0
  let seg1 := seg1.forget
    (kv' := [⟨x8, Classical.choose pre.a1⟩,
      ⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x1, BitVec.ofNat 64 0x129ec⟩,
      ⟨x10, Classical.choose pre.a0⟩, ⟨x11, Classical.choose pre.a1⟩])
    (by simp)
  obtain ⟨retired6, after, hS1, seg2⟩ := seg1.stepWitness
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78336 ∧ 78336 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp) x9 (Classical.choose pre.a0) (BitVec.ofNat 64 0x13204)
    (by
      simpa only [zeroAdd] using
        (level4_rawNewPayloadRequestDeinit_move_s1_step machine1 (Agree.refl afterS0)
          seg1.retired code1 (fromStep + 5) seg1.atPc
          a0AfterS0))
    (by decide) (fun r h => Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hS1, afterRegisterWrite_mem]
    exact code1
  refine ⟨after, ⟨seg2.trace, seg2.confined, seg2.writes, seg2.mem, seg2, seg2.atPc,
    seg2.reg x2 (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)) (by simp),
    seg2.reg x1 (BitVec.ofNat 64 0x129ec) (by simp),
    seg2.reg x8 (Classical.choose pre.a1) (by simp),
    seg2.reg x9 (Classical.choose pre.a0) (by simp), code2, ?_, seg2.retired⟩⟩
  have writes2 : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites afterS0 after := by
    rw [hS1]
    exact (afterRegisterWrite_writes afterS0 (BitVec.ofNat 64 0x13200) retired6 x9
      (Classical.choose pre.a0)).mono (fun r h => h.elim Or.inl (fun h => h ▸ Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rw [hS1] at writes2 ⊢
  exact machine1.mono
    (writes2.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
    (afterRegisterWrite_retired_present afterS0 (BitVec.ofNat 64 0x13200) retired6 x9 (Classical.choose pre.a0))

/-- Handoff after loading both allocator words into the call argument registers. -/
structure Level4RawNewPayloadRequestDeinitAllocatorLoadsHandoff
    {margs : DecoderMachineArgs} {origin before : State}
    (frame : Level4DecodeRawParentFrame margs origin before)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) (after : State) : Prop where
  trace : Trace fromStep 8 before after
  confined : ConfinedPrefix Level4RawNewPayloadRequestDeinitPcs
    Level4RawNewPayloadRequestDeinitExit Level4RawNewPayloadRequestDeinitChildSummary fromStep 8
    before after
  writes : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites before after
  memory : WritesOnlyWithin (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
    before after
  seg : ∃ first second,
    Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
      Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
      (level4RawNewPayloadRequestDeinitSaveMemory (frame.stack - 0x690))
      [⟨x11, BitVec.ofNat 64 second⟩, ⟨x10, BitVec.ofNat 64 first⟩,
        ⟨x9, Classical.choose pre.a0⟩, ⟨x8, Classical.choose pre.a1⟩,
        ⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩,
        ⟨x1, BitVec.ofNat 64 0x129ec⟩]
      fromStep 8 before after (BitVec.ofNat 64 0x1320c)
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x1320c)
  childSp : after.regs.get? x2 = some (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50))
  ra : after.regs.get? x1 = some (BitVec.ofNat 64 0x129ec)
  s0 : after.regs.get? x8 = some (Classical.choose pre.a1)
  s1 : after.regs.get? x9 = some (Classical.choose pre.a0)
  a0 : ∃ first, after.regs.get? x10 = some (BitVec.ofNat 64 first)
  a1 : ∃ second, after.regs.get? x11 = some (BitVec.ofNat 64 second)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs after
  retired : RetiredCounterPresent after

/-- Append the two allocator-pair loads.  The typed nonalias clause transports both words through
the preceding child saves; each load then forgets the overwritten argument binding. -/
theorem level4_rawNewPayloadRequestDeinit_allocator_loads_handoff
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ after, Level4RawNewPayloadRequestDeinitAllocatorLoadsHandoff frame pre fromStep after := by
  obtain ⟨beforeLoads, handoff⟩ := level4_rawNewPayloadRequestDeinit_argument_moves_handoff frame pre fromStep
  obtain ⟨first, second, firstWord, secondWord, firstFits, secondFits, pairFits⟩ := pre.allocatorPair
  have pairAfter := level4_rawNewPayloadRequestDeinit_allocator_pair_through_saves handoff.memory
    pre.allocatorOutsideSave ⟨firstWord, secondWord⟩
  have firstReadable : DecoderAccessRange (DecoderReadableByte margs) (Classical.choose pre.a1) 8 := by
    simpa only [BitVec.ofNat_toNat] using
      level4_rawNewPayloadRequestDeinit_allocator_first_readable pre.allocatorReadable
  let seg0 := handoff.seg.forget
    (kv' := [⟨x9, Classical.choose pre.a0⟩, ⟨x8, Classical.choose pre.a1⟩,
      ⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩, ⟨x1, BitVec.ofNat 64 0x129ec⟩,
      ⟨x11, Classical.choose pre.a1⟩]) (by simp)
  obtain ⟨retired7, afterA0, hA0, seg1⟩ := seg0.stepWitness
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78340 ∧ 78340 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp) x10 (BitVec.ofNat 64 first) (BitVec.ofNat 64 0x13208)
    (by
      apply level4_rawNewPayloadRequestDeinit_load_a0_step handoff.machine (Agree.refl beforeLoads)
        seg0.retired handoff.code (fromStep + 6) seg0.atPc
        (seg0.reg x11 (Classical.choose pre.a1) (by simp))
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstFits]
      exact pairAfter.1
      exact firstReadable
      simpa only [BitVec.ofNat_toNat] using pre.allocatorAligned)
    (by decide) (fun r h => Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (by decide) (by decide) (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterA0.mem := by
    rw [hA0, afterRegisterWrite_mem]
    exact handoff.code
  have writes1 : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites beforeLoads afterA0 := by
    rw [hA0]
    exact (afterRegisterWrite_writes beforeLoads (BitVec.ofNat 64 0x13204) retired7 x10
      (BitVec.ofNat 64 first)).mono (fun r h => h.elim Or.inl
        (fun h => h ▸ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have machine1 : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs afterA0 := by
    rw [hA0] at writes1 ⊢
    exact handoff.machine.mono
      (writes1.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
      (afterRegisterWrite_retired_present beforeLoads (BitVec.ofNat 64 0x13204) retired7 x10
        (BitVec.ofNat 64 first))
  have secondAfterA0 : DecodedValue.Word64LERep afterA0 ((Classical.choose pre.a1).toNat + 8) second :=
    pairAfter.2.rebase (by
      intro index bound
      rw [hA0, afterRegisterWrite_mem])
  have secondReadable : DecoderAccessRange (DecoderReadableByte margs)
      (Classical.choose pre.a1 + 8) 8 := by
    simpa only [BitVec.ofNat_toNat] using
      level4_rawNewPayloadRequestDeinit_allocator_second_readable pre.allocatorReadable
        (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact pairFits)
  have a1AfterA0 : afterA0.regs.get? x11 = some (Classical.choose pre.a1) :=
    seg1.reg x11 (Classical.choose pre.a1) (by simp)
  let seg1 := seg1.forget
    (kv' := [⟨x10, BitVec.ofNat 64 first⟩, ⟨x9, Classical.choose pre.a0⟩,
      ⟨x8, Classical.choose pre.a1⟩, ⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩,
      ⟨x1, BitVec.ofNat 64 0x129ec⟩]) (by simp)
  obtain ⟨retired8, after, hA1, seg2⟩ := seg1.stepWitness
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78344 ∧ 78344 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp) x11 (BitVec.ofNat 64 second) (BitVec.ofNat 64 0x1320c)
    (by
      apply level4_rawNewPayloadRequestDeinit_load_a1_step machine1 (Agree.refl afterA0)
        seg1.retired code1 (fromStep + 7) seg1.atPc
      exact a1AfterA0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt secondFits]
      exact secondAfterA0
      have : (Classical.choose pre.a1).toNat + 8 < 2 ^ 64 := by omega
      exact this
      exact secondReadable
      simpa only [BitVec.ofNat_toNat] using pre.allocatorSecondAligned)
    (by decide) (fun r h => Or.inl h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    (by decide) (by decide) (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hA1, afterRegisterWrite_mem]
    exact code1
  refine ⟨after, ⟨seg2.trace, seg2.confined, seg2.writes, seg2.mem, ⟨first, second, seg2⟩, seg2.atPc,
    seg2.reg x2 _ (by simp), seg2.reg x1 _ (by simp), seg2.reg x8 _ (by simp),
    seg2.reg x9 _ (by simp), ⟨first, seg2.reg x10 _ (by simp)⟩,
    ⟨second, seg2.reg x11 _ (by simp)⟩, code2, ?_, seg2.retired⟩⟩
  have writes2 : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites afterA0 after := by
    rw [hA1]
    exact (afterRegisterWrite_writes afterA0 (BitVec.ofNat 64 0x13208) retired8 x11
      (BitVec.ofNat 64 second)).mono (fun r h => h.elim Or.inl
        (fun h => h ▸ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  rw [hA1] at writes2 ⊢
  exact machine1.mono
    (writes2.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
    (afterRegisterWrite_retired_present afterA0 (BitVec.ofNat 64 0x13208) retired8 x11
      (BitVec.ofNat 64 second))

/-- The first loaded allocator word is stored in the child call frame at `sp+8`. -/
structure Level4RawNewPayloadRequestDeinitFirstArgumentStoreHandoff
    {margs : DecoderMachineArgs} {origin before : State}
    (frame : Level4DecodeRawParentFrame margs origin before)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) (after : State) : Prop where
  seg : ∃ first second,
    Seg Level4RawNewPayloadRequestDeinitPcs Level4RawNewPayloadRequestDeinitExit
      Level4RawNewPayloadRequestDeinitChildSummary level4RawNewPayloadRequestDeinitWrites
      (level4RawNewPayloadRequestDeinitCallMemory (frame.stack - 0x690))
      [⟨x11, BitVec.ofNat 64 second⟩, ⟨x10, BitVec.ofNat 64 first⟩,
        ⟨x9, Classical.choose pre.a0⟩, ⟨x8, Classical.choose pre.a1⟩,
        ⟨x2, BitVec.ofNat 64 (frame.stack - 0x690 - 0x50)⟩,
        ⟨x1, BitVec.ofNat 64 0x129ec⟩]
      fromStep 9 before after (BitVec.ofNat 64 0x13210)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre Level4RawNewPayloadRequestDeinitPcs margs after

/-- Append the exact `sd a0,8(sp)` to the allocator-load handoff. -/
theorem level4_rawNewPayloadRequestDeinit_first_argument_store_handoff
    {margs : DecoderMachineArgs} {origin current : State}
    (frame : Level4DecodeRawParentFrame margs origin current)
    (pre : Level4RawNewPayloadRequestDeinitPre frame) (fromStep : Nat) :
    ∃ after, Level4RawNewPayloadRequestDeinitFirstArgumentStoreHandoff frame pre fromStep after := by
  obtain ⟨beforeStore, handoff⟩ :=
    level4_rawNewPayloadRequestDeinit_allocator_loads_handoff frame pre fromStep
  obtain ⟨first, second, narrow⟩ := handoff.seg
  let seg0 := level4_rawNewPayloadRequestDeinit_widen_seg_memory
    (wider := level4RawNewPayloadRequestDeinitCallMemory (frame.stack - 0x690))
    (fun address member => Or.inl member) narrow
  rcases pre.preservation with ⟨entry, stackEq, -, -, -, -, -, -, -, -, -, -, -, -⟩
  have childBase : frame.stack - 0x690 - 0x50 = entry.postStack - 0x50 := by
    rw [← stackEq, entry.postStackEq]
    omega
  have fits : frame.stack - 0x690 - 0x50 + 0x10 ≤ 2 ^ 64 := by
    rw [childBase]
    exact level4_rawNewPayloadRequestDeinit_slot_fits entry (offset := 8) (by omega)
  have writable : ∀ index, index < 8 → canonicalContractParams.env.stack
      (frame.stack - 0x690 - 0x50 + 8 + index) := by
    intro index bound
    rw [childBase]
    exact level4_rawNewPayloadRequestDeinit_slot_writable entry (offset := 8) (by omega) bound
  have aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (BitVec.ofNat 64 (frame.stack - 0x690 - 0x50 + 8))) 8 = true := by
    rw [childBase]
    exact level4_rawNewPayloadRequestDeinit_slot_aligned entry (offset := 8) (by omega) (by decide)
  obtain ⟨retired9, after, hStore, seg1⟩ := seg0.stepStoreWitness
    (frame.stack - 0x690 - 0x50 + 8) (BitVec.ofNat 64 first) (BitVec.ofNat 64 0x13210)
    (by
      change ∃ range : BinaryFv.Binary.AddressRange,
        range ∈ excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit.regions ∧
          range.start ≤ 78348 ∧ 78348 < range.stop
      exact ⟨{ start := 78316, size := 180 }, by native_decide, by decide, by decide⟩)
    (by simp)
    (level4_rawNewPayloadRequestDeinit_store_a0_step handoff.machine (Agree.refl beforeStore)
      seg0.retired handoff.code (fromStep + 8) (frame.stack - 0x690 - 0x50) seg0.atPc
      (seg0.reg x2 _ (by simp)) (seg0.reg x10 _ (by simp)) fits writable aligned)
    (by decide)
    (by
      intro address lower upper
      exact Or.inr ⟨by omega, by omega⟩)
    (fun r h => Or.inl h) (by exact of_decide_eq_true rfl)
  have codeAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hStore]
    have written := fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement beforeStore)
        (BitVec.ofNat 64 0x1320c))
      (frame.stack - 0x690 - 0x50 + 8) (BitVec.ofNat 64 first)
      (fun index => canonicalStack_not_fileByte (writable index index.isLt))
      (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using handoff.code)
    simpa [afterMemoryWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using written
  refine ⟨after, ⟨first, second, seg1⟩, codeAfter, ?_⟩
  have stepWrites : WritesOnlyRegs level4RawNewPayloadRequestDeinitWrites beforeStore after := by
    rw [hStore]
    exact (storeRetirement_writes beforeStore (BitVec.ofNat 64 0x1320c)
      (BitVec.ofNat 64 0x13210) retired9 (frame.stack - 0x690 - 0x50 + 8)
      (BitVec.ofNat 64 first)).mono (fun r h => Or.inl h)
  exact handoff.machine.mono
    (stepWrites.agree decoderPreserved_level4RawNewPayloadRequestDeinitWrites_disjoint)
    seg1.retired

end BinaryFv.Zesu.MachineExecution
