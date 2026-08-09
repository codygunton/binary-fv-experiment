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
  preservation : frame.PreservedTo current

/-- Exact union of the three eight-byte child-save slots. -/
def level4RawNewPayloadRequestDeinitSaveMemory (postStack : Nat) : Region := fun address =>
  (postStack - 0x50 + 0x48 ≤ address ∧ address < postStack - 0x50 + 0x50) ∨
  (postStack - 0x50 + 0x40 ≤ address ∧ address < postStack - 0x50 + 0x48) ∨
  (postStack - 0x50 + 0x38 ≤ address ∧ address < postStack - 0x50 + 0x40)

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

end BinaryFv.Zesu.MachineExecution
