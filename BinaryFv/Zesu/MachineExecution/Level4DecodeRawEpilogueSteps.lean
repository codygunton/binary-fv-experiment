import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.DecoderBitVectorLoad
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineContract
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Saved frame for the emitted `decodeRaw` epilogue -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The words loaded by `zesu_decode_raw` from `0x104f8` through `0x10528` after its
`addi sp, sp, 0x690` at `0x104f4`. -/
def Level4DecodeRawSavedFrame (state : State) (stack : Nat)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64) : Prop :=
  SavedWordBytes state (stack + 0x7e8) ra ∧
    SavedWordBytes state (stack + 0x7e0) s0 ∧
      SavedWordBytes state (stack + 0x7d8) s1 ∧
        SavedWordBytes state (stack + 0x7d0) s2 ∧
          SavedWordBytes state (stack + 0x7c8) s3 ∧
            SavedWordBytes state (stack + 0x7c0) s4 ∧
              SavedWordBytes state (stack + 0x7b8) s5 ∧
                SavedWordBytes state (stack + 0x7b0) s6 ∧
                  SavedWordBytes state (stack + 0x7a8) s7 ∧
                    SavedWordBytes state (stack + 0x7a0) s8 ∧
                      SavedWordBytes state (stack + 0x798) s9 ∧
                        SavedWordBytes state (stack + 0x790) s10 ∧
                          SavedWordBytes state (stack + 0x788) s11

/-- The 16 direct `decodeRaw` instructions which restore the saved frame and return. -/
def level4DecodeRawEpiloguePcs : List Nat :=
  [ 0x104f4, 0x104f8, 0x104fc, 0x10500, 0x10504, 0x10508, 0x1050c, 0x10510
  , 0x10514, 0x10518, 0x1051c, 0x10520, 0x10524, 0x10528, 0x1052c, 0x10530 ]

/-- The exact parent-owned instruction scope for the raw decoder's restore and return sequence.
Unlike a generated function exit predicate, this scope intentionally permits the final `ret` to
retire: the phase result, not a child contract, records its return target. -/
abbrev Level4DecodeRawEpiloguePcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4DecodeRawEpiloguePcs

/-- This literal list has no unreviewed PCs. -/
theorem level4DecodeRawEpiloguePcs_exact :
    level4DecodeRawEpiloguePcs =
      [ 0x104f4, 0x104f8, 0x104fc, 0x10500, 0x10504, 0x10508, 0x1050c, 0x10510
      , 0x10514, 0x10518, 0x1051c, 0x10520, 0x10524, 0x10528, 0x1052c, 0x10530 ] := rfl

theorem level4DecodeRawEpiloguePcs_count : level4DecodeRawEpiloguePcs.length = 16 := rfl

/-- The exact 16-PC epilogue is a subset of the generated 172-PC direct-parent partition. -/
theorem level4DecodeRawEpiloguePcs_subset_direct :
    level4DecodeRawEpiloguePcs.all decodeRawDirectPcs.contains = true := by native_decide

/-- The epilogue is owned by the generated rejection/cleanup/status/copy phase. -/
theorem level4DecodeRawEpiloguePcs_subset_rejectionCleanupStatusCopyEpilogue :
    level4DecodeRawEpiloguePcs.all
      decodeRawRejectionCleanupStatusCopyEpiloguePcs.contains = true := by native_decide

abbrev Level4DecodeRawEpilogueExit : BitVec 64 → Prop := fun _ => False

abbrev Level4DecodeRawEpilogueChildSummary : FunctionInstanceId → Nat → Nat → State → State → Prop :=
  fun _ _ _ _ _ => False

local macro "level4_epilogue_pc" : tactic =>
  `(tactic| native_decide)

local macro "owned_pc" : tactic =>
  `(tactic| level4_epilogue_pc)

set_option genInjectivity false in
/-- Concrete input to the raw epilogue. Parent routes, rather than `hLevel4`, establish its
machine/code frame, stack restoration, and every byte of the 13-word save area. -/
structure Level4DecodeRawEpiloguePre (margs : DecoderMachineArgs) (base state : State) where
  machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base
  agree : Agree decoderPreserved base state
  retired : RetiredCounterPresent state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104f4)
  stackBase : Nat
  stackBefore : BitVec 64
  stackValue : state.regs.get? x2 = some stackBefore
  stackRestore : stackBefore + sign_extend (m := 64) 0x690#12 = BitVec.ofNat 64 stackBase
  stackFits : stackBase + 0x7f0 < 2 ^ 64
  saveAreaReadable : DecoderAccessRange (DecoderReadableByte margs)
    (BitVec.ofNat 64 (stackBase + 0x788)) 104
  slotAligned : ∀ offset, 0x788 ≤ offset → offset ≤ 0x7e8 → offset % 8 = 0 →
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (stackBase + offset))) 8 = true
  ra : BitVec 64
  s0 : BitVec 64
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  s6 : BitVec 64
  s7 : BitVec 64
  s8 : BitVec 64
  s9 : BitVec 64
  s10 : BitVec 64
  s11 : BitVec 64
  saved : Level4DecodeRawSavedFrame state stackBase ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
  returnTarget : Sail.BitVec.update ra 0 0#1 = ra
  returnBit1 : Sail.BitVec.access ra 1 = 0#1

set_option genInjectivity false in
/-- The concrete state handed from the rejection/cleanup/status/copy route to the final 16 direct
`decodeRaw` instructions.  The preceding phase theorem must construct this object; it is not a
Level 4 contract assumption. -/
structure Level4RejectionCleanupStatusEpilogueHandoff
    (margs : DecoderMachineArgs) (base state : State) where
  phase : DecodeRawCfgPhaseInterface
  phaseIsRejectionCleanupStatusCopyEpilogue :
    phase = decodeRawCfgPhaseInterface .rejectionCleanupStatusCopyEpilogue
  machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base
  agree : Agree decoderPreserved base state
  retired : RetiredCounterPresent state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104f4)
  stackBase : Nat
  stackBefore : BitVec 64
  stackValue : state.regs.get? x2 = some stackBefore
  stackRestore : stackBefore + sign_extend (m := 64) 0x690#12 = BitVec.ofNat 64 stackBase
  stackFits : stackBase + 0x7f0 < 2 ^ 64
  saveAreaReadable : DecoderAccessRange (DecoderReadableByte margs)
    (BitVec.ofNat 64 (stackBase + 0x788)) 104
  slotAligned : ∀ offset, 0x788 ≤ offset → offset ≤ 0x7e8 → offset % 8 = 0 →
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (stackBase + offset))) 8 = true
  ra : BitVec 64
  s0 : BitVec 64
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  s6 : BitVec 64
  s7 : BitVec 64
  s8 : BitVec 64
  s9 : BitVec 64
  s10 : BitVec 64
  s11 : BitVec 64
  saved : Level4DecodeRawSavedFrame state stackBase ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
  returnTarget : Sail.BitVec.update ra 0 0#1 = ra
  returnBit1 : Sail.BitVec.access ra 1 = 0#1

/-- The typed handoff supplies exactly the parent-owned precondition of the 16-step epilogue. -/
def level4DecodeRawEpiloguePre_of_rejectionCleanupStatusHandoff
    (handoff : Level4RejectionCleanupStatusEpilogueHandoff margs base state) :
    Level4DecodeRawEpiloguePre margs base state :=
  ⟨handoff.machine, handoff.agree, handoff.retired, handoff.code, handoff.atPc,
    handoff.stackBase, handoff.stackBefore, handoff.stackValue, handoff.stackRestore,
    handoff.stackFits, handoff.saveAreaReadable, handoff.slotAligned, handoff.ra, handoff.s0,
    handoff.s1, handoff.s2, handoff.s3, handoff.s4, handoff.s5, handoff.s6, handoff.s7,
    handoff.s8, handoff.s9, handoff.s10, handoff.s11, handoff.saved, handoff.returnTarget,
    handoff.returnBit1⟩

private theorem level4_extend_value_dword (v : BitVec (8 * 8)) : extend_value false v = v := by
  unfold extend_value
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

local macro "level4_gen_wx_run" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(private theorem $name (state : State) (value : BitVec 64) :
      Runs (wX_bits (.Regidx (BitVec.ofNat 5 $idx)) value) state
        { state with regs := state.regs.insert $reg value } () := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [wX_bits, wX, PreSail.writeReg, index, EStateM.run, EStateM.bind, EStateM.modifyGet,
      EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
      xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
      encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
      LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg])

level4_gen_wx_run 20 ↦ x20, level4_wX_x20_run
level4_gen_wx_run 23 ↦ x23, level4_wX_x23_run
level4_gen_wx_run 24 ↦ x24, level4_wX_x24_run
level4_gen_wx_run 25 ↦ x25, level4_wX_x25_run
level4_gen_wx_run 26 ↦ x26, level4_wX_x26_run
level4_gen_wx_run 27 ↦ x27, level4_wX_x27_run

private theorem level4_stack_base_lt (pre : Level4DecodeRawEpiloguePre margs base state) :
    pre.stackBase < 2 ^ 64 := by
  have h := pre.stackFits
  omega

private theorem level4_slot_address_toNat (pre : Level4DecodeRawEpiloguePre margs base state)
    {offset : Nat} (offsetBound : offset + 8 ≤ 0x7f0) :
    (BitVec.ofNat 64 (pre.stackBase + offset)).toNat = pre.stackBase + offset := by
  have h := pre.stackFits
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

private theorem level4_slot_access (pre : Level4DecodeRawEpiloguePre margs base state)
    {offset : Nat} (lower : 0x788 ≤ offset) (upper : offset + 8 ≤ 0x7f0) :
    DecoderAccessRange (DecoderReadableByte margs)
      (BitVec.ofNat 64 (pre.stackBase + offset)) 8 := by
  rcases pre.saveAreaReadable with ⟨nonempty, noWrap, readable⟩
  have fits := pre.stackFits
  have baseLt := level4_stack_base_lt pre
  have lowerLt : pre.stackBase + 0x788 < 2 ^ 64 := by omega
  have upperLt : pre.stackBase + offset < 2 ^ 64 := by omega
  refine ⟨by decide, ?_, ?_⟩
  · rw [level4_slot_address_toNat pre (by omega)]
    omega
  · intro index indexBound
    have h := readable (offset - 0x788 + index) (by omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lowerLt] at h
    rw [level4_slot_address_toNat pre (by omega)]
    simpa [Nat.add_sub_of_le lower, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

private theorem level4_slot_address_eq (stackBase offset : Nat)
    (extend : sign_extend (m := 64) (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset) :
    BitVec.ofNat 64 stackBase + sign_extend (m := 64) (BitVec.ofNat 12 offset) =
      BitVec.ofNat 64 (stackBase + offset) := by
  rw [extend, ← BitVec.ofNat_add]

private theorem level4_decode_raw_epilogue_stack_step
    (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat) :
    ∃ retired, Runs (try_step fromStep false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104f4) retired x2
        (BitVec.ofNat 64 pre.stackBase)) false := by
  obtain ⟨retired, run⟩ := decoderITypeStepOfDecoderAgree pre.machine pre.agree pre.retired pre.code
    fromStep 0x104f4 0x13 0x01 0x01 0x69 0x690#12 2#5 2#5 .ADDI pre.atPc
    (rX_x2_run _ pre.stackBefore (decoderExecuteState_get? pre.stackValue))
    (wX_x2_run _ (pre.stackBefore + sign_extend (m := 64) 0x690#12))
    (pcIn := ⟨by native_decide, by native_decide⟩)
  rw [pre.stackRestore] at run
  exact ⟨retired, run⟩

theorem Level4DecodeRawSavedFrame.of_mem_eq {before after : State} {stack : Nat}
    {ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64}
    (saved : Level4DecodeRawSavedFrame before stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    (memory : after.mem = before.mem) :
    Level4DecodeRawSavedFrame after stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 := by
  rw [Level4DecodeRawSavedFrame] at saved ⊢
  simp only [SavedWordBytes] at saved ⊢
  rw [memory]
  exact saved

private theorem level4_epilogue_load_ra {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104f8))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7e8) pre.ra) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104f8) retired x1 pre.ra) false :=
  decoderLoadStepOfDecoderAgree (dest := x1) (value := pre.ra) machine agree retired code stepNo
    0x104f8 0x83 0x30 0x81 0x7e 0x7e8#12 2#5 1#5 false 8 pre.ra atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x104f8) 0x7e8#12
      (.Regidx 2#5) pre.ra
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7e8))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7e8 (by decide)) (pre.stackBase + 0x7e8)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7e8 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x1_run _ pre.ra)

private theorem level4_epilogue_load_s0 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104fc))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7e0) pre.s0) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104fc) retired x8 pre.s0) false :=
  decoderLoadStepOfDecoderAgree (dest := x8) (value := pre.s0) machine agree retired code stepNo
    0x104fc 0x03 0x34 0x01 0x7e 0x7e0#12 2#5 8#5 false 8 pre.s0 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x104fc) 0x7e0#12
      (.Regidx 2#5) pre.s0
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7e0))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7e0 (by decide)) (pre.stackBase + 0x7e0)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7e0 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x8_run _ pre.s0)

private theorem level4_epilogue_load_s1 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10500))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7d8) pre.s1) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10500) retired x9 pre.s1) false :=
  decoderLoadStepOfDecoderAgree (dest := x9) (value := pre.s1) machine agree retired code stepNo
    0x10500 0x83 0x34 0x81 0x7d 0x7d8#12 2#5 9#5 false 8 pre.s1 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10500) 0x7d8#12
      (.Regidx 2#5) pre.s1
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7d8))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7d8 (by decide)) (pre.stackBase + 0x7d8)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7d8 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x9_run _ pre.s1)

private theorem level4_epilogue_load_s2 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10504))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7d0) pre.s2) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10504) retired x18 pre.s2) false :=
  decoderLoadStepOfDecoderAgree (dest := x18) (value := pre.s2) machine agree retired code stepNo
    0x10504 0x03 0x39 0x01 0x7d 0x7d0#12 2#5 18#5 false 8 pre.s2 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10504) 0x7d0#12
      (.Regidx 2#5) pre.s2
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7d0))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7d0 (by decide)) (pre.stackBase + 0x7d0)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7d0 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x18_run _ pre.s2)

private theorem level4_epilogue_load_s3 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10508))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7c8) pre.s3) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10508) retired x19 pre.s3) false :=
  decoderLoadStepOfDecoderAgree (dest := x19) (value := pre.s3) machine agree retired code stepNo
    0x10508 0x83 0x39 0x81 0x7c 0x7c8#12 2#5 19#5 false 8 pre.s3 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10508) 0x7c8#12
      (.Regidx 2#5) pre.s3
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7c8))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7c8 (by decide)) (pre.stackBase + 0x7c8)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7c8 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x19_run _ pre.s3)

private theorem level4_epilogue_load_s4 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1050c))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7c0) pre.s4) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1050c) retired x20 pre.s4) false :=
  decoderLoadStepOfDecoderAgree (dest := x20) (value := pre.s4) machine agree retired code stepNo
    0x1050c 0x03 0x3a 0x01 0x7c 0x7c0#12 2#5 20#5 false 8 pre.s4 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x1050c) 0x7c0#12
      (.Regidx 2#5) pre.s4
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7c0))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7c0 (by decide)) (pre.stackBase + 0x7c0)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7c0 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact level4_wX_x20_run _ pre.s4)

private theorem level4_epilogue_load_s5 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10510))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7b8) pre.s5) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10510) retired x21 pre.s5) false :=
  decoderLoadStepOfDecoderAgree (dest := x21) (value := pre.s5) machine agree retired code stepNo
    0x10510 0x83 0x3a 0x81 0x7b 0x7b8#12 2#5 21#5 false 8 pre.s5 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10510) 0x7b8#12
      (.Regidx 2#5) pre.s5
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7b8))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7b8 (by decide)) (pre.stackBase + 0x7b8)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7b8 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x21_run _ pre.s5)

private theorem level4_epilogue_load_s6 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10514))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7b0) pre.s6) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10514) retired x22 pre.s6) false :=
  decoderLoadStepOfDecoderAgree (dest := x22) (value := pre.s6) machine agree retired code stepNo
    0x10514 0x03 0x3b 0x01 0x7b 0x7b0#12 2#5 22#5 false 8 pre.s6 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10514) 0x7b0#12
      (.Regidx 2#5) pre.s6
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7b0))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7b0 (by decide)) (pre.stackBase + 0x7b0)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7b0 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact wX_x22_run _ pre.s6)

private theorem level4_epilogue_load_s7 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10518))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7a8) pre.s7) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10518) retired x23 pre.s7) false :=
  decoderLoadStepOfDecoderAgree (dest := x23) (value := pre.s7) machine agree retired code stepNo
    0x10518 0x83 0x3b 0x81 0x7a 0x7a8#12 2#5 23#5 false 8 pre.s7 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10518) 0x7a8#12
      (.Regidx 2#5) pre.s7
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7a8))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7a8 (by decide)) (pre.stackBase + 0x7a8)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7a8 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact level4_wX_x23_run _ pre.s7)

private theorem level4_epilogue_load_s8 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1051c))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x7a0) pre.s8) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1051c) retired x24 pre.s8) false :=
  decoderLoadStepOfDecoderAgree (dest := x24) (value := pre.s8) machine agree retired code stepNo
    0x1051c 0x03 0x3c 0x01 0x7a 0x7a0#12 2#5 24#5 false 8 pre.s8 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x1051c) 0x7a0#12
      (.Regidx 2#5) pre.s8
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x7a0))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x7a0 (by decide)) (pre.stackBase + 0x7a0)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x7a0 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact level4_wX_x24_run _ pre.s8)

private theorem level4_epilogue_load_s9 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10520))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x798) pre.s9) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10520) retired x25 pre.s9) false :=
  decoderLoadStepOfDecoderAgree (dest := x25) (value := pre.s9) machine agree retired code stepNo
    0x10520 0x83 0x3c 0x81 0x79 0x798#12 2#5 25#5 false 8 pre.s9 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10520) 0x798#12
      (.Regidx 2#5) pre.s9
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x798))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x798 (by decide)) (pre.stackBase + 0x798)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x798 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact level4_wX_x25_run _ pre.s9)

private theorem level4_epilogue_load_s10 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10524))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x790) pre.s10) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10524) retired x26 pre.s10) false :=
  decoderLoadStepOfDecoderAgree (dest := x26) (value := pre.s10) machine agree retired code stepNo
    0x10524 0x03 0x3d 0x01 0x79 0x790#12 2#5 26#5 false 8 pre.s10 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10524) 0x790#12
      (.Regidx 2#5) pre.s10
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x790))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x790 (by decide)) (pre.stackBase + 0x790)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x790 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact level4_wX_x26_run _ pre.s10)

private theorem level4_epilogue_load_s11 {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10528))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase))
    (saved : SavedWordBytes state (pre.stackBase + 0x788) pre.s11) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10528) retired x27 pre.s11) false :=
  decoderLoadStepOfDecoderAgree (dest := x27) (value := pre.s11) machine agree retired code stepNo
    0x10528 0x83 0x3d 0x81 0x78 0x788#12 2#5 27#5 false 8 pre.s11 atPc
    (pcIn := ⟨by native_decide, by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x10528) 0x788#12
      (.Regidx 2#5) pre.s11
      (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 (pre.stackBase + 0x788))
      (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
      (level4_slot_address_eq pre.stackBase 0x788 (by decide)) (pre.stackBase + 0x788)
      (level4_slot_address_toNat pre (by omega)).symm saved.bitVectorLERep
      (pre.slotAligned 0x788 (by omega) (by omega) (by decide))
      (level4_slot_access pre (by omega) (by omega)))
    (by rw [level4_extend_value_dword]; exact level4_wX_x27_run _ pre.s11)

/-- Every architectural register changed by the restore sequence, including retirement bookkeeping. -/
def level4DecodeRawEpilogueWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x1 ∨ r = x2 ∨ r = x8 ∨ r = x9 ∨ r = x18 ∨ r = x19 ∨ r = x20 ∨
    r = x21 ∨ r = x22 ∨ r = x23 ∨ r = x24 ∨ r = x25 ∨ r = x26 ∨ r = x27

private theorem decoderPreserved_level4DecodeRawEpilogueWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4DecodeRawEpilogueWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with book | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint r platform book
  · exact notLink rfl
  all_goals simp [platformPreserved] at platform

private theorem level4_epilogue_bookkeeping (r : Register) (h : stepBookkeeping r) :
    level4DecodeRawEpilogueWrites r := Or.inl h

private theorem level4_epilogue_agree
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (seg : Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory kv fromStep len before state pc) :
    Agree decoderPreserved base state :=
  pre.agree.trans (seg.agree decoderPreserved_level4DecodeRawEpilogueWrites_disjoint)

private theorem level4_epilogue_code
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (seg : Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory kv fromStep len before state pc) :
    Artifacts.programImage.fileBytesLoadedFaithfully state.mem := by
  rw [seg.memEq noMemory_empty]
  exact pre.code

private theorem level4_epilogue_saved
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (seg : Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory kv fromStep len before state pc) :
    Level4DecodeRawSavedFrame state pre.stackBase pre.ra pre.s0 pre.s1 pre.s2 pre.s3 pre.s4 pre.s5
      pre.s6 pre.s7 pre.s8 pre.s9 pre.s10 pre.s11 :=
  pre.saved.of_mem_eq (seg.memEq noMemory_empty)

private theorem level4_epilogue_stack_final_step {margs : DecoderMachineArgs} {base before state : State}
    (pre : Level4DecodeRawEpiloguePre margs base before)
    (machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1052c))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stackBase)) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1052c) retired x2
        (BitVec.ofNat 64 (pre.stackBase + 0x7f0))) false := by
  obtain ⟨retired, run⟩ := decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x1052c 0x13 0x01 0x01 0x7f 0x7f0#12 2#5 2#5 .ADDI atPc
    (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
    (wX_x2_run _ (BitVec.ofNat 64 pre.stackBase + sign_extend (m := 64) 0x7f0#12))
    (pcIn := ⟨by native_decide, by native_decide⟩)
  rw [level4_slot_address_eq pre.stackBase 0x7f0 (by decide)] at run
  exact ⟨retired, run⟩

/-- The full restore phase is parent-owned execution, not a Level 4 local contract. -/
structure Level4DecodeRawEpilogueResult (fromStep : Nat) (before after : State)
    (pre : Level4DecodeRawEpiloguePre margs base before) : Prop where
  trace : Trace fromStep 16 before after
  confined : ConfinedPrefix Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
    Level4DecodeRawEpilogueChildSummary fromStep 16 before after
  writes : WritesOnlyRegs level4DecodeRawEpilogueWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some pre.ra
  sp : after.regs.get? x2 = some (BitVec.ofNat 64 (pre.stackBase + 0x7f0))
  ra : after.regs.get? x1 = some pre.ra
  s0 : after.regs.get? x8 = some pre.s0
  s1 : after.regs.get? x9 = some pre.s1
  s2 : after.regs.get? x18 = some pre.s2
  s3 : after.regs.get? x19 = some pre.s3
  s4 : after.regs.get? x20 = some pre.s4
  s5 : after.regs.get? x21 = some pre.s5
  s6 : after.regs.get? x22 = some pre.s6
  s7 : after.regs.get? x23 = some pre.s7
  s8 : after.regs.get? x24 = some pre.s8
  s9 : after.regs.get? x25 = some pre.s9
  s10 : after.regs.get? x26 = some pre.s10
  s11 : after.regs.get? x27 = some pre.s11
  saved : Level4DecodeRawSavedFrame after pre.stackBase pre.ra pre.s0 pre.s1 pre.s2 pre.s3 pre.s4
    pre.s5 pre.s6 pre.s7 pre.s8 pre.s9 pre.s10 pre.s11
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre Level4DecodeRawEpiloguePcs margs after
  retired : RetiredCounterPresent after

private theorem level4_decode_raw_epilogue_opening
    (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat) :
    ∃ after, Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory
      [⟨x1, pre.ra⟩, ⟨x2, BitVec.ofNat 64 pre.stackBase⟩] fromStep 2 state after
      (BitVec.ofNat 64 0x104fc) := by
  let seg0 := Seg.nil Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
    Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory fromStep pre.retired pre.atPc
  obtain ⟨afterStack, seg1⟩ := seg0.step (by owned_pc) (by simp) x2
    (BitVec.ofNat 64 pre.stackBase) (BitVec.ofNat 64 0x104f8)
    (level4_decode_raw_epilogue_stack_step pre fromStep) (by decide)
    level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide) (by decide)
    (by intro p hp; cases hp)
  have frame1 : Agree decoderPreserved base afterStack :=
    pre.agree.trans (seg1.agree decoderPreserved_level4DecodeRawEpilogueWrites_disjoint)
  have machine1 : DecoderMachinePre Level4DecodeRawEpiloguePcs margs afterStack :=
    pre.machine.mono frame1 seg1.retired
  have memory1 := seg1.memEq noMemory_empty
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterStack.mem := by
    rw [memory1]
    exact pre.code
  have saved1 := pre.saved.of_mem_eq memory1
  have stack1 := seg1.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterRa, seg2⟩ := seg1.step (by owned_pc) (by simp) x1 pre.ra
    (BitVec.ofNat 64 0x104fc)
    (level4_epilogue_load_ra pre pre.machine frame1 seg1.retired code1 (fromStep + 1)
      seg1.atPc stack1 saved1.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  simpa only [Nat.add_zero, List.cons_append, List.nil_append] using ⟨afterRa, seg2⟩

private theorem level4_decode_raw_epilogue_first_restores
    (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat) :
    ∃ after, Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory
      [⟨x18, pre.s2⟩, ⟨x9, pre.s1⟩, ⟨x8, pre.s0⟩, ⟨x1, pre.ra⟩,
        ⟨x2, BitVec.ofNat 64 pre.stackBase⟩] fromStep 5 state after (BitVec.ofNat 64 0x10508) := by
  obtain ⟨afterRa, seg2⟩ := level4_decode_raw_epilogue_opening pre fromStep
  have frame2 := level4_epilogue_agree pre seg2
  have code2 := level4_epilogue_code pre seg2
  have saved2 := level4_epilogue_saved pre seg2
  have stack2 := seg2.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS0, seg3⟩ := seg2.step (by owned_pc) (by simp) x8 pre.s0
    (BitVec.ofNat 64 0x10500)
    (level4_epilogue_load_s0 pre pre.machine frame2 seg2.retired code2 (fromStep + 2)
      seg2.atPc stack2 saved2.2.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame3 := level4_epilogue_agree pre seg3
  have code3 := level4_epilogue_code pre seg3
  have saved3 := level4_epilogue_saved pre seg3
  have stack3 := seg3.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS1, seg4⟩ := seg3.step (by owned_pc) (by simp) x9 pre.s1
    (BitVec.ofNat 64 0x10504)
    (level4_epilogue_load_s1 pre pre.machine frame3 seg3.retired code3 (fromStep + 3)
      seg3.atPc stack3 saved3.2.2.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame4 := level4_epilogue_agree pre seg4
  have code4 := level4_epilogue_code pre seg4
  have saved4 := level4_epilogue_saved pre seg4
  have stack4 := seg4.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS2, seg5⟩ := seg4.step (by owned_pc) (by simp) x18 pre.s2
    (BitVec.ofNat 64 0x10508)
    (level4_epilogue_load_s2 pre pre.machine frame4 seg4.retired code4 (fromStep + 4)
      seg4.atPc stack4 saved4.2.2.2.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  simpa only [Nat.add_zero, List.cons_append, List.nil_append] using ⟨afterS2, seg5⟩

private theorem level4_decode_raw_epilogue_middle_restores
    (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat) :
    ∃ after, Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory
      [⟨x21, pre.s5⟩, ⟨x20, pre.s4⟩, ⟨x19, pre.s3⟩, ⟨x18, pre.s2⟩, ⟨x9, pre.s1⟩,
        ⟨x8, pre.s0⟩, ⟨x1, pre.ra⟩, ⟨x2, BitVec.ofNat 64 pre.stackBase⟩]
      fromStep 8 state after (BitVec.ofNat 64 0x10514) := by
  obtain ⟨afterS2, seg5⟩ := level4_decode_raw_epilogue_first_restores pre fromStep
  have frame5 := level4_epilogue_agree pre seg5
  have code5 := level4_epilogue_code pre seg5
  have saved5 := level4_epilogue_saved pre seg5
  have stack5 := seg5.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS3, seg6⟩ := seg5.step (by owned_pc) (by simp) x19 pre.s3
    (BitVec.ofNat 64 0x1050c)
    (level4_epilogue_load_s3 pre pre.machine frame5 seg5.retired code5 (fromStep + 5)
      seg5.atPc stack5 saved5.2.2.2.2.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame6 := level4_epilogue_agree pre seg6
  have code6 := level4_epilogue_code pre seg6
  have saved6 := level4_epilogue_saved pre seg6
  have stack6 := seg6.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS4, seg7⟩ := seg6.step (by owned_pc) (by simp) x20 pre.s4
    (BitVec.ofNat 64 0x10510)
    (level4_epilogue_load_s4 pre pre.machine frame6 seg6.retired code6 (fromStep + 6)
      seg6.atPc stack6 saved6.2.2.2.2.2.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame7 := level4_epilogue_agree pre seg7
  have code7 := level4_epilogue_code pre seg7
  have saved7 := level4_epilogue_saved pre seg7
  have stack7 := seg7.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS5, seg8⟩ := seg7.step (by owned_pc) (by simp) x21 pre.s5
    (BitVec.ofNat 64 0x10514)
    (level4_epilogue_load_s5 pre pre.machine frame7 seg7.retired code7 (fromStep + 7)
      seg7.atPc stack7 saved7.2.2.2.2.2.2.1)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  simpa only [Nat.add_zero, List.cons_append, List.nil_append] using ⟨afterS5, seg8⟩

private theorem level4_decode_raw_epilogue_all_restores
    (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat) :
    ∃ after, Seg Level4DecodeRawEpiloguePcs Level4DecodeRawEpilogueExit
      Level4DecodeRawEpilogueChildSummary level4DecodeRawEpilogueWrites noMemory
      [⟨x27, pre.s11⟩, ⟨x26, pre.s10⟩, ⟨x25, pre.s9⟩, ⟨x24, pre.s8⟩, ⟨x23, pre.s7⟩,
        ⟨x22, pre.s6⟩, ⟨x21, pre.s5⟩, ⟨x20, pre.s4⟩, ⟨x19, pre.s3⟩, ⟨x18, pre.s2⟩,
        ⟨x9, pre.s1⟩, ⟨x8, pre.s0⟩, ⟨x1, pre.ra⟩, ⟨x2, BitVec.ofNat 64 pre.stackBase⟩]
      fromStep 14 state after (BitVec.ofNat 64 0x1052c) := by
  obtain ⟨afterS5, seg8⟩ := level4_decode_raw_epilogue_middle_restores pre fromStep
  have frame8 := level4_epilogue_agree pre seg8
  have code8 := level4_epilogue_code pre seg8
  obtain ⟨_, _, _, _, _, _, _, savedS6, _, _, _, _, _⟩ := level4_epilogue_saved pre seg8
  have stack8 := seg8.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS6, seg9⟩ := seg8.step (by owned_pc) (by simp) x22 pre.s6
    (BitVec.ofNat 64 0x10518)
    (level4_epilogue_load_s6 pre pre.machine frame8 seg8.retired code8 (fromStep + 8)
      seg8.atPc stack8 savedS6)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame9 := level4_epilogue_agree pre seg9
  have code9 := level4_epilogue_code pre seg9
  obtain ⟨_, _, _, _, _, _, _, _, savedS7, _, _, _, _⟩ := level4_epilogue_saved pre seg9
  have stack9 := seg9.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS7, seg10⟩ := seg9.step (by owned_pc) (by simp) x23 pre.s7
    (BitVec.ofNat 64 0x1051c)
    (level4_epilogue_load_s7 pre pre.machine frame9 seg9.retired code9 (fromStep + 9)
      seg9.atPc stack9 savedS7)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame10 := level4_epilogue_agree pre seg10
  have code10 := level4_epilogue_code pre seg10
  obtain ⟨_, _, _, _, _, _, _, _, _, savedS8, _, _, _⟩ := level4_epilogue_saved pre seg10
  have stack10 := seg10.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS8, seg11⟩ := seg10.step (by owned_pc) (by simp) x24 pre.s8
    (BitVec.ofNat 64 0x10520)
    (level4_epilogue_load_s8 pre pre.machine frame10 seg10.retired code10 (fromStep + 10)
      seg10.atPc stack10 savedS8)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame11 := level4_epilogue_agree pre seg11
  have code11 := level4_epilogue_code pre seg11
  obtain ⟨_, _, _, _, _, _, _, _, _, _, savedS9, _, _⟩ := level4_epilogue_saved pre seg11
  have stack11 := seg11.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS9, seg12⟩ := seg11.step (by owned_pc) (by simp) x25 pre.s9
    (BitVec.ofNat 64 0x10524)
    (level4_epilogue_load_s9 pre pre.machine frame11 seg11.retired code11 (fromStep + 11)
      seg11.atPc stack11 savedS9)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame12 := level4_epilogue_agree pre seg12
  have code12 := level4_epilogue_code pre seg12
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, savedS10, _⟩ := level4_epilogue_saved pre seg12
  have stack12 := seg12.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS10, seg13⟩ := seg12.step (by owned_pc) (by simp) x26 pre.s10
    (BitVec.ofNat 64 0x10528)
    (level4_epilogue_load_s10 pre pre.machine frame12 seg12.retired code12 (fromStep + 12)
      seg12.atPc stack12 savedS10)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame13 := level4_epilogue_agree pre seg13
  have code13 := level4_epilogue_code pre seg13
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, savedS11⟩ := level4_epilogue_saved pre seg13
  have stack13 := seg13.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterS11, seg14⟩ := seg13.step (by owned_pc) (by simp) x27 pre.s11
    (BitVec.ofNat 64 0x1052c)
    (level4_epilogue_load_s11 pre pre.machine frame13 seg13.retired code13 (fromStep + 13)
      seg13.atPc stack13 savedS11)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  simpa only [Nat.add_zero, List.cons_append, List.nil_append] using ⟨afterS11, seg14⟩

/-- Sail executes every parent-owned restore and return instruction from `0x104f4` through
`0x10530`. The result retains the exact restored callee-saved values and the ordinary machine frame
for the enclosing Level 4 rejection/cleanup/status/epilogue phase. -/
theorem level4_decode_raw_epilogue
    (pre : Level4DecodeRawEpiloguePre margs base state) (fromStep : Nat) :
    ∃ after, Level4DecodeRawEpilogueResult fromStep state after pre := by
  obtain ⟨afterS11, seg14⟩ := level4_decode_raw_epilogue_all_restores pre fromStep
  let seg14' := seg14.forget (kv' :=
    [⟨x27, pre.s11⟩, ⟨x26, pre.s10⟩, ⟨x25, pre.s9⟩, ⟨x24, pre.s8⟩, ⟨x23, pre.s7⟩,
      ⟨x22, pre.s6⟩, ⟨x21, pre.s5⟩, ⟨x20, pre.s4⟩, ⟨x19, pre.s3⟩, ⟨x18, pre.s2⟩,
      ⟨x9, pre.s1⟩, ⟨x8, pre.s0⟩, ⟨x1, pre.ra⟩]) (by
        intro p hp
        change p ∈
          ([⟨x27, pre.s11⟩, ⟨x26, pre.s10⟩, ⟨x25, pre.s9⟩, ⟨x24, pre.s8⟩, ⟨x23, pre.s7⟩,
            ⟨x22, pre.s6⟩, ⟨x21, pre.s5⟩, ⟨x20, pre.s4⟩, ⟨x19, pre.s3⟩, ⟨x18, pre.s2⟩,
            ⟨x9, pre.s1⟩, ⟨x8, pre.s0⟩, ⟨x1, pre.ra⟩] ++ [⟨x2, BitVec.ofNat 64 pre.stackBase⟩])
        exact List.mem_append_left _ hp)
  have frame14 := level4_epilogue_agree pre seg14'
  have code14 := level4_epilogue_code pre seg14'
  have stack14 := seg14.reg x2 (BitVec.ofNat 64 pre.stackBase) (by simp)
  obtain ⟨afterStack, seg15⟩ := seg14'.step (by owned_pc) (by simp) x2
    (BitVec.ofNat 64 (pre.stackBase + 0x7f0)) (BitVec.ofNat 64 0x10530)
    (level4_epilogue_stack_final_step pre pre.machine frame14 seg14'.retired code14 (fromStep + 14)
      seg14'.atPc stack14)
    (by decide) level4_epilogue_bookkeeping (by simp [level4DecodeRawEpilogueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have frame15 := level4_epilogue_agree pre seg15
  have code15 := level4_epilogue_code pre seg15
  have ra15 := seg15.reg x1 pre.ra (by simp)
  obtain ⟨retiredReturn, returnRun⟩ := decoderRetStep pre.machine frame15 seg15.retired code15
    (fromStep + 15) 0x10530 0x67 0x80 0x00 0x00 1#5 pre.ra pre.ra seg15.atPc
    (rX_x1_run _ _ (decoderExecuteState_get? ra15)) (target := pre.returnTarget)
    (sourceBit1 := pre.returnBit1)
    (pcIn := ⟨by native_decide, by native_decide⟩)
  obtain ⟨after, seg16⟩ := seg15.stepJump pre.ra (by owned_pc) (by simp) ⟨retiredReturn, returnRun⟩
    level4_epilogue_bookkeeping (by exact of_decide_eq_true rfl)
  refine ⟨after, ⟨seg16.trace, seg16.confined, seg16.writes, seg16.memEq noMemory_empty, seg16.atPc,
    seg16.reg x2 (BitVec.ofNat 64 (pre.stackBase + 0x7f0)) (by simp),
    seg16.reg x1 pre.ra (by simp), seg16.reg x8 pre.s0 (by simp), seg16.reg x9 pre.s1 (by simp),
    seg16.reg x18 pre.s2 (by simp), seg16.reg x19 pre.s3 (by simp), seg16.reg x20 pre.s4 (by simp),
    seg16.reg x21 pre.s5 (by simp), seg16.reg x22 pre.s6 (by simp), seg16.reg x23 pre.s7 (by simp),
    seg16.reg x24 pre.s8 (by simp), seg16.reg x25 pre.s9 (by simp), seg16.reg x26 pre.s10 (by simp),
    seg16.reg x27 pre.s11 (by simp), ?_, level4_epilogue_code pre seg16,
    pre.machine.mono (level4_epilogue_agree pre seg16) seg16.retired, seg16.retired⟩⟩
  exact pre.saved.of_mem_eq (seg16.memEq noMemory_empty)

/-- Execute the epilogue from the typed output of the preceding rejection/cleanup/status route.
The theorem deliberately does not claim that route has been composed yet. -/
theorem level4_decode_raw_epilogue_of_rejectionCleanupStatusHandoff
    (handoff : Level4RejectionCleanupStatusEpilogueHandoff margs base state) (fromStep : Nat) :
    ∃ after, Level4DecodeRawEpilogueResult fromStep state after
      (level4DecodeRawEpiloguePre_of_rejectionCleanupStatusHandoff handoff) :=
  level4_decode_raw_epilogue
    (level4DecodeRawEpiloguePre_of_rejectionCleanupStatusHandoff handoff) fromStep

/-!
The subsequent 16-step theorem consumes `Level4DecodeRawEpiloguePre`; its readable interval is
phase-local and is not an assumption of the public Level 4 contract gauge.
-/

end BinaryFv.Zesu.MachineExecution
