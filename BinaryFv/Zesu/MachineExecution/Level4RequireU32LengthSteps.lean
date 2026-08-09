import BinaryFv.Zesu.MachineExecution.Level4DecodeRawPrologueSteps
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Exact `requireU32Length` leaf in the emitted raw decoder -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The three generated instructions of the selected `requireU32Length` occurrence. -/
def level4RequireU32LengthPcs : List Nat := [0x10484, 0x10488, 0x1048c]

/-- Literal reviewed ownership for the inlined `requireU32Length` occurrence. -/
abbrev Level4RequireU32LengthPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4RequireU32LengthPcs

theorem level4RequireU32LengthPcs_exact :
    level4RequireU32LengthPcs = [0x10484, 0x10488, 0x1048c] := rfl

theorem level4RequireU32LengthPcs_count : level4RequireU32LengthPcs.length = 3 := rfl

theorem level4RequireU32LengthPcs_subset_child :
    ∀ pc, Level4RequireU32LengthPcs pc → functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_requireU32Length_in_ssz_raw_decodeRaw_at_191_25 pc := by
  intro pc hpc
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  simp only [Level4RequireU32LengthPcs, level4RequireU32LengthPcs, List.mem_cons,
    List.not_mem_nil, or_false] at hpc
  rcases hpc with h | h | h
  · have hp : pc = BitVec.ofNat 64 0x10484 := by
      apply BitVec.eq_of_toNat_eq
      simpa using h
    subst pc
    native_decide
  · have hp : pc = BitVec.ofNat 64 0x10488 := by
      apply BitVec.eq_of_toNat_eq
      simpa using h
    subst pc
    native_decide
  · have hp : pc = BitVec.ofNat 64 0x1048c := by
      apply BitVec.eq_of_toNat_eq
      simpa using h
    subst pc
    native_decide

abbrev Level4RequireU32LengthExit : BitVec 64 → Prop := fun _ => False

abbrev Level4RequireU32LengthChildSummary :
    FunctionInstanceId → Nat → Nat → State → State → Prop := fun _ _ _ _ _ => False

def level4RequireU32LengthWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x10 ∨ r = x11 ∨ r = x21

private theorem decoderPreserved_level4RequireU32LengthWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4RequireU32LengthWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with book | rfl | rfl | rfl
  · exact platformPreserved_disjoint r platform book
  all_goals simp [platformPreserved] at platform

private theorem level4RequireU32Length_srli_zero (n : Nat) (bound : n < 2 ^ 32) :
    shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 n) = 0#64 := by
  have amount : Sail.BitVec.extractLsb 32#6
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0 = 32#6 := by decide
  rw [shiftIopResult, amount]
  apply BitVec.eq_of_toNat_eq
  simp [Sail.shift_bits_right, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] <;> omega

private theorem level4RequireU32Length_srli_value (n : Nat) (fits : n < 2 ^ 64) :
    shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 n) = BitVec.ofNat 64 (n / 2 ^ 32) := by
  have amount : Sail.BitVec.extractLsb 32#6
      (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0 = 32#6 := by decide
  have quotientFits : n / 2 ^ 32 < 2 ^ 64 := by omega
  rw [shiftIopResult, amount]
  apply BitVec.eq_of_toNat_eq
  simp [Sail.shift_bits_right, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt fits,
    Nat.mod_eq_of_lt quotientFits]

private theorem level4RequireU32Length_semantics (bytes : ByteArray) (fits : bytes.size < 2 ^ 64) :
    meaningRequireU32Length bytes = .ok () ↔
      shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 bytes.size) = 0#64 := by
  constructor
  · intro meaning
    rw [meaningRequireU32Length] at meaning
    split at meaning
    · exact level4RequireU32Length_srli_zero _ (by omega)
    · simp at meaning
  · intro high
    rw [level4RequireU32Length_srli_value _ fits] at high
    have quotientFits : bytes.size / 2 ^ 32 < 2 ^ 64 := by omega
    have highNat := congrArg BitVec.toNat high
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt quotientFits] at highNat
    rw [meaningRequireU32Length]
    split <;> simp_all
    omega

theorem level4RequireU32LengthPcs_subset_decodeRaw :
    ∀ pc, Level4RequireU32LengthPcs pc → RegisterWriteStep.decodeRawExecutionPcs pc := by
  intro pc hpc
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  simp only [Level4RequireU32LengthPcs, level4RequireU32LengthPcs, List.mem_cons,
    List.not_mem_nil, or_false] at hpc
  rcases hpc with h | h | h
  · have hp : pc = BitVec.ofNat 64 0x10484 := by
      apply BitVec.eq_of_toNat_eq
      simpa using h
    subst pc
    native_decide
  · have hp : pc = BitVec.ofNat 64 0x10488 := by
      apply BitVec.eq_of_toNat_eq
      simpa using h
    subst pc
    native_decide
  · have hp : pc = BitVec.ofNat 64 0x1048c := by
      apply BitVec.eq_of_toNat_eq
      simpa using h
    subst pc
    native_decide

/-- Concrete state at the selected inline leaf.  `a0` is the caller result slot, `a2` the
borrowed-input pointer, and `a3` its length; these are the optimized entry registers, not an ABI
invented for the inlined Zig source. -/
structure Level4RequireU32LengthPre (margs : DecoderMachineArgs) (state : State) where
  decodeRawMachine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10484)
  resultBase : Nat
  resultBaseValue : state.regs.get? x10 = some (BitVec.ofNat 64 resultBase)
  inputBaseValue : state.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase)
  lengthValue : state.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size)
  lengthFits : margs.bytes.size < 2 ^ 64

private def level4RequireU32LengthMachine (pre : Level4RequireU32LengthPre margs state) :
    DecoderMachinePre Level4RequireU32LengthPcs margs state :=
  pre.decodeRawMachine.restrict level4RequireU32LengthPcs_subset_decodeRaw

/-- The child returns at the parent-owned `beqz` with its high-word check, prepared invalid-SSZ
tag, and result-slot carrier all explicit.  The branch itself is deliberately outside this leaf. -/
structure Level4RequireU32LengthHandoff (fromStep : Nat) (before after : State)
    (pre : Level4RequireU32LengthPre margs before) : Prop where
  trace : Trace fromStep 3 before after
  confined : ConfinedPrefix Level4RequireU32LengthPcs Level4RequireU32LengthExit
    Level4RequireU32LengthChildSummary fromStep 3 before after
  writes : WritesOnlyRegs level4RequireU32LengthWrites before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10490)
  highLength : after.regs.get? x11 = some
    (shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 margs.bytes.size))
  resultBase : after.regs.get? x21 = some (BitVec.ofNat 64 pre.resultBase)
  preparedInvalidSszTag : after.regs.get? x10 = some (BitVec.ofNat 64 2)
  inputBase : after.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase)
  inputLength : after.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size)
  lengthSemantics : meaningRequireU32Length margs.bytes = .ok () ↔
    after.regs.get? x11 = some 0#64
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  decodeRawMachine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs after
  retired : RetiredCounterPresent after

private theorem level4_require_u32_length_srli_step {base state : State}
    (machine : DecoderMachinePre Level4RequireU32LengthPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10484))
    (length : state.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10484) stepRetired x11
        (shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 margs.bytes.size))) false := by
  exact decoderShiftIopStepOfDecoderAgree machine agree retired code stepNo
    0x10484 0x93 0xd5 0x06 0x02 32#6 13#5 11#5 .SRLI atPc
    (rX_x13_run _ _ (decoderExecuteState_get? length)) (wX_x11_run _ _)
    (pcIn := ⟨by simp [Level4RequireU32LengthPcs, level4RequireU32LengthPcs], by native_decide⟩)

private theorem level4_require_u32_length_save_result_step {base state : State}
    (machine : DecoderMachinePre Level4RequireU32LengthPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10488))
    (resultBase : Nat) (resultBaseValue : state.regs.get? x10 = some (BitVec.ofNat 64 resultBase)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10488) stepRetired x21
        (BitVec.ofNat 64 resultBase)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x10488 0x93 0x0a 0x05 0x00 0#12 10#5 21#5 .ADDI atPc
    (rX_x10_run _ _ (decoderExecuteState_get? resultBaseValue))
    (by simp only [iTypeResult]
        rw [show sign_extend 0#12 = 0#64 by decide]
        simp only [BitVec.add_zero]
        exact wX_x21_run _ _)
    (pcIn := ⟨by simp [Level4RequireU32LengthPcs, level4RequireU32LengthPcs], by native_decide⟩)

private theorem level4_require_u32_length_prepare_invalid_step {base state : State}
    (machine : DecoderMachinePre Level4RequireU32LengthPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1048c)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1048c) stepRetired x10
        (BitVec.ofNat 64 2)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x1048c 0x13 0x05 0x20 0x00 0x002#12 0#5 10#5 .ADDI atPc (rX_x0_run _)
    (by rw [show iTypeResult .ADDI 0x002#12 (0#64) = BitVec.ofNat 64 2 by decide]
        exact wX_x10_run _ _)
    (pcIn := ⟨by simp [Level4RequireU32LengthPcs, level4RequireU32LengthPcs], by native_decide⟩)

/-- Sail executes the complete selected `requireU32Length` leaf.  It is unconditional: all three
of its optimized instructions are discharged here, so this occurrence does not become an
`hLevel4` contract field. -/
theorem level4_require_u32_length
    (pre : Level4RequireU32LengthPre margs state) (fromStep : Nat) :
    ∃ after, Level4RequireU32LengthHandoff fromStep state after pre := by
  let machine := level4RequireU32LengthMachine pre
  let seg0 := Seg.nil Level4RequireU32LengthPcs Level4RequireU32LengthExit
    Level4RequireU32LengthChildSummary level4RequireU32LengthWrites noMemory fromStep
    machine.retiredCounter pre.atPc
  let seg0' := ((seg0.know x10 (BitVec.ofNat 64 pre.resultBase) pre.resultBaseValue).know x12
    (BitVec.ofNat 64 margs.inputBase) pre.inputBaseValue).know x13
    (BitVec.ofNat 64 margs.bytes.size) pre.lengthValue
  obtain ⟨afterHigh, seg1⟩ := seg0'.step (by simp [Level4RequireU32LengthPcs,
      level4RequireU32LengthPcs]) (by simp) x11
    (shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 margs.bytes.size)) (BitVec.ofNat 64 0x10488)
    (level4_require_u32_length_srli_step machine (Agree.refl state) seg0'.retired pre.code fromStep
      seg0'.atPc pre.lengthValue)
    (by decide) (by intro r h; exact Or.inl h) (by simp [level4RequireU32LengthWrites])
    (by decide) (by decide) (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterHigh.mem := by
    rw [seg1.memEq noMemory_empty]
    exact pre.code
  have machine1 : DecoderMachinePre Level4RequireU32LengthPcs margs afterHigh :=
    machine.mono (seg1.agree decoderPreserved_level4RequireU32LengthWrites_disjoint) seg1.retired
  have resultBase1 : afterHigh.regs.get? x10 = some (BitVec.ofNat 64 pre.resultBase) :=
    seg1.reg x10 (BitVec.ofNat 64 pre.resultBase) (by simp)
  obtain ⟨afterResult, seg2⟩ := seg1.step (by simp [Level4RequireU32LengthPcs,
      level4RequireU32LengthPcs]) (by simp) x21 (BitVec.ofNat 64 pre.resultBase)
    (BitVec.ofNat 64 0x1048c)
    (level4_require_u32_length_save_result_step machine1 (Agree.refl afterHigh) seg1.retired code1
      (fromStep + 1) seg1.atPc pre.resultBase resultBase1)
    (by decide) (by intro r h; exact Or.inl h) (by simp [level4RequireU32LengthWrites])
    (by decide) (by decide) (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully afterResult.mem := by
    rw [seg2.memEq noMemory_empty]
    exact pre.code
  have machine2 : DecoderMachinePre Level4RequireU32LengthPcs margs afterResult :=
    machine.mono (seg2.agree decoderPreserved_level4RequireU32LengthWrites_disjoint) seg2.retired
  let seg2' := seg2.forget (kv' := [⟨x21, BitVec.ofNat 64 pre.resultBase⟩,
    ⟨x11, shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 margs.bytes.size)⟩,
    ⟨x13, BitVec.ofNat 64 margs.bytes.size⟩, ⟨x12, BitVec.ofNat 64 margs.inputBase⟩]) (by simp)
  obtain ⟨after, seg3⟩ := seg2'.step (by simp [Level4RequireU32LengthPcs,
      level4RequireU32LengthPcs]) (by simp) x10 (BitVec.ofNat 64 2) (BitVec.ofNat 64 0x10490)
    (level4_require_u32_length_prepare_invalid_step machine2 (Agree.refl afterResult) seg2'.retired code2
      (fromStep + 2) seg2'.atPc)
    (by decide) (by intro r h; exact Or.inl h) (by simp [level4RequireU32LengthWrites])
    (by decide) (by decide) (by exact of_decide_eq_true rfl)
  have code3 : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [seg3.memEq noMemory_empty]
    exact pre.code
  have high := seg3.reg x11 (shiftIopResult .SRLI 32#6 (BitVec.ofNat 64 margs.bytes.size)) (by simp)
  have result := seg3.reg x21 (BitVec.ofNat 64 pre.resultBase) (by simp)
  have tag := seg3.reg x10 (BitVec.ofNat 64 2) (by simp)
  have inputBase : after.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase) :=
    seg3.reg x12 (BitVec.ofNat 64 margs.inputBase) (by simp)
  have inputLength : after.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size) :=
    seg3.reg x13 (BitVec.ofNat 64 margs.bytes.size) (by simp)
  refine ⟨after, ⟨seg3.trace, seg3.confined, seg3.writes, seg3.atPc, high, result, tag, inputBase,
    inputLength, ?_, code3,
    pre.decodeRawMachine.mono
      (seg3.agree decoderPreserved_level4RequireU32LengthWrites_disjoint) seg3.retired,
    seg3.retired⟩⟩
  rw [level4RequireU32Length_semantics margs.bytes pre.lengthFits]
  constructor
  · intro h
    exact high.trans (congrArg some h)
  · intro h
    exact Option.some.inj (high.symm.trans h)

end BinaryFv.Zesu.MachineExecution
