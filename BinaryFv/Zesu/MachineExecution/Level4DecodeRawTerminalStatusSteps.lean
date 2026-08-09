import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Exact terminal status stores in `ssz_raw.decodeRaw` -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

abbrev level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ decodeRawRejectionCleanupStatusCopyEpiloguePcs

private theorem level4_terminal_status_fetch_10738 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x10738) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_11ba4 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x11ba4) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_129f0 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x129f0) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_12ff4 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x12ff4) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_1073c :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x1073c) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_11ba8 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x11ba8) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_129f4 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x129f4) := ⟨by native_decide, by native_decide⟩

private theorem level4_terminal_status_fetch_12ff8 :
    DecoderFetchPc level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs
      (BitVec.ofNat 64 0x12ff8) := ⟨by native_decide, by native_decide⟩

/-- Sail execution of `sh s7, 0x340(s5)` at `0x10738`. -/
theorem level4_status_store_s7_step {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10738))
    (statusBase status target : BitVec 64)
    (baseValue : state.regs.get? x21 = some statusBase)
    (statusValue : state.regs.get? x23 = some status)
    (targetEq : statusBase + sign_extend (m := 64) 0x340#12 = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 2 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 2) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x10738) nextRetired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) false := by
  exact decoderStoreHalfStep machine agree retired code stepNo
    0x10738 0x23 0x90 0x7a 0x35 0x340#12 23#5 21#5 statusBase status target atPc
    (rX_x21_run _ _ (decoderExecuteState_get? baseValue))
    (rX_x23_run _ _ (decoderExecuteState_get? statusValue)) targetEq allowed
    level4_terminal_status_fetch_10738 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) aligned

/-- Sail execution of `sh a0, 0x340(s5)` at `0x11ba4`. -/
theorem level4_status_store_a0_s5_step {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x11ba4))
    (statusBase status target : BitVec 64)
    (baseValue : state.regs.get? x21 = some statusBase)
    (statusValue : state.regs.get? x10 = some status)
    (targetEq : statusBase + sign_extend (m := 64) 0x340#12 = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 2 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 2) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x11ba4) nextRetired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) false := by
  exact decoderStoreHalfStep machine agree retired code stepNo
    0x11ba4 0x23 0x90 0xaa 0x34 0x340#12 10#5 21#5 statusBase status target atPc
    (rX_x21_run _ _ (decoderExecuteState_get? baseValue))
    (rX_x10_run _ _ (decoderExecuteState_get? statusValue)) targetEq allowed
    level4_terminal_status_fetch_11ba4 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) aligned

/-- Sail execution of `sh s1, 0x340(a0)` at `0x129f0`. -/
theorem level4_status_store_s1_step {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x129f0))
    (statusBase status target : BitVec 64)
    (baseValue : state.regs.get? x10 = some statusBase)
    (statusValue : state.regs.get? x9 = some status)
    (targetEq : statusBase + sign_extend (m := 64) 0x340#12 = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 2 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 2) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x129f0) nextRetired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) false := by
  exact decoderStoreHalfStep machine agree retired code stepNo
    0x129f0 0x23 0x10 0x95 0x34 0x340#12 9#5 10#5 statusBase status target atPc
    (rX_x10_run _ _ (decoderExecuteState_get? baseValue))
    (rX_x9_run _ _ (decoderExecuteState_get? statusValue)) targetEq allowed
    level4_terminal_status_fetch_129f0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) aligned

/-- Sail execution of `sh s6, 0x340(a0)` at `0x12ff4`. -/
theorem level4_status_store_s6_step {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12ff4))
    (statusBase status target : BitVec 64)
    (baseValue : state.regs.get? x10 = some statusBase)
    (statusValue : state.regs.get? x22 = some status)
    (targetEq : statusBase + sign_extend (m := 64) 0x340#12 = target)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr target) 2 = true)
    (allowed : DecoderAccessRange DecoderWritableByte target 2) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x12ff4) nextRetired target.toNat
        (width := 2) (Sail.BitVec.extractLsb status 15 0)) false := by
  exact decoderStoreHalfStep machine agree retired code stepNo
    0x12ff4 0x23 0x10 0x65 0x35 0x340#12 22#5 10#5 statusBase status target atPc
    (rX_x10_run _ _ (decoderExecuteState_get? baseValue))
    (rX_x22_run _ _ (decoderExecuteState_get? statusValue)) targetEq allowed
    level4_terminal_status_fetch_12ff4 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) aligned

/-- Sail execution of the terminal `j 0x104f4` at `0x1073c`. -/
theorem level4_terminal_jump_1073c {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1073c)) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x1073c)
          (BitVec.ofNat 64 0x104f4))
        (BitVec.ofNat 64 0x104f4) nextRetired) false := by
  exact decoderJalStep machine agree retired code stepNo
    0x1073c 0x6f 0xf0 0x9f 0xdb 0x1ffdb8#21 (BitVec.ofNat 64 0x104f4) atPc
    level4_terminal_status_fetch_1073c (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide)

/-- Sail execution of the terminal `j 0x104f4` at `0x11ba8`. -/
theorem level4_terminal_jump_11ba8 {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x11ba8)) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x11ba8)
          (BitVec.ofNat 64 0x104f4))
        (BitVec.ofNat 64 0x104f4) nextRetired) false := by
  exact decoderJalStep machine agree retired code stepNo
    0x11ba8 0x6f 0xe0 0xdf 0x94 0x1fe94c#21 (BitVec.ofNat 64 0x104f4) atPc
    level4_terminal_status_fetch_11ba8 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide)

/-- Sail execution of the terminal `j 0x104f4` at `0x129f4`. -/
theorem level4_terminal_jump_129f4 {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x129f4)) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x129f4)
          (BitVec.ofNat 64 0x104f4))
        (BitVec.ofNat 64 0x104f4) nextRetired) false := by
  exact decoderJalStep machine agree retired code stepNo
    0x129f4 0x6f 0xd0 0x1f 0xb0 0x1fdb00#21 (BitVec.ofNat 64 0x104f4) atPc
    level4_terminal_status_fetch_129f4 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide)

/-- Sail execution of the terminal `j 0x104f4` at `0x12ff8`. -/
theorem level4_terminal_jump_12ff8 {base state : State} {margs : DecoderMachineArgs}
    (machine : DecoderMachinePre level4DecodeRawRejectionCleanupStatusCopyEpiloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12ff8)) :
    ∃ nextRetired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12ff8)
          (BitVec.ofNat 64 0x104f4))
        (BitVec.ofNat 64 0x104f4) nextRetired) false := by
  exact decoderJalStep machine agree retired code stepNo
    0x12ff8 0x6f 0xd0 0xcf 0xcf 0x1fd4fc#21 (BitVec.ofNat 64 0x104f4) atPc
    level4_terminal_status_fetch_12ff8 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by decide) (by decoder_decode)
    (by unfold BaseInstructionEncoding; decide) (by decide) (by decide) (by decide)

end BinaryFv.Zesu.MachineExecution
