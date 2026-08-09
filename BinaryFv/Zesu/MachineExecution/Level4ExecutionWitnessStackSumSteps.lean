import BinaryFv.Zesu.MachineExecution.DecoderBitVectorLoad
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.MachineExecution.Level4DecodeRawParentInvariant
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Execution-witness stack-sum parent corridor -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.DecodedValue BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The direct parent instructions between the generated r3 H and R boundaries. -/
def level4ExecutionWitnessStackSumPcs : List Nat := [0x12794, 0x12798, 0x1279c]

abbrev Level4ExecutionWitnessStackSumPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4ExecutionWitnessStackSumPcs

theorem level4ExecutionWitnessStackSumPcs_count : level4ExecutionWitnessStackSumPcs.length = 3 := rfl

theorem level4ExecutionWitnessStackSumPcs_subset_phase :
    level4ExecutionWitnessStackSumPcs.all decodeRawSpecializedDispatchReturnsSuccessPcs.contains = true := by
  native_decide

theorem level4ExecutionWitnessStackSumPcs_subset_direct :
    level4ExecutionWitnessStackSumPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

private theorem level4_executionWitness_stack_sum_12794_parent :
    Level4ExecutionWitnessStackSumPcs (BitVec.ofNat 64 0x12794) := by
  simp [Level4ExecutionWitnessStackSumPcs, level4ExecutionWitnessStackSumPcs]

private theorem level4_executionWitness_stack_sum_12798_parent :
    Level4ExecutionWitnessStackSumPcs (BitVec.ofNat 64 0x12798) := by
  simp [Level4ExecutionWitnessStackSumPcs, level4ExecutionWitnessStackSumPcs]

private theorem level4_executionWitness_stack_sum_1279c_parent :
    Level4ExecutionWitnessStackSumPcs (BitVec.ofNat 64 0x1279c) := by
  simp [Level4ExecutionWitnessStackSumPcs, level4ExecutionWitnessStackSumPcs]

private theorem level4_executionWitness_stack_sum_owned (pc : Nat)
    (inCorridor : pc = 0x12794 ∨ pc = 0x12798 ∨ pc = 0x1279c) :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 pc) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  rcases inCorridor with rfl | rfl | rfl <;> native_decide

private theorem level4_executionWitness_extend_value_dword (v : BitVec (8 * 8)) :
    extend_value false v = v := by
  unfold extend_value
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

private theorem level4_executionWitness_rX_x19_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x19 = some value) :
    Runs (rX_bits (.Regidx 19#5)) state state value := by
  have index : (Sail.BitVec.toNatInt 19#5).toNat = 19 := by decide
  unfold Runs
  simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]

private theorem level4_executionWitness_stack_sum_left_load_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo postStack left : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12794))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 postStack))
    (word : stackWord state postStack 0x238 left)
    (readable : DecoderAccessRange (DecoderReadableByte margs)
      (BitVec.ofNat 64 (postStack + 0x238)) 8)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (postStack + 0x238))) 8 = true)
    (fits : postStack + 0x240 < 2 ^ 64) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x12794) stepRetired x19
        (BitVec.ofNat 64 left)) false := by
  have targetEq : BitVec.ofNat 64 postStack + sign_extend (m := 64) 0x238#12 =
      BitVec.ofNat 64 (postStack + 0x238) := by
    rw [show sign_extend (m := 64) 0x238#12 = BitVec.ofNat 64 0x238 by decide, ← BitVec.ofNat_add]
  have targetToNat : (BitVec.ofNat 64 (postStack + 0x238)).toNat = postStack + 0x238 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  change BitVectorLERep state (postStack + 0x238) (BitVec.ofNat 64 left) at word
  exact decoderLoadStepOfDecoderAgree (dest := x19) (value := BitVec.ofNat 64 left) machine agree
    retired code stepNo 0x12794 0x83 0x39 0x81 0x23 0x238#12 2#5 19#5 false 8
    (BitVec.ofNat 64 left) atPc
    (pcIn := ⟨level4_executionWitness_stack_sum_owned _ (Or.inl rfl), by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x12794) 0x238#12
      (.Regidx 2#5) (BitVec.ofNat 64 left) (BitVec.ofNat 64 postStack)
      (BitVec.ofNat 64 (postStack + 0x238))
      (rX_x2_run _ _ (decoderExecuteState_get? spValue)) targetEq (postStack + 0x238)
      targetToNat.symm word aligned readable)
    (by rw [level4_executionWitness_extend_value_dword]; exact wX_x19_run _ _)

private theorem level4_executionWitness_stack_sum_right_load_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo postStack right : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12798))
    (spValue : state.regs.get? x2 = some (BitVec.ofNat 64 postStack))
    (word : stackWord state postStack 0x248 right)
    (readable : DecoderAccessRange (DecoderReadableByte margs)
      (BitVec.ofNat 64 (postStack + 0x248)) 8)
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (postStack + 0x248))) 8 = true)
    (fits : postStack + 0x250 < 2 ^ 64) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x12798) stepRetired x10
        (BitVec.ofNat 64 right)) false := by
  have targetEq : BitVec.ofNat 64 postStack + sign_extend (m := 64) 0x248#12 =
      BitVec.ofNat 64 (postStack + 0x248) := by
    rw [show sign_extend (m := 64) 0x248#12 = BitVec.ofNat 64 0x248 by decide, ← BitVec.ofNat_add]
  have targetToNat : (BitVec.ofNat 64 (postStack + 0x248)).toNat = postStack + 0x248 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  change BitVectorLERep state (postStack + 0x248) (BitVec.ofNat 64 right) at word
  exact decoderLoadStepOfDecoderAgree (dest := x10) (value := BitVec.ofNat 64 right) machine agree
    retired code stepNo 0x12798 0x03 0x35 0x81 0x24 0x248#12 2#5 10#5 false 8
    (BitVec.ofNat 64 right) atPc
    (pcIn := ⟨level4_executionWitness_stack_sum_owned _ (Or.inr (Or.inl rfl)), by native_decide⟩)
    (decoderDwordReadOfBitVectorLERep machine agree (BitVec.ofNat 64 0x12798) 0x248#12
      (.Regidx 2#5) (BitVec.ofNat 64 right) (BitVec.ofNat 64 postStack)
      (BitVec.ofNat 64 (postStack + 0x248))
      (rX_x2_run _ _ (decoderExecuteState_get? spValue)) targetEq (postStack + 0x248)
      targetToNat.symm word aligned readable)
    (by rw [level4_executionWitness_extend_value_dword]; exact wX_x10_run _ _)

private theorem level4_executionWitness_stack_sum_add_step {base state : State}
    (machine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1279c))
    (leftValue : state.regs.get? x19 = some left) (rightValue : state.regs.get? x10 = some right) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1279c) stepRetired x19
        (rTypeResult .ADD left right)) false := by
  exact decoderRTypeStepOfDecoderAgree machine agree retired code stepNo
    0x1279c 0xb3 0x89 0xa9 0x00 10#5 19#5 19#5 .ADD atPc
    (level4_executionWitness_rX_x19_run _ _ (decoderExecuteState_get? leftValue))
    (rX_x10_run _ _ (decoderExecuteState_get? rightValue)) (wX_x19_run _ _)
    (pcIn := ⟨level4_executionWitness_stack_sum_owned _ (Or.inr (Or.inr rfl)), by native_decide⟩)

def level4ExecutionWitnessStackSumWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x19 ∨ r = x10

private theorem decoderPreserved_level4ExecutionWitnessStackSumWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4ExecutionWitnessStackSumWrites := by
  intro r preserved written
  rcases preserved with ⟨notLink, platform⟩
  rcases written with bookkeeping | rfl | rfl
  · exact platformPreserved_disjoint r platform bookkeeping
  all_goals simp [platformPreserved] at platform

structure Level4ExecutionWitnessStackSumPre (margs : DecoderMachineArgs) (origin state : State) where
  frame : Level4DecodeRawParentFrame margs origin state
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12794)
  postStack : Nat
  sp : state.regs.get? x2 = some (BitVec.ofNat 64 postStack)
  postFits : postStack + 0x250 < 2 ^ 64
  left : Nat
  leftWord : stackWord state postStack 0x238 left
  right : Nat
  rightWord : stackWord state postStack 0x248 right

structure Level4ExecutionWitnessStackSumHandoff (fromStep : Nat) (before after : State)
    (pre : Level4ExecutionWitnessStackSumPre margs origin before) : Prop where
  trace : Trace fromStep 3 before after
  confined : ConfinedPrefix Level4ExecutionWitnessStackSumPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 3 before after
  writes : WritesOnlyRegs level4ExecutionWitnessStackSumWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x127a0)
  sum : after.regs.get? x19 = some
    (rTypeResult .ADD (BitVec.ofNat 64 pre.left) (BitVec.ofNat 64 pre.right))
  preserved : pre.frame.PreservedTo after

private theorem level4_executionWitness_stack_sum_aligned (postStack offset : Nat)
    (postFits : postStack + offset + 8 < 2 ^ 64) (postStackAligned : postStack % 16 = 0)
    (offsetAligned : offset % 8 = 0) :
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (postStack + offset))) 8 = true := by
  have targetAligned : (postStack + offset) % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Nat.dvd_add
    · exact Nat.dvd_trans (by decide) (Nat.dvd_of_mod_eq_zero postStackAligned)
    · exact Nat.dvd_of_mod_eq_zero offsetAligned
  simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp [Int.tmod, targetAligned]

private theorem level4_executionWitness_stack_sum_frame_preserved
    {margs : DecoderMachineArgs} {origin before after : State}
    (frame : Level4DecodeRawParentFrame margs origin before)
    (memory : after.mem = before.mem)
    (stackPointer : after.regs.get? x2 = before.regs.get? x2)
    (decoderAgree : Agree decoderPreserved before after)
    (retired : RetiredCounterPresent after) :
    frame.PreservedTo after := by
  rcases frame.invariant with ⟨entry, stackEq, raEq, saved, sp, inputMemory, inputSeparated,
    stackWritable, rawWritable, rawSeparated, postStackAligned, code, machine, -⟩
  have inputAfter : MemoryBytes after margs.inputBase margs.bytes := by
    apply inputMemory.of_mem_eq
    intro index indexBound
    rw [memory]
  have codeAfter : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [memory]
    exact code
  refine ⟨entry, stackEq, raEq, ?_, stackPointer.trans sp,
    inputAfter, inputSeparated, stackWritable, rawWritable, rawSeparated, postStackAligned,
    codeAfter, machine.mono decoderAgree retired, retired⟩
  rw [Level4DecodeRawPrologueSavedFrame] at saved ⊢
  simp only [SavedWordBytes] at saved ⊢
  rw [memory]
  exact saved

/-- Sail executes the exact r3 `ld; ld; add` parent corridor and retains the raw-entry frame. -/
theorem level4_executionWitness_stack_sum
    (pre : Level4ExecutionWitnessStackSumPre margs origin state) (fromStep : Nat) :
    ∃ after, Level4ExecutionWitnessStackSumHandoff fromStep state after pre := by
  rcases pre.frame.invariant with ⟨entry, stackEq, raEq, saved, frameSp, inputMemory,
    inputSeparated, stackWritable, rawWritable, rawSeparated, postStackAligned, code, machine,
    retired⟩
  have entryFits : entry.postStack + 0x250 < 2 ^ 64 := by
    have stackFits := entry.stackFits
    rw [entry.postStackEq] at stackFits
    omega
  have stackEqBits : BitVec.ofNat 64 pre.postStack = BitVec.ofNat 64 entry.postStack := by
    exact Option.some.inj (pre.sp.symm.trans frameSp)
  have postStackEq : pre.postStack = entry.postStack := by
    have toNatEq := congrArg BitVec.toNat stackEqBits
    have preFits := pre.postFits
    have preStackFits : pre.postStack < 2 ^ 64 := by omega
    have entryStackFits : entry.postStack < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt preStackFits,
      Nat.mod_eq_of_lt entryStackFits] at toNatEq
    exact toNatEq
  have rawFits : pre.postStack + 0x7f0 < 2 ^ 64 := by
    have stackFits := entry.stackFits
    rw [entry.postStackEq, ← postStackEq] at stackFits
    omega
  have rawWritablePre : ∀ index, index < 0x7f0 →
      canonicalContractParams.env.stack (pre.postStack + index) := by
    simpa [postStackEq] using rawWritable
  have postStackAlignedPre : pre.postStack % 16 = 0 := by
    simpa [postStackEq] using postStackAligned
  have leftReadable : DecoderAccessRange (DecoderReadableByte margs)
      (BitVec.ofNat 64 (pre.postStack + 0x238)) 8 :=
    rawFrameReadable_of_writable rawFits rawWritablePre 0x238 (by omega)
  have rightReadable : DecoderAccessRange (DecoderReadableByte margs)
      (BitVec.ofNat 64 (pre.postStack + 0x248)) 8 :=
    rawFrameReadable_of_writable rawFits rawWritablePre 0x248 (by omega)
  have leftAligned : is_aligned_vaddr
      (virtaddr.Virtaddr (BitVec.ofNat 64 (pre.postStack + 0x238))) 8 = true :=
    level4_executionWitness_stack_sum_aligned _ _ (by omega) postStackAlignedPre (by decide)
  have rightAligned : is_aligned_vaddr
      (virtaddr.Virtaddr (BitVec.ofNat 64 (pre.postStack + 0x248))) 8 = true :=
    level4_executionWitness_stack_sum_aligned _ _ (by omega) postStackAlignedPre (by decide)
  let seg0 := Seg.nil Level4ExecutionWitnessStackSumPcs (fun _ => False)
    (fun _ _ _ _ _ => False) level4ExecutionWitnessStackSumWrites noMemory fromStep retired pre.atPc
  let seg0' := seg0.know x2 (BitVec.ofNat 64 pre.postStack) pre.sp
  obtain ⟨afterLeft, seg1⟩ := seg0'.step level4_executionWitness_stack_sum_12794_parent (by simp)
    x19 (BitVec.ofNat 64 pre.left) (BitVec.ofNat 64 0x12798)
    (level4_executionWitness_stack_sum_left_load_step machine (Agree.refl state) seg0'.retired code
      fromStep pre.postStack pre.left seg0'.atPc pre.sp pre.leftWord leftReadable leftAligned (by omega))
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4ExecutionWitnessStackSumWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterLeft.mem := by
    rw [seg1.memEq noMemory_empty]
    exact code
  have machine1 : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs afterLeft :=
    machine.mono (seg1.agree decoderPreserved_level4ExecutionWitnessStackSumWrites_disjoint) seg1.retired
  have rightWord1 : stackWord afterLeft pre.postStack 0x248 pre.right := by
    change BitVectorLERep afterLeft (pre.postStack + 0x248) (BitVec.ofNat 64 pre.right)
    have rightWord := pre.rightWord
    change BitVectorLERep state (pre.postStack + 0x248) (BitVec.ofNat 64 pre.right) at rightWord
    intro index bound
    rw [seg1.memEq noMemory_empty]
    exact rightWord index bound
  have sp1 : afterLeft.regs.get? x2 = some (BitVec.ofNat 64 pre.postStack) :=
    seg1.writes x2 (by simp [level4ExecutionWitnessStackSumWrites]) |>.trans pre.sp
  let seg1' := seg1.forget (kv' := [⟨x19, BitVec.ofNat 64 pre.left⟩, ⟨x2, BitVec.ofNat 64 pre.postStack⟩])
    (by intro p hp; simpa using hp)
  obtain ⟨afterRight, seg2⟩ := seg1'.step level4_executionWitness_stack_sum_12798_parent (by simp)
    x10 (BitVec.ofNat 64 pre.right) (BitVec.ofNat 64 0x1279c)
    (level4_executionWitness_stack_sum_right_load_step machine1 (Agree.refl afterLeft) seg1'.retired code1
      (fromStep + 1) pre.postStack pre.right seg1'.atPc sp1 rightWord1 rightReadable rightAligned (by omega))
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4ExecutionWitnessStackSumWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully afterRight.mem := by
    rw [seg2.memEq noMemory_empty]
    exact code
  have machine2 : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs afterRight :=
    machine.mono (seg2.agree decoderPreserved_level4ExecutionWitnessStackSumWrites_disjoint) seg2.retired
  have left2 : afterRight.regs.get? x19 = some (BitVec.ofNat 64 pre.left) :=
    seg2.reg x19 (BitVec.ofNat 64 pre.left) (by simp)
  let seg2' := seg2.forget (kv' := [⟨x10, BitVec.ofNat 64 pre.right⟩]) (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
    exact Or.inl hp)
  obtain ⟨after, seg3⟩ := seg2'.step level4_executionWitness_stack_sum_1279c_parent (by simp)
    x19 (rTypeResult .ADD (BitVec.ofNat 64 pre.left) (BitVec.ofNat 64 pre.right))
    (BitVec.ofNat 64 0x127a0)
    (level4_executionWitness_stack_sum_add_step machine2 (Agree.refl afterRight) seg2'.retired code2
      (fromStep + 2) seg2'.atPc
      left2
      (seg2'.reg x10 (BitVec.ofNat 64 pre.right) (by simp)))
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4ExecutionWitnessStackSumWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have preserved : pre.frame.PreservedTo after :=
    level4_executionWitness_stack_sum_frame_preserved pre.frame (seg3.memEq noMemory_empty)
      (seg3.writes x2 (by simp [level4ExecutionWitnessStackSumWrites]))
      (seg3.agree decoderPreserved_level4ExecutionWitnessStackSumWrites_disjoint) seg3.retired
  exact ⟨after, ⟨seg3.trace, seg3.confined, seg3.writes, seg3.memEq noMemory_empty, seg3.atPc,
    seg3.reg x19 (rTypeResult .ADD (BitVec.ofNat 64 pre.left) (BitVec.ofNat 64 pre.right))
      (by simp), preserved⟩⟩

end BinaryFv.Zesu.MachineExecution
