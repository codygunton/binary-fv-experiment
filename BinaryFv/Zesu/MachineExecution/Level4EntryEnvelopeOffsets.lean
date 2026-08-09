import BinaryFv.Zesu.MachineExecution.Level4RequireU32LengthSteps
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4Contracts
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Seg

/-! # Remaining direct entry/envelope/offset instructions of `ssz_raw.decodeRaw`

The preceding prologue owns sixteen direct PCs.  The selected `requireU32Length` occurrence owns
three further PCs but is intentionally not counted in this parent-owned list.  These twenty-nine
literal PCs are therefore exactly the unfinished direct part of the reviewed forty-five-PC phase.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- Direct parent PCs after the prologue in the successful entry/envelope/offset route. -/
def level4EntryEnvelopeOffsetsRemainingDirectPcs : List Nat :=
  [ 0x10490, 0x10498
  , 0x104a8, 0x104ac, 0x104b0, 0x104b4, 0x104b8, 0x104bc, 0x104c0, 0x104c4
  , 0x104c8, 0x104cc, 0x104d0, 0x104d4, 0x104d8
  , 0x105d4, 0x105d8, 0x105dc, 0x105e0, 0x105e4, 0x105e8, 0x105ec, 0x105f0
  , 0x105f4, 0x105f8, 0x105fc, 0x10600, 0x10604, 0x10608 ]

abbrev Level4EntryEnvelopeOffsetsRemainingDirectPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4EntryEnvelopeOffsetsRemainingDirectPcs

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_count :
    level4EntryEnvelopeOffsetsRemainingDirectPcs.length = 29 := rfl

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_exact :
    decodeRawEntryEnvelopeOffsetsPcs =
      level4DecodeRawEntryProloguePcs ++ level4EntryEnvelopeOffsetsRemainingDirectPcs := rfl

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_subset_direct :
    level4EntryEnvelopeOffsetsRemainingDirectPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

theorem level4EntryEnvelopeOffsetsRemainingDirectPcs_subset_phase :
    level4EntryEnvelopeOffsetsRemainingDirectPcs.all decodeRawEntryEnvelopeOffsetsPcs.contains = true := by
  native_decide

/-- Direct consumer regression for the exact read-only `requireU32Length` leaf frame.  This is the
saved state later read by the raw-decoder epilogue, not an additional child premise. -/
theorem level4RequireU32LengthHandoff_preserves_saved_frame {margs : DecoderMachineArgs}
    {before after : State} {fromStep : Nat}
    {pre : Level4RequireU32LengthPre margs before}
    {stack : Nat} {ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64}
    (handoff : Level4RequireU32LengthHandoff fromStep before after pre)
    (saved : Level4DecodeRawPrologueSavedFrame before stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) :
    Level4DecodeRawPrologueSavedFrame after stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 := by
  rw [Level4DecodeRawPrologueSavedFrame] at saved ⊢
  simp only [SavedWordBytes] at saved ⊢
  rw [handoff.memory]
  exact saved

/-- Exact post-state of the parent-owned high-word acceptance branch at `0x10490`. -/
def level4EntryLengthHighWordBranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10490) (BitVec.ofNat 64 0x10498))
    (BitVec.ofNat 64 0x10498) retired

/-- The accepted `requireU32Length` result retires the actual parent `beqz a1, 0x10498`.
The branch owns the semantic split; the selected leaf only establishes the high-word fact. -/
structure Level4EntryLengthHighWordAcceptedHandoff (fromStep : Nat) (origin leafState after : State)
    (pre : Level4RequireU32LengthPre margs origin) : Prop where
  trace : Trace fromStep 1 leafState after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10498)
  resultBase : after.regs.get? x21 = some (BitVec.ofNat 64 pre.resultBase)
  preparedInvalidSszTag : after.regs.get? x10 = some (BitVec.ofNat 64 2)
  inputBase : after.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase)
  inputLength : after.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size)
  /-- The parent branch is read-only and composes with the selected leaf's read-only frame, so
  this reaches the prologue state rather than merely the branch's immediate predecessor. -/
  memory : after.mem = origin.mem
  writes : WritesOnlyRegs stepBookkeeping leafState after
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  decodeRawMachine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs after
  retired : RetiredCounterPresent after

/-- Sail proof of the accepted high-word parent branch.  This is the first parent-owned
instruction after the selected `requireU32Length` leaf, so it consumes that leaf's exact semantic
equivalence rather than assuming a branch outcome. -/
theorem level4_entry_length_high_word_accepts (fromStep : Nat) {before state : State}
    (pre : Level4RequireU32LengthPre margs before)
    (handoff : Level4RequireU32LengthHandoff fromStep before state pre)
    (accepted : meaningRequireU32Length margs.bytes = .ok ()) :
    ∃ after, Level4EntryLengthHighWordAcceptedHandoff (fromStep + 3) before state after pre := by
  have highZero : state.regs.get? x11 = some 0#64 := handoff.lengthSemantics.mp accepted
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ :=
    decoderDecodeContextOfDecoderAgree handoff.decodeRawMachine (Agree.refl state)
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x10490)
  have x11AtExecute : executeState.regs.get? x11 = some 0#64 :=
    decoderExecuteState_get? highZero
  have condition : Runs (bTypeTaken (.Regidx 0#5) (.Regidx 11#5) .BEQ)
      executeState executeState true := by
    unfold bTypeTaken
    refine Runs.bind (rX_x11_run _ _ x11AtExecute) ?_
    refine Runs.bind (rX_x0_run _) ?_
    rfl
  obtain ⟨retired, run⟩ : ∃ retired, Runs (try_step (fromStep + 3) false) state
      (level4EntryLengthHighWordBranchAfter state retired) false :=
    decoderBranchTakenStep handoff.decodeRawMachine (Agree.refl state) handoff.retired handoff.code
      (fromStep + 3) 0x10490 0x63 0x84 0x05 0x00 0x8#13 0#5 11#5 .BEQ
      (BitVec.ofNat 64 0x10498) handoff.pc condition
  have preserved : Agree decoderPreserved state
      (level4EntryLengthHighWordBranchAfter state retired) :=
    Agree.weaken (fun _ h => h.2)
      ((jumpRetirement_writes _ _ _ _).agree platformPreserved_disjoint)
  have branchMemory : (level4EntryLengthHighWordBranchAfter state retired).mem = state.mem := by
    simpa only [level4EntryLengthHighWordBranchAfter] using
      jumpRetirement_mem state (BitVec.ofNat 64 0x10490) (BitVec.ofNat 64 0x10498) retired
  have branchWrites : WritesOnlyRegs stepBookkeeping state
      (level4EntryLengthHighWordBranchAfter state retired) := by
    simpa only [level4EntryLengthHighWordBranchAfter] using
      jumpRetirement_writes state (BitVec.ofNat 64 0x10490) (BitVec.ofNat 64 0x10498) retired
  refine ⟨level4EntryLengthHighWordBranchAfter state retired,
    ⟨Trace.one (fromStep + 3) _ _ run, ?_, ?_, ?_, ?_, ?_, ?_, branchWrites, ?_, ?_, ?_⟩⟩
  · simp [level4EntryLengthHighWordBranchAfter, tryStepControlFlowAfterRetired,
      tryStepControlFlowAfterTick, controlFlowJumpState, coreControlFlowNextState,
      tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]
  · exact ((jumpRetirement_writes state _ _ retired).get x21 (by decide)).trans handoff.resultBase
  · exact ((jumpRetirement_writes state _ _ retired).get x10 (by decide)).trans
      handoff.preparedInvalidSszTag
  · exact ((jumpRetirement_writes state _ _ retired).get x12 (by decide)).trans handoff.inputBase
  · exact ((jumpRetirement_writes state _ _ retired).get x13 (by decide)).trans handoff.inputLength
  · exact branchMemory.trans handoff.memory
  · rw [branchMemory]
    exact handoff.code
  · exact handoff.decodeRawMachine.mono preserved
      ⟨Sail.BitVec.addInt retired 1, by
        simp [level4EntryLengthHighWordBranchAfter, tryStepControlFlowAfterRetired,
          tryStepControlFlowAfterTick]⟩
  · exact ⟨Sail.BitVec.addInt retired 1, by
      simp [level4EntryLengthHighWordBranchAfter, tryStepControlFlowAfterRetired,
        tryStepControlFlowAfterTick]⟩

end BinaryFv.Zesu.MachineExecution
