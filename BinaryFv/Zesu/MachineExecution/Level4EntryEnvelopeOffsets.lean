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
open BinaryFv.RiscV.Sep

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

/-! ## Ordinary-input header setup

The six words at `0x10498` through `0x104b8` are the direct parent corridor for an ordinary
input pointer.  The second, byte-reading corridor starts at `0x104bc`; it deliberately remains
outside this register-only segment until the caller-derived input/save-area adapter provides its
input snapshot.
-/

/-- Exact direct-parent PCs before the first raw-header byte load. -/
def level4EntryEnvelopeHeaderSetupPcs : List Nat :=
  [0x10498, 0x104a8, 0x104ac, 0x104b0, 0x104b4, 0x104b8]

abbrev Level4EntryEnvelopeHeaderSetupPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4EntryEnvelopeHeaderSetupPcs

theorem level4EntryEnvelopeHeaderSetupPcs_subset_direct :
    level4EntryEnvelopeHeaderSetupPcs.all decodeRawDirectPcs.contains = true := by
  native_decide

theorem level4EntryEnvelopeHeaderSetupPcs_subset_phase :
    level4EntryEnvelopeHeaderSetupPcs.all decodeRawEntryEnvelopeOffsetsPcs.contains = true := by
  native_decide

private theorem level4_entry_header_setup_owned {pc : Nat}
    (member : pc ∈ level4EntryEnvelopeHeaderSetupPcs) :
    Level4EntryEnvelopeHeaderSetupPcs (BitVec.ofNat 64 pc) := by
  simp only [level4EntryEnvelopeHeaderSetupPcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- Registers written by the ordinary-input setup corridor. -/
def level4EntryEnvelopeHeaderSetupWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x9 ∨ r = x20 ∨ r = x10

private theorem decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4EntryEnvelopeHeaderSetupWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with bookkeeping | rfl | rfl | rfl
  · exact platformPreserved_disjoint r platform bookkeeping
  all_goals simp [platformPreserved] at platform

private theorem level4_entry_header_setup_length_condition (state : State) (length : Nat)
    (lengthValue : state.regs.get? x13 = some (BitVec.ofNat 64 length))
    (tagValue : state.regs.get? x10 = some (BitVec.ofNat 64 2))
    (lengthFits : length < 2 ^ 64) (twoBytes : 2 ≤ length) :
    Runs (bTypeTaken (.Regidx 10#5) (.Regidx 13#5) .BGEU)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10498))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10498))
      true := by
  unfold bTypeTaken
  refine Runs.bind (rX_x13_run _ _ (decoderExecuteState_get? lengthValue)) ?_
  refine Runs.bind (rX_x10_run _ _ (decoderExecuteState_get? tagValue)) ?_
  simp only [zopz0zKzJ_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lengthFits, Nat.mod_eq_of_lt (by omega : 2 < 2 ^ 64)]
  have comparison : (Int.ofNat length ≥b Int.ofNat 2) = true := by
    simpa only [decide_eq_true_eq] using Int.ofNat_le.mpr twoBytes
  rw [comparison]
  rfl

private theorem level4_entry_header_setup_nonstatic_condition (state : State) (inputBase : Nat)
    (inputValue : state.regs.get? x12 = some (BitVec.ofNat 64 inputBase))
    (staticValue : state.regs.get? x10 = some (BitVec.ofNat 64 0x142e0))
    (ordinaryInput : BitVec.ofNat 64 inputBase ≠ BitVec.ofNat 64 0x142e0) :
    Runs (bTypeTaken (.Regidx 10#5) (.Regidx 12#5) .BEQ)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104b8))
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104b8))
      false := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run _ _ (decoderExecuteState_get? inputValue)) ?_
  refine Runs.bind (rX_x10_run _ _ (decoderExecuteState_get? staticValue)) ?_
  have unequal : (BitVec.ofNat 64 inputBase == BitVec.ofNat 64 0x142e0) = false := by
    simpa using ordinaryInput
  rw [unequal]
  rfl

private theorem level4_entry_addi_zero (value : BitVec 64) :
    iTypeResult .ADDI 0#12 value = value := by
  unfold iTypeResult
  rw [show sign_extend (0#12) = (0#64) by decide]
  simp

private theorem level4_wX_x20_run (state : State) (value : BitVec 64) :
    Runs (wX_bits (.Regidx 20#5) value) state { state with regs := state.regs.insert x20 value } () := by
  have index : (Sail.BitVec.toNatInt 20#5).toNat = 20 := by decide
  unfold Runs
  simp [wX_bits, wX, PreSail.writeReg, index, EStateM.run, EStateM.bind, EStateM.modifyGet,
    EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
    xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
    encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
    LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]

private theorem level4_entry_header_setup_move_link_step {base state : State}
    (machine : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104a8))
    (linkValue : state.regs.get? x1 = some link) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104a8) stepRetired x9 link) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x104a8 0x93 0x84 0x00 0x00 0#12 1#5 9#5 .ADDI atPc
    (rX_x1_run _ _ (decoderExecuteState_get? linkValue)) (by
      rw [level4_entry_addi_zero]
      exact wX_x9_run
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104a8)) link)
    (pcIn := ⟨level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs]),
      by native_decide⟩)

private theorem level4_entry_header_setup_move_input_step {base state : State}
    (machine : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104ac))
    (inputValue : state.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104ac) stepRetired x20
        (BitVec.ofNat 64 margs.inputBase)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x104ac 0x13 0x0a 0x06 0x00 0#12 12#5 20#5 .ADDI atPc
    (rX_x12_run _ _ (decoderExecuteState_get? inputValue)) (by
      rw [level4_entry_addi_zero]
      exact level4_wX_x20_run
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104ac))
        (BitVec.ofNat 64 margs.inputBase))
    (pcIn := ⟨level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs]),
      by native_decide⟩)

private theorem level4_entry_header_setup_page_step {base state : State}
    (machine : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104b0)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104b0) stepRetired x10
        (BitVec.ofNat 64 0x144b0)) false := by
  exact decoderAuipcStepOfDecoderAgree machine agree retired code stepNo
    0x104b0 0x17 0x45 0x00 0x00 0x00004#20 10#5 atPc (by
      simpa [show BitVec.ofNat 64 0x104b0 +
          sign_extend (m := 64) (0x00004#20 ++ 0x000#12) = BitVec.ofNat 64 0x144b0 by decide]
        using wX_x10_run
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104b0))
          (BitVec.ofNat 64 0x144b0))
    (pcIn := ⟨level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs]),
      by native_decide⟩)

private theorem level4_entry_header_setup_static_pointer_step {base state : State}
    (machine : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104b4))
    (pageValue : state.regs.get? x10 = some (BitVec.ofNat 64 0x144b0)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104b4) stepRetired x10
        (BitVec.ofNat 64 0x142e0)) false := by
  exact decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x104b4 0x13 0x05 0x05 0xe3 0xe30#12 10#5 10#5 .ADDI atPc
    (rX_x10_run _ _ (decoderExecuteState_get? pageValue)) (by
      simpa [iTypeResult] using wX_x10_run
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x104b4))
        (BitVec.ofNat 64 0x142e0))
    (pcIn := ⟨level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs]),
      by native_decide⟩)

structure Level4EntryEnvelopeHeaderSetupPre (margs : DecoderMachineArgs) (state : State) where
  decodeRawMachine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs state
  machine : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10498)
  resultTag : state.regs.get? x10 = some (BitVec.ofNat 64 2)
  inputBase : state.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase)
  inputLength : state.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size)
  inputLengthFits : margs.bytes.size < 2 ^ 64
  inputAtLeastTwo : 2 ≤ margs.bytes.size
  link : BitVec 64
  linkValue : state.regs.get? x1 = some link
  ordinaryInput : BitVec.ofNat 64 margs.inputBase ≠ BitVec.ofNat 64 0x142e0
  retired : RetiredCounterPresent state

structure Level4EntryEnvelopeHeaderSetupHandoff (fromStep : Nat) (before after : State)
    (pre : Level4EntryEnvelopeHeaderSetupPre margs before) : Prop where
  trace : Trace fromStep 6 before after
  confined : ConfinedPrefix Level4EntryEnvelopeHeaderSetupPcs (fun _ => False)
    (fun _ _ _ _ _ => False) fromStep 6 before after
  writes : WritesOnlyRegs level4EntryEnvelopeHeaderSetupWrites before after
  memory : after.mem = before.mem
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x104bc)
  savedLink : after.regs.get? x9 = some pre.link
  inputPointer : after.regs.get? x20 = some (BitVec.ofNat 64 margs.inputBase)
  inputBase : after.regs.get? x12 = some (BitVec.ofNat 64 margs.inputBase)
  inputLength : after.regs.get? x13 = some (BitVec.ofNat 64 margs.bytes.size)
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  decodeRawMachine : DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs after
  retired : RetiredCounterPresent after

/-- Sail executes the ordinary-input parent corridor from the post-`requireU32Length` length
gate to the first raw-header byte read.  Its endpoint intentionally carries no input-memory claim:
the pending caller-derived adapter is responsible for connecting that snapshot across the prologue. -/
theorem level4_entry_envelope_header_setup
    (pre : Level4EntryEnvelopeHeaderSetupPre margs state) (fromStep : Nat) :
    ∃ after, Level4EntryEnvelopeHeaderSetupHandoff fromStep state after pre := by
  let seg0 := Seg.nil Level4EntryEnvelopeHeaderSetupPcs (fun _ => False) (fun _ _ _ _ _ => False)
    level4EntryEnvelopeHeaderSetupWrites noMemory fromStep pre.retired pre.atPc
  obtain ⟨afterLength, seg1⟩ := seg0.stepJump (BitVec.ofNat 64 0x104a8)
    (level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs])) (by simp)
    (decoderBranchTakenStep pre.machine (Agree.refl state) seg0.retired pre.code fromStep
      0x10498 0x63 0xf8 0xa6 0x00 0x10#13 10#5 13#5 .BGEU (BitVec.ofNat 64 0x104a8)
      seg0.atPc (level4_entry_header_setup_length_condition state margs.bytes.size pre.inputLength
        pre.resultTag pre.inputLengthFits pre.inputAtLeastTwo)
      (pcIn := ⟨level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs]),
        by native_decide⟩))
    (by intro r h; exact Or.inl h) (by intro p hp; cases hp)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterLength.mem := by
    rw [seg1.memEq noMemory_empty]
    exact pre.code
  have machine1 : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs afterLength :=
    pre.machine.mono (seg1.agree decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint)
      seg1.retired
  obtain ⟨afterLink, seg2⟩ := seg1.step
    (level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs])) (by simp) x9
    pre.link (BitVec.ofNat 64 0x104ac)
    (level4_entry_header_setup_move_link_step machine1 (Agree.refl afterLength) seg1.retired code1
      (fromStep + 1) seg1.atPc
      ((seg1.get x1 (by simp [level4EntryEnvelopeHeaderSetupWrites])).trans pre.linkValue))
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4EntryEnvelopeHeaderSetupWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully afterLink.mem := by
    rw [seg2.memEq noMemory_empty]
    exact pre.code
  have machine2 : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs afterLink :=
    pre.machine.mono (seg2.agree decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint)
      seg2.retired
  obtain ⟨afterInput, seg3⟩ := seg2.step
    (level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs])) (by simp) x20
    (BitVec.ofNat 64 margs.inputBase) (BitVec.ofNat 64 0x104b0)
    (level4_entry_header_setup_move_input_step machine2 (Agree.refl afterLink) seg2.retired code2
      (fromStep + 2) seg2.atPc
      ((seg2.get x12 (by simp [level4EntryEnvelopeHeaderSetupWrites])).trans pre.inputBase))
    (by decide) (by intro r h; exact Or.inl h)
    (by simp [level4EntryEnvelopeHeaderSetupWrites]) (by decide) (by decide)
    (by exact of_decide_eq_true rfl)
  have code3 : Artifacts.programImage.fileBytesLoadedFaithfully afterInput.mem := by
    rw [seg3.memEq noMemory_empty]
    exact pre.code
  have machine3 : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs afterInput :=
    pre.machine.mono (seg3.agree decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint)
      seg3.retired
  obtain ⟨afterPage, seg4⟩ :=
    (seg3.forget (kv' := [⟨x20, BitVec.ofNat 64 margs.inputBase⟩, ⟨x9, pre.link⟩]) (by simp)).step
      (level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs])) (by simp) x10
      (BitVec.ofNat 64 0x144b0) (BitVec.ofNat 64 0x104b4)
      (level4_entry_header_setup_page_step machine3 (Agree.refl afterInput) seg3.retired code3
        (fromStep + 3) seg3.atPc)
      (by decide) (by intro r h; exact Or.inl h)
      (by simp [level4EntryEnvelopeHeaderSetupWrites]) (by decide) (by decide)
      (by exact of_decide_eq_true rfl)
  have code4 : Artifacts.programImage.fileBytesLoadedFaithfully afterPage.mem := by
    rw [seg4.memEq noMemory_empty]
    exact pre.code
  have machine4 : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs afterPage :=
    pre.machine.mono (seg4.agree decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint)
      seg4.retired
  obtain ⟨afterStatic, seg5⟩ :=
    (seg4.forget (kv' := [⟨x20, BitVec.ofNat 64 margs.inputBase⟩, ⟨x9, pre.link⟩]) (by simp)).step
      (level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs])) (by simp) x10
      (BitVec.ofNat 64 0x142e0) (BitVec.ofNat 64 0x104b8)
      (level4_entry_header_setup_static_pointer_step machine4 (Agree.refl afterPage) seg4.retired code4
        (fromStep + 4) seg4.atPc (seg4.reg x10 (BitVec.ofNat 64 0x144b0) (by simp)))
      (by decide) (by intro r h; exact Or.inl h)
      (by simp [level4EntryEnvelopeHeaderSetupWrites]) (by decide) (by decide)
      (by exact of_decide_eq_true rfl)
  have code5 : Artifacts.programImage.fileBytesLoadedFaithfully afterStatic.mem := by
    rw [seg5.memEq noMemory_empty]
    exact pre.code
  have machine5 : DecoderMachinePre Level4EntryEnvelopeHeaderSetupPcs margs afterStatic :=
    pre.machine.mono (seg5.agree decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint)
      seg5.retired
  obtain ⟨after, seg6⟩ := seg5.stepFallThrough (BitVec.ofNat 64 0x104bc)
    (level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs])) (by simp)
    (decoderBranchNotTakenStep machine5
      (Agree.refl afterStatic) seg5.retired code5
      (fromStep + 5) 0x104b8 0x63 0x0c 0xa6 0x00 0x18#13 10#5 12#5 .BEQ seg5.atPc
      (level4_entry_header_setup_nonstatic_condition afterStatic margs.inputBase
        ((seg5.get x12 (by simp [level4EntryEnvelopeHeaderSetupWrites])).trans pre.inputBase)
        (seg5.reg x10 (BitVec.ofNat 64 0x142e0) (by simp)) pre.ordinaryInput)
      (pcIn := ⟨level4_entry_header_setup_owned (by simp [level4EntryEnvelopeHeaderSetupPcs]),
        by native_decide⟩))
    (by intro r h; exact Or.inl h) (by exact of_decide_eq_true rfl)
  refine ⟨after, ⟨seg6.trace, seg6.confined, seg6.writes, seg6.memEq noMemory_empty, seg6.atPc,
    seg6.reg x9 pre.link (by simp), seg6.reg x20 (BitVec.ofNat 64 margs.inputBase) (by simp),
    (seg6.get x12 (by simp [level4EntryEnvelopeHeaderSetupWrites])).trans pre.inputBase,
    (seg6.get x13 (by simp [level4EntryEnvelopeHeaderSetupWrites])).trans pre.inputLength, ?_, ?_,
    seg6.retired⟩⟩
  · rw [seg6.memEq noMemory_empty]
    exact pre.code
  · exact pre.decodeRawMachine.mono
      (seg6.agree decoderPreserved_level4EntryEnvelopeHeaderSetupWrites_disjoint) seg6.retired

/-! ## First ordinary-input header byte -/

/-- The first parent-owned byte read after the header setup. -/
def level4EntryHeaderFirstReadPcs : List Nat := [0x104bc]

abbrev Level4EntryHeaderFirstReadPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4EntryHeaderFirstReadPcs

theorem level4EntryHeaderFirstReadPcs_subset_direct :
    level4EntryHeaderFirstReadPcs.all decodeRawDirectPcs.contains = true := by native_decide

theorem level4EntryHeaderFirstReadPcs_subset_phase :
    level4EntryHeaderFirstReadPcs.all decodeRawEntryEnvelopeOffsetsPcs.contains = true := by native_decide

private theorem level4_entry_header_first_read_owned :
    Level4EntryHeaderFirstReadPcs (BitVec.ofNat 64 0x104bc) := by native_decide

private theorem level4_entry_header_first_read_machine_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x104bc) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

/-- The first header read consumes the caller-derived input snapshot retained in the Level 4
parent frame.  The length gate has already established the required two-byte lower bound. -/
theorem level4_entry_header_first_lbu {margs : DecoderMachineArgs} {origin state : State}
    (frame : Level4DecodeRawParentFrame margs origin state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104bc))
    (inputPointer : state.regs.get? x20 = some (BitVec.ofNat 64 margs.inputBase))
    (inputAtLeastTwo : 2 ≤ margs.bytes.size) (inputFits : margs.inputBase + margs.bytes.size ≤ 2 ^ 64)
    (stepNo : Nat) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x104bc) retired x10
        (BitVec.ofNat 64 (margs.bytes[0]'(by omega)).toNat)) false := by
  rcases frame.invariant with ⟨entry, -, -, -, -, inputMemory, -, -, code, machine, retired⟩
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
    (BitVec.ofNat 64 0x104bc)
  let address := BitVec.ofNat 64 margs.inputBase
  have inputBound : 0 < margs.bytes.size := by omega
  have inputBaseFits : margs.inputBase < 2 ^ 64 := by omega
  have inputAtExecute : executeState.regs.get? x20 = some (BitVec.ofNat 64 margs.inputBase) := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, inputPointer]
  obtain ⟨mstatusBits, mstatusRead, mprvZero⟩ := machine.mstatus
  obtain ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩ := machine.mseccfg
  have mstatusAtExecute : executeState.regs.get? mstatus = some mstatusBits := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, mstatusRead]
  have privilegeAtExecute : executeState.regs.get? cur_privilege = some Privilege.Machine := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, machine.normal.2.1]
  have mseccfgAtExecute : executeState.regs.get? Register.mseccfg = some mseccfgBits := by
    simp [executeState, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
      Std.ExtDHashMap.get?_insert, mseccfgRead]
  have addressRun : Runs
      (get_transformed_data_addr (.Regidx 20#5) (sign_extend (m := 64) 0#12)
        (MemoryAccessType.Load mem_payload.Data) 1)
      executeState executeState (.Ext_DataAddr_OK (virtaddr.Virtaddr address)) := by
    have addressEq : BitVec.ofNat 64 margs.inputBase + sign_extend (m := 64) 0#12 = address := by
      rw [show sign_extend (m := 64) 0#12 = 0#64 by decide]
      simp [address]
    rw [← addressEq]
    exact get_transformed_data_addr_machine_load_run executeState (.Regidx 20#5)
      (BitVec.ofNat 64 margs.inputBase) (sign_extend (m := 64) 0#12) mstatusBits mseccfgBits
      (rX_x20_run executeState _ inputAtExecute) mstatusAtExecute privilegeAtExecute mprvZero
      mseccfgAtExecute pmmDisabled
  have executeAgree : Agree platformPreserved state executeState :=
    agree_decoderExecuteState state (BitVec.ofNat 64 0x104bc)
  have allowed : DecoderAccessRange (DecoderReadableByte margs) address 1 := by
    refine ⟨by decide, ?_, ?_⟩
    · simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits]
      omega
    · intro index indexLt
      have indexZero : index = 0 := by omega
      subst index
      right
      left
      have addressNat : address.toNat = margs.inputBase := by
        simp [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits]
      rw [addressNat]
      exact ⟨Nat.le_refl _, by omega⟩
  obtain ⟨physAccess, loadNoMMIO⟩ := machine.dataAccess.load executeState address 1
    (Agree.weaken (fun _ preserved => preserved.2) executeAgree) allowed (by simp [is_aligned_paddr])
  let inputByte := margs.bytes[0]'inputBound
  have memoryByte : ∀ index (indexLt : index < (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)).length),
      executeState.mem.get? (address.toNat + index) =
        some ((leBytes 1 (BitVec.ofNat 8 inputByte.toNat))[index]'(by
          simpa only [leBytes_length] using indexLt)) := by
    intro index indexLt
    rw [leBytes_length] at indexLt
    have indexZero : index = 0 := by omega
    subst index
    simpa [executeState, address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt inputBaseFits,
      leBytes, inputByte] using inputMemory 0 inputBound
  have readMemory : Runs (vmem_read (.Regidx 20#5) (sign_extend (m := 64) 0#12) 1
      (MemoryAccessType.Load mem_payload.Data) false false false) executeState executeState
      (.Ok (BitVec.ofNat 8 inputByte.toNat)) := by
    have hread := mem_read_load_run executeState address mstatusBits
      (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)) mstatusAtExecute privilegeAtExecute mprvZero
      memoryByte physAccess loadNoMMIO
    rw [show leWord (leBytes 1 (BitVec.ofNat 8 inputByte.toNat)) = BitVec.ofNat 8 inputByte.toNat
      from by simpa using leWord_leBytes 1 (BitVec.ofNat 8 inputByte.toNat)] at hread
    exact vmem_read_byte_run executeState (.Regidx 20#5) (sign_extend (m := 64) 0#12) address
      mstatusBits (BitVec.ofNat 8 inputByte.toNat) mstatusAtExecute privilegeAtExecute mprvZero
      addressRun (is_aligned_vaddr_one _) hread
  exact decoderLoadStepOfDecoderAgree machine (Agree.refl state) retired code stepNo
    0x104bc 0x03 0x45 0x0a 0x00 0#12 20#5 10#5 true 1 (BitVec.ofNat 8 inputByte.toNat)
    atPc readMemory (by
      have zeroExtend : extend_value true (BitVec.ofNat 8 inputByte.toNat) =
          BitVec.ofNat 64 inputByte.toNat := by
        apply BitVec.eq_of_toNat_eq
        simp [extend_value, zero_extend, Sail.BitVec.zeroExtend]
      rw [zeroExtend]
      exact wX_x10_run executeState (BitVec.ofNat 64 inputByte.toNat))
    (pcIn := ⟨level4_entry_header_first_read_machine_owned, by native_decide⟩)

/-! ## First-header-byte zero gate -/

/-- The parent-owned branch which rejects a nonzero first header byte. -/
def level4EntryHeaderFirstZeroBranchPcs : List Nat := [0x104c0]

abbrev Level4EntryHeaderFirstZeroBranchPcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4EntryHeaderFirstZeroBranchPcs

theorem level4EntryHeaderFirstZeroBranchPcs_subset_direct :
    level4EntryHeaderFirstZeroBranchPcs.all decodeRawDirectPcs.contains = true := by native_decide

theorem level4EntryHeaderFirstZeroBranchPcs_subset_phase :
    level4EntryHeaderFirstZeroBranchPcs.all decodeRawEntryEnvelopeOffsetsPcs.contains = true := by
  native_decide

private theorem level4_entry_header_first_zero_branch_machine_owned :
    RegisterWriteStep.decodeRawExecutionPcs (BitVec.ofNat 64 0x104c0) := by
  apply functionInstanceExecutionPcs_iff_ranges.mpr
  apply RegionPcs.iff_inRanges.mpr
  native_decide

/-- Sail executes the fall-through of `bnez a0, 0x1049c`: a zero first header byte reaches the
second byte read at `0x104c4`. -/
theorem level4_entry_header_first_zero_branch {margs : DecoderMachineArgs} {origin state : State}
    (frame : Level4DecodeRawParentFrame margs origin state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x104c0))
    (firstByteZero : state.regs.get? x10 = some (0#64)) (stepNo : Nat) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
          (BitVec.ofNat 64 0x104c0))
        (BitVec.ofNat 64 0x104c4) retired) false := by
  rcases frame.invariant with ⟨entry, -, -, -, -, inputMemory, -, -, code, machine, retired⟩
  exact decoderBranchNotTakenStep machine (Agree.refl state) retired code stepNo
    0x104c0 0xe3 0x1e 0x05 0xfc 0x1fdc#13 0#5 10#5 .BNE atPc
    (by
      unfold bTypeTaken
      refine Runs.bind (rX_x10_run _ _ (decoderExecuteState_get? firstByteZero)) ?_
      refine Runs.bind (rX_x0_run _) ?_
      rfl)
    (pcIn := ⟨level4_entry_header_first_zero_branch_machine_owned, by native_decide⟩)

end BinaryFv.Zesu.MachineExecution
