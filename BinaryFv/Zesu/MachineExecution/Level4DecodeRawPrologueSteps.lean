import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.Zesu.MachineExecution.Level2WrapperSteps
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Seg
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineContract
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

/-! # Exact entry prologue for the emitted raw decoder -/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

/-- The sixteen parent-owned instructions before `requireU32Length` begins at `0x10484`. -/
def level4DecodeRawEntryProloguePcs : List Nat :=
  [ 0x10444, 0x10448, 0x1044c, 0x10450, 0x10454, 0x10458, 0x1045c, 0x10460
  , 0x10464, 0x10468, 0x1046c, 0x10470, 0x10474, 0x10478, 0x1047c, 0x10480 ]

/-- The reviewed, literal parent scope.  `0x10484` is deliberately absent: it is the selected
`requireU32Length` child entry, not a prologue instruction. -/
abbrev Level4DecodeRawEntryProloguePcs (pc : BitVec 64) : Prop :=
  pc.toNat ∈ level4DecodeRawEntryProloguePcs

theorem level4DecodeRawEntryProloguePcs_exact :
    level4DecodeRawEntryProloguePcs =
      [ 0x10444, 0x10448, 0x1044c, 0x10450, 0x10454, 0x10458, 0x1045c, 0x10460
      , 0x10464, 0x10468, 0x1046c, 0x10470, 0x10474, 0x10478, 0x1047c, 0x10480 ] := rfl

theorem level4DecodeRawEntryProloguePcs_count : level4DecodeRawEntryProloguePcs.length = 16 := rfl

theorem level4DecodeRawEntryProloguePcs_subset_direct :
    level4DecodeRawEntryProloguePcs.all decodeRawDirectPcs.contains = true := by native_decide

theorem level4DecodeRawEntryProloguePcs_subset_entryEnvelopeOffsets :
    level4DecodeRawEntryProloguePcs.all decodeRawEntryEnvelopeOffsetsPcs.contains = true := by
  native_decide

abbrev Level4DecodeRawEntryPrologueExit : BitVec 64 → Prop := fun _ => False

abbrev Level4DecodeRawEntryPrologueChildSummary :
    FunctionInstanceId → Nat → Nat → State → State → Prop := fun _ _ _ _ _ => False

local macro "owned_pc" : tactic => `(tactic| native_decide)

/-- The thirteen dwords written by the prologue, in the exact offsets read by the epilogue. -/
def Level4DecodeRawPrologueSavedFrame (state : State) (stack : Nat)
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

private theorem level4_prologue_saved_frame_of_mem_eq {before after : State} {stack : Nat}
    {ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64}
    (saved : Level4DecodeRawPrologueSavedFrame before stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    (memory : after.mem = before.mem) :
    Level4DecodeRawPrologueSavedFrame after stack ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 := by
  rw [Level4DecodeRawPrologueSavedFrame] at saved ⊢
  simp only [SavedWordBytes] at saved ⊢
  rw [memory]
  exact saved

/-- Caller facts and concrete machine layout required at the raw decoder's emitted entry.  The
callee-saved values are not an ABI assumption: `frame` is exactly the caller-derived
`DecodeRawEntryFrame` used by the two real call routes. -/
structure Level4DecodeRawEntryProloguePre (margs : DecoderMachineArgs) (state : State) where
  machine : DecoderMachinePre
    Level4DecodeRawEntryProloguePcs margs state
  code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem
  atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10444)
  frame : DecodeRawEntryFrame state
  ra : BitVec 64
  raValue : state.regs.get? x1 = some ra
  a1 : BitVec 64
  a1Value : state.regs.get? x11 = some a1
  stack : Nat
  entryStackValue : state.regs.get? x2 = some (BitVec.ofNat 64 (stack + 0x7f0))
  postStack : Nat
  postStackEq : stack = postStack + 0x690
  stackFits : stack + 0x7f0 < 2 ^ 64
  saveAreaWritable : ∀ index, index < 104 → canonicalContractParams.env.stack (stack + 0x788 + index)
  slotAligned : ∀ offset, 0x788 ≤ offset → offset ≤ 0x7e8 → offset % 8 = 0 →
    is_aligned_vaddr (virtaddr.Virtaddr (BitVec.ofNat 64 (stack + offset))) 8 = true

/-- The prologue writes only its two modified architectural registers plus normal retirement
bookkeeping; stores themselves modify memory but no additional register. -/
def level4DecodeRawEntryPrologueWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x2 ∨ r = x8

/-- The handoff to the selected entry/envelope/offset phase.  It has no Level 4 hypothesis: the
trace below produces every field from the caller-derived entry object. -/
structure Level4DecodeRawEntryEnvelopeOffsetsHandoff (fromStep : Nat) (before after : State)
    (pre : Level4DecodeRawEntryProloguePre margs before)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64) : Prop where
  trace : Trace fromStep 16 before after
  confined : ConfinedPrefix Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
    Level4DecodeRawEntryPrologueChildSummary fromStep 16 before after
  writes : WritesOnlyRegs level4DecodeRawEntryPrologueWrites before after
  saved : Level4DecodeRawPrologueSavedFrame after pre.stack pre.ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
    s10 s11
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10484)
  sp : after.regs.get? x2 = some (BitVec.ofNat 64 pre.postStack)
  s0 : after.regs.get? x8 = some pre.a1
  code : Artifacts.programImage.fileBytesLoadedFaithfully after.mem
  machine : DecoderMachinePre
    Level4DecodeRawEntryProloguePcs margs after
  retired : RetiredCounterPresent after

private theorem level4_prologue_bookkeeping (r : Register) (h : stepBookkeeping r) :
    level4DecodeRawEntryPrologueWrites r := Or.inl h

private theorem decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint :
    RegSet.Disjoint decoderPreserved level4DecodeRawEntryPrologueWrites := by
  intro r hr hw
  rcases hr with ⟨notLink, platform⟩
  rcases hw with book | rfl | rfl
  · exact platformPreserved_disjoint r platform book
  · simp [platformPreserved] at platform
  · simp [platformPreserved] at platform

private theorem level4_prologue_stack_lt (pre : Level4DecodeRawEntryProloguePre margs state) :
    pre.stack < 2 ^ 64 := by
  have h := pre.stackFits
  omega

private theorem level4_prologue_stack_address_toNat (pre : Level4DecodeRawEntryProloguePre margs state)
    {offset : Nat} (bound : offset + 8 ≤ 0x7f0) :
    (BitVec.ofNat 64 (pre.stack + offset)).toNat = pre.stack + offset := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have h := pre.stackFits
  omega

private theorem level4_prologue_stack_address_eq (stack offset : Nat)
    (extend : sign_extend (m := 64) (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset) :
    BitVec.ofNat 64 stack + sign_extend (m := 64) (BitVec.ofNat 12 offset) =
      BitVec.ofNat 64 (stack + offset) := by
  rw [extend, ← BitVec.ofNat_add]

private theorem level4_prologue_first_frame_value (stack : Nat) :
    iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (stack + 0x7f0)) = BitVec.ofNat 64 stack := by
  rw [show BitVec.ofNat 64 (stack + 0x7f0) =
    BitVec.ofNat 64 stack + BitVec.ofNat 64 0x7f0 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 stack = BitVec.ofNat 64 stack + BitVec.ofNat 64 0 by
    rw [← BitVec.ofNat_add]
    simp]
  unfold iTypeResult
  rw [show sign_extend (0x810#12) = (0xfffffffffffff810#64) by decide]
  bv_decide

private theorem level4_decode_raw_first_stack_step (pre : Level4DecodeRawEntryProloguePre margs state)
    (fromStep : Nat) :
    ∃ retired, Runs (try_step fromStep false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10444) retired x2
        (BitVec.ofNat 64 pre.stack)) false := by
  obtain ⟨retired, run⟩ := decoderITypeStepOfDecoderAgree pre.machine (Agree.refl state)
    pre.machine.retiredCounter pre.code fromStep 0x10444 0x13 0x01 0x01 0x81 0x810#12 2#5 2#5
    .ADDI pre.atPc
    (rX_x2_run _ _ (decoderExecuteState_get? pre.entryStackValue))
    (wX_x2_run _ (iTypeResult .ADDI 0x810#12 (BitVec.ofNat 64 (pre.stack + 0x7f0))))
    (pcIn := ⟨by native_decide, by native_decide⟩)
  rw [level4_prologue_first_frame_value] at run
  exact ⟨retired, run⟩

local macro "level4_gen_rx_run" idx:num " ↦ " reg:ident ", " name:ident : command =>
  `(private theorem $name (state : State) (value : BitVec 64)
      (stored : state.regs.get? $reg = some value) :
      Runs (rX_bits (.Regidx (BitVec.ofNat 5 $idx))) state state value := by
    have index : (Sail.BitVec.toNatInt (BitVec.ofNat 5 $idx)).toNat = $idx := by decide
    unfold Runs
    simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
      EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg])

level4_gen_rx_run 18 ↦ x18, level4_rX_x18_run
level4_gen_rx_run 19 ↦ x19, level4_rX_x19_run
level4_gen_rx_run 20 ↦ x20, level4_rX_x20_run
level4_gen_rx_run 21 ↦ x21, level4_rX_x21_run
level4_gen_rx_run 22 ↦ x22, level4_rX_x22_run
level4_gen_rx_run 23 ↦ x23, level4_rX_x23_run
level4_gen_rx_run 24 ↦ x24, level4_rX_x24_run
level4_gen_rx_run 25 ↦ x25, level4_rX_x25_run
level4_gen_rx_run 26 ↦ x26, level4_rX_x26_run
level4_gen_rx_run 27 ↦ x27, level4_rX_x27_run

private theorem level4_prologue_slot_writable (pre : Level4DecodeRawEntryProloguePre margs state)
    {offset : Nat} (lower : 0x788 ≤ offset) (upper : offset + 8 ≤ 0x7f0) :
    DecoderAccessRange DecoderWritableByte (BitVec.ofNat 64 (pre.stack + offset)) 8 := by
  have stackFits := pre.stackFits
  refine ⟨by decide, ?_, ?_⟩
  · rw [level4_prologue_stack_address_toNat pre (by omega)]
    omega
  · intro index indexBound
    rw [level4_prologue_stack_address_toNat pre (by omega)]
    rw [show pre.stack + offset + index = pre.stack + 0x788 + (offset - 0x788 + index) by omega]
    exact Or.inl (pre.saveAreaWritable (offset - 0x788 + index) (by omega))

private theorem level4_decode_raw_store_ra {base state : State}
    (pre : Level4DecodeRawEntryProloguePre margs base)
    (machine : DecoderMachinePre Level4DecodeRawEntryProloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10448))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stack))
    (raValue : state.regs.get? x1 = some pre.ra) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterMemoryWrite state (BitVec.ofNat 64 0x10448) stepRetired (pre.stack + 0x7e8)
        (width := 8) pre.ra) false := by
  obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
  have decode := wrapper_save_link_decode (tryStepControlFlowAfterIncrement state) privilege
    mseccfgBits mseccfgRead
  obtain ⟨stepRetired, run⟩ := wrapper_dword_store_step machine agree retired stepNo
    (BitVec.ofNat 64 0x10448) ⟨by owned_pc, by native_decide⟩ atPc
    0x23#8 0x34#8 0x11#8 0x7e#8 0x7e8#12 (.Regidx 1#5)
    (BitVec.ofNat 64 pre.stack) pre.ra (BitVec.ofNat 64 (pre.stack + 0x7e8)) stackValue
    (rX_x1_run _ _ (decoderExecuteState_get? raValue))
    (level4_prologue_stack_address_eq pre.stack 0x7e8 (by decide))
    (pre.slotAligned 0x7e8 (by omega) (by omega) (by decide))
    (level4_prologue_slot_writable pre (by omega) (by omega))
    (fetchFileInstruction state 0x10448 0x23 0x34 0x11 0x7e code
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide))
    (by unfold BaseInstructionEncoding; decide) decode
  have targetToNat := level4_prologue_stack_address_toNat pre (offset := 0x7e8) (by omega)
  exact ⟨stepRetired, by simpa [wrapperAfterDwordStore, afterMemoryWrite, targetToNat] using run⟩

local macro "level4_store_theorem " name:ident pc:num byte0:num byte1:num byte2:num byte3:num immediate:num source:num offset:num : command =>
  `(private theorem $name {margs : DecoderMachineArgs} {base state : State} (pre : Level4DecodeRawEntryProloguePre margs base)
      (machine : DecoderMachinePre Level4DecodeRawEntryProloguePcs margs base)
      (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
      (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
      (value : BitVec 64)
      (atPc : state.regs.get? PC = some (BitVec.ofNat 64 $pc))
      (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stack))
      (sourceRun : Runs (rX_bits (.Regidx (BitVec.ofNat 5 $source)))
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 $pc))
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 $pc)) value) :
      ∃ stepRetired, Runs (try_step stepNo false) state
        (afterMemoryWrite state (BitVec.ofNat 64 $pc) stepRetired (pre.stack + $offset)
          (width := 8) value) false := by
    obtain ⟨privilege, mseccfgBits, mseccfgRead⟩ := decoderDecodeContextOfDecoderAgree machine agree
    have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 $byte0) (BitVec.ofNat 8 $byte1)
        (BitVec.ofNat 8 $byte2) (BitVec.ofNat 8 $byte3)))
        (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state)
        (.STORE (BitVec.ofNat 12 $immediate, .Regidx (BitVec.ofNat 5 $source), .Regidx 2#5, 8)) := by
      decode_run
    obtain ⟨stepRetired, run⟩ := wrapper_dword_store_step machine agree retired stepNo
      (BitVec.ofNat 64 $pc) ⟨by owned_pc, by native_decide⟩ atPc
      (BitVec.ofNat 8 $byte0) (BitVec.ofNat 8 $byte1) (BitVec.ofNat 8 $byte2) (BitVec.ofNat 8 $byte3)
      (BitVec.ofNat 12 $immediate) (.Regidx (BitVec.ofNat 5 $source))
      (BitVec.ofNat 64 pre.stack) value (BitVec.ofNat 64 (pre.stack + $offset)) stackValue sourceRun
      (level4_prologue_stack_address_eq pre.stack $offset (by decide))
      (pre.slotAligned $offset (by omega) (by omega) (by decide))
      (level4_prologue_slot_writable pre (by omega) (by omega))
      (fetchFileInstruction state $pc $byte0 $byte1 $byte2 $byte3 code
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by decide))
      (by unfold BaseInstructionEncoding; decide) decode
    have targetToNat := level4_prologue_stack_address_toNat pre (offset := $offset) (by omega)
    exact ⟨stepRetired, by simpa [wrapperAfterDwordStore, afterMemoryWrite, targetToNat] using run⟩)

level4_store_theorem level4_decode_raw_store_s0 0x1044c 0x23 0x30 0x81 0x7e 0x7e0 8 0x7e0
level4_store_theorem level4_decode_raw_store_s1 0x10450 0x23 0x3c 0x91 0x7c 0x7d8 9 0x7d8
level4_store_theorem level4_decode_raw_store_s2 0x10454 0x23 0x38 0x21 0x7d 0x7d0 18 0x7d0
level4_store_theorem level4_decode_raw_store_s3 0x10458 0x23 0x34 0x31 0x7d 0x7c8 19 0x7c8
level4_store_theorem level4_decode_raw_store_s4 0x1045c 0x23 0x30 0x41 0x7d 0x7c0 20 0x7c0
level4_store_theorem level4_decode_raw_store_s5 0x10460 0x23 0x3c 0x51 0x7b 0x7b8 21 0x7b8
level4_store_theorem level4_decode_raw_store_s6 0x10464 0x23 0x38 0x61 0x7b 0x7b0 22 0x7b0
level4_store_theorem level4_decode_raw_store_s7 0x10468 0x23 0x34 0x71 0x7b 0x7a8 23 0x7a8
level4_store_theorem level4_decode_raw_store_s8 0x1046c 0x23 0x30 0x81 0x7b 0x7a0 24 0x7a0
level4_store_theorem level4_decode_raw_store_s9 0x10470 0x23 0x3c 0x91 0x79 0x798 25 0x798
level4_store_theorem level4_decode_raw_store_s10 0x10474 0x23 0x38 0xa1 0x79 0x790 26 0x790
level4_store_theorem level4_decode_raw_store_s11 0x10478 0x23 0x34 0xb1 0x79 0x788 27 0x788

private theorem level4_prologue_second_frame_value (postStack : Nat) :
    iTypeResult .ADDI 0x970#12 (BitVec.ofNat 64 (postStack + 0x690)) =
      BitVec.ofNat 64 postStack := by
  rw [show BitVec.ofNat 64 (postStack + 0x690) =
    BitVec.ofNat 64 postStack + BitVec.ofNat 64 0x690 by rw [← BitVec.ofNat_add]]
  rw [show BitVec.ofNat 64 postStack = BitVec.ofNat 64 postStack + BitVec.ofNat 64 0 by
    rw [← BitVec.ofNat_add]
    simp]
  unfold iTypeResult
  rw [show sign_extend (0x970#12) = (0xfffffffffffff970#64) by decide]
  bv_decide

private theorem level4_decode_raw_second_stack_step {base state : State}
    (pre : Level4DecodeRawEntryProloguePre margs base)
    (machine : DecoderMachinePre Level4DecodeRawEntryProloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1047c))
    (stackValue : state.regs.get? x2 = some (BitVec.ofNat 64 pre.stack)) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x1047c) stepRetired x2
        (BitVec.ofNat 64 pre.postStack)) false := by
  obtain ⟨stepRetired, run⟩ := decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x1047c 0x13 0x01 0x01 0x97 0x970#12 2#5 2#5 .ADDI atPc
    (rX_x2_run _ _ (decoderExecuteState_get? stackValue))
    (wX_x2_run _ (iTypeResult .ADDI 0x970#12 (BitVec.ofNat 64 pre.stack)))
    (pcIn := ⟨by owned_pc, by native_decide⟩)
  rw [pre.postStackEq, level4_prologue_second_frame_value] at run
  exact ⟨stepRetired, run⟩

private theorem level4_decode_raw_move_a1_step {base state : State}
    (pre : Level4DecodeRawEntryProloguePre margs base)
    (machine : DecoderMachinePre Level4DecodeRawEntryProloguePcs margs base)
    (agree : Agree decoderPreserved base state) (retired : RetiredCounterPresent state)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) (stepNo : Nat)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x10480))
    (a1Value : state.regs.get? x11 = some pre.a1) :
    ∃ stepRetired, Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x10480) stepRetired x8 pre.a1) false := by
  obtain ⟨stepRetired, run⟩ := decoderITypeStepOfDecoderAgree machine agree retired code stepNo
    0x10480 0x13 0x84 0x05 0x00 0#12 11#5 8#5 .ADDI atPc
    (rX_x11_run _ _ (decoderExecuteState_get? a1Value))
    (wX_x8_run _ (iTypeResult .ADDI 0#12 pre.a1))
    (pcIn := ⟨by owned_pc, by native_decide⟩)
  have value : iTypeResult .ADDI 0#12 pre.a1 = pre.a1 := by
    unfold iTypeResult
    rw [show sign_extend 0#12 = (0#64) by decide]
    simp
  rw [value] at run
  exact ⟨stepRetired, run⟩

private theorem level4_after_store_savedWord (state : State) (pc retired target data : BitVec 64)
    (base : Nat) (targetValue : target.toNat = base) :
    SavedWordBytes (afterMemoryWrite state pc retired target.toNat (width := 8) data) base data := by
  intro index bound
  rw [BinaryFv.RiscV.Sep.leBytes_length] at bound
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨
      index = 6 ∨ index = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [afterMemoryWrite, afterWriteBytes, afterByteWrites, targetValue,
      tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem_insert,
      BinaryFv.RiscV.Sep.leBytes, BinaryFv.RiscV.Sep.leBytes_length] <;> omega

private theorem level4_after_store_preserves_savedWord (state : State)
    (pc retired target data : BitVec 64) (targetBase savedBase : Nat) (value : BitVec 64)
    (targetValue : target.toNat = targetBase)
    (disjoint : targetBase + 8 ≤ savedBase ∨ savedBase + 8 ≤ targetBase)
    (saved : SavedWordBytes state savedBase value) :
    SavedWordBytes (afterMemoryWrite state pc retired target.toNat (width := 8) data) savedBase value := by
  intro index bound
  rw [BinaryFv.RiscV.Sep.leBytes_length] at bound
  refine (storeRetirement_mem_writes state pc (Sail.BitVec.addInt pc 4) retired target.toNat data
    (savedBase + index) ?_).trans (saved index bound)
  rintro ⟨lower, upper⟩
  rw [targetValue] at lower upper
  rcases disjoint with left | right <;> omega

/-- Saved frame words accumulated as a list while the prologue stores them.  This avoids a
quadratic, state-specific preservation proof: each new store transports the one list invariant. -/
def Level4DecodeRawSavedSlots (state : State) (stack : Nat) (slots : List (Nat × BitVec 64)) : Prop :=
  ∀ slot ∈ slots, SavedWordBytes state (stack + slot.1) slot.2

private theorem level4_savedSlots_store (state : State) (pc retired target data : BitVec 64)
    (stack offset : Nat) (targetValue : target.toNat = stack + offset)
    (slots : List (Nat × BitVec 64))
    (separated : ∀ slot ∈ slots, offset + 8 ≤ slot.1 ∨ slot.1 + 8 ≤ offset)
    (saved : Level4DecodeRawSavedSlots state stack slots) :
    Level4DecodeRawSavedSlots (afterMemoryWrite state pc retired target.toNat (width := 8) data) stack
      ((offset, data) :: slots) := by
  intro slot member
  rcases List.mem_cons.mp member with current | previous
  · rcases current with ⟨rfl, rfl⟩
    simpa [targetValue] using level4_after_store_savedWord state pc retired target data
      (stack + offset) targetValue
  · exact level4_after_store_preserves_savedWord state pc retired target data (stack + offset)
      (stack + slot.1) slot.2 targetValue (by
        rcases separated slot previous with left | right <;> omega)
      (saved slot previous)

private theorem level4_prologue_store_code (state : State) (pc retired : BitVec 64)
    (address : Nat) (data : BitVec 64)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (address + index))
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    Artifacts.programImage.fileBytesLoadedFaithfully
      (afterMemoryWrite state pc retired address (width := 8) data).mem := by
  have notFile : ∀ index : Fin 8,
      Artifacts.programImage.readFileByte? (address + index.val) = none :=
    fun index => canonicalStack_not_fileByte (writable index.val index.isLt)
  have written := fileBytesLoadedFaithfully_afterWriteBytes Artifacts.programImage
    (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) address data notFile
    (by simpa [coreControlFlowNextState, tryStepControlFlowAfterIncrement] using code)
  simpa [afterMemoryWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick] using written

private theorem level4_prologue_store_inside (pre : Level4DecodeRawEntryProloguePre margs state)
    (offset : Nat) (lower : 0x788 ≤ offset) (upper : offset + 8 ≤ 0x7f0) :
    ∀ other, pre.stack + offset ≤ other → other < pre.stack + offset + 8 → DecoderWritableByte other := by
  intro other low high
  left
  rw [show other = pre.stack + 0x788 + (offset - 0x788 + (other - (pre.stack + offset))) by omega]
  exact pre.saveAreaWritable _ (by omega)

private theorem level4_prologue_store_stack_writable
    (pre : Level4DecodeRawEntryProloguePre margs state) (offset : Nat)
    (lower : 0x788 ≤ offset) (upper : offset + 8 ≤ 0x7f0) :
    ∀ index, index < 8 → canonicalContractParams.env.stack (pre.stack + offset + index) := by
  intro index indexBound
  rw [show pre.stack + offset + index = pre.stack + 0x788 + (offset - 0x788 + index) by omega]
  exact pre.saveAreaWritable _ (by omega)

private theorem level4_decode_raw_prologue_first_save
    (pre : Level4DecodeRawEntryProloguePre margs state) (fromStep : Nat) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 after,
      Seg Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
      Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte
      [⟨x2, BitVec.ofNat 64 pre.stack⟩, ⟨x27, s11⟩, ⟨x26, s10⟩, ⟨x25, s9⟩, ⟨x24, s8⟩,
        ⟨x23, s7⟩, ⟨x22, s6⟩, ⟨x21, s5⟩, ⟨x20, s4⟩, ⟨x19, s3⟩, ⟨x18, s2⟩,
        ⟨x9, s1⟩, ⟨x8, s0⟩, ⟨x1, pre.ra⟩] fromStep 2 state after
      (BitVec.ofNat 64 0x1044c) ∧
      Level4DecodeRawSavedSlots after pre.stack [(0x7e8, pre.ra)] ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  obtain ⟨_, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, _, s0At, s1At, s2At,
    s3At, s4At, s5At, s6At, s7At, s8At, s9At, s10At, s11At⟩ := pre.frame
  let seg0 := Seg.nil Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
    Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte
    fromStep pre.machine.retiredCounter pre.atPc
  let seg0 := seg0.know x1 pre.ra pre.raValue
  let seg0 := seg0.know x8 s0 s0At
  let seg0 := seg0.know x9 s1 s1At
  let seg0 := seg0.know x18 s2 s2At
  let seg0 := seg0.know x19 s3 s3At
  let seg0 := seg0.know x20 s4 s4At
  let seg0 := seg0.know x21 s5 s5At
  let seg0 := seg0.know x22 s6 s6At
  let seg0 := seg0.know x23 s7 s7At
  let seg0 := seg0.know x24 s8 s8At
  let seg0 := seg0.know x25 s9 s9At
  let seg0 := seg0.know x26 s10 s10At
  let seg0 := seg0.know x27 s11 s11At
  obtain ⟨retired1, afterStack, hStack, seg1⟩ := seg0.stepWitness (by owned_pc) (by simp) x2
    (BitVec.ofNat 64 pre.stack) (BitVec.ofNat 64 0x10448)
    (level4_decode_raw_first_stack_step pre fromStep) (by decide)
    level4_prologue_bookkeeping (by simp [level4DecodeRawEntryPrologueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully afterStack.mem := by
    rw [hStack, afterRegisterWrite_mem]
    exact pre.code
  have agree1 : Agree decoderPreserved state afterStack :=
    seg1.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack1 := seg1.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have ra1 := seg1.reg x1 pre.ra (by simp)
  obtain ⟨retired2, afterRa, hRa, seg2⟩ := seg1.stepStoreWitness (pre.stack + 0x7e8) pre.ra
    (BitVec.ofNat 64 0x1044c) (by owned_pc) (by simp)
    (level4_decode_raw_store_ra pre pre.machine agree1 seg1.retired code1 (fromStep + 1)
      seg1.atPc stack1 ra1)
    (by decide) (level4_prologue_store_inside pre 0x7e8 (by omega) (by omega))
    level4_prologue_bookkeeping (by exact of_decide_eq_true rfl)
  have saved2 : Level4DecodeRawSavedSlots afterRa pre.stack [(0x7e8, pre.ra)] := by
    rw [hRa]
    let target := BitVec.ofNat 64 (pre.stack + 0x7e8)
    have targetValue : target.toNat = pre.stack + 0x7e8 :=
      level4_prologue_stack_address_toNat pre (offset := 0x7e8) (by omega)
    simpa [target, targetValue] using level4_savedSlots_store afterStack (BitVec.ofNat 64 0x10448)
      retired2 target pre.ra pre.stack 0x7e8 targetValue [] (by intro slot h; cases h)
      (by intro slot h; cases h)
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully afterRa.mem := by
    rw [hRa]
    exact level4_prologue_store_code afterStack (BitVec.ofNat 64 0x10448) retired2
      (pre.stack + 0x7e8) pre.ra
      (level4_prologue_store_stack_writable pre 0x7e8 (by omega) (by omega)) code1
  refine ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, afterRa, ?_, saved2, code2⟩
  change Seg Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
    Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte
    [⟨x2, BitVec.ofNat 64 pre.stack⟩, ⟨x27, s11⟩, ⟨x26, s10⟩, ⟨x25, s9⟩, ⟨x24, s8⟩,
      ⟨x23, s7⟩, ⟨x22, s6⟩, ⟨x21, s5⟩, ⟨x20, s4⟩, ⟨x19, s3⟩, ⟨x18, s2⟩,
      ⟨x9, s1⟩, ⟨x8, s0⟩, ⟨x1, pre.ra⟩] fromStep (0 + 1 + 1) state afterRa
      (BitVec.ofNat 64 0x1044c)
  exact seg2

private theorem level4_prologue_accumulate_store
    (seg : Seg Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
      Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte
      regSlots fromStep used base state pc)
    (saved : Level4DecodeRawSavedSlots state stack savedSlots)
    (code : Artifacts.programImage.fileBytesLoadedFaithfully state.mem)
    (address offset : Nat) (value : BitVec 64) (nextPc : BitVec 64)
    (addressEq : address = stack + offset)
    (targetValue : (BitVec.ofNat 64 address).toNat = address)
    (run : ∃ retired, Runs (try_step (fromStep + used) false) state
      (afterMemoryWrite state pc retired address (width := 8) value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (inRegion : Level4DecodeRawEntryProloguePcs pc)
    (notExit : ¬ Level4DecodeRawEntryPrologueExit pc)
    (inside : ∀ other, address ≤ other → other < address + 8 → DecoderWritableByte other)
    (writable : ∀ index, index < 8 → canonicalContractParams.env.stack (address + index))
    (separated : ∀ slot ∈ savedSlots, offset + 8 ≤ slot.1 ∨ slot.1 + 8 ≤ offset)
    (keep : RegsOutside stepBookkeeping regSlots) :
    ∃ after, Seg Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
      Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte
      regSlots fromStep (used + 1) base after nextPc ∧
      Level4DecodeRawSavedSlots after stack ((offset, value) :: savedSlots) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  obtain ⟨retired, after, hAfter, seg'⟩ := seg.stepStoreWitness address value nextPc inRegion
    notExit run advance inside level4_prologue_bookkeeping keep
  have saved' : Level4DecodeRawSavedSlots after stack ((offset, value) :: savedSlots) := by
    rw [hAfter]
    let target := BitVec.ofNat 64 address
    have targetStack : target.toNat = stack + offset := targetValue.trans addressEq
    simpa [target, targetValue] using level4_savedSlots_store state pc retired target value stack offset
      targetStack savedSlots separated saved
  have code' : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hAfter]
    exact level4_prologue_store_code state pc retired address value writable code
  exact ⟨after, seg', saved', code'⟩

private theorem level4_decode_raw_prologue_saves
    (pre : Level4DecodeRawEntryProloguePre margs state) (fromStep : Nat) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 after,
      Seg Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
        Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte
        [⟨x2, BitVec.ofNat 64 pre.stack⟩, ⟨x27, s11⟩, ⟨x26, s10⟩, ⟨x25, s9⟩, ⟨x24, s8⟩,
          ⟨x23, s7⟩, ⟨x22, s6⟩, ⟨x21, s5⟩, ⟨x20, s4⟩, ⟨x19, s3⟩, ⟨x18, s2⟩,
          ⟨x9, s1⟩, ⟨x8, s0⟩, ⟨x1, pre.ra⟩] fromStep 14 state after
        (BitVec.ofNat 64 0x1047c) ∧
      Level4DecodeRawSavedSlots after pre.stack
        [(0x788, s11), (0x790, s10), (0x798, s9), (0x7a0, s8), (0x7a8, s7), (0x7b0, s6),
          (0x7b8, s5), (0x7c0, s4), (0x7c8, s3), (0x7d0, s2), (0x7d8, s1), (0x7e0, s0),
          (0x7e8, pre.ra)] ∧
      Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, afterRa, seg2, saved2, code2⟩ :=
    level4_decode_raw_prologue_first_save pre fromStep
  have agree2 := seg2.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack2 := seg2.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s0At := seg2.reg x8 s0 (by simp)
  have targetS0 : (BitVec.ofNat 64 (pre.stack + 0x7e0)).toNat = pre.stack + 0x7e0 :=
    level4_prologue_stack_address_toNat pre (offset := 0x7e0) (by omega)
  obtain ⟨afterS0, seg3, saved3, code3⟩ := level4_prologue_accumulate_store seg2 saved2 code2
    (pre.stack + 0x7e0) 0x7e0 s0 (BitVec.ofNat 64 0x10450)
    (by rfl)
    targetS0
    (level4_decode_raw_store_s0 pre pre.machine agree2 seg2.retired code2 (fromStep + 2) s0 seg2.atPc
      stack2 (rX_x8_run _ _ (decoderExecuteState_get? s0At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7e0 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7e0 (by omega) (by omega))
    (by
      rintro ⟨slotOffset, slotValue⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have h' := congrArg Prod.fst h
      omega)
    (by exact of_decide_eq_true rfl)
  have agree3 := seg3.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack3 := seg3.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s1At := seg3.reg x9 s1 (by simp)
  obtain ⟨afterS1, seg4, saved4, code4⟩ := level4_prologue_accumulate_store seg3 saved3 code3
    (pre.stack + 0x7d8) 0x7d8 s1 (BitVec.ofNat 64 0x10454)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7d8) (by omega))
    (level4_decode_raw_store_s1 pre pre.machine agree3 seg3.retired code3 (fromStep + 3) s1 seg3.atPc
      stack3 (rX_x9_run _ _ (decoderExecuteState_get? s1At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7d8 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7d8 (by omega) (by omega))
    (by
      intro slot h
      rcases slot with ⟨slotOffset, slotValue⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      all_goals have h' := congrArg Prod.fst h
      all_goals omega)
    (by exact of_decide_eq_true rfl)
  have agree4 := seg4.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack4 := seg4.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s2At := seg4.reg x18 s2 (by simp)
  obtain ⟨afterS2, seg5, saved5, code5⟩ := level4_prologue_accumulate_store seg4 saved4 code4
    (pre.stack + 0x7d0) 0x7d0 s2 (BitVec.ofNat 64 0x10458)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7d0) (by omega))
    (level4_decode_raw_store_s2 pre pre.machine agree4 seg4.retired code4 (fromStep + 4) s2 seg4.atPc
      stack4 (level4_rX_x18_run _ _ (decoderExecuteState_get? s2At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7d0 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7d0 (by omega) (by omega))
    (by
      intro slot h
      rcases slot with ⟨slotOffset, slotValue⟩
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree5 := seg5.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack5 := seg5.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s3At := seg5.reg x19 s3 (by simp)
  obtain ⟨afterS3, seg6, saved6, code6⟩ := level4_prologue_accumulate_store seg5 saved5 code5
    (pre.stack + 0x7c8) 0x7c8 s3 (BitVec.ofNat 64 0x1045c)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7c8) (by omega))
    (level4_decode_raw_store_s3 pre pre.machine agree5 seg5.retired code5 (fromStep + 5) s3 seg5.atPc
      stack5 (level4_rX_x19_run _ _ (decoderExecuteState_get? s3At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7c8 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7c8 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree6 := seg6.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack6 := seg6.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s4At := seg6.reg x20 s4 (by simp)
  obtain ⟨afterS4, seg7, saved7, code7⟩ := level4_prologue_accumulate_store seg6 saved6 code6
    (pre.stack + 0x7c0) 0x7c0 s4 (BitVec.ofNat 64 0x10460)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7c0) (by omega))
    (level4_decode_raw_store_s4 pre pre.machine agree6 seg6.retired code6 (fromStep + 6) s4 seg6.atPc
      stack6 (level4_rX_x20_run _ _ (decoderExecuteState_get? s4At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7c0 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7c0 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree7 := seg7.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack7 := seg7.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s5At := seg7.reg x21 s5 (by simp)
  obtain ⟨afterS5, seg8, saved8, code8⟩ := level4_prologue_accumulate_store seg7 saved7 code7
    (pre.stack + 0x7b8) 0x7b8 s5 (BitVec.ofNat 64 0x10464)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7b8) (by omega))
    (level4_decode_raw_store_s5 pre pre.machine agree7 seg7.retired code7 (fromStep + 7) s5 seg7.atPc
      stack7 (level4_rX_x21_run _ _ (decoderExecuteState_get? s5At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7b8 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7b8 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree8 := seg8.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack8 := seg8.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s6At := seg8.reg x22 s6 (by simp)
  obtain ⟨afterS6, seg9, saved9, code9⟩ := level4_prologue_accumulate_store seg8 saved8 code8
    (pre.stack + 0x7b0) 0x7b0 s6 (BitVec.ofNat 64 0x10468)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7b0) (by omega))
    (level4_decode_raw_store_s6 pre pre.machine agree8 seg8.retired code8 (fromStep + 8) s6 seg8.atPc
      stack8 (level4_rX_x22_run _ _ (decoderExecuteState_get? s6At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7b0 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7b0 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree9 := seg9.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack9 := seg9.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s7At := seg9.reg x23 s7 (by simp)
  obtain ⟨afterS7, seg10, saved10, code10⟩ := level4_prologue_accumulate_store seg9 saved9 code9
    (pre.stack + 0x7a8) 0x7a8 s7 (BitVec.ofNat 64 0x1046c)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7a8) (by omega))
    (level4_decode_raw_store_s7 pre pre.machine agree9 seg9.retired code9 (fromStep + 9) s7 seg9.atPc
      stack9 (level4_rX_x23_run _ _ (decoderExecuteState_get? s7At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7a8 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7a8 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree10 := seg10.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack10 := seg10.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s8At := seg10.reg x24 s8 (by simp)
  obtain ⟨afterS8, seg11, saved11, code11⟩ := level4_prologue_accumulate_store seg10 saved10 code10
    (pre.stack + 0x7a0) 0x7a0 s8 (BitVec.ofNat 64 0x10470)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x7a0) (by omega))
    (level4_decode_raw_store_s8 pre pre.machine agree10 seg10.retired code10 (fromStep + 10) s8 seg10.atPc
      stack10 (level4_rX_x24_run _ _ (decoderExecuteState_get? s8At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x7a0 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x7a0 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree11 := seg11.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack11 := seg11.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s9At := seg11.reg x25 s9 (by simp)
  obtain ⟨afterS9, seg12, saved12, code12⟩ := level4_prologue_accumulate_store seg11 saved11 code11
    (pre.stack + 0x798) 0x798 s9 (BitVec.ofNat 64 0x10474)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x798) (by omega))
    (level4_decode_raw_store_s9 pre pre.machine agree11 seg11.retired code11 (fromStep + 11) s9 seg11.atPc
      stack11 (level4_rX_x25_run _ _ (decoderExecuteState_get? s9At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x798 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x798 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree12 := seg12.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack12 := seg12.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s10At := seg12.reg x26 s10 (by simp)
  obtain ⟨afterS10, seg13, saved13, code13⟩ := level4_prologue_accumulate_store seg12 saved12 code12
    (pre.stack + 0x790) 0x790 s10 (BitVec.ofNat 64 0x10478)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x790) (by omega))
    (level4_decode_raw_store_s10 pre pre.machine agree12 seg12.retired code12 (fromStep + 12) s10 seg12.atPc
      stack12 (level4_rX_x26_run _ _ (decoderExecuteState_get? s10At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x790 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x790 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  have agree13 := seg13.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack13 := seg13.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  have s11At := seg13.reg x27 s11 (by simp)
  obtain ⟨afterS11, seg14, saved14, code14⟩ := level4_prologue_accumulate_store seg13 saved13 code13
    (pre.stack + 0x788) 0x788 s11 (BitVec.ofNat 64 0x1047c)
    (by rfl)
    (level4_prologue_stack_address_toNat pre (offset := 0x788) (by omega))
    (level4_decode_raw_store_s11 pre pre.machine agree13 seg13.retired code13 (fromStep + 13) s11 seg13.atPc
      stack13 (level4_rX_x27_run _ _ (decoderExecuteState_get? s11At)))
    (by decide) (by owned_pc) (by simp)
    (level4_prologue_store_inside pre 0x788 (by omega) (by omega))
    (level4_prologue_store_stack_writable pre 0x788 (by omega) (by omega))
    (by intro slot h; rcases slot with ⟨slotOffset, slotValue⟩; simp_all only [List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] <;> omega)
    (by exact of_decide_eq_true rfl)
  refine ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, afterS11, ?_, saved14, code14⟩
  change Seg Level4DecodeRawEntryProloguePcs Level4DecodeRawEntryPrologueExit
    Level4DecodeRawEntryPrologueChildSummary level4DecodeRawEntryPrologueWrites DecoderWritableByte _
    fromStep (2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) state afterS11
    (BitVec.ofNat 64 0x1047c)
  exact seg14

/-- Sail executes every parent-owned entry instruction from `0x10444` through `0x10480`, saves the
callee frame at the exact epilogue offsets, and enters the selected `requireU32Length` phase. -/
theorem level4_decode_raw_entry_prologue
    (pre : Level4DecodeRawEntryProloguePre margs state) (fromStep : Nat) :
    ∃ after s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
      Level4DecodeRawEntryEnvelopeOffsetsHandoff fromStep state after pre s0 s1 s2 s3 s4 s5 s6 s7
        s8 s9 s10 s11 := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, afterS11, seg14, saved14, code14⟩ :=
    level4_decode_raw_prologue_saves pre fromStep
  have agree14 := seg14.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have stack14 := seg14.reg x2 (BitVec.ofNat 64 pre.stack) (by simp)
  let seg14' := seg14.forget (kv' := []) (by intro p hp; cases hp)
  obtain ⟨retired15, afterStack, hStack, seg15⟩ := seg14'.stepWitness (by owned_pc) (by simp) x2
    (BitVec.ofNat 64 pre.postStack) (BitVec.ofNat 64 0x10480)
    (level4_decode_raw_second_stack_step pre pre.machine agree14 seg14'.retired code14 (fromStep + 14)
      seg14'.atPc stack14)
    (by decide) level4_prologue_bookkeeping (by simp [level4DecodeRawEntryPrologueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have code15 : Artifacts.programImage.fileBytesLoadedFaithfully afterStack.mem := by
    rw [hStack, afterRegisterWrite_mem]
    exact code14
  have agree15 := seg15.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint
  have a1At : afterStack.regs.get? x11 = some pre.a1 :=
    (seg15.get x11 (by simp [level4DecodeRawEntryPrologueWrites])).trans pre.a1Value
  let seg15' := seg15.forget (kv' := []) (by intro p hp; cases hp)
  obtain ⟨retired16, after, hAfter, seg16⟩ := seg15'.stepWitness (by owned_pc) (by simp) x8 pre.a1
    (BitVec.ofNat 64 0x10484)
    (level4_decode_raw_move_a1_step pre pre.machine agree15 seg15'.retired code15 (fromStep + 15)
      seg15'.atPc a1At)
    (by decide) level4_prologue_bookkeeping (by simp [level4DecodeRawEntryPrologueWrites]) (by decide)
    (by decide) (by exact of_decide_eq_true rfl)
  have code16 : Artifacts.programImage.fileBytesLoadedFaithfully after.mem := by
    rw [hAfter, afterRegisterWrite_mem]
    exact code15
  have sp16 : after.regs.get? x2 = some (BitVec.ofNat 64 pre.postStack) := by
    have sp15 : afterStack.regs.get? x2 = some (BitVec.ofNat 64 pre.postStack) := by
      rw [hStack]
      exact afterRegisterWrite_destination afterS11 (BitVec.ofNat 64 0x1047c) retired15 x2
        (BitVec.ofNat 64 pre.postStack) (by decide) (by decide)
    rw [hAfter]
    exact ((afterRegisterWrite_writes afterStack (BitVec.ofNat 64 0x10480) retired16 x8 pre.a1).get x2
      (by decide)).trans sp15
  have memory16 : after.mem = afterS11.mem := by
    rw [hAfter, hStack, afterRegisterWrite_mem, afterRegisterWrite_mem]
  have savedFrame14 :
      Level4DecodeRawPrologueSavedFrame afterS11 pre.stack pre.ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 := by
    exact ⟨saved14 (0x7e8, pre.ra) (by simp), saved14 (0x7e0, s0) (by simp),
      saved14 (0x7d8, s1) (by simp), saved14 (0x7d0, s2) (by simp),
      saved14 (0x7c8, s3) (by simp), saved14 (0x7c0, s4) (by simp),
      saved14 (0x7b8, s5) (by simp), saved14 (0x7b0, s6) (by simp),
      saved14 (0x7a8, s7) (by simp), saved14 (0x7a0, s8) (by simp),
      saved14 (0x798, s9) (by simp), saved14 (0x790, s10) (by simp),
      saved14 (0x788, s11) (by simp)⟩
  have savedFrame16 := level4_prologue_saved_frame_of_mem_eq savedFrame14 memory16
  refine ⟨after, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11,
    ⟨seg16.trace, seg16.confined, seg16.writes, savedFrame16, seg16.atPc, sp16,
      seg16.reg x8 pre.a1 (by simp), code16,
      pre.machine.mono (seg16.agree decoderPreserved_level4DecodeRawEntryPrologueWrites_disjoint)
        seg16.retired, seg16.retired⟩⟩

end BinaryFv.Zesu.MachineExecution
