import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
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

/-- Caller facts and concrete machine layout required at the raw decoder's emitted entry.  The
callee-saved values are not an ABI assumption: `frame` is exactly the caller-derived
`DecodeRawEntryFrame` used by the two real call routes. -/
structure Level4DecodeRawEntryProloguePre (margs : DecoderMachineArgs) (state : State) where
  machine : DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw) margs state
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

/-- The handoff to the selected entry/envelope/offset phase.  It has no Level 4 hypothesis: the
trace below produces every field from the caller-derived entry object. -/
structure Level4DecodeRawEntryEnvelopeOffsetsHandoff (fromStep : Nat) (before after : State)
    (pre : Level4DecodeRawEntryProloguePre margs before)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64) where
  phase : DecodeRawCfgPhaseInterface
  phaseIsEntryEnvelopeOffsets : phase = decodeRawCfgPhaseInterface .entryEnvelopeOffsets
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
    (functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeRaw) margs after
  retired : RetiredCounterPresent after

/-- The prologue writes only its two modified architectural registers plus normal retirement
bookkeeping; stores themselves modify memory but no additional register. -/
def level4DecodeRawEntryPrologueWrites : RegSet := fun r =>
  stepBookkeeping r ∨ r = x2 ∨ r = x8

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

end BinaryFv.Zesu.MachineExecution
