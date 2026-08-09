import BinaryFv.Zesu.MachineExecution.Level4DecodeRawPrologueSteps

/-! # Protected frame across Level 4 `decodeRaw` fragments

The four large inlined decoders may allocate and write their results, but parent interleaves and
their resumable contracts must retain the prologue's saved return frame.  This is the concrete
state carried from the raw entry through every fragment handoff; it deliberately does not impose a
global write set on dynamic decoder bodies.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open LeanRV64DExecutable.Functions Register RegisterWriteStep

/-- The facts a `decodeRaw` fragment must preserve for the later cleanup and epilogue route.
`origin` is the one emitted raw-decoder entry: a re-entry never substitutes a new origin. -/
def Level4DecodeRawParentInvariant (margs : DecoderMachineArgs) (origin state : State)
    (stack : Nat) (savedRa savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8
      savedS9 savedS10 savedS11 : BitVec 64) : Prop :=
  ∃ entry : Level4DecodeRawEntryProloguePre margs origin,
    entry.stack = stack ∧ entry.ra = savedRa ∧
      Level4DecodeRawPrologueSavedFrame state stack savedRa savedS0 savedS1 savedS2 savedS3 savedS4
        savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11 ∧
      state.regs.get? x2 = some (BitVec.ofNat 64 entry.postStack) ∧
      DecodedValue.MemoryBytes state margs.inputBase margs.bytes ∧
      (∀ address, stack + 0x788 ≤ address → address < stack + 0x7f0 →
        margs.inputBase + margs.bytes.size ≤ address ∨ address < margs.inputBase) ∧
      (∀ index, index < 0xa20 →
        canonicalContractParams.env.stack (stack + 0x7f0 + index)) ∧
      (∀ index, index < 0x7f0 →
        canonicalContractParams.env.stack (entry.postStack + index)) ∧
      Artifacts.programImage.fileBytesLoadedFaithfully state.mem ∧
      DecoderMachinePre RegisterWriteStep.decodeRawExecutionPcs margs state ∧ RetiredCounterPresent state

/-- Existentially package the concrete saved values once.  Later fragment contracts receive this
same frame and must return `PreservedTo`, which fixes all values and the original entry. -/
structure Level4DecodeRawParentFrame (margs : DecoderMachineArgs) (origin state : State) where
  stack : Nat
  savedRa : BitVec 64
  savedS0 : BitVec 64
  savedS1 : BitVec 64
  savedS2 : BitVec 64
  savedS3 : BitVec 64
  savedS4 : BitVec 64
  savedS5 : BitVec 64
  savedS6 : BitVec 64
  savedS7 : BitVec 64
  savedS8 : BitVec 64
  savedS9 : BitVec 64
  savedS10 : BitVec 64
  savedS11 : BitVec 64
  invariant : Level4DecodeRawParentInvariant margs origin state stack savedRa savedS0 savedS1 savedS2
    savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11

def Level4DecodeRawParentFrame.PreservedTo
    (frame : Level4DecodeRawParentFrame margs origin current) (after : State) : Prop :=
  Level4DecodeRawParentInvariant margs origin after frame.stack frame.savedRa frame.savedS0 frame.savedS1
    frame.savedS2 frame.savedS3 frame.savedS4 frame.savedS5 frame.savedS6 frame.savedS7 frame.savedS8
    frame.savedS9 frame.savedS10 frame.savedS11

def Level4DecodeRawParentFrame.toState (frame : Level4DecodeRawParentFrame margs origin current)
    (preserved : frame.PreservedTo after) : Level4DecodeRawParentFrame margs origin after :=
  { stack := frame.stack
    savedRa := frame.savedRa
    savedS0 := frame.savedS0
    savedS1 := frame.savedS1
    savedS2 := frame.savedS2
    savedS3 := frame.savedS3
    savedS4 := frame.savedS4
    savedS5 := frame.savedS5
    savedS6 := frame.savedS6
    savedS7 := frame.savedS7
    savedS8 := frame.savedS8
    savedS9 := frame.savedS9
    savedS10 := frame.savedS10
    savedS11 := frame.savedS11
    invariant := preserved }

/-- The exact 16-step raw-decoder prologue constructs the protected frame once.  Every later
fragment/re-entry receives this object with `before` fixed as its semantic origin. -/
def Level4DecodeRawParentFrame.of_entryEnvelopeHandoff
    {margs : DecoderMachineArgs} {fromStep : Nat} {before state : State}
    {pre : Level4DecodeRawEntryProloguePre margs before}
    {savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10
      savedS11 : BitVec 64}
    (handoff : Level4DecodeRawEntryEnvelopeOffsetsHandoff fromStep before state pre savedS0 savedS1
      savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11) :
    Level4DecodeRawParentFrame margs before state :=
  { stack := pre.stack
    savedRa := pre.ra
    savedS0 := savedS0
    savedS1 := savedS1
    savedS2 := savedS2
    savedS3 := savedS3
    savedS4 := savedS4
    savedS5 := savedS5
    savedS6 := savedS6
    savedS7 := savedS7
    savedS8 := savedS8
    savedS9 := savedS9
    savedS10 := savedS10
    savedS11 := savedS11
    invariant := ⟨pre, rfl, rfl, handoff.saved, handoff.sp, handoff.inputMemory,
      handoff.inputStackSeparated, handoff.stackFrameWritable, handoff.rawFrameWritable,
      handoff.code, handoff.machine,
      handoff.retired⟩ }

theorem Level4DecodeRawParentFrame.of_entryEnvelopeHandoff_saved
    {margs : DecoderMachineArgs} {fromStep : Nat} {before state : State}
    {pre : Level4DecodeRawEntryProloguePre margs before}
    {savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10
      savedS11 : BitVec 64}
    (handoff : Level4DecodeRawEntryEnvelopeOffsetsHandoff fromStep before state pre savedS0 savedS1
      savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11) :
    Level4DecodeRawPrologueSavedFrame state pre.stack pre.ra savedS0 savedS1 savedS2 savedS3 savedS4
      savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11 :=
  handoff.saved

/-- A mutation of the saved return-link bytes is incompatible with the protected parent frame. -/
def Level4DecodeRawClobbersSavedReturnLink (state : State) (stack : Nat) (savedRa : BitVec 64) : Prop :=
  ¬ SavedWordBytes state (stack + 0x7e8) savedRa

theorem not_level4DecodeRawParentInvariant_of_clobbered_return_link
    {state origin : State} {margs : DecoderMachineArgs} {stack : Nat}
    {savedRa savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10
      savedS11 : BitVec 64}
    (clobbered : Level4DecodeRawClobbersSavedReturnLink state stack savedRa) :
    ¬ Level4DecodeRawParentInvariant margs origin state stack savedRa savedS0 savedS1 savedS2 savedS3
      savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11 := by
  rintro ⟨-, -, -, saved, -, -, -, -, -, -, -, -⟩
  exact clobbered saved.1

/-- No arbitrary mutation of the thirteen-word raw save area can be passed off as dynamic-fragment
progress: `PreservedTo` requires the complete concrete prologue frame, not just a register frame. -/
def Level4DecodeRawClobbersSavedFrame (state : State) (stack : Nat)
    (savedRa savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10
      savedS11 : BitVec 64) : Prop :=
  ¬ Level4DecodeRawPrologueSavedFrame state stack savedRa savedS0 savedS1 savedS2 savedS3 savedS4
    savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11

theorem not_level4DecodeRawParentInvariant_of_clobbered_saved_frame
    {state origin : State} {margs : DecoderMachineArgs} {stack : Nat}
    {savedRa savedS0 savedS1 savedS2 savedS3 savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10
      savedS11 : BitVec 64}
    (clobbered : Level4DecodeRawClobbersSavedFrame state stack savedRa savedS0 savedS1 savedS2 savedS3
      savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11) :
    ¬ Level4DecodeRawParentInvariant margs origin state stack savedRa savedS0 savedS1 savedS2 savedS3
      savedS4 savedS5 savedS6 savedS7 savedS8 savedS9 savedS10 savedS11 := by
  rintro ⟨-, -, -, saved, -, -, -, -, -, -, -, -⟩
  exact clobbered saved

end BinaryFv.Zesu.MachineExecution
