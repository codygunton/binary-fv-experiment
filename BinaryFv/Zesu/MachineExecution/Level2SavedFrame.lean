import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts

/-!
# Saved wrapper frame

The wrapper prologue's four saved callee registers are byte-exact machine facts.  This small module
is shared by the prologue transport and epilogue load proofs without imposing an ABI on inline code.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions

/-- Exact eight-byte little-endian representation of a saved RV64 register value. -/
def SavedWordBytes (state : State) (base : Nat) (value : BitVec 64) : Prop :=
  ∀ index (bound : index < (BinaryFv.RiscV.Sep.leBytes 8 value).length),
    state.mem.get? (base + index) = some (getElem (BinaryFv.RiscV.Sep.leBytes 8 value) index bound)

/-- The four words written by the wrapper prologue and read by its epilogue. The offsets are the
actual save slots in the emitted `0xa20`-byte frame, measured from the caller's stack base. -/
def WrapperSavedRegisterFrame (stackBase : Nat) (link s0 s1 s2 : BitVec 64) (state : State) : Prop :=
  SavedWordBytes state (stackBase + 0xa18) link ∧
  SavedWordBytes state (stackBase + 0xa10) s0 ∧
  SavedWordBytes state (stackBase + 0xa08) s1 ∧
  SavedWordBytes state (stackBase + 0xa00) s2

/-- Register-only epilogue instructions preserve the saved wrapper frame. -/
theorem WrapperSavedRegisterFrame.of_mem_eq {stackBase : Nat} {link s0 s1 s2 : BitVec 64}
    {before after : State} (frame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 before)
    (memory : after.mem = before.mem) : WrapperSavedRegisterFrame stackBase link s0 s1 s2 after := by
  rw [WrapperSavedRegisterFrame] at frame ⊢
  simp only [SavedWordBytes] at frame ⊢
  rw [memory]
  exact frame

/-- A proved `memcpy` into the inline `stored_result` payload leaves every wrapper save slot intact.
The separation is derived from `ZesuDecodeRawMachinePre.stackFrameWritable`, whose addresses belong to
the canonical runner stack; no continuation caller supplies a stack/global separation premise. -/
theorem WrapperSavedRegisterFrame.of_stored_result_copy
    {args : BinaryFv.Zesu.Contracts.ZesuDecodeRawArgs} {stackBase : Nat} {entry before after : State}
    {link s0 s1 s2 : BitVec 64} (machine : Entrypoints.ZesuDecodeRaw.ZesuDecodeRawMachinePre args stackBase entry)
    (frame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 before)
    (copyArgs : BinaryFv.Zesu.Contracts.CopyArgs)
    (destination : copyArgs.destination = 0x4215030) (length : copyArgs.length = 832)
    (copyFrame : BinaryFv.Zesu.Contracts.CopyDestinationFrame copyArgs before after) :
    WrapperSavedRegisterFrame stackBase link s0 s1 s2 after := by
  rw [WrapperSavedRegisterFrame] at frame ⊢
  rcases frame with ⟨linkFrame, s0Frame, s1Frame, s2Frame⟩
  have stackAfterResult : 0x4215030 + 832 ≤ stackBase :=
    Entrypoints.ZesuDecodeRaw.wrapper_stack_after_stored_result machine
  have preserve (offset : Nat) (offsetBound : offset + 8 ≤ 0xa20) (value : BitVec 64)
      (saved : SavedWordBytes before (stackBase + offset) value) :
      SavedWordBytes after (stackBase + offset) value := by
    intro index indexBound
    rw [BinaryFv.RiscV.Sep.leBytes_length] at indexBound
    rw [copyFrame (stackBase + offset + index) (by
      right
      rw [destination, length]
      omega)]
    exact saved index indexBound
  exact ⟨preserve 0xa18 (by omega) link linkFrame,
    preserve 0xa10 (by omega) s0 s0Frame,
    preserve 0xa08 (by omega) s1 s1Frame,
    preserve 0xa00 (by omega) s2 s2Frame⟩

end BinaryFv.Zesu.MachineExecution
