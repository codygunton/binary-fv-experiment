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

end BinaryFv.Zesu.MachineExecution
