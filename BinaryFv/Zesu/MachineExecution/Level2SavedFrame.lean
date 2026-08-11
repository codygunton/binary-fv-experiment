import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.DecodedValue.StatelessInput

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

/-- A saved machine word is also the ordinary little-endian bit-vector representation consumed by
the generic decoder-load helper. -/
theorem SavedWordBytes.bitVectorLERep {state : State} {base : Nat} {value : BitVec 64}
    (saved : SavedWordBytes state base value) : DecodedValue.BitVectorLERep state base value := by
  intro index bound
  rw [saved index (by simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BinaryFv.RiscV.Sep.leBytes, List.getElem_ofFn, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  rw [show 256 = 2 ^ 8 by decide, ← Nat.pow_mul]
  exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))).symm

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

private theorem wrapperSavedRegisterFrame_of_save_area {stackBase : Nat} {link s0 s1 s2 : BitVec 64}
    {before after : State} (frame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 before)
    (saveArea : ∀ index, index < 32 →
      after.mem.get? (stackBase + 0xa00 + index) = before.mem.get? (stackBase + 0xa00 + index)) :
    WrapperSavedRegisterFrame stackBase link s0 s1 s2 after := by
  rw [WrapperSavedRegisterFrame] at frame ⊢
  rcases frame with ⟨linkFrame, s0Frame, s1Frame, s2Frame⟩
  have preserve (offset : Nat) (minimum : 0xa00 ≤ offset) (offsetBound : offset + 8 ≤ 0xa20)
      (value : BitVec 64)
      (saved : SavedWordBytes before (stackBase + offset) value) :
      SavedWordBytes after (stackBase + offset) value := by
    intro index indexBound
    have indexLt : index < 8 := by
      rw [BinaryFv.RiscV.Sep.leBytes_length] at indexBound
      exact indexBound
    have saveIndex : offset - 0xa00 + index < 32 := by omega
    have preserved := saveArea (offset - 0xa00 + index) saveIndex
    have address : stackBase + 0xa00 + (offset - 0xa00 + index) =
        stackBase + offset + index := by omega
    rw [address] at preserved
    exact preserved.trans (saved index indexBound)
  exact ⟨preserve 0xa18 (by omega) (by omega) link linkFrame,
    preserve 0xa10 (by omega) (by omega) s0 s0Frame,
    preserve 0xa08 (by omega) (by omega) s1 s1Frame,
    preserve 0xa00 (by omega) (by omega) s2 s2Frame⟩

/-- The emitted `decodeRaw` child preserves the four wrapper words because its caller-save-area
clause starts at `allocatorBase + 0x9f0 = stackBase + 0xa00` and covers exactly 32 bytes. -/
theorem WrapperSavedRegisterFrame.of_decode_raw_caller_save_area
    {args : BinaryFv.Zesu.Contracts.EntryArgs} {stackBase : Nat} {link s0 s1 s2 : BitVec 64}
    {before after : State}
    (allocatorBase : args.allocatorBase = stackBase + 0x10)
    (frame : WrapperSavedRegisterFrame stackBase link s0 s1 s2 before)
    (saveArea : BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeRawCallerSaveArea args before after) :
    WrapperSavedRegisterFrame stackBase link s0 s1 s2 after := by
  apply wrapperSavedRegisterFrame_of_save_area frame
  intro index indexBound
  have preserved := saveArea index indexBound
  rw [allocatorBase] at preserved
  have address : stackBase + 0x10 + 0x9f0 + index = stackBase + 0xa00 + index := by omega
  rw [address] at preserved
  exact preserved

/-- Every selected `decode` exit carries the wrapper's caller-save equality at its final stack
base, so it transports the saved frame without an ABI or address-alignment premise. -/
theorem WrapperSavedRegisterFrame.of_decode_inline_caller_save_area
    {args : BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineArgs} {link s0 s1 s2 : BitVec 64}
    {before after : State} (frame : WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 before)
    (saveArea : BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineCallerSaveArea args before after) :
    WrapperSavedRegisterFrame args.stackBase link s0 s1 s2 after := by
  apply wrapperSavedRegisterFrame_of_save_area frame
  simpa only [BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.DecodeInlineCallerSaveArea] using saveArea

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
