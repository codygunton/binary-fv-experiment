import BinaryFv.RISCV.RegisterFrame
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Every generated integer register read leaves the machine state unchanged. -/
theorem rX_bits_state_projection (state : State) (source : regidx) :
    (match (rX_bits source).run state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  rcases source with ⟨index⟩
  have indexLt : index.toNat < 32 := by
    simpa using index.isLt
  have sailIndexNat : (Sail.BitVec.toNatInt index).toNat = index.toNat := rfl
  have indexCases : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 ∨
      index.toNat = 3 ∨ index.toNat = 4 ∨ index.toNat = 5 ∨ index.toNat = 6 ∨
      index.toNat = 7 ∨ index.toNat = 8 ∨ index.toNat = 9 ∨ index.toNat = 10 ∨
      index.toNat = 11 ∨ index.toNat = 12 ∨ index.toNat = 13 ∨ index.toNat = 14 ∨
      index.toNat = 15 ∨ index.toNat = 16 ∨ index.toNat = 17 ∨ index.toNat = 18 ∨
      index.toNat = 19 ∨ index.toNat = 20 ∨ index.toNat = 21 ∨ index.toNat = 22 ∨
      index.toNat = 23 ∨ index.toNat = 24 ∨ index.toNat = 25 ∨ index.toNat = 26 ∨
      index.toNat = 27 ∨ index.toNat = 28 ∨ index.toNat = 29 ∨ index.toNat = 30 ∨
      index.toNat = 31 := by
    omega
  rcases indexCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    simp [rX_bits, rX, h, sailIndexNat, PreSail.readReg, EStateM.run, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe] <;>
      first
      | rfl
      | cases hRead : state.regs.get? x1 <;> rfl
      | cases hRead : state.regs.get? x2 <;> rfl
      | cases hRead : state.regs.get? x3 <;> rfl
      | cases hRead : state.regs.get? x4 <;> rfl
      | cases hRead : state.regs.get? x5 <;> rfl
      | cases hRead : state.regs.get? x6 <;> rfl
      | cases hRead : state.regs.get? x7 <;> rfl
      | cases hRead : state.regs.get? x8 <;> rfl
      | cases hRead : state.regs.get? x9 <;> rfl
      | cases hRead : state.regs.get? x10 <;> rfl
      | cases hRead : state.regs.get? x11 <;> rfl
      | cases hRead : state.regs.get? x12 <;> rfl
      | cases hRead : state.regs.get? x13 <;> rfl
      | cases hRead : state.regs.get? x14 <;> rfl
      | cases hRead : state.regs.get? x15 <;> rfl
      | cases hRead : state.regs.get? x16 <;> rfl
      | cases hRead : state.regs.get? x17 <;> rfl
      | cases hRead : state.regs.get? x18 <;> rfl
      | cases hRead : state.regs.get? x19 <;> rfl
      | cases hRead : state.regs.get? x20 <;> rfl
      | cases hRead : state.regs.get? x21 <;> rfl
      | cases hRead : state.regs.get? x22 <;> rfl
      | cases hRead : state.regs.get? x23 <;> rfl
      | cases hRead : state.regs.get? x24 <;> rfl
      | cases hRead : state.regs.get? x25 <;> rfl
      | cases hRead : state.regs.get? x26 <;> rfl
      | cases hRead : state.regs.get? x27 <;> rfl
      | cases hRead : state.regs.get? x28 <;> rfl
      | cases hRead : state.regs.get? x29 <;> rfl
      | cases hRead : state.regs.get? x30 <;> rfl
      | cases hRead : state.regs.get? x31 <;> rfl

end BinaryFv.RISCV
