import BinaryFv.RiscV.Instruction.Frame.Register
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Every generated integer register read leaves the machine state unchanged. -/
private theorem rX_bits_state_projection (state : State) (source : regidx) :
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

private theorem write_after_rX_preserves_stack_pointer (state : State) (source destination : regidx)
    (result : BitVec 64 → BitVec 64) (notStack : destination ≠ stackPointer) :
    (match (do
      let value ← rX_bits source
      wX_bits destination (result value)
      pure RETIRE_SUCCESS).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases hRead : (rX_bits source).run state with
  | ok value afterRead =>
    change rX_bits source state = .ok value afterRead at hRead
    have afterReadEq : afterRead = state := by
      have preserved := rX_bits_state_projection state source
      change (match rX_bits source state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hRead] using preserved
    subst afterRead
    have frame := wX_bits_preserves_stack_pointer state destination (result value) notStack
    cases hWrite : (wX_bits destination (result value)).run state with
    | ok written afterWrite =>
      change wX_bits destination (result value) state = .ok written afterWrite at hWrite
      simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hRead, hWrite]
        using frame
    | error error afterWrite =>
      change wX_bits destination (result value) state = .error error afterWrite at hWrite
      simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hRead, hWrite]
        using frame
  | error error afterRead =>
    change rX_bits source state = .error error afterRead at hRead
    have afterReadEq : afterRead = state := by
      have preserved := rX_bits_state_projection state source
      change (match rX_bits source state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hRead] using preserved
    subst afterRead
    simp [EStateM.run, EStateM.bind, EStateM.instMonad, hRead]

/-- Every generated I-type pure integer writer preserves `x2` off the stack destination. -/
theorem execute_ITYPE_preserves_stack_pointer (state : State) (immediate : BitVec 12)
    (source destination : regidx) (op : iop) (notStack : destination ≠ stackPointer) :
    (match (execute_ITYPE immediate source destination op).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases op with
  | ADDI =>
    simpa [execute_ITYPE] using
      write_after_rX_preserves_stack_pointer state source destination
        (fun value => value + sign_extend (m := 64) immediate) notStack
  | SLTI =>
    simpa [execute_ITYPE] using
      write_after_rX_preserves_stack_pointer state source destination
        (fun value => zero_extend (m := 64)
          (bool_to_bit (zopz0zI_s value (sign_extend (m := 64) immediate)))) notStack
  | SLTIU =>
    simpa [execute_ITYPE] using
      write_after_rX_preserves_stack_pointer state source destination
        (fun value => zero_extend (m := 64)
          (bool_to_bit (zopz0zI_u value (sign_extend (m := 64) immediate)))) notStack
  | ANDI =>
    simpa [execute_ITYPE] using
      write_after_rX_preserves_stack_pointer state source destination
        (fun value => value &&& sign_extend (m := 64) immediate) notStack
  | ORI =>
    simpa [execute_ITYPE] using
      write_after_rX_preserves_stack_pointer state source destination
        (fun value => value ||| sign_extend (m := 64) immediate) notStack
  | XORI =>
    simpa [execute_ITYPE] using
      write_after_rX_preserves_stack_pointer state source destination
        (fun value => value ^^^ sign_extend (m := 64) immediate) notStack

end BinaryFv.RiscV
