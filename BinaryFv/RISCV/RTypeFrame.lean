import BinaryFv.RISCV.RegisterFrame
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RISCV

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

/-- A generated integer write followed by retirement preserves `x2` off the stack destination. -/
private theorem write_retire_preserves_stack_pointer (state : State) (destination : regidx)
    (data : BitVec 64) (notStack : destination ≠ stackPointer) :
    (match (do
      wX_bits destination data
      pure RETIRE_SUCCESS).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  have frame := wX_bits_preserves_stack_pointer state destination data notStack
  cases hAction : (wX_bits destination data).run state with
  | ok value after =>
    change wX_bits destination data state = .ok value after at hAction
    simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hAction] using frame
  | error error after =>
    change wX_bits destination data state = .error error after at hAction
    simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hAction] using frame

/-- Two generated integer reads followed by a non-stack write preserve `x2` on all outcomes. -/
private theorem rX_bits_binary_write_preserves_stack_pointer (state : State)
    (source1 source2 destination : regidx) (result : BitVec 64 → BitVec 64 → BitVec 64)
    (notStack : destination ≠ stackPointer) :
    (match (do
      let value1 ← rX_bits source1
      let value2 ← rX_bits source2
      wX_bits destination (result value1 value2)
      pure RETIRE_SUCCESS).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases hFirst : (rX_bits source1).run state with
  | error error after =>
    change rX_bits source1 state = .error error after at hFirst
    have afterEq : after = state := by
      have preserved := rX_bits_state_projection state source1
      change (match rX_bits source1 state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hFirst] using preserved
    subst after
    simp [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst]
  | ok value1 afterFirst =>
    change rX_bits source1 state = .ok value1 afterFirst at hFirst
    have afterFirstEq : afterFirst = state := by
      have preserved := rX_bits_state_projection state source1
      change (match rX_bits source1 state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hFirst] using preserved
    subst afterFirst
    cases hSecond : (rX_bits source2).run state with
    | error error afterSecond =>
      change rX_bits source2 state = .error error afterSecond at hSecond
      have afterSecondEq : afterSecond = state := by
        have preserved := rX_bits_state_projection state source2
        change (match rX_bits source2 state with
          | .ok _ state' => state'
          | .error _ state' => state') = state at preserved
        simpa [hSecond] using preserved
      subst afterSecond
      simp [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst, hSecond]
    | ok value2 afterSecond =>
      change rX_bits source2 state = .ok value2 afterSecond at hSecond
      have afterSecondEq : afterSecond = state := by
        have preserved := rX_bits_state_projection state source2
        change (match rX_bits source2 state with
          | .ok _ state' => state'
          | .error _ state' => state') = state at preserved
        simpa [hSecond] using preserved
      subst afterSecond
      simpa [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst, hSecond] using
        write_retire_preserves_stack_pointer state destination (result value1 value2) notStack

/-- Every generated R-type pure integer writer preserves `x2` off the stack destination. -/
theorem execute_RTYPE_preserves_stack_pointer (state : State)
    (source2 source1 destination : regidx) (op : rop) (notStack : destination ≠ stackPointer) :
    (match (execute_RTYPE source2 source1 destination op).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases op with
  | ADD =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 => value1 + value2) notStack
  | SUB =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 => value1 - value2) notStack
  | SLL =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 =>
          Sail.shift_bits_left value1
            (Sail.BitVec.extractLsb value2 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
        notStack
  | SLT =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 =>
          zero_extend (m := 64) (bool_to_bit (zopz0zI_s value1 value2))) notStack
  | SLTU =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 =>
          zero_extend (m := 64) (bool_to_bit (zopz0zI_u value1 value2))) notStack
  | XOR =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 => value1 ^^^ value2) notStack
  | SRL =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 =>
          Sail.shift_bits_right value1
            (Sail.BitVec.extractLsb value2 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
        notStack
  | SRA =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 =>
          LeanRV64DExecutable.Functions.shift_bits_right_arith value1
            (Sail.BitVec.extractLsb value2 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))
        notStack
  | OR =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 => value1 ||| value2) notStack
  | AND =>
    simpa [execute_RTYPE] using
      rX_bits_binary_write_preserves_stack_pointer state source1 source2 destination
        (fun value1 value2 => value1 &&& value2) notStack

end BinaryFv.RISCV
