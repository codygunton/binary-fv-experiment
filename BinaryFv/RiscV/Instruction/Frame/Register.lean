import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Analysis.StackFlow
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated integer-register write callback completes normally without changing state. -/
theorem xreg_write_callback_run (state : State) (register : regidx) (data : BitVec 64) :
    (xreg_write_callback register data).run state = .ok () state := by
  rcases register with ⟨index⟩
  simp [xreg_write_callback, xreg_full_write_callback, reg_name_forwards,
    encdec_reg_forwards, encdec_reg_forwards_matches, get_config_use_abi_names,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad,
    LeanRV64DExecutable.Functions.not]

private theorem xreg_write_callback_apply (state : State) (register : regidx) (data : BitVec 64) :
    xreg_write_callback register data state = .ok () state :=
  xreg_write_callback_run state register data

/-- A generated integer write to any non-stack destination preserves the old `x2` value. -/
theorem wX_bits_preserves_stack_pointer (state : State) (destination : regidx) (data : BitVec 64)
    (notStack : destination ≠ stackPointer) :
    (match (wX_bits destination data).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  rcases destination with ⟨index⟩
  have indexNotStack : index ≠ 2#5 := by
    intro equals
    apply notStack
    simp [stackPointer, equals]
  have indexNatNotStack : index.toNat ≠ 2 := by
    have unequal := BitVec.toNat_ne.mp indexNotStack
    simpa using unequal
  have sailIndexNat : (Sail.BitVec.toNatInt index).toNat = index.toNat := rfl
  have indexLt : index.toNat < 32 := by
    simpa using index.isLt
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
    first
    | omega
    | simp [wX_bits, wX, h, sailIndexNat, PreSail.writeReg, EStateM.run, EStateM.bind,
        EStateM.modifyGet, EStateM.pure, EStateM.instMonad, MonadState.modifyGet,
        MonadStateOf.modifyGet, modify, regval_into_reg, xreg_write_callback_apply,
        Std.ExtDHashMap.get?_insert]

/-- A generated `LUI` preserves `x2` whenever it writes a non-stack destination. -/
theorem execute_UTYPE_lui_preserves_stack_pointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute_UTYPE immediate destination .LUI).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  rw [show execute_UTYPE immediate destination .LUI =
      (do
        wX_bits destination (sign_extend (m := 64) (immediate ++ 0x000#12))
        pure RETIRE_SUCCESS) by rfl]
  have frame := wX_bits_preserves_stack_pointer state destination
    (sign_extend (m := 64) (immediate ++ 0x000#12)) notStack
  cases hAction : (wX_bits destination
      (sign_extend (m := 64) (immediate ++ 0x000#12))).run state with
  | ok value after =>
    change wX_bits destination (sign_extend (m := 64) (immediate ++ 0x000#12)) state =
      .ok value after at hAction
    simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hAction] using frame
  | error error after =>
    change wX_bits destination (sign_extend (m := 64) (immediate ++ 0x000#12)) state =
      .error error after at hAction
    simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hAction] using frame

private theorem get_arch_pc_state_projection (state : State) :
    (match (get_arch_pc ()).run state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  simp [get_arch_pc, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe]
  cases h : state.regs.get? PC <;> rfl

private theorem execute_UTYPE_auipc_preserves_stack_pointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute_UTYPE immediate destination .AUIPC).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  simp only [execute_UTYPE]
  cases hPc : (get_arch_pc ()).run state with
  | ok pc after =>
    change get_arch_pc () state = .ok pc after at hPc
    have afterEq : after = state := by
      have preserved := get_arch_pc_state_projection state
      change (match get_arch_pc () state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hPc] using preserved
    subst after
    have frame := wX_bits_preserves_stack_pointer state destination
      (pc + sign_extend (m := 64) (immediate ++ 0x000#12)) notStack
    cases hWrite : (wX_bits destination
        (pc + sign_extend (m := 64) (immediate ++ 0x000#12))).run state with
    | ok value after =>
      change wX_bits destination (pc + sign_extend (m := 64) (immediate ++ 0x000#12)) state =
        .ok value after at hWrite
      simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hPc, hWrite]
        using frame
    | error error after =>
      change wX_bits destination (pc + sign_extend (m := 64) (immediate ++ 0x000#12)) state =
        .error error after at hWrite
      simpa [EStateM.run, EStateM.bind, EStateM.pure, EStateM.instMonad, hPc, hWrite]
        using frame
  | error error after =>
    change get_arch_pc () state = .error error after at hPc
    have afterEq : after = state := by
      have preserved := get_arch_pc_state_projection state
      change (match get_arch_pc () state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hPc] using preserved
    subst after
    simp [EStateM.run, EStateM.bind, EStateM.instMonad, hPc]

/-- Every generated U-type pure integer writer preserves `x2` off the stack destination. -/
theorem execute_UTYPE_preserves_stack_pointer (state : State) (immediate : BitVec 20)
    (destination : regidx) (op : uop) (notStack : destination ≠ stackPointer) :
    (match (execute_UTYPE immediate destination op).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases op with
  | LUI => exact execute_UTYPE_lui_preserves_stack_pointer state immediate destination notStack
  | AUIPC => exact execute_UTYPE_auipc_preserves_stack_pointer state immediate destination notStack

end BinaryFv.RiscV
