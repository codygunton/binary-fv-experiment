import BinaryFv.RiscV.Logic.ReadFrame

namespace BinaryFv.RiscV

/-!
# The stack-pointer preservation calculus

`PreservesStackPointer` and its monadic calculus over `SailM`/`ExceptT`/`SailME`, plus the
primitive frames every instruction frame is assembled from.  This is generic framing, so it lives in
`Logic`: the platform frames (`Platform.ExtensionFrame`, `ClintFrame`, `HtifFrame`,
`TranslationFrame`) depend on it, and routing them through `Instruction/` would invert the layering.

The calculus is published rather than `private` because it now crosses a module boundary.
-/

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- An action preserves the observed stack-pointer register on normal and error outcomes. -/
def PreservesStackPointer {α : Type} (action : SailM α) : Prop :=
  ∀ (state : State),
    (match action.run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2

theorem preservesStackPointer_pure {α : Type} (value : α) :
    PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

theorem preservesStackPointer_throw {α : Type} (error : Sail.Error exception) :
    PreservesStackPointer (throw error : SailM α) := by
  intro state
  rfl

theorem preservesStackPointer_bind {α β : Type} (action : SailM α)
    (next : α → SailM β) (actionFrame : PreservesStackPointer action)
    (nextFrame : ∀ value, PreservesStackPointer (next value)) :
    PreservesStackPointer (action >>= next) := by
  intro state
  cases hAction : action.run state with
  | ok value middle =>
    change action state = .ok value middle at hAction
    have actionFrame' := actionFrame state
    change (match action state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at actionFrame'
    calc
      (match (action >>= next).run state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) =
        (match (next value).run middle with
        | .ok _ state' => state'.regs.get? x2
        | .error _ state' => state'.regs.get? x2) := by
          change (match EStateM.bind action next state with
          | .ok _ state' => state'.regs.get? x2
          | .error _ state' => state'.regs.get? x2) = _
          unfold EStateM.bind
          rw [hAction]
          rfl
      _ = middle.regs.get? x2 := nextFrame value middle
      _ = state.regs.get? x2 := by simpa only [hAction] using actionFrame'
  | error error middle =>
    change action state = .error error middle at hAction
    have actionFrame' := actionFrame state
    change (match action state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at actionFrame'
    change (match EStateM.bind action next state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = _
    unfold EStateM.bind
    rw [hAction]
    simpa only [hAction] using actionFrame'

def PreservesStackPointerExcept {ε α : Type} (action : ExceptT ε SailM α) : Prop :=
  PreservesStackPointer (ExceptT.run action)

theorem preservesStackPointerExcept_pure {ε α : Type} (value : α) :
    PreservesStackPointerExcept (pure value : ExceptT ε SailM α) := by
  intro state
  rfl

theorem preservesStackPointerExcept_lift {ε α : Type} (action : SailM α)
    (frame : PreservesStackPointer action) :
    PreservesStackPointerExcept (ExceptT.lift action : ExceptT ε SailM α) := by
  intro state
  simp only [ExceptT.lift, ExceptT.mk, ExceptT.run, EStateM.instMonad]
  cases hAction : action state with
  | ok value after =>
    have frame' := frame state
    change (match action state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at frame'
    simpa [EStateM.run, EStateM.bind, EStateM.map, hAction] using frame'
  | error error after =>
    have frame' := frame state
    change (match action state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at frame'
    simpa [EStateM.run, EStateM.bind, EStateM.map, hAction] using frame'

theorem preservesStackPointerExcept_liftBind {ε α β : Type} (action : SailM α)
    (next : α → ExceptT ε SailM β) (actionFrame : PreservesStackPointer action)
    (nextFrame : ∀ value, PreservesStackPointerExcept (next value)) :
    PreservesStackPointerExcept (do
      let current ← liftM action
      next current) := by
  unfold PreservesStackPointerExcept
  change PreservesStackPointer (ExceptT.run ((ExceptT.lift action) >>= next))
  have runEq : ExceptT.run ((ExceptT.lift action) >>= next) = (do
      let current ← action
      ExceptT.run (next current)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.lift, ExceptT.mk,
      ExceptT.run, EStateM.instMonad]
    funext state
    cases hAction : action state <;>
      simp [EStateM.bind, EStateM.map, ExceptT.bindCont, hAction]
  rw [runEq]
  apply preservesStackPointer_bind action _ actionFrame
  intro value
  exact nextFrame value

theorem preservesStackPointerExcept_bind {ε α β : Type} (action : ExceptT ε SailM α)
    (next : α → ExceptT ε SailM β) (actionFrame : PreservesStackPointerExcept action)
    (nextFrame : ∀ value, PreservesStackPointerExcept (next value)) :
    PreservesStackPointerExcept (action >>= next) := by
  unfold PreservesStackPointerExcept
  have runEq : ExceptT.run (action >>= next) = (do
      let result ← ExceptT.run action
      match result with
      | .ok value => ExceptT.run (next value)
      | .error error => pure (.error error)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.run, ExceptT.mk,
      EStateM.instMonad]
    rfl
  rw [runEq]
  apply preservesStackPointer_bind (ExceptT.run action) _
  · exact actionFrame
  · intro result
    cases result with
    | ok value => exact nextFrame value
    | error error =>
      exact preservesStackPointer_pure (Except.error error : Except ε β)

theorem preservesStackPointerSailMERun {α : Type} (action : SailME α α)
    (frame : PreservesStackPointerExcept action) :
    PreservesStackPointer (Sail.SailME.run action) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  apply preservesStackPointer_bind (ExceptT.run action) _
  · exact frame
  · intro result
    cases result with
    | ok value => exact preservesStackPointer_pure value
    | error error =>
      cases error with
      | inl error => exact preservesStackPointer_throw error
      | inr value => exact preservesStackPointer_pure value

theorem readReg_preserves_stack_pointer (register : Register) :
    PreservesStackPointer (Sail.readReg register) := by
  intro state
  cases hAction : (Sail.readReg register).run state with
  | ok value after =>
    change (Sail.readReg register : SailM (RegisterType register)) state =
      .ok value after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    change (Sail.readReg register : SailM (RegisterType register)) state =
      .error error after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection

theorem rXBits_preserves_stack_pointer (source : regidx) :
    PreservesStackPointer (rX_bits source) := by
  intro state
  cases hAction : (rX_bits source).run state with
  | ok value after =>
    have projection := rX_bits_state_projection state source
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    have projection := rX_bits_state_projection state source
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection

theorem assert_preserves_stack_pointer (condition : Bool) (message : String) :
    PreservesStackPointer (Sail.assert condition message) := by
  unfold Sail.assert PreSail.assert
  by_cases conditionTrue : condition = true
  · rw [if_pos conditionTrue]
    exact preservesStackPointer_pure ()
  · rw [if_neg conditionTrue]
    exact preservesStackPointer_throw (Sail.Error.Assertion message)

theorem writeNextPc_preserves_stack_pointer (target : BitVec 64) :
    PreservesStackPointer (Sail.writeReg nextPC target) := by
  intro state
  rw [writeReg_run]
  exact writeReg_read_unchanged state nextPC x2 target (by decide)

theorem setNextPc_preserves_stack_pointer (target : BitVec 64) :
    PreservesStackPointer (set_next_pc target) := by
  unfold set_next_pc sail_branch_announce
  apply preservesStackPointer_bind (Sail.writeReg nextPC target) _
  · exact writeNextPc_preserves_stack_pointer target
  · intro _
    exact preservesStackPointer_pure (redirect_callback target)

theorem currentlyEnabledC_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled extension.Ext_C) := by
  unfold currentlyEnabled
  apply preservesStackPointer_bind (Sail.readReg misa) _
  · exact readReg_preserves_stack_pointer misa
  · intro _
    exact preservesStackPointer_pure _

theorem currentlyEnabledZca_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled extension.Ext_Zca) := by
  unfold currentlyEnabled
  apply preservesStackPointer_bind (currentlyEnabled extension.Ext_C) _
  · exact currentlyEnabledC_preserves_stack_pointer
  · intro _
    exact preservesStackPointer_pure _

theorem memoryException_preserves_stack_pointer (address : virtaddr)
    (exception : ExceptionType) :
    PreservesStackPointer (memory_exception address exception) := by
  unfold memory_exception trap
  apply preservesStackPointer_bind (Sail.readReg cur_privilege) _
  · exact readReg_preserves_stack_pointer cur_privilege
  · intro privilege
    apply preservesStackPointer_bind (Sail.readReg PC) _
    · exact readReg_preserves_stack_pointer PC
    · intro pc
      exact preservesStackPointer_pure (ExecutionResult.Trap
        (privilege, make_sync_exception exception (bits_of_virtaddr address), pc))

/-- The generated branch target has explicit all-outcome frames through its `SailME` wrapper. -/
theorem jump_to_preserves_stack_pointer (target : BitVec 64) :
    PreservesStackPointer (jump_to target) := by
  unfold jump_to
  simp only [ext_control_check_pc]
  apply preservesStackPointerSailMERun
  refine preservesStackPointerExcept_bind (pure ()) (fun _ => ?_)
    (preservesStackPointerExcept_pure ()) ?_
  intro _
  refine preservesStackPointerExcept_liftBind
    (Sail.assert (Sail.BitVec.access target 0 == 0#1)
      "extensions/I/base_insts.sail:59.25-59.26")
    (fun _ => ?_)
    (assert_preserves_stack_pointer _ _) ?_
  intro _
  simp only
  refine preservesStackPointerExcept_liftBind (currentlyEnabled extension.Ext_Zca)
    (fun enabled =>
      if (bit_to_bool (Sail.BitVec.access target 1) &&
          LeanRV64DExecutable.Functions.not enabled) = true
      then liftM (memory_exception (virtaddr.Virtaddr target)
        (ExceptionType.E_Fetch_Addr_Align ()))
      else do
        liftM (set_next_pc target)
        pure RETIRE_SUCCESS)
    currentlyEnabledZca_preserves_stack_pointer ?_
  intro enabled
  by_cases taken : (bit_to_bool (Sail.BitVec.access target 1) &&
      LeanRV64DExecutable.Functions.not enabled) = true
  · simp only [taken]
    exact preservesStackPointerExcept_lift _
      (memoryException_preserves_stack_pointer (virtaddr.Virtaddr target)
        (ExceptionType.E_Fetch_Addr_Align ()))
  · simp only [taken]
    refine preservesStackPointerExcept_liftBind (set_next_pc target)
      (fun _ => pure RETIRE_SUCCESS)
      (setNextPc_preserves_stack_pointer target) ?_
    intro _
    exact preservesStackPointerExcept_pure RETIRE_SUCCESS

end BinaryFv.RiscV
