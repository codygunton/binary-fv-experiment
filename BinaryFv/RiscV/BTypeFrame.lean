import BinaryFv.RiscV.ReadFrame

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- An action preserves the observed stack-pointer register on normal and error outcomes. -/
def PreservesStackPointer {α : Type} (action : SailM α) : Prop :=
  ∀ (state : State),
    (match action.run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2

private theorem preservesStackPointer_pure {α : Type} (value : α) :
    PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

private theorem preservesStackPointer_throw {α : Type} (error : Sail.Error exception) :
    PreservesStackPointer (throw error : SailM α) := by
  intro state
  rfl

private theorem preservesStackPointer_bind {α β : Type} (action : SailM α)
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

private def PreservesStackPointerExcept {ε α : Type} (action : ExceptT ε SailM α) : Prop :=
  PreservesStackPointer (ExceptT.run action)

private theorem preservesStackPointerExcept_pure {ε α : Type} (value : α) :
    PreservesStackPointerExcept (pure value : ExceptT ε SailM α) := by
  intro state
  rfl

private theorem preservesStackPointerExcept_lift {ε α : Type} (action : SailM α)
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

private theorem preservesStackPointerExcept_liftBind {ε α β : Type} (action : SailM α)
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

private theorem preservesStackPointerExcept_bind {ε α β : Type} (action : ExceptT ε SailM α)
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

private theorem preservesStackPointerSailMERun {α : Type} (action : SailME α α)
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

private theorem readReg_preserves_stack_pointer (register : Register) :
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

private theorem rXBits_preserves_stack_pointer (source : regidx) :
    PreservesStackPointer (rX_bits source) := by
  intro state
  cases hAction : (rX_bits source).run state with
  | ok value after =>
    have projection := rX_bits_state_projection state source
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    have projection := rX_bits_state_projection state source
    simpa [hAction] using congrArg (fun state : State => state.regs.get? x2) projection

private theorem assert_preserves_stack_pointer (condition : Bool) (message : String) :
    PreservesStackPointer (Sail.assert condition message) := by
  unfold Sail.assert PreSail.assert
  by_cases conditionTrue : condition = true
  · rw [if_pos conditionTrue]
    exact preservesStackPointer_pure ()
  · rw [if_neg conditionTrue]
    exact preservesStackPointer_throw (Sail.Error.Assertion message)

private theorem writeNextPc_preserves_stack_pointer (target : BitVec 64) :
    PreservesStackPointer (Sail.writeReg nextPC target) := by
  intro state
  rw [writeReg_run]
  exact writeReg_read_unchanged state nextPC x2 target (by decide)

private theorem setNextPc_preserves_stack_pointer (target : BitVec 64) :
    PreservesStackPointer (set_next_pc target) := by
  unfold set_next_pc sail_branch_announce
  apply preservesStackPointer_bind (Sail.writeReg nextPC target) _
  · exact writeNextPc_preserves_stack_pointer target
  · intro _
    exact preservesStackPointer_pure (redirect_callback target)

private theorem currentlyEnabledC_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled extension.Ext_C) := by
  unfold currentlyEnabled
  apply preservesStackPointer_bind (Sail.readReg misa) _
  · exact readReg_preserves_stack_pointer misa
  · intro _
    exact preservesStackPointer_pure _

private theorem currentlyEnabledZca_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled extension.Ext_Zca) := by
  unfold currentlyEnabled
  apply preservesStackPointer_bind (currentlyEnabled extension.Ext_C) _
  · exact currentlyEnabledC_preserves_stack_pointer
  · intro _
    exact preservesStackPointer_pure _

private theorem memoryException_preserves_stack_pointer (address : virtaddr)
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

private theorem rXBitsComparison_preserves_stack_pointer (rs1 rs2 : regidx)
    (comparison : BitVec 64 → BitVec 64 → Bool) :
    PreservesStackPointer (do
      let left ← rX_bits rs1
      let right ← rX_bits rs2
      pure (comparison left right)) := by
  apply preservesStackPointer_bind (rX_bits rs1) _
  · exact rXBits_preserves_stack_pointer rs1
  · intro left
    apply preservesStackPointer_bind (rX_bits rs2) _
    · exact rXBits_preserves_stack_pointer rs2
    · intro right
      exact preservesStackPointer_pure (comparison left right)

private def bTypeCondition (rs2 rs1 : regidx) (op : bop) : SailM Bool := do
  match op with
  | .BEQ => pure ((← rX_bits rs1) == (← rX_bits rs2))
  | .BNE => pure ((← rX_bits rs1) != (← rX_bits rs2))
  | .BLT => pure (zopz0zI_s (← rX_bits rs1) (← rX_bits rs2))
  | .BGE => pure (zopz0zKzJ_s (← rX_bits rs1) (← rX_bits rs2))
  | .BLTU => pure (zopz0zI_u (← rX_bits rs1) (← rX_bits rs2))
  | .BGEU => pure (zopz0zKzJ_u (← rX_bits rs1) (← rX_bits rs2))

private theorem bTypeCondition_preserves_stack_pointer (rs2 rs1 : regidx) (op : bop) :
    PreservesStackPointer (bTypeCondition rs2 rs1 op) := by
  cases op with
  | BEQ =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2
      (fun left right => left == right)
  | BNE =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2
      (fun left right => left != right)
  | BLT =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zI_s
  | BGE =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zKzJ_s
  | BLTU =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zI_u
  | BGEU =>
    simpa [bTypeCondition] using rXBitsComparison_preserves_stack_pointer rs1 rs2 zopz0zKzJ_u

private def bTypeOutcome (imm : BitVec 13) (taken : Bool) : SailM ExecutionResult := do
  if taken then
    jump_to ((← Sail.readReg PC) + sign_extend (m := 64) imm)
  else
    pure RETIRE_SUCCESS

private theorem bTypeOutcome_preserves_stack_pointer (imm : BitVec 13) (taken : Bool) :
    PreservesStackPointer (bTypeOutcome imm taken) := by
  unfold bTypeOutcome
  by_cases takenTrue : taken = true
  · rw [if_pos takenTrue]
    apply preservesStackPointer_bind (Sail.readReg PC) _
    · exact readReg_preserves_stack_pointer PC
    · intro pc
      exact jump_to_preserves_stack_pointer (pc + sign_extend (m := 64) imm)
  · rw [if_neg takenTrue]
    exact preservesStackPointer_pure RETIRE_SUCCESS

private theorem execute_BTYPE_factor (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    execute_BTYPE imm rs2 rs1 op = (do
      let taken ← bTypeCondition rs2 rs1 op
      bTypeOutcome imm taken) := by
  rfl

/-- `execute_BTYPE` preserves `x2` across normal and error outcomes for every branch opcode. -/
theorem execute_BTYPE_preserves_stack_pointer (imm : BitVec 13) (rs2 rs1 : regidx) (op : bop) :
    PreservesStackPointer (execute_BTYPE imm rs2 rs1 op) := by
  rw [execute_BTYPE_factor]
  apply preservesStackPointer_bind (bTypeCondition rs2 rs1 op) _
  · exact bTypeCondition_preserves_stack_pointer rs2 rs1 op
  · intro taken
    exact bTypeOutcome_preserves_stack_pointer imm taken

end BinaryFv.RiscV
