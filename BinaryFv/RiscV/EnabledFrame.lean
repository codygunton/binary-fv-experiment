import BinaryFv.RiscV.BTypeFrame

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open extension

/--
The current LOAD/STORE paths only query the extensions framed below.  This intentionally excludes
unrelated Zicfilp and stateen helper trees, which need their own generated-action frames.
-/
private theorem enabled_preserves_pure (value : α) :
    PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

private theorem enabled_preserves_bind (action : SailM α) (next : α → SailM β)
    (actionFrame : PreservesStackPointer action)
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

private theorem enabled_readReg_preserves_stack_pointer (register : Register) :
    PreservesStackPointer (readReg register : SailM (RegisterType register)) := by
  intro state
  cases hAction : (readReg register : SailM (RegisterType register)).run state with
  | ok value after =>
    change (readReg register : SailM (RegisterType register)) state = .ok value after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun current : State => current.regs.get? x2) projection
  | error error after =>
    change (readReg register : SailM (RegisterType register)) state = .error error after at hAction
    have projection := readReg_state_projection state register
    simpa [hAction] using congrArg (fun current : State => current.regs.get? x2) projection

/-- The generated Zicsr enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_zicsr_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Zicsr) := by
  rw [currentlyEnabled.eq_61]
  all_goals try simp
  exact enabled_preserves_pure _

/-- The generated supervisor-mode enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_s_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_S) := by
  rw [currentlyEnabled.eq_20]
  apply enabled_preserves_bind (readReg misa)
  · exact enabled_readReg_preserves_stack_pointer misa
  · intro _
    apply enabled_preserves_bind (currentlyEnabled Ext_Zicsr)
    · exact currentlyEnabled_zicsr_preserves_stack_pointer
    · intro _
      exact enabled_preserves_pure _

/-- The generated Sstc enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_sstc_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Sstc) := by
  rw [currentlyEnabled.eq_18]
  exact enabled_preserves_pure _

/-- The generated Svade enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_svade_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Svade) := by
  rw [currentlyEnabled.eq_54]
  exact enabled_preserves_pure _

/-- The generated Svadu enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_svadu_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Svadu) := by
  rw [currentlyEnabled.eq_55]
  exact enabled_preserves_pure _

/-- The generated Sv39 enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_sv39_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Sv39) := by
  rw [currentlyEnabled.eq_24]
  apply enabled_preserves_bind (currentlyEnabled Ext_S)
  · exact currentlyEnabled_s_preserves_stack_pointer
  · intro _
    exact enabled_preserves_pure _

/-- The generated Svnapot enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_svnapot_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Svnapot) := by
  rw [currentlyEnabled.eq_50]
  apply enabled_preserves_bind (currentlyEnabled Ext_Sv39)
  · exact currentlyEnabled_sv39_preserves_stack_pointer
  · intro _
    exact enabled_preserves_pure _

/-- The generated Svrsw60t59b enablement query leaves the observed stack pointer unchanged. -/
theorem currentlyEnabled_svrsw60t59b_preserves_stack_pointer :
    PreservesStackPointer (currentlyEnabled Ext_Svrsw60t59b) := by
  rw [currentlyEnabled.eq_52]
  apply enabled_preserves_bind (currentlyEnabled Ext_Sv39)
  · exact currentlyEnabled_sv39_preserves_stack_pointer
  · intro _
    exact enabled_preserves_pure _

end BinaryFv.RiscV
