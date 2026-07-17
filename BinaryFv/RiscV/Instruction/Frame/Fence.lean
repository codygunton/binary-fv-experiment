import BinaryFv.RiscV.Instruction.Frame.Register

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open barrier_kind

private theorem readReg_state_projection (state : State) (register : Register) :
    (match (readReg register : SailM (RegisterType register)) state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  cases hRead : state.regs.get? register <;>
    simp [PreSail.readReg, EStateM.bind, EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, MonadState.get,
      MonadStateOf.get, getThe, hRead] <;> rfl

private theorem is_fiom_active_state_projection (state : State) :
    (match is_fiom_active () state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  cases hPrivilege : (readReg cur_privilege : SailM Privilege).run state with
  | error error afterPrivilege =>
    change readReg cur_privilege state = .error error afterPrivilege at hPrivilege
    have afterPrivilegeEq : afterPrivilege = state := by
      have preserved := readReg_state_projection state cur_privilege
      simpa [hPrivilege] using preserved
    subst afterPrivilege
    simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege]
  | ok privilege afterPrivilege =>
    change readReg cur_privilege state = .ok privilege afterPrivilege at hPrivilege
    have afterPrivilegeEq : afterPrivilege = state := by
      have preserved := readReg_state_projection state cur_privilege
      simpa [hPrivilege] using preserved
    subst afterPrivilege
    cases privilege with
    | Machine =>
      simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege] <;> rfl
    | Supervisor =>
      cases hMenvcfg : (readReg menvcfg : SailM (BitVec 64)).run state with
      | error error afterMenvcfg =>
        change readReg menvcfg state = .error error afterMenvcfg at hMenvcfg
        have afterMenvcfgEq : afterMenvcfg = state := by
          have preserved := readReg_state_projection state menvcfg
          simpa [hMenvcfg] using preserved
        subst afterMenvcfg
        simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege,
          hMenvcfg] <;> rfl
      | ok menvcfgValue afterMenvcfg =>
        change readReg menvcfg state = .ok menvcfgValue afterMenvcfg at hMenvcfg
        have afterMenvcfgEq : afterMenvcfg = state := by
          have preserved := readReg_state_projection state menvcfg
          simpa [hMenvcfg] using preserved
        subst afterMenvcfg
        simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege,
          hMenvcfg] <;> rfl
    | User =>
      cases hMenvcfg : (readReg menvcfg : SailM (BitVec 64)).run state with
      | error error afterMenvcfg =>
        change readReg menvcfg state = .error error afterMenvcfg at hMenvcfg
        have afterMenvcfgEq : afterMenvcfg = state := by
          have preserved := readReg_state_projection state menvcfg
          simpa [hMenvcfg] using preserved
        subst afterMenvcfg
        simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege,
          hMenvcfg]
      | ok menvcfgValue afterMenvcfg =>
        change readReg menvcfg state = .ok menvcfgValue afterMenvcfg at hMenvcfg
        have afterMenvcfgEq : afterMenvcfg = state := by
          have preserved := readReg_state_projection state menvcfg
          simpa [hMenvcfg] using preserved
        subst afterMenvcfg
        cases hSenvcfg : (readReg senvcfg : SailM (BitVec 64)).run state with
        | error error afterSenvcfg =>
          change readReg senvcfg state = .error error afterSenvcfg at hSenvcfg
          have afterSenvcfgEq : afterSenvcfg = state := by
            have preserved := readReg_state_projection state senvcfg
            simpa [hSenvcfg] using preserved
          subst afterSenvcfg
          simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege,
            hMenvcfg, hSenvcfg] <;> rfl
        | ok senvcfgValue afterSenvcfg =>
          change readReg senvcfg state = .ok senvcfgValue afterSenvcfg at hSenvcfg
          have afterSenvcfgEq : afterSenvcfg = state := by
            have preserved := readReg_state_projection state senvcfg
            simpa [hSenvcfg] using preserved
          subst afterSenvcfg
          simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege,
            hMenvcfg, hSenvcfg] <;> rfl
    | VirtualUser =>
      simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege] <;> rfl
    | VirtualSupervisor =>
      simp [is_fiom_active, EStateM.bind, EStateM.instMonad, hPrivilege] <;> rfl

private theorem execute_fence_barrier_run (state : State) (pred succ : BitVec 4) :
    ((do
      match (Sail.BitVec.extractLsb pred 1 0, Sail.BitVec.extractLsb succ 1 0) with
      | (0b11, 0b11) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_rw_rw
      | (0b10, 0b11) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_r_rw
      | (0b10, 0b10) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_r_r
      | (0b11, 0b01) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_rw_w
      | (0b01, 0b01) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_w_w
      | (0b01, 0b11) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_w_rw
      | (0b11, 0b10) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_rw_r
      | (0b10, 0b01) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_r_w
      | (0b01, 0b10) => PreSail.ConcurrencyInterfaceV1.sail_barrier Barrier_RISCV_w_r
      | (_, 0b00) => pure ()
      | (_, _) => pure ()
      pure RETIRE_SUCCESS) : SailM ExecutionResult).run state = .ok RETIRE_SUCCESS state := by
  split <;> rfl

/-- The generated TSO fence is a state-preserving barrier. -/
theorem execute_FENCE_TSO_preserves_stack_pointer (state : State) :
    (match (execute_FENCE_TSO ()).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  rfl

/-- Every generated FENCE path, including FIOM-read errors, preserves `x2`. -/
theorem execute_FENCE_preserves_stack_pointer (state : State) (fm pred succ : BitVec 4)
    (source destination : regidx) :
    (match (execute_FENCE fm pred succ source destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases hFiom : (is_fiom_active ()).run state with
  | error error afterFiom =>
    change is_fiom_active () state = .error error afterFiom at hFiom
    have afterFiomEq : afterFiom = state := by
      have preserved := is_fiom_active_state_projection state
      simpa [hFiom] using preserved
    subst afterFiom
    simp [execute_FENCE, EStateM.run, EStateM.bind, EStateM.instMonad, hFiom]
  | ok fiom afterFiom =>
    change is_fiom_active () state = .ok fiom afterFiom at hFiom
    have afterFiomEq : afterFiom = state := by
      have preserved := is_fiom_active_state_projection state
      simpa [hFiom] using preserved
    subst afterFiom
    have barrierRun := execute_fence_barrier_run state
      (effective_fence_set pred fiom) (effective_fence_set succ fiom)
    have observed := congrArg (fun outcome =>
      match outcome with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) barrierRun
    simpa [execute_FENCE, EStateM.run, EStateM.bind, EStateM.instMonad, hFiom] using observed

end BinaryFv.RiscV
