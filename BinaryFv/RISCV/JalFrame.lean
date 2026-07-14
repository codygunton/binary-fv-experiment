import BinaryFv.RISCV.BTypeFrame

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open extension

/-- An action whose successful and failing outcomes retain the entire machine state. -/
private def StateProjection (action : SailM α) : Prop :=
  ∀ state,
    (match action.run state with
    | .ok _ state' => state'
    | .error _ state' => state') = state

private theorem state_projection_bind (first : SailM α) (next : α → SailM β)
    (firstFrame : StateProjection first) (nextFrame : ∀ value, StateProjection (next value)) :
    StateProjection (first >>= next) := by
  intro state
  cases hFirst : first.run state with
  | error error after =>
    change first state = .error error after at hFirst
    have afterEq : after = state := by
      have preserved := firstFrame state
      change (match first state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hFirst] using preserved
    subst after
    simp [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst]
  | ok value afterFirst =>
    change first state = .ok value afterFirst at hFirst
    have afterFirstEq : afterFirst = state := by
      have preserved := firstFrame state
      change (match first state with
        | .ok _ state' => state'
        | .error _ state' => state') = state at preserved
      simpa [hFirst] using preserved
    subst afterFirst
    cases hNext : (next value).run state with
    | error error after =>
      change next value state = .error error after at hNext
      have afterEq : after = state := by
        have preserved := nextFrame value state
        change (match next value state with
          | .ok _ state' => state'
          | .error _ state' => state') = state at preserved
        simpa [hNext] using preserved
      subst after
      simp [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst, hNext]
    | ok result after =>
      change next value state = .ok result after at hNext
      have afterEq : after = state := by
        have preserved := nextFrame value state
        change (match next value state with
          | .ok _ state' => state'
          | .error _ state' => state') = state at preserved
        simpa [hNext] using preserved
      subst after
      simp [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst, hNext]

private theorem state_projection_pure (value : α) : StateProjection (pure value : SailM α) := by
  intro state
  rfl

private theorem preserves_stack_pointer_bind (first : SailM α) (next : α → SailM β)
    (firstFrame : PreservesStackPointer first)
    (nextFrame : ∀ value, PreservesStackPointer (next value)) :
    PreservesStackPointer (first >>= next) := by
  intro state
  cases hFirst : first.run state with
  | error error after =>
    change first state = .error error after at hFirst
    have afterEq : after.regs.get? x2 = state.regs.get? x2 := by
      simpa [EStateM.run, hFirst] using firstFrame state
    simpa [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst] using afterEq
  | ok value afterFirst =>
    change first state = .ok value afterFirst at hFirst
    have afterFirstEq : afterFirst.regs.get? x2 = state.regs.get? x2 := by
      simpa [EStateM.run, hFirst] using firstFrame state
    cases hNext : (next value).run afterFirst with
    | error error after =>
      change next value afterFirst = .error error after at hNext
      have afterEq : after.regs.get? x2 = afterFirst.regs.get? x2 := by
        simpa [EStateM.run, hNext] using nextFrame value afterFirst
      simpa [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst, hNext] using
        afterEq.trans afterFirstEq
    | ok result after =>
      change next value afterFirst = .ok result after at hNext
      have afterEq : after.regs.get? x2 = afterFirst.regs.get? x2 := by
        simpa [EStateM.run, hNext] using nextFrame value afterFirst
      simpa [EStateM.run, EStateM.bind, EStateM.instMonad, hFirst, hNext] using
        afterEq.trans afterFirstEq

private theorem state_projection_preserves_stack_pointer (action : SailM α)
    (stateFrame : StateProjection action) : PreservesStackPointer action := by
  intro state
  cases hAction : action.run state <;>
    simpa [hAction] using congrArg (fun state => state.regs.get? x2) (stateFrame state)

private theorem preserves_stack_pointer_pure (value : α) :
    PreservesStackPointer (pure value : SailM α) :=
  state_projection_preserves_stack_pointer _ (state_projection_pure value)

private theorem readReg_state_projection' (register : Register) :
    StateProjection (readReg register : SailM (RegisterType register)) := by
  intro state
  cases hAction : (readReg register : SailM (RegisterType register)) state <;>
    simpa [EStateM.run, hAction] using readReg_state_projection state register

private theorem read_senvcfg_state_projection : StateProjection (read_senvcfg ()) := by
  simpa [read_senvcfg] using
    state_projection_bind (readReg senvcfg : SailM (BitVec 64))
      (fun first => do
        let menv ← (readReg menvcfg : SailM (BitVec 64))
        let second ← (readReg senvcfg : SailM (BitVec 64))
        pure (_update_SEnvcfg_SSE first (_get_MEnvcfg_SSE menv &&& _get_SEnvcfg_SSE second)))
      (readReg_state_projection' senvcfg)
      (fun first =>
        state_projection_bind (readReg menvcfg : SailM (BitVec 64))
          (fun menv => do
            let second ← (readReg senvcfg : SailM (BitVec 64))
            pure (_update_SEnvcfg_SSE first (_get_MEnvcfg_SSE menv &&& _get_SEnvcfg_SSE second)))
          (readReg_state_projection' menvcfg)
          (fun menv =>
            state_projection_bind (readReg senvcfg : SailM (BitVec 64))
              (fun second =>
                pure
                  (_update_SEnvcfg_SSE first
                    (_get_MEnvcfg_SSE menv &&& _get_SEnvcfg_SSE second)))
              (readReg_state_projection' senvcfg)
              (fun _ => state_projection_pure _)))

private theorem currently_enabled_zicsr_state_projection :
    StateProjection (currentlyEnabled Ext_Zicsr) := by
  intro state
  simp [currentlyEnabled, EStateM.run, EStateM.pure, EStateM.instMonad]

private theorem currently_enabled_s_state_projection :
    StateProjection (currentlyEnabled Ext_S) := by
  simpa [currentlyEnabled] using
    state_projection_bind (readReg misa : SailM (BitVec 64))
      (fun misaValue => do
        let zicsr ← currentlyEnabled Ext_Zicsr
        pure (hartSupports Ext_S && ((_get_Misa_S misaValue == 1#1) && zicsr)))
      (readReg_state_projection' misa)
      (fun misaValue =>
        state_projection_bind (currentlyEnabled Ext_Zicsr)
          (fun zicsr => pure (hartSupports Ext_S && ((_get_Misa_S misaValue == 1#1) && zicsr)))
          currently_enabled_zicsr_state_projection
          (fun zicsr => state_projection_pure _))

private theorem get_xLPE_state_projection (privilege : Privilege) :
    StateProjection (get_xLPE privilege) := by
  cases privilege with
  | Machine =>
    simpa [get_xLPE] using
      state_projection_bind (readReg mseccfg : SailM (BitVec 64))
        (fun value => pure (bool_bit_backwards (_get_Seccfg_MLPE value)))
        (readReg_state_projection' mseccfg)
        (fun _ => state_projection_pure _)
  | Supervisor =>
    simpa [get_xLPE] using
      state_projection_bind (readReg menvcfg : SailM (BitVec 64))
        (fun value => pure (bool_bit_backwards (_get_MEnvcfg_LPE value)))
        (readReg_state_projection' menvcfg)
        (fun _ => state_projection_pure _)
  | User =>
    simpa [get_xLPE] using
      state_projection_bind (currentlyEnabled Ext_S)
        (fun enabled =>
          if enabled then
            do
              let value ← read_senvcfg ()
              pure (bool_bit_backwards (_get_SEnvcfg_LPE value))
          else
            do
              let value ← (readReg menvcfg : SailM (BitVec 64))
              pure (bool_bit_backwards (_get_MEnvcfg_LPE value)))
        currently_enabled_s_state_projection
        (fun enabled => by
          cases enabled
          · exact state_projection_bind (readReg menvcfg : SailM (BitVec 64))
              (fun value => pure (bool_bit_backwards (_get_MEnvcfg_LPE value)))
              (readReg_state_projection' menvcfg)
              (fun _ => state_projection_pure _)
          · exact state_projection_bind (read_senvcfg ())
              (fun value => pure (bool_bit_backwards (_get_SEnvcfg_LPE value)))
              read_senvcfg_state_projection
              (fun _ => state_projection_pure _))
  | VirtualSupervisor =>
    intro state
    unfold get_xLPE internal_error
    unfold Sail.sailThrow
    simp only [EStateM.run]
    rfl
  | VirtualUser =>
    intro state
    unfold get_xLPE internal_error
    unfold Sail.sailThrow
    simp only [EStateM.run]
    rfl

private theorem currently_enabled_zicfilp_state_projection :
    StateProjection (currentlyEnabled Ext_Zicfilp) := by
  simpa [currentlyEnabled] using
    state_projection_bind (readReg cur_privilege : SailM Privilege)
      (fun privilege => do
        let lpe ← get_xLPE privilege
        let zicsr ← currentlyEnabled Ext_Zicsr
        pure (zicsr && (hartSupports Ext_Zicfilp && lpe)))
      (readReg_state_projection' cur_privilege)
      (fun privilege =>
        state_projection_bind (get_xLPE privilege)
          (fun lpe => do
            let zicsr ← currentlyEnabled Ext_Zicsr
            pure (zicsr && (hartSupports Ext_Zicfilp && lpe)))
          (get_xLPE_state_projection privilege)
          (fun lpe =>
            state_projection_bind (currentlyEnabled Ext_Zicsr)
              (fun zicsr => pure (zicsr && (hartSupports Ext_Zicfilp && lpe)))
              currently_enabled_zicsr_state_projection
              (fun zicsr => state_projection_pure _)))

/-- The generated next-PC read leaves the machine state unchanged on every outcome. -/
private theorem get_next_pc_state_projection (state : State) :
    (match (get_next_pc ()).run state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  cases stored : state.regs.get? nextPC <;>
    simp [get_next_pc, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
      EStateM.pure, EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable,
      MonadState.get, MonadStateOf.get, getThe, stored] <;> rfl

/-- The generated Zicfilp link-state update preserves `x2` on every outcome. -/
private theorem update_elp_state_preserves_stack_pointer (state : State) (source : regidx) :
    (match (update_elp_state source).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  cases hEnabled : (currentlyEnabled Ext_Zicfilp).run state with
  | error error after =>
    change currentlyEnabled Ext_Zicfilp state = .error error after at hEnabled
    have afterEq : after = state := by
      have preserved := currently_enabled_zicfilp_state_projection state
      simpa [EStateM.run, hEnabled] using preserved
    subst after
    simp [update_elp_state, EStateM.run, EStateM.bind, EStateM.instMonad, hEnabled]
  | ok enabled after =>
    change currentlyEnabled Ext_Zicfilp state = .ok enabled after at hEnabled
    have afterEq : after = state := by
      have preserved := currently_enabled_zicfilp_state_projection state
      simpa [EStateM.run, hEnabled] using preserved
    subst after
    cases enabled <;>
      simp [update_elp_state, PreSail.writeReg, EStateM.run, EStateM.bind, EStateM.modifyGet,
        EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
        hEnabled, Std.ExtDHashMap.get?_insert]

private theorem get_next_pc_frame : PreservesStackPointer (get_next_pc ()) := by
  intro state
  cases hAction : (get_next_pc ()).run state <;>
    simpa [hAction] using
      congrArg (fun state => state.regs.get? x2) (get_next_pc_state_projection state)

private theorem readReg_frame (register : Register) :
    PreservesStackPointer (readReg register : SailM (RegisterType register)) :=
  state_projection_preserves_stack_pointer _ (readReg_state_projection' register)

private theorem rX_bits_frame (source : regidx) : PreservesStackPointer (rX_bits source) := by
  intro state
  cases hAction : (rX_bits source).run state <;>
    simpa [hAction] using
      congrArg (fun state => state.regs.get? x2) (rX_bits_state_projection state source)

private theorem update_elp_state_frame (source : regidx) :
    PreservesStackPointer (update_elp_state source) := by
  intro state
  cases hAction : (update_elp_state source).run state <;>
    simpa [hAction] using update_elp_state_preserves_stack_pointer state source

private theorem wX_bits_frame (destination : regidx) (data : BitVec 64)
    (notStack : destination ≠ stackPointer) : PreservesStackPointer (wX_bits destination data) := by
  intro state
  cases hAction : (wX_bits destination data).run state <;>
    simpa [hAction] using wX_bits_preserves_stack_pointer state destination data notStack

private theorem write_retire_frame (destination : regidx) (data : BitVec 64)
    (notStack : destination ≠ stackPointer) :
    PreservesStackPointer (do
      wX_bits destination data
      pure RETIRE_SUCCESS) :=
  preserves_stack_pointer_bind (wX_bits destination data) (fun _ => pure RETIRE_SUCCESS)
    (wX_bits_frame destination data notStack)
    (fun _ => preserves_stack_pointer_pure _)

private theorem jump_to_frame (target : BitVec 64) : PreservesStackPointer (jump_to target) := by
  intro state
  have frame := jump_to_preserves_stack_pointer target
  cases hAction : (jump_to target).run state <;>
    simpa [hAction] using frame state

private theorem jump_then_write_frame (target link : BitVec 64) (destination : regidx)
    (notStack : destination ≠ stackPointer) (jumpFrame : PreservesStackPointer (jump_to target)) :
    PreservesStackPointer (do
      match ← jump_to target with
      | .Retire_Success () => do
        wX_bits destination link
        pure RETIRE_SUCCESS
      | failure => pure failure) := by
  refine preserves_stack_pointer_bind (jump_to target) (fun outcome =>
    match outcome with
    | .Retire_Success () => do
      wX_bits destination link
      pure RETIRE_SUCCESS
    | failure => pure failure) jumpFrame ?_
  intro outcome
  cases outcome
  · exact write_retire_frame destination link notStack
  all_goals
    exact preserves_stack_pointer_pure _

private theorem execute_JAL_frame (immediate : BitVec 21) (destination : regidx)
    (notStack : destination ≠ stackPointer)
    (jumpFrame : ∀ target, PreservesStackPointer (jump_to target)) :
    PreservesStackPointer (execute_JAL immediate destination) := by
  simpa [execute_JAL] using
    preserves_stack_pointer_bind (get_next_pc ()) (fun link => do
      let pc ← (readReg PC : SailM (BitVec 64))
      match ← jump_to (pc + sign_extend (m := 64) immediate) with
      | .Retire_Success () => do
        wX_bits destination link
        pure RETIRE_SUCCESS
      | failure => pure failure) get_next_pc_frame
      (fun link =>
        preserves_stack_pointer_bind (readReg PC : SailM (BitVec 64)) (fun pc =>
          do
            match ← jump_to (pc + sign_extend (m := 64) immediate) with
            | .Retire_Success () => do
              wX_bits destination link
              pure RETIRE_SUCCESS
            | failure => pure failure) (readReg_frame PC)
          (fun pc =>
            jump_then_write_frame (pc + sign_extend (m := 64) immediate) link destination notStack
              (jumpFrame (pc + sign_extend (m := 64) immediate))))

private theorem jalr_target_frame (immediate : BitVec 12) (source destination : regidx)
    (link : BitVec 64) (notStack : destination ≠ stackPointer)
    (jumpFrame : ∀ target, PreservesStackPointer (jump_to target)) :
    PreservesStackPointer (do
      let target ← do pure ((← rX_bits source) + sign_extend (m := 64) immediate)
      match ← jump_to (Sail.BitVec.update target 0 0#1) with
      | .Retire_Success () => do
        wX_bits destination link
        pure RETIRE_SUCCESS
      | failure => pure failure) := by
  simpa [EStateM.bind, EStateM.pure, EStateM.instMonad] using
    preserves_stack_pointer_bind (rX_bits source) (fun value =>
      do
        match ← jump_to (Sail.BitVec.update (value + sign_extend (m := 64) immediate) 0 0#1) with
        | .Retire_Success () => do
          wX_bits destination link
          pure RETIRE_SUCCESS
        | failure => pure failure) (rX_bits_frame source)
      (fun value =>
        jump_then_write_frame
          (Sail.BitVec.update (value + sign_extend (m := 64) immediate) 0 0#1) link destination
          notStack
          (jumpFrame (Sail.BitVec.update (value + sign_extend (m := 64) immediate) 0 0#1)))

private theorem execute_JALR_frame (immediate : BitVec 12) (source destination : regidx)
    (notStack : destination ≠ stackPointer)
    (jumpFrame : ∀ target, PreservesStackPointer (jump_to target)) :
    PreservesStackPointer (execute_JALR immediate source destination) := by
  simpa [execute_JALR] using
    preserves_stack_pointer_bind (update_elp_state source) (fun _ => do
      let link ← get_next_pc ()
      let target ← do pure ((← rX_bits source) + sign_extend (m := 64) immediate)
      match ← jump_to (Sail.BitVec.update target 0 0#1) with
      | .Retire_Success () => do
        wX_bits destination link
        pure RETIRE_SUCCESS
      | failure => pure failure) (update_elp_state_frame source)
      (fun _ =>
        preserves_stack_pointer_bind (get_next_pc ()) (fun link => do
          let target ← do pure ((← rX_bits source) + sign_extend (m := 64) immediate)
          match ← jump_to (Sail.BitVec.update target 0 0#1) with
          | .Retire_Success () => do
            wX_bits destination link
            pure RETIRE_SUCCESS
          | failure => pure failure) get_next_pc_frame
          (fun link =>
            jalr_target_frame immediate source destination link notStack jumpFrame))

private theorem execute_JAL_with_jump_frame (state : State) (immediate : BitVec 21)
    (destination : regidx) (notStack : destination ≠ stackPointer)
    (jumpFrame : ∀ target, PreservesStackPointer (jump_to target)) :
    (match (execute_JAL immediate destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  have frame := execute_JAL_frame immediate destination notStack jumpFrame
  cases hAction : (execute_JAL immediate destination).run state <;>
    simpa [hAction] using frame state

private theorem execute_JALR_with_jump_frame (state : State) (immediate : BitVec 12)
    (source destination : regidx) (notStack : destination ≠ stackPointer)
    (jumpFrame : ∀ target, PreservesStackPointer (jump_to target)) :
    (match (execute_JALR immediate source destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  have frame := execute_JALR_frame immediate source destination notStack jumpFrame
  cases hAction : (execute_JALR immediate source destination).run state <;>
    simpa [hAction] using frame state

/-- Generated JAL preserves `x2` whenever its link destination is not the stack pointer. -/
theorem execute_JAL_preserves_stack_pointer (state : State) (immediate : BitVec 21)
    (destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute_JAL immediate destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  exact execute_JAL_with_jump_frame state immediate destination notStack jump_to_frame

/-- Generated JALR preserves `x2` whenever its link destination is not the stack pointer. -/
theorem execute_JALR_preserves_stack_pointer (state : State) (immediate : BitVec 12)
    (source destination : regidx) (notStack : destination ≠ stackPointer) :
    (match (execute_JALR immediate source destination).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  exact execute_JALR_with_jump_frame state immediate source destination notStack jump_to_frame

end BinaryFv.RISCV
