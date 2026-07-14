import BinaryFv.RISCV.ClintFrame

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

private theorem htif_frame_pure (value : α) :
    PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

private theorem htif_frame_throw (error : Sail.Error exception) :
    PreservesStackPointer (EStateM.throw error : SailM α) := by
  intro state
  rfl

private theorem htif_frame_bind (first : SailM α) (next : α → SailM β)
    (firstFrame : PreservesStackPointer first)
    (nextFrame : ∀ value, PreservesStackPointer (next value)) :
    PreservesStackPointer (first >>= next) := by
  intro state
  cases hFirst : first.run state with
  | error error middle =>
    change first state = .error error middle at hFirst
    have firstFrame' := firstFrame state
    change (match first state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at firstFrame'
    change (match EStateM.bind first next state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = _
    unfold EStateM.bind
    rw [hFirst]
    simpa only [hFirst] using firstFrame'
  | ok value middle =>
    change first state = .ok value middle at hFirst
    have firstFrame' := firstFrame state
    change (match first state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at firstFrame'
    calc
      (match (first >>= next).run state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) =
        (match (next value).run middle with
        | .ok _ state' => state'.regs.get? x2
        | .error _ state' => state'.regs.get? x2) := by
          change (match EStateM.bind first next state with
          | .ok _ state' => state'.regs.get? x2
          | .error _ state' => state'.regs.get? x2) = _
          unfold EStateM.bind
          rw [hFirst]
          rfl
      _ = middle.regs.get? x2 := nextFrame value middle
      _ = state.regs.get? x2 := by simpa only [hFirst] using firstFrame'

private theorem htif_frame_map (action : SailM α) (function : α → β)
    (actionFrame : PreservesStackPointer action) :
    PreservesStackPointer (function <$> action) := by
  exact htif_frame_bind action (fun value => (EStateM.pure (function value) : SailM β))
    actionFrame (fun _ => htif_frame_pure _)

private theorem htif_frame_ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : PreservesStackPointer whenTrue)
    (falseFrame : PreservesStackPointer whenFalse) :
    PreservesStackPointer (if condition then whenTrue else whenFalse) := by
  cases condition
  · exact falseFrame
  · exact trueFrame

private theorem htif_frame_read_reg (register : Register) :
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

private theorem htif_frame_write_reg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) :
    PreservesStackPointer (writeReg written value) := by
  intro before
  change (match (PreSail.writeReg written value : SailM PUnit).run before with
    | .ok _ after => after.regs.get? x2
    | .error _ after => after.regs.get? x2) = before.regs.get? x2
  rw [writeReg_run]
  exact writeReg_read_unchanged before written x2 value notStack

private theorem htif_frame_internal_error (file : String) (line : Int) (message : String) :
    PreservesStackPointer (internal_error file line message : SailM α) := by
  unfold internal_error Sail.sailThrow PreSail.sailThrow
  exact htif_frame_throw _

private def PreservesStackPointerE (action : SailME ε α) : Prop :=
  PreservesStackPointer (ExceptT.run action)

private theorem htif_frame_e_lift (action : SailM α) (actionFrame : PreservesStackPointer action) :
    PreservesStackPointerE (liftM action : SailME ε α) := by
  change PreservesStackPointer (ExceptT.run (liftM action : SailME ε α))
  simpa only [ExceptT.run, ExceptT.mk, MonadLift.monadLift] using
    htif_frame_map action (fun value =>
      (Except.ok value : Except (Sail.Error exception ⊕ ε) α)) actionFrame

private theorem htif_frame_e_bind (first : SailME ε α) (next : α → SailME ε β)
    (firstFrame : PreservesStackPointerE first)
    (nextFrame : ∀ value, PreservesStackPointerE (next value)) :
    PreservesStackPointerE (first >>= next) := by
  change PreservesStackPointer (ExceptT.run first >>= ExceptT.bindCont next)
  apply htif_frame_bind
  · exact firstFrame
  · intro result
    cases result with
    | error error => exact htif_frame_pure _
    | ok value => exact nextFrame value

private theorem htif_frame_e_pure (value : α) :
    PreservesStackPointerE (pure value : SailME ε α) := by
  change PreservesStackPointer (ExceptT.run (ExceptT.pure value : SailME ε α))
  exact htif_frame_pure _

private theorem htif_frame_e_throw (error : ε) :
    PreservesStackPointerE (Sail.SailME.throw error : SailME ε α) := by
  change PreservesStackPointer (ExceptT.run (Sail.SailME.throw error : SailME ε α))
  unfold Sail.SailME.throw PreSail.PreSailME.throw
  exact htif_frame_pure _

private theorem htif_frame_e_ite (condition : Bool) (whenTrue whenFalse : SailME ε α)
    (trueFrame : PreservesStackPointerE whenTrue)
    (falseFrame : PreservesStackPointerE whenFalse) :
    PreservesStackPointerE (if condition then whenTrue else whenFalse) := by
  cases condition
  · exact falseFrame
  · exact trueFrame

private theorem htif_frame_sail_me_run (action : SailME α α)
    (actionFrame : PreservesStackPointerE action) :
    PreservesStackPointer (Sail.SailME.run action) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  apply htif_frame_bind
  · exact actionFrame
  · intro result
    cases result with
    | error error =>
      cases error with
      | inl error => exact htif_frame_throw error
      | inr error => exact htif_frame_pure error
    | ok value => exact htif_frame_pure value

private theorem htif_frame_access_fault (access : MemoryAccessType mem_payload) :
    PreservesStackPointer (accessFaultFromAccessType access) := by
  intro state
  cases access with
  | InstructionFetch _ => rfl
  | Load payload => cases payload <;> rfl
  | Store payload => cases payload <;> rfl
  | LoadReserved payload => cases payload <;> rfl
  | StoreConditional payload => cases payload <;> rfl
  | Atomic request =>
    rcases request with ⟨operation, readPayload, writePayload⟩
    cases readPayload <;> cases writePayload <;> rfl
  | CacheAccess operation =>
    cases operation with
    | CB_manage operation => rfl
    | CB_zero _ => rfl
    | CB_prefetch operation => cases operation <;> rfl

private theorem htif_frame_load_base :
    PreservesStackPointer ((do
      match (← readReg htif_tohost_base) with
      | some base => pure base
      | none => (internal_error "sys/platform.sail" 268
        "HTIF load while HTIF isn't enabled" : SailM physaddrbits)) : SailM physaddrbits) := by
  apply htif_frame_bind (readReg htif_tohost_base)
  · exact htif_frame_read_reg htif_tohost_base
  · intro base
    cases base with
    | some address => exact htif_frame_pure address
    | none => exact htif_frame_internal_error _ _ _

private theorem htif_frame_read_then_pure (register : Register)
    (next : RegisterType register → α) :
    PreservesStackPointer (readReg register >>= fun value => pure (next value)) := by
  apply htif_frame_bind (readReg register)
  · exact htif_frame_read_reg register
  · intro value
    exact htif_frame_pure _

/-- The generated HTIF load path preserves `x2` on normal and error outcomes. -/
theorem htif_load_preserves_stack_pointer (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat) :
    PreservesStackPointer (htif_load access address width) := by
  unfold htif_load
  simp only [get_config_print_htif, Bool.false_eq_true, ↓reduceIte]
  apply htif_frame_bind (pure ())
  · exact htif_frame_pure _
  · intro _
    apply htif_frame_bind
    · exact htif_frame_load_base
    · intro base
      apply htif_frame_ite
      · exact htif_frame_read_then_pure htif_tohost _
      · apply htif_frame_ite
        · exact htif_frame_read_then_pure htif_tohost _
        · apply htif_frame_ite
          · exact htif_frame_read_then_pure htif_tohost _
          · apply htif_frame_bind (accessFaultFromAccessType access)
            · exact htif_frame_access_fault access
            · intro _
              exact htif_frame_pure _

private theorem htif_frame_reset : PreservesStackPointer (reset_htif ()) := by
  unfold reset_htif
  apply htif_frame_bind (writeReg htif_cmd_write _)
  · exact htif_frame_write_reg htif_cmd_write _ (by decide)
  · intro _
    apply htif_frame_bind (writeReg htif_payload_writes _)
    · exact htif_frame_write_reg htif_payload_writes _ (by decide)
    · intro _
      exact htif_frame_write_reg htif_tohost _ (by decide)

private theorem htif_frame_plat_term_write (value : BitVec 8) :
    PreservesStackPointer (plat_term_write value) := by
  unfold plat_term_write
  intro state
  rfl

private theorem htif_frame_e_read_reg (register : Register) :
    PreservesStackPointerE (liftM (Sail.readReg register) : SailME ε (RegisterType register)) := by
  exact htif_frame_e_lift (Sail.readReg register) (htif_frame_read_reg register)

private theorem htif_frame_e_write_reg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) :
    PreservesStackPointerE (liftM (Sail.writeReg written value) : SailME ε PUnit) := by
  exact htif_frame_e_lift (Sail.writeReg written value)
    (htif_frame_write_reg written value notStack)

private theorem htif_frame_e_base :
    PreservesStackPointerE ((do
      match (← liftM (Sail.readReg htif_tohost_base)) with
      | some base => pure base
      | none => liftM (internal_error "sys/platform.sail" 288
          "HTIF store while HTIF isn't enabled" : SailM physaddrbits)) :
      SailME (Sail.Result Bool ExceptionType) physaddrbits) := by
  apply htif_frame_e_bind
  · exact htif_frame_e_read_reg htif_tohost_base
  · intro base
    cases base with
    | some address => exact htif_frame_e_pure address
    | none => exact htif_frame_e_lift (internal_error _ _ _) (htif_frame_internal_error _ _ _)

private def htif_frame_store_eight_initial (width : Nat) (data : BitVec (8 * width)) :
    SailME (Sail.Result Bool ExceptionType) PUnit := do
  liftM (Sail.writeReg htif_cmd_write 1#1)
  let payloadWrites ← liftM (Sail.readReg htif_payload_writes)
  liftM (Sail.writeReg htif_payload_writes (Sail.BitVec.addInt payloadWrites 1))
  liftM (Sail.writeReg htif_tohost (zero_extend (m := 64) data))

private theorem htif_frame_store_eight_initial_preserves_stack_pointer (width : Nat)
    (data : BitVec (8 * width)) :
    PreservesStackPointerE (htif_frame_store_eight_initial width data) := by
  unfold htif_frame_store_eight_initial
  apply htif_frame_e_bind
  · exact htif_frame_e_write_reg htif_cmd_write _ (by decide)
  · intro _
    apply htif_frame_e_bind
    · exact htif_frame_e_read_reg htif_payload_writes
    · intro payloadWrites
      apply htif_frame_e_bind
      · exact htif_frame_e_write_reg htif_payload_writes _ (by decide)
      · intro _
        exact htif_frame_e_write_reg htif_tohost _ (by decide)

private def htif_frame_store_low_initial (width : Nat) (_paddr _base : physaddrbits)
    (data : BitVec (8 * width)) : SailME (Sail.Result Bool ExceptionType) PUnit := do
  let tohost ← liftM (Sail.readReg htif_tohost)
  if data == Sail.BitVec.extractLsb tohost 31 0 then do
    let payloadWrites ← liftM (Sail.readReg htif_payload_writes)
    liftM (Sail.writeReg htif_payload_writes (Sail.BitVec.addInt payloadWrites 1))
  else liftM (Sail.writeReg htif_payload_writes 0x1#4)
  let latestTohost ← liftM (Sail.readReg htif_tohost)
  liftM (Sail.writeReg htif_tohost
    (Sail.BitVec.updateSubrange latestTohost 31 0 (BitVec.setWidth (31 - 0 + 1) data)))

private theorem htif_frame_store_low_initial_preserves_stack_pointer (width : Nat)
    (paddr base : physaddrbits) (data : BitVec (8 * width)) :
    PreservesStackPointerE (htif_frame_store_low_initial width paddr base data) := by
  unfold htif_frame_store_low_initial
  apply htif_frame_e_bind
  · exact htif_frame_e_read_reg htif_tohost
  · intro tohost
    apply htif_frame_e_ite
    · apply htif_frame_e_bind
      · exact htif_frame_e_read_reg htif_payload_writes
      · intro payloadWrites
        apply htif_frame_e_bind
        · exact htif_frame_e_write_reg htif_payload_writes _ (by decide)
        · intro _
          apply htif_frame_e_bind
          · exact htif_frame_e_read_reg htif_tohost
          · intro latestTohost
            exact htif_frame_e_write_reg htif_tohost _ (by decide)
    · apply htif_frame_e_bind
      · exact htif_frame_e_write_reg htif_payload_writes _ (by decide)
      · intro _
        apply htif_frame_e_bind
        · exact htif_frame_e_read_reg htif_tohost
        · intro latestTohost
          exact htif_frame_e_write_reg htif_tohost _ (by decide)

private def htif_frame_store_high_initial (width : Nat) (_paddr _base : physaddrbits)
    (data : BitVec (8 * width)) : SailME (Sail.Result Bool ExceptionType) PUnit := do
  let tohost ← liftM (Sail.readReg htif_tohost)
  if Sail.BitVec.extractLsb data 15 0 == Sail.BitVec.extractLsb tohost 47 32 then do
    let payloadWrites ← liftM (Sail.readReg htif_payload_writes)
    liftM (Sail.writeReg htif_payload_writes (Sail.BitVec.addInt payloadWrites 1))
  else liftM (Sail.writeReg htif_payload_writes 0x1#4)
  liftM (Sail.writeReg htif_cmd_write 1#1)
  let latestTohost ← liftM (Sail.readReg htif_tohost)
  liftM (Sail.writeReg htif_tohost
    (Sail.BitVec.updateSubrange latestTohost 63 32 (BitVec.setWidth (63 - 32 + 1) data)))

private theorem htif_frame_store_high_initial_preserves_stack_pointer (width : Nat)
    (paddr base : physaddrbits) (data : BitVec (8 * width)) :
    PreservesStackPointerE (htif_frame_store_high_initial width paddr base data) := by
  unfold htif_frame_store_high_initial
  apply htif_frame_e_bind
  · exact htif_frame_e_read_reg htif_tohost
  · intro tohost
    apply htif_frame_e_ite
    · apply htif_frame_e_bind
      · exact htif_frame_e_read_reg htif_payload_writes
      · intro payloadWrites
        apply htif_frame_e_bind
        · exact htif_frame_e_write_reg htif_payload_writes _ (by decide)
        · intro _
          apply htif_frame_e_bind
          · exact htif_frame_e_write_reg htif_cmd_write _ (by decide)
          · intro _
            apply htif_frame_e_bind
            · exact htif_frame_e_read_reg htif_tohost
            · intro latestTohost
              exact htif_frame_e_write_reg htif_tohost _ (by decide)
    · apply htif_frame_e_bind
      · exact htif_frame_e_write_reg htif_payload_writes _ (by decide)
      · intro _
        apply htif_frame_e_bind
        · exact htif_frame_e_write_reg htif_cmd_write _ (by decide)
        · intro _
          apply htif_frame_e_bind
          · exact htif_frame_e_read_reg htif_tohost
          · intro latestTohost
            exact htif_frame_e_write_reg htif_tohost _ (by decide)

private def htif_frame_store_rest_initial (width : Nat) (paddr base : physaddrbits)
    (data : BitVec (8 * width)) : SailME (Sail.Result Bool ExceptionType) PUnit :=
  if ((width == 4) && (paddr == base)) then
    htif_frame_store_low_initial width paddr base data
  else if ((width == 4) && (paddr == Sail.BitVec.addInt base 4)) then
    htif_frame_store_high_initial width paddr base data
  else Sail.SailME.throw (Sail.Err (ExceptionType.E_SAMO_Access_Fault ()))

private theorem htif_frame_store_rest_initial_preserves_stack_pointer (width : Nat)
    (paddr base : physaddrbits) (data : BitVec (8 * width)) :
    PreservesStackPointerE (htif_frame_store_rest_initial width paddr base data) := by
  unfold htif_frame_store_rest_initial
  apply htif_frame_e_ite
  · exact htif_frame_store_low_initial_preserves_stack_pointer width paddr base data
  · apply htif_frame_e_ite
    · exact htif_frame_store_high_initial_preserves_stack_pointer width paddr base data
    · exact htif_frame_e_throw _

private theorem htif_frame_e_command_action (command : BitVec 64)
    (data : BitVec (8 * width)) :
    PreservesStackPointerE (match _get_htif_cmd_device command with
      | 0x00 =>
        if Sail.BitVec.access (_get_htif_cmd_payload command) 0 == 1#1 then
          (do
            liftM (Sail.writeReg htif_done true)
            liftM (Sail.writeReg htif_exit_code
              ((zero_extend (m := 64) (_get_htif_cmd_payload command)) >>> 1)))
        else pure ()
      | 0x01 =>
        (do
          match _get_htif_cmd_cmd command with
          | 0x00 => pure ()
          | 0x01 => liftM (plat_term_write
              (Sail.BitVec.extractLsb (_get_htif_cmd_payload command) 7 0))
          | unknown => pure (Sail.print ("Unknown term cmd: " ++
              Sail.BitVec.toFormatted unknown))
          liftM (reset_htif ()))
      | _ => pure (Sail.print ("htif-???? cmd: " ++
          Sail.BitVec.toFormatted data)) : SailME (Sail.Result Bool ExceptionType) PUnit) := by
  split
  · apply htif_frame_e_ite
    · apply htif_frame_e_bind
      · exact htif_frame_e_write_reg htif_done _ (by decide)
      · intro _
        exact htif_frame_e_write_reg htif_exit_code _ (by decide)
    · exact htif_frame_e_pure _
  · split
    · apply htif_frame_e_bind
      · exact htif_frame_e_pure _
      · intro _
        exact htif_frame_e_lift (reset_htif ()) htif_frame_reset
    · apply htif_frame_e_bind
      · exact htif_frame_e_lift (plat_term_write _) (htif_frame_plat_term_write _)
      · intro _
        exact htif_frame_e_lift (reset_htif ()) htif_frame_reset
    · apply htif_frame_e_bind
      · exact htif_frame_e_pure _
      · intro _
        exact htif_frame_e_lift (reset_htif ()) htif_frame_reset
  · exact htif_frame_e_pure _

private def htif_frame_e_command_dispatch (data : BitVec (8 * width)) :
    SailME (Sail.Result Bool ExceptionType) PUnit := do
  let tohost ← liftM (Sail.readReg htif_tohost)
  let command ← pure (Mk_htif_cmd tohost)
  match _get_htif_cmd_device command with
  | 0x00 =>
    if Sail.BitVec.access (_get_htif_cmd_payload command) 0 == 1#1 then do
      liftM (Sail.writeReg htif_done true)
      liftM (Sail.writeReg htif_exit_code
        ((zero_extend (m := 64) (_get_htif_cmd_payload command)) >>> 1))
    else pure ()
  | 0x01 =>
    match _get_htif_cmd_cmd command with
    | 0x00 => pure ()
    | 0x01 => liftM (plat_term_write
        (Sail.BitVec.extractLsb (_get_htif_cmd_payload command) 7 0))
    | unknown => pure (Sail.print ("Unknown term cmd: " ++ Sail.BitVec.toFormatted unknown))
    liftM (reset_htif ())
  | _ => pure (Sail.print ("htif-???? cmd: " ++ Sail.BitVec.toFormatted data))

private theorem htif_frame_e_command_dispatch_preserves_stack_pointer (data : BitVec (8 * width)) :
    PreservesStackPointerE (htif_frame_e_command_dispatch data) := by
  unfold htif_frame_e_command_dispatch
  apply htif_frame_e_bind
  · exact htif_frame_e_read_reg htif_tohost
  · intro tohost
    apply htif_frame_e_bind
    · exact htif_frame_e_pure (Mk_htif_cmd tohost)
    · intro command
      exact htif_frame_e_command_action command data

/-- The generated HTIF store path preserves `x2` on normal and error outcomes. -/
theorem htif_store_preserves_stack_pointer (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) :
    PreservesStackPointer (htif_store address width data) := by
  rcases address with ⟨paddr⟩
  unfold htif_store
  apply htif_frame_sail_me_run
  apply htif_frame_e_bind
  · exact htif_frame_e_base
  · intro base
    apply htif_frame_e_ite
    · apply htif_frame_e_bind
      · exact htif_frame_store_eight_initial_preserves_stack_pointer width data
      · intro _
        apply htif_frame_e_bind
        · exact htif_frame_e_read_reg htif_cmd_write
        · intro commandWritten
          apply htif_frame_e_bind
          · apply htif_frame_e_bind
            · exact htif_frame_e_read_reg htif_payload_writes
            · intro payloadWrites
              exact htif_frame_e_pure _
          · intro payloadForZero
            apply htif_frame_e_bind
            · apply htif_frame_e_bind
              · exact htif_frame_e_read_reg htif_payload_writes
              · intro payloadWrites
                exact htif_frame_e_pure _
            · intro payloadForTwo
              apply htif_frame_e_ite
              · apply htif_frame_e_bind
                · exact htif_frame_e_command_dispatch_preserves_stack_pointer data
                · intro _
                  exact htif_frame_e_pure _
              · apply htif_frame_e_bind
                · exact htif_frame_e_pure _
                · intro _
                  exact htif_frame_e_pure _
    · apply htif_frame_e_bind
      · exact htif_frame_store_rest_initial_preserves_stack_pointer width paddr base data
      · intro _
        apply htif_frame_e_bind
        · exact htif_frame_e_read_reg htif_cmd_write
        · intro commandWritten
          apply htif_frame_e_bind
          · apply htif_frame_e_bind
            · exact htif_frame_e_read_reg htif_payload_writes
            · intro payloadWrites
              exact htif_frame_e_pure _
          · intro payloadForZero
            apply htif_frame_e_bind
            · apply htif_frame_e_bind
              · exact htif_frame_e_read_reg htif_payload_writes
              · intro payloadWrites
                exact htif_frame_e_pure _
            · intro payloadForTwo
              apply htif_frame_e_ite
              · apply htif_frame_e_bind
                · exact htif_frame_e_command_dispatch_preserves_stack_pointer data
                · intro _
                  exact htif_frame_e_pure _
              · apply htif_frame_e_bind
                · exact htif_frame_e_pure _
                · intro _
                  exact htif_frame_e_pure _

end BinaryFv.RISCV
