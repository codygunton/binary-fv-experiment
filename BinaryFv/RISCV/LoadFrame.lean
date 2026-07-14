import BinaryFv.RISCV.BTypeFrame
import BinaryFv.RISCV.ClintFrame
import BinaryFv.RISCV.EnabledFrame
import BinaryFv.RISCV.HtifFrame
import BinaryFv.RISCV.TranslationFrameAudit
import Lean.Elab.Tactic.Omega

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

private theorem load_preserves_bind (first : SailM α) (next : α → SailM β)
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
  | ok value afterFirst =>
    change first state = .ok value afterFirst at hFirst
    have firstFrame' := firstFrame state
    change (match first state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 at firstFrame'
    calc
      (match (first >>= next).run state with
      | .ok _ state' => state'.regs.get? x2
      | .error _ state' => state'.regs.get? x2) =
        (match (next value).run afterFirst with
        | .ok _ state' => state'.regs.get? x2
        | .error _ state' => state'.regs.get? x2) := by
          change (match EStateM.bind first next state with
          | .ok _ state' => state'.regs.get? x2
          | .error _ state' => state'.regs.get? x2) = _
          unfold EStateM.bind
          rw [hFirst]
          rfl
      _ = afterFirst.regs.get? x2 := nextFrame value afterFirst
      _ = state.regs.get? x2 := by simpa only [hFirst] using firstFrame'

private theorem load_preserves_pure (value : α) : PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

private theorem load_preserves_throw (error : Sail.Error exception) :
    PreservesStackPointer (throw error : SailM α) := by
  intro state
  rfl

private theorem load_preserves_map (action : SailM α) (function : α → β)
    (frame : PreservesStackPointer action) : PreservesStackPointer (function <$> action) :=
  load_preserves_bind action (fun value => pure (function value)) frame (fun _ =>
    load_preserves_pure _)

private theorem load_preserves_ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : PreservesStackPointer whenTrue) (falseFrame : PreservesStackPointer whenFalse) :
    PreservesStackPointer (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

private theorem load_preserves_readReg (register : Register) :
    PreservesStackPointer (readReg register : SailM (RegisterType register)) := by
  intro state
  cases hRead : (readReg register : SailM (RegisterType register)).run state with
  | ok value after =>
    change (readReg register : SailM (RegisterType register)) state = .ok value after at hRead
    have projection := readReg_state_projection state register
    simpa [hRead] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    change (readReg register : SailM (RegisterType register)) state = .error error after at hRead
    have projection := readReg_state_projection state register
    simpa [hRead] using congrArg (fun state : State => state.regs.get? x2) projection

private theorem load_preserves_rX_bits (source : regidx) :
    PreservesStackPointer (rX_bits source) := by
  intro state
  cases hRead : (rX_bits source).run state with
  | ok value after =>
    have projection := rX_bits_state_projection state source
    simpa [hRead] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    have projection := rX_bits_state_projection state source
    simpa [hRead] using congrArg (fun state : State => state.regs.get? x2) projection

private theorem load_preserves_assert (condition : Bool) (message : String) :
    PreservesStackPointer (Sail.assert condition message) := by
  unfold Sail.assert PreSail.assert
  split <;> exact load_preserves_pure () <;> exact load_preserves_throw _

private theorem load_preserves_writeReg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) : PreservesStackPointer (writeReg written value) := by
  intro state
  rw [writeReg_run]
  exact writeReg_read_unchanged state written x2 value notStack

private def LoadPreservesExcept {ε α : Type} (action : ExceptT ε SailM α) : Prop :=
  PreservesStackPointer (ExceptT.run action)

private theorem load_preserves_except_pure {ε α : Type} (value : α) :
    LoadPreservesExcept (pure value : ExceptT ε SailM α) := by
  intro state
  rfl

private theorem load_preserves_except_throw {ε α : Type} (error : ε) :
    LoadPreservesExcept (Sail.SailME.throw error : SailME ε α) := by
  change PreservesStackPointer (ExceptT.run (Sail.SailME.throw error : SailME ε α))
  unfold Sail.SailME.throw PreSail.PreSailME.throw
  exact load_preserves_pure _

private theorem load_preserves_except_ite {ε α : Type} (condition : Bool)
    (whenTrue whenFalse : SailME ε α) (trueFrame : LoadPreservesExcept whenTrue)
    (falseFrame : LoadPreservesExcept whenFalse) :
    LoadPreservesExcept (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

private theorem load_preserves_except_lift {ε α : Type} (action : SailM α)
    (frame : PreservesStackPointer action) :
    LoadPreservesExcept (ExceptT.lift action : ExceptT ε SailM α) := by
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

private theorem load_preserves_except_lift_bind {ε α β : Type} (action : SailM α)
    (next : α → ExceptT ε SailM β) (actionFrame : PreservesStackPointer action)
    (nextFrame : ∀ value, LoadPreservesExcept (next value)) :
    LoadPreservesExcept (do
      let current ← liftM action
      next current) := by
  unfold LoadPreservesExcept
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
  apply load_preserves_bind action _ actionFrame
  intro value
  exact nextFrame value

private theorem load_preserves_except_bind {ε α β : Type} (action : ExceptT ε SailM α)
    (next : α → ExceptT ε SailM β) (actionFrame : LoadPreservesExcept action)
    (nextFrame : ∀ value, LoadPreservesExcept (next value)) :
    LoadPreservesExcept (action >>= next) := by
  unfold LoadPreservesExcept
  have runEq : ExceptT.run (action >>= next) = (do
      let result ← ExceptT.run action
      match result with
      | .ok value => ExceptT.run (next value)
      | .error error => pure (.error error)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.run, ExceptT.mk,
      EStateM.instMonad]
    rfl
  rw [runEq]
  apply load_preserves_bind (ExceptT.run action) _ actionFrame
  intro result
  cases result with
  | ok value => exact nextFrame value
  | error error => exact load_preserves_pure (Except.error error : Except ε β)

private theorem load_preserves_except_ite_bind {ε α β : Type} (condition : Bool)
    (whenTrue whenFalse : SailME ε α) (next : α → SailME ε β)
    (trueFrame : LoadPreservesExcept whenTrue) (falseFrame : LoadPreservesExcept whenFalse)
    (nextFrame : ∀ value, LoadPreservesExcept (next value)) :
    LoadPreservesExcept (do
      let value ← if condition then whenTrue else whenFalse
      next value) := by
  apply load_preserves_except_ite
  · exact load_preserves_except_bind whenTrue next trueFrame nextFrame
  · exact load_preserves_except_bind whenFalse next falseFrame nextFrame

private theorem load_preserves_sailME_run {α : Type} (action : SailME α α)
    (frame : LoadPreservesExcept action) : PreservesStackPointer (Sail.SailME.run action) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  apply load_preserves_bind (ExceptT.run action) _ frame
  intro result
  cases result with
  | ok value => exact load_preserves_pure value
  | error error =>
    cases error with
    | inl error => exact load_preserves_throw error
    | inr value => exact load_preserves_pure value

private theorem load_preserves_untilFuelM {ε α : Type} (fuel : Nat)
    (condition : α → SailME ε Bool) (step : α → SailME ε α)
    (conditionFrame : ∀ value, LoadPreservesExcept (condition value))
    (stepFrame : ∀ value, LoadPreservesExcept (step value)) (initial : α) :
    LoadPreservesExcept (untilFuelM fuel condition initial step) := by
  induction fuel generalizing initial with
  | zero =>
    unfold untilFuelM
    exact load_preserves_except_pure _
  | succ fuel induction =>
    unfold untilFuelM
    apply load_preserves_except_bind
    · exact stepFrame initial
    · intro afterStep
      apply load_preserves_except_bind
      · exact conditionFrame afterStep
      · intro done
        apply load_preserves_except_ite
        · exact load_preserves_except_pure _
        · exact induction afterStep

private theorem load_preserves_privLevel_bits_forwards (arg : BitVec 2 × BitVec 1) :
    PreservesStackPointer (privLevel_bits_forwards arg) := by
  have levelCases : arg.1.toNat = 0 ∨ arg.1.toNat = 1 ∨ arg.1.toNat = 2 ∨ arg.1.toNat = 3 := by
    omega
  have virtualCases : arg.2.toNat = 0 ∨ arg.2.toNat = 1 := by
    omega
  rcases levelCases with hLevel | hLevel | hLevel | hLevel <;>
    rcases virtualCases with hVirtual | hVirtual
  all_goals
    have levelValue : arg.1 = BitVec.ofNat 2 arg.1.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    have virtualValue : arg.2 = BitVec.ofNat 1 arg.2.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    have argValue : arg = (BitVec.ofNat 2 arg.1.toNat, BitVec.ofNat 1 arg.2.toNat) :=
      Prod.ext levelValue virtualValue
    rw [argValue]
    simp [privLevel_bits_forwards, hLevel, hVirtual, internal_error, Sail.sailThrow,
      PreSail.sailThrow, EStateM.instMonad]
    all_goals first | exact load_preserves_pure _ | exact load_preserves_throw _

private theorem load_preserves_effectivePrivilege (access : MemoryAccessType mem_payload)
    (mstatusBits : BitVec 64) (privilege : Privilege) :
    PreservesStackPointer (effectivePrivilege access mstatusBits privilege) := by
  unfold effectivePrivilege
  apply load_preserves_ite
  · exact load_preserves_privLevel_bits_forwards _
  · exact load_preserves_pure _

private theorem load_preserves_is_pmm_applicable (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesStackPointer (is_pmm_applicable access privilege) := by
  unfold is_pmm_applicable
  apply load_preserves_bind (readReg mstatus)
  · exact load_preserves_readReg mstatus
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_read_senvcfg : PreservesStackPointer (read_senvcfg ()) := by
  unfold read_senvcfg
  apply load_preserves_bind (readReg senvcfg)
  · exact load_preserves_readReg senvcfg
  · intro _
    apply load_preserves_bind (readReg menvcfg)
    · exact load_preserves_readReg menvcfg
    · intro _
      apply load_preserves_bind (readReg senvcfg)
      · exact load_preserves_readReg senvcfg
      · intro _
        exact load_preserves_pure _

private theorem load_preserves_currentlyEnabled_Zicsr :
    PreservesStackPointer (currentlyEnabled extension.Ext_Zicsr) :=
  currentlyEnabled_zicsr_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_S :
    PreservesStackPointer (currentlyEnabled extension.Ext_S) :=
  currentlyEnabled_s_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_Sstc :
    PreservesStackPointer (currentlyEnabled extension.Ext_Sstc) :=
  currentlyEnabled_sstc_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_Svade :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svade) :=
  currentlyEnabled_svade_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_Svadu :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svadu) :=
  currentlyEnabled_svadu_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_Sv39 :
    PreservesStackPointer (currentlyEnabled extension.Ext_Sv39) :=
  currentlyEnabled_sv39_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_Svnapot :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svnapot) :=
  currentlyEnabled_svnapot_preserves_stack_pointer

private theorem load_preserves_currentlyEnabled_Svrsw60t59b :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svrsw60t59b) :=
  currentlyEnabled_svrsw60t59b_preserves_stack_pointer

private theorem load_preserves_internal_error (file : String) (line : Int) (message : String) :
    PreservesStackPointer (internal_error file line message : SailM α) := by
  unfold internal_error Sail.sailThrow PreSail.sailThrow
  exact load_preserves_throw _

private theorem load_preserves_is_shadow_stack_access (access : MemoryAccessType mem_payload) :
    PreservesStackPointer (is_shadow_stack_access access) := by
  unfold is_shadow_stack_access
  cases access with
  | InstructionFetch _ => exact load_preserves_pure _
  | Load payload =>
    cases payload <;> exact load_preserves_pure _
  | LoadReserved payload =>
    cases payload <;>
      first
      | exact load_preserves_pure _
      | exact load_preserves_internal_error _ _ _
  | Store payload =>
    cases payload <;> exact load_preserves_pure _
  | StoreConditional payload =>
    cases payload <;>
      first
      | exact load_preserves_pure _
      | exact load_preserves_internal_error _ _ _
  | Atomic payload =>
    rcases payload with ⟨operation, readPayload, writePayload⟩
    cases readPayload <;> cases writePayload <;>
      first | exact load_preserves_pure _ | exact load_preserves_internal_error _ _ _
  | CacheAccess operation => exact load_preserves_pure _

private theorem load_preserves_get_pmm (privilege : Privilege) :
    PreservesStackPointer (get_pmm privilege) := by
  cases privilege <;> unfold get_pmm
  · apply load_preserves_bind (currentlyEnabled extension.Ext_S)
    · exact load_preserves_currentlyEnabled_S
    · intro enabled
      apply load_preserves_ite
      · exact load_preserves_bind (read_senvcfg ())
          (fun bits => pure (pmm_mode_backwards (_get_SEnvcfg_PMM bits)))
          load_preserves_read_senvcfg (fun _ => load_preserves_pure _)
      · exact load_preserves_bind (readReg menvcfg)
          (fun bits => pure (pmm_mode_backwards (_get_MEnvcfg_PMM bits)))
          (load_preserves_readReg menvcfg) (fun _ => load_preserves_pure _)
  · exact load_preserves_internal_error _ _ _
  · exact load_preserves_bind (readReg menvcfg)
      (fun bits => pure (pmm_mode_backwards (_get_MEnvcfg_PMM bits)))
      (load_preserves_readReg menvcfg) (fun _ => load_preserves_pure _)
  · exact load_preserves_internal_error _ _ _
  · exact load_preserves_bind (readReg mseccfg)
      (fun bits => pure (pmm_mode_backwards (_get_Seccfg_PMM bits)))
      (load_preserves_readReg mseccfg) (fun _ => load_preserves_pure _)

private theorem load_preserves_get_pmlen (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesStackPointer (get_pmlen access privilege) := by
  unfold get_pmlen
  apply load_preserves_bind (is_pmm_applicable access privilege)
  · exact load_preserves_is_pmm_applicable access privilege
  · intro applicable
    apply load_preserves_ite
    · apply load_preserves_bind (get_pmm privilege)
      · exact load_preserves_get_pmm privilege
      · intro pmm
        cases pmm
        · exact load_preserves_pure _
        · exact load_preserves_bind
            (internal_error "extensions/pointer_masking/pm_utils.sail" 32
              "Invalid pointer masking mode")
            (fun _ => pure 0) (load_preserves_internal_error _ _ _) (fun _ => load_preserves_pure _)
        · exact load_preserves_pure _
        · exact load_preserves_pure _
    · exact load_preserves_pure _

private theorem load_preserves_architecture_bits_backwards (arg : BitVec 2) :
    PreservesStackPointer (architecture_bits_backwards arg) := by
  have cases : arg.toNat = 0 ∨ arg.toNat = 1 ∨ arg.toNat = 2 ∨ arg.toNat = 3 := by
    omega
  rcases cases with h | h | h | h
  all_goals
    have argValue : arg = BitVec.ofNat 2 arg.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [argValue]
    simp [architecture_bits_backwards, h, internal_error, Sail.sailThrow, PreSail.sailThrow,
      EStateM.instMonad]
    all_goals first | exact load_preserves_pure _ | exact load_preserves_throw _

private theorem load_preserves_architecture_supervisor :
    PreservesStackPointer (architecture .Supervisor) := by
  simp only [architecture]
  apply load_preserves_bind (do
    let bits ← readReg mstatus
    pure (_get_Mstatus_SXL bits))
  · apply load_preserves_bind (readReg mstatus)
    · exact load_preserves_readReg mstatus
    · intro _
      exact load_preserves_pure _
  · intro bits
    exact load_preserves_architecture_bits_backwards bits

private theorem load_preserves_satp_mode_result (arch : Architecture) (bits : BitVec 4) :
    PreservesStackPointer (match satpMode_of_bits arch bits with
      | some mode => pure mode
      | none => internal_error "sys/vmem.sail" 263 "invalid translation mode in satp") := by
  cases hMode : satpMode_of_bits arch bits
  · exact load_preserves_internal_error _ _ _
  · exact load_preserves_pure _

private theorem load_preserves_translationMode (privilege : Privilege) :
    PreservesStackPointer (translationMode privilege) := by
  unfold translationMode
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_bind (architecture .Supervisor)
    · exact load_preserves_architecture_supervisor
    · intro arch
      cases arch <;> simp only
      · apply load_preserves_bind (do
          let bits ← readReg satp
          pure (0b000#3 ++ _get_Satp32_Mode (Mk_Satp32 (Sail.BitVec.extractLsb bits 31 0))))
        · apply load_preserves_bind (readReg satp)
          · exact load_preserves_readReg satp
          · intro _
            exact load_preserves_pure _
        · intro bits
          exact load_preserves_satp_mode_result .RV32 bits
      · apply load_preserves_bind (do
          Sail.assert (LeanRV64DExecutable.Functions.xlen ≥b 64) "sys/vmem.sail:254.25-254.26"
          let bits ← readReg satp
          pure (_get_Satp64_Mode (Mk_Satp64 bits)))
        · apply load_preserves_bind
            (Sail.assert (LeanRV64DExecutable.Functions.xlen ≥b 64)
              "sys/vmem.sail:254.25-254.26")
          · exact load_preserves_assert _ _
          · intro _
            apply load_preserves_bind (readReg satp)
            · exact load_preserves_readReg satp
            · intro _
              exact load_preserves_pure _
        · intro bits
          exact load_preserves_satp_mode_result .RV64 bits
      · exact load_preserves_internal_error _ _ _

private theorem load_preserves_satp_mode_width_forwards (mode : SATPMode) :
    PreservesStackPointer (satp_mode_width_forwards mode) := by
  cases mode <;> unfold satp_mode_width_forwards
  all_goals first
    | exact load_preserves_pure _
    | exact load_preserves_bind (Sail.assert false "Pattern match failure at unknown location")
        (fun _ => throw Sail.Error.Exit) (load_preserves_assert _ _)
        (fun _ => load_preserves_throw _)

private theorem load_preserves_get_satp (svWidth : Nat) :
    PreservesStackPointer (get_satp svWidth) := by
  unfold get_satp
  apply load_preserves_bind
      (Sail.assert ((svWidth == 32) || (LeanRV64DExecutable.Functions.xlen == 64))
        "sys/vmem.sail:395.30-395.31")
  · exact load_preserves_assert _ _
  · intro _
    by_cases hWidth : svWidth = 32
    · subst svWidth
      simp
      apply load_preserves_bind (readReg satp)
      · exact load_preserves_readReg satp
      · intro _
        exact load_preserves_pure _
    · have hWidthBool : (svWidth == 32) = false := beq_eq_false_iff_ne.mpr hWidth
      rw [hWidthBool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply load_preserves_bind (readReg satp)
      · exact load_preserves_readReg satp
      · intro _
        exact load_preserves_pure _

private theorem load_preserves_translationException_load_data (failure : PTW_Error) :
    PreservesStackPointer (translationException (.Load mem_payload.Data) failure) := by
  unfold translationException
  cases failure <;> exact load_preserves_pure _

private theorem load_preserves_transform_effective_address (address : virtaddr)
    (access : MemoryAccessType mem_payload) :
    PreservesStackPointer (transform_effective_address address access) := by
  unfold transform_effective_address
  apply load_preserves_bind (readReg mstatus)
  · exact load_preserves_readReg mstatus
  · intro mstatusBits
    apply load_preserves_bind (readReg cur_privilege)
    · exact load_preserves_readReg cur_privilege
    · intro privilege
      apply load_preserves_bind (effectivePrivilege access mstatusBits privilege)
      · exact load_preserves_effectivePrivilege access mstatusBits privilege
      · intro effective
        apply load_preserves_bind (get_pmlen access effective)
        · exact load_preserves_get_pmlen access effective
        · intro pmlen
          apply load_preserves_bind (translationMode effective)
          · exact load_preserves_translationMode effective
          · intro mode
            apply load_preserves_ite
            · exact load_preserves_pure _
            · exact load_preserves_pure _

private theorem load_preserves_ext_data_get_addr (source : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesStackPointer (ext_data_get_addr source offset access width) := by
  simp only [ext_data_get_addr]
  apply load_preserves_bind (rX_bits source)
  · exact load_preserves_rX_bits source
  · intro base
    exact load_preserves_pure _

private theorem load_preserves_get_transformed_data_addr (source : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesStackPointer (get_transformed_data_addr source offset access width) := by
  unfold get_transformed_data_addr
  apply load_preserves_bind (ext_data_get_addr source offset access width)
  · exact load_preserves_ext_data_get_addr source offset access width
  · intro result
    cases result with
    | Ext_DataAddr_Error error => exact load_preserves_pure _
    | Ext_DataAddr_OK address =>
      apply load_preserves_bind (transform_effective_address address access)
      · exact load_preserves_transform_effective_address address access
      · intro _
        exact load_preserves_pure _

private theorem load_preserves_read_then_pure (register : Register)
    (next : RegisterType register → α) :
    PreservesStackPointer (do
      let value ← readReg register
      pure (next value)) := by
  apply load_preserves_bind (readReg register)
  · exact load_preserves_readReg register
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_memory_exception (address : virtaddr) (exception : ExceptionType) :
    PreservesStackPointer (memory_exception address exception) := by
  unfold memory_exception trap
  apply load_preserves_bind (readReg cur_privilege)
  · exact load_preserves_readReg cur_privilege
  · intro _
    apply load_preserves_bind (readReg PC)
    · exact load_preserves_readReg PC
    · intro _
      exact load_preserves_pure _

private theorem load_preserves_plat_misaligned_exception (access : MemoryAccessType mem_payload)
    (reservation : Bool) :
    PreservesStackPointer (plat_misaligned_exception access reservation) := by
  unfold plat_misaligned_exception
  apply load_preserves_bind (Sail.assert (LeanRV64DExecutable.Functions.not (is_amo_access access))
    "sys/vmem_utils.sail:85.35-85.36")
  · exact load_preserves_assert _ _
  · intro _
    apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_ite
      · exact load_preserves_pure _
      · exact load_preserves_pure _

private theorem load_preserves_split_misaligned (address : virtaddr) (width : Nat) :
    PreservesStackPointer (split_misaligned address width) := by
  unfold split_misaligned
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_bind (Sail.assert
          (width == (Int.tdiv width
            (2 ^i Sail.BitVec.countTrailingZeros (bits_of_virtaddr address)) *i
            (2 ^i Sail.BitVec.countTrailingZeros (bits_of_virtaddr address))).toNat)
          "sys/vmem_utils.sail:63.51-63.52")
      · exact load_preserves_assert _ _
      · intro _
        exact load_preserves_pure _

private theorem load_preserves_access_fault_load_data :
    PreservesStackPointer (accessFaultFromAccessType (.Load mem_payload.Data)) := by
  unfold accessFaultFromAccessType
  exact load_preserves_pure _

private theorem load_preserves_access_fault_load_pte :
    PreservesStackPointer (accessFaultFromAccessType (.Load mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact load_preserves_pure _

private theorem load_preserves_access_fault_store_pte :
    PreservesStackPointer (accessFaultFromAccessType (.Store mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact load_preserves_pure _

private theorem load_preserves_alignment_fault_load_data :
    PreservesStackPointer (alignmentFaultFromAccessType (.Load mem_payload.Data)) := by
  unfold alignmentFaultFromAccessType
  exact load_preserves_pure _

private theorem load_preserves_alignment_fault_load_pte :
    PreservesStackPointer (alignmentFaultFromAccessType (.Load mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact load_preserves_pure _

private theorem load_preserves_alignment_fault_store_pte :
    PreservesStackPointer (alignmentFaultFromAccessType (.Store mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact load_preserves_pure _

private theorem load_preserves_readByte (address : Nat) :
    PreservesStackPointer (PreSail.readByte address : SailM (BitVec 8)) := by
  intro state
  unfold PreSail.readByte
  simp only [EStateM.run, EStateM.instMonad, EStateM.bind, instMonadStateOfMonadStateOf,
    EStateM.instMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe]
  unfold EStateM.get
  simp only
  cases hRead : state.mem.get? address with
  | none => rfl
  | some value => rfl

private theorem load_preserves_readBytes (size address : Nat) :
    PreservesStackPointer (PreSail.readBytes size address) := by
  induction size generalizing address with
  | zero => exact load_preserves_pure _
  | succ size ih =>
    cases size with
    | zero =>
      simp only [PreSail.readBytes]
      apply load_preserves_bind (PreSail.readByte address)
      · exact load_preserves_readByte address
      · intro _
        exact load_preserves_pure _
    | succ size =>
      simp only [PreSail.readBytes]
      apply load_preserves_bind (PreSail.readByte address)
      · exact load_preserves_readByte address
      · intro _
        apply load_preserves_bind (PreSail.readBytes (size + 1) (address + 1))
        · exact ih (address := address + 1)
        · intro _
          exact load_preserves_pure _

private def load_read_ram_plain_request (address : physaddrbits) (width : Nat) :
    SailM (Sail.ConcurrencyInterfaceV1.Mem_read_request width 64 physaddrbits Unit
      RISCV_strong_access) := do
  let accessKind ← pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal })
  pure { access_kind := accessKind
         va := none
         pa := address
         translation := ()
         size := width
         tag := false }

private theorem load_preserves_read_ram_plain_request (address : physaddrbits) (width : Nat) :
    PreservesStackPointer (load_read_ram_plain_request address width) := by
  unfold load_read_ram_plain_request
  apply load_preserves_bind (pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal }))
  · exact load_preserves_pure _
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_plain_sail_mem_read
    (request : Sail.ConcurrencyInterfaceV1.Mem_read_request width 64 physaddrbits Unit
      RISCV_strong_access) :
    PreservesStackPointer (Sail.ConcurrencyInterfaceV1.sail_mem_read request) := by
  delta Sail.ConcurrencyInterfaceV1.sail_mem_read
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_read
  apply load_preserves_bind (PreSail.readBytes width request.pa.toNat)
  · exact load_preserves_readBytes width request.pa.toNat
  · intro _
    exact load_preserves_pure _

private theorem load_read_ram_plain_unfold (address : physaddrbits) (width : Nat) :
    read_ram .Read_plain (.Physaddr address) width false = (do
      let request ← load_read_ram_plain_request address width
      match ← Sail.ConcurrencyInterfaceV1.sail_mem_read request with
      | .Ok (value, _) => pure (value, default_meta)
      | .Err () => throw Sail.Error.Exit) := by
  rfl

private theorem load_preserves_read_ram_plain (address : physaddr) (width : Nat) :
    PreservesStackPointer (read_ram .Read_plain address width false) := by
  rcases address with ⟨address⟩
  rw [load_read_ram_plain_unfold]
  apply load_preserves_bind (load_read_ram_plain_request address width)
  · exact load_preserves_read_ram_plain_request address width
  · intro request
    apply load_preserves_bind (Sail.ConcurrencyInterfaceV1.sail_mem_read request)
    · exact load_preserves_plain_sail_mem_read request
    · intro result
      cases result with
      | Ok value => exact load_preserves_pure _
      | Err error => exact load_preserves_throw _

private theorem load_preserves_pmpCheckRWX_load_data (config : BitVec 8) :
    PreservesStackPointer (pmpCheckRWX config (.Load mem_payload.Data)) := by
  unfold pmpCheckRWX
  exact load_preserves_pure _

private theorem load_preserves_pmpCheckRWX_load_pte (config : BitVec 8) :
    PreservesStackPointer (pmpCheckRWX config (.Load mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact load_preserves_pure _

private theorem load_preserves_pmpCheckRWX_store_pte (config : BitVec 8) :
    PreservesStackPointer (pmpCheckRWX config (.Store mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact load_preserves_pure _

private theorem load_preserves_pmpReadAddrReg (index : Nat) :
    PreservesStackPointer (pmpReadAddrReg index) := by
  unfold pmpReadAddrReg
  apply load_preserves_bind (readReg pmpcfg_n)
  · exact load_preserves_readReg pmpcfg_n
  · intro config
    apply load_preserves_bind (pure _)
    · exact load_preserves_pure _
    · intro matchType
      apply load_preserves_bind (readReg pmpaddr_n)
      · exact load_preserves_readReg pmpaddr_n
      · intro addresses
        apply load_preserves_bind (pure _)
        · exact load_preserves_pure _
        · intro address
          have bitCases : (Sail.BitVec.access matchType 1).toNat = 0 ∨
              (Sail.BitVec.access matchType 1).toNat = 1 := by
            omega
          rcases bitCases with hBit | hBit
          all_goals
            have bitValue : Sail.BitVec.access matchType 1 =
                BitVec.ofNat 1 (Sail.BitVec.access matchType 1).toNat := by
              rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
              omega
            rw [bitValue]
            simp [hBit]
            all_goals split <;> exact load_preserves_pure _

private theorem load_preserves_pmpMatchAddr (address : physaddr) (width : BitVec 64)
    (config : BitVec 8) (current previous : BitVec 64) :
    PreservesStackPointer (pmpMatchAddr address width config current previous) := by
  unfold pmpMatchAddr
  cases hMatch : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A config)
  · exact load_preserves_pure _
  · apply load_preserves_ite <;> exact load_preserves_pure _
  · apply load_preserves_bind (Sail.assert _ _)
    · exact load_preserves_assert _ _
    · intro _
      exact load_preserves_pure _
  · exact load_preserves_pure _

private def load_pmp_loop_range : IntRange := {
  start := 0
  stop := sys_pmp_count - 1
  step := 1
  step_pos := by omega
}

private def load_pmp_loop_after_prev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let rawConfig ← liftM (Sail.readReg pmpcfg_n)
  let config ← pure (GetElem?.getElem! rawConfig index)
  let currentPmpaddr ← liftM (pmpReadAddrReg index.toNat)
  match (← liftM (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)) with
  | .PMP_NoMatch => pure ()
  | .PMP_PartialMatch =>
    Sail.SailME.throw (← do pure (some (← liftM (accessFaultFromAccessType access))))
  | .PMP_Match =>
    Sail.SailME.throw (← do
      if (((← liftM (pmpCheckRWX config access)) ||
          ((privilege == .Machine) &&
            LeanRV64DExecutable.Functions.not (pmpLocked config))) : Bool) then
        pure none
      else pure (some (← liftM (accessFaultFromAccessType access))))
  pure PUnit.unit
  pure (.yield loopVars)

private theorem load_preserves_pmp_loop_after_prev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    LoadPreservesExcept
      (load_pmp_loop_after_prev address width access privilege index previousPmpaddr loopVars) := by
  unfold load_pmp_loop_after_prev
  apply load_preserves_except_bind
  · exact load_preserves_except_lift (Sail.readReg pmpcfg_n)
      (load_preserves_readReg pmpcfg_n)
  · intro rawConfig
    apply load_preserves_except_bind
    · exact load_preserves_except_pure _
    · intro config
      apply load_preserves_except_bind
      · exact load_preserves_except_lift (pmpReadAddrReg index.toNat)
          (load_preserves_pmpReadAddrReg index.toNat)
      · intro currentPmpaddr
        apply load_preserves_except_bind
        · exact load_preserves_except_lift
            (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
            (load_preserves_pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
        · intro matched
          cases matched with
          | PMP_NoMatch => exact load_preserves_except_pure _
          | PMP_PartialMatch =>
            apply load_preserves_except_bind
            · apply load_preserves_except_bind
              · exact load_preserves_except_lift (accessFaultFromAccessType access)
                  accessFaultFrame
              · intro fault
                exact load_preserves_except_pure (some fault)
            · intro fault
              exact load_preserves_except_throw fault
          | PMP_Match =>
            apply load_preserves_except_bind
            · apply load_preserves_except_bind
              · exact load_preserves_except_lift (pmpCheckRWX config access) (rwxFrame config)
              · intro permitted
                apply load_preserves_except_ite
                · exact load_preserves_except_pure none
                · apply load_preserves_except_bind
                  · exact load_preserves_except_lift (accessFaultFromAccessType access)
                      accessFaultFrame
                  · intro fault
                    exact load_preserves_except_pure (some fault)
            · intro fault
              exact load_preserves_except_throw fault

private def load_pmp_loop_body (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (index : Int) (_ : index ∈ load_pmp_loop_range) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let () := loopVars
  if ((index >b 0) : Bool) then do
    let previousPmpaddr ← liftM (pmpReadAddrReg (index - 1).toNat)
    load_pmp_loop_after_prev address width access privilege index previousPmpaddr loopVars
  else load_pmp_loop_after_prev address width access privilege index zeros loopVars

private theorem load_preserves_pmp_loop_body (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (index : Int) (inRange : index ∈ load_pmp_loop_range) (loopVars : Unit)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    LoadPreservesExcept
      (load_pmp_loop_body address width access privilege index inRange loopVars) := by
  unfold load_pmp_loop_body
  apply load_preserves_except_ite
  · apply load_preserves_except_bind
    · exact load_preserves_except_lift (pmpReadAddrReg (index - 1).toNat)
        (load_preserves_pmpReadAddrReg (index - 1).toNat)
    · intro previousPmpaddr
      exact load_preserves_pmp_loop_after_prev address width access privilege index previousPmpaddr
        loopVars accessFaultFrame rwxFrame
  · exact load_preserves_pmp_loop_after_prev address width access privilege index zeros loopVars
      accessFaultFrame rwxFrame

private theorem load_preserves_pmp_loop_invariant
    (body : (index : Int) → index ∈ load_pmp_loop_range → Unit →
      SailME (Option ExceptionType) (ForInStep Unit))
    (bodyFrame : ∀ (index : Int) (inRange : index ∈ load_pmp_loop_range),
      LoadPreservesExcept (body index inRange ()))
    (index : Int) (stepDiv : (index - load_pmp_loop_range.start) % load_pmp_loop_range.step = 0) :
    LoadPreservesExcept (IntRange.forIn'.loop load_pmp_loop_range body () index stepDiv) := by
  unfold IntRange.forIn'.loop
  by_cases inRange : index ∈ load_pmp_loop_range
  · simp only [dif_pos inRange]
    apply load_preserves_except_bind
    · exact bodyFrame index inRange
    · intro result
      cases result with
      | done loopVars => exact load_preserves_except_pure _
      | yield loopVars =>
        exact load_preserves_pmp_loop_invariant body bodyFrame
          (index + load_pmp_loop_range.step) (by
            rw [Int.add_comm, Int.add_sub_assoc]
            simp_all)
  · simp only [dif_neg inRange]
    exact load_preserves_except_pure _
termination_by (sys_pmp_count - index).toNat
decreasing_by
  change (sys_pmp_count - (index + 1)).toNat < (sys_pmp_count - index).toNat
  have bounds : (0 : Int) ≤ index ∧ index ≤ sys_pmp_count - 1 := by
    simpa [load_pmp_loop_range, IntRange.instMemIntRange] using inRange
  omega

private theorem load_preserves_pmp_loop (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    LoadPreservesExcept (IntRange.forIn' load_pmp_loop_range ()
      (load_pmp_loop_body address width access privilege)) := by
  unfold IntRange.forIn'
  exact load_preserves_pmp_loop_invariant
    (load_pmp_loop_body address width access privilege)
    (fun index inRange =>
      load_preserves_pmp_loop_body address width access privilege index inRange () accessFaultFrame
        rwxFrame)
    load_pmp_loop_range.start (by simp)

private def load_pmp_check_loop (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    SailM (Option ExceptionType) := Sail.SailME.run do
  let loopVars ← IntRange.forIn' load_pmp_loop_range ()
    (load_pmp_loop_body address (to_bits width) access privilege)
  pure loopVars
  if ((privilege == .Machine) : Bool) then pure none
  else pure (some (← liftM (accessFaultFromAccessType access)))

private theorem load_pmpCheck_loop_eq (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    pmpCheck address width access privilege =
      load_pmp_check_loop address width access privilege := by
  unfold pmpCheck load_pmp_check_loop load_pmp_loop_range load_pmp_loop_body
    load_pmp_loop_after_prev
  simp only [sys_pmp_count]
  have countNotZero : ((16 : Int) == 0) = false := rfl
  simp only [countNotZero, Bool.false_eq_true, ↓reduceIte]
  rw [forIn_eq_forIn']
  rfl

private theorem load_preserves_pmpCheck (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesStackPointer (pmpCheckRWX config access)) :
    PreservesStackPointer (pmpCheck address width access privilege) := by
  rw [load_pmpCheck_loop_eq]
  unfold load_pmp_check_loop
  apply load_preserves_sailME_run
  apply load_preserves_except_bind
  · exact load_preserves_pmp_loop address (to_bits width) access privilege accessFaultFrame rwxFrame
  · intro loopVars
    apply load_preserves_except_bind
    · exact load_preserves_except_pure loopVars
    · intro _
      apply load_preserves_except_ite
      · exact load_preserves_except_pure _
      · apply load_preserves_except_bind
        · exact load_preserves_except_lift (accessFaultFromAccessType access) accessFaultFrame
        · intro fault
          exact load_preserves_except_pure (some fault)

private theorem load_preserves_pmpCheck_load_data (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesStackPointer (pmpCheck address width (.Load mem_payload.Data) privilege) :=
  load_preserves_pmpCheck address width (.Load mem_payload.Data) privilege
    load_preserves_access_fault_load_data load_preserves_pmpCheckRWX_load_data

private theorem load_preserves_pmpCheck_load_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesStackPointer (pmpCheck address width (.Load mem_payload.PageTableEntry) privilege) :=
  load_preserves_pmpCheck address width (.Load mem_payload.PageTableEntry) privilege
    load_preserves_access_fault_load_pte load_preserves_pmpCheckRWX_load_pte

private theorem load_preserves_pmpCheck_store_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesStackPointer (pmpCheck address width (.Store mem_payload.PageTableEntry) privilege) :=
  load_preserves_pmpCheck address width (.Store mem_payload.PageTableEntry) privilege
    load_preserves_access_fault_store_pte load_preserves_pmpCheckRWX_store_pte

private theorem load_preserves_pmaCheck_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesStackPointer
      (pmaCheck address width (.Load mem_payload.Data) pbmt reservation) := by
  unfold pmaCheck
  apply load_preserves_bind (readReg pma_regions)
  · exact load_preserves_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.Data))
      · exact load_preserves_access_fault_load_data
      · intro _
        exact load_preserves_pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply load_preserves_bind
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · unfold pma_misaligned_exception
          exact load_preserves_pure _
      · intro exception
        cases exception with
        | none =>
          apply load_preserves_bind
          · apply load_preserves_bind (Sail.assert _ _)
            · exact load_preserves_assert _ _
            · intro _
              exact load_preserves_pure _
          · intro canAccess
            apply load_preserves_ite
            · exact load_preserves_pure _
            · apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.Data))
              · exact load_preserves_access_fault_load_data
              · intro _
                exact load_preserves_pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.Data))
            · exact load_preserves_access_fault_load_data
            · intro _
              exact load_preserves_pure _
          | AlignmentException =>
            apply load_preserves_bind (alignmentFaultFromAccessType (.Load mem_payload.Data))
            · exact load_preserves_alignment_fault_load_data
            · intro _
              exact load_preserves_pure _

private theorem load_preserves_pmaCheck_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesStackPointer
      (pmaCheck address width (.Load mem_payload.PageTableEntry) pbmt reservation) := by
  unfold pmaCheck
  apply load_preserves_bind (readReg pma_regions)
  · exact load_preserves_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      apply load_preserves_bind (accessFaultFromAccessType (.Load mem_payload.PageTableEntry))
      · exact load_preserves_access_fault_load_pte
      · intro _
        exact load_preserves_pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply load_preserves_bind
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · unfold pma_misaligned_exception
          exact load_preserves_pure _
      · intro exception
        cases exception with
        | none =>
          apply load_preserves_bind
          · apply load_preserves_bind (Sail.assert _ _)
            · exact load_preserves_assert _ _
            · intro _
              exact load_preserves_pure _
          · intro canAccess
            apply load_preserves_ite
            · exact load_preserves_pure _
            · apply load_preserves_bind
                (accessFaultFromAccessType (.Load mem_payload.PageTableEntry))
              · exact load_preserves_access_fault_load_pte
              · intro _
                exact load_preserves_pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply load_preserves_bind
                (accessFaultFromAccessType (.Load mem_payload.PageTableEntry))
            · exact load_preserves_access_fault_load_pte
            · intro _
              exact load_preserves_pure _
          | AlignmentException =>
            apply load_preserves_bind
                (alignmentFaultFromAccessType (.Load mem_payload.PageTableEntry))
            · exact load_preserves_alignment_fault_load_pte
            · intro _
              exact load_preserves_pure _

private theorem load_preserves_pmaCheck_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesStackPointer
      (pmaCheck address width (.Store mem_payload.PageTableEntry) pbmt reservation) := by
  unfold pmaCheck
  apply load_preserves_bind (readReg pma_regions)
  · exact load_preserves_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      apply load_preserves_bind (accessFaultFromAccessType (.Store mem_payload.PageTableEntry))
      · exact load_preserves_access_fault_store_pte
      · intro _
        exact load_preserves_pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply load_preserves_bind
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · unfold pma_misaligned_exception
          exact load_preserves_pure _
      · intro exception
        cases exception with
        | none =>
          apply load_preserves_bind
          · apply load_preserves_bind (Sail.assert _ _)
            · exact load_preserves_assert _ _
            · intro _
              exact load_preserves_pure _
          · intro canAccess
            apply load_preserves_ite
            · exact load_preserves_pure _
            · apply load_preserves_bind
                (accessFaultFromAccessType (.Store mem_payload.PageTableEntry))
              · exact load_preserves_access_fault_store_pte
              · intro _
                exact load_preserves_pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply load_preserves_bind
                (accessFaultFromAccessType (.Store mem_payload.PageTableEntry))
            · exact load_preserves_access_fault_store_pte
            · intro _
              exact load_preserves_pure _
          | AlignmentException =>
            apply load_preserves_bind
                (alignmentFaultFromAccessType (.Store mem_payload.PageTableEntry))
            · exact load_preserves_alignment_fault_store_pte
            · intro _
              exact load_preserves_pure _

private theorem load_preserves_alignmentOrAccessFaultPriority (exception : ExceptionType) :
    PreservesStackPointer (alignmentOrAccessFaultPriority exception) := by
  cases exception <;>
    simp [alignmentOrAccessFaultPriority, internal_error, Sail.sailThrow, PreSail.sailThrow,
      EStateM.instMonad]
  all_goals first | exact load_preserves_pure _ | exact load_preserves_throw _

private theorem load_preserves_highestPriorityAlignmentOrAccessFault
    (left right : ExceptionType) :
    PreservesStackPointer (highestPriorityAlignmentOrAccessFault left right) := by
  unfold highestPriorityAlignmentOrAccessFault
  apply load_preserves_bind (alignmentOrAccessFaultPriority left)
  · exact load_preserves_alignmentOrAccessFaultPriority left
  · intro leftPriority
    apply load_preserves_bind (alignmentOrAccessFaultPriority right)
    · exact load_preserves_alignmentOrAccessFaultPriority right
    · intro rightPriority
      apply load_preserves_ite <;> exact load_preserves_pure _

private theorem load_preserves_phys_access_check (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (privilege : Privilege)
    (reservation : Bool)
    (pmpFrame : PreservesStackPointer (pmpCheck address width access privilege))
    (pmaFrame : PreservesStackPointer (pmaCheck address width access pbmt reservation)) :
    PreservesStackPointer (phys_access_check access pbmt privilege address width reservation) := by
  unfold phys_access_check
  apply load_preserves_bind (pmpCheck address width access privilege)
  · exact pmpFrame
  · intro pmpError
    apply load_preserves_bind (pmaCheck address width access pbmt reservation)
    · exact pmaFrame
    · intro pmaError
      cases pmpError <;> cases pmaError
      · exact load_preserves_pure _
      · exact load_preserves_pure _
      · exact load_preserves_pure _
      · apply load_preserves_bind (highestPriorityAlignmentOrAccessFault _ _)
        · exact load_preserves_highestPriorityAlignmentOrAccessFault _ _
        · intro _
          exact load_preserves_pure _

private theorem load_preserves_phys_access_check_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesStackPointer
      (phys_access_check (.Load mem_payload.Data) pbmt privilege address width reservation) :=
  load_preserves_phys_access_check address width (.Load mem_payload.Data) pbmt privilege reservation
    (load_preserves_pmpCheck_load_data address width privilege)
    (load_preserves_pmaCheck_load_data address width pbmt reservation)

private theorem load_preserves_phys_access_check_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesStackPointer
      (phys_access_check (.Load mem_payload.PageTableEntry) pbmt privilege address width
        reservation) :=
  load_preserves_phys_access_check address width (.Load mem_payload.PageTableEntry) pbmt privilege
    reservation (load_preserves_pmpCheck_load_pte address width privilege)
    (load_preserves_pmaCheck_load_pte address width pbmt reservation)

private theorem load_preserves_phys_access_check_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesStackPointer
      (phys_access_check (.Store mem_payload.PageTableEntry) pbmt privilege address width
        reservation) :=
  load_preserves_phys_access_check address width (.Store mem_payload.PageTableEntry) pbmt privilege
    reservation (load_preserves_pmpCheck_store_pte address width privilege)
    (load_preserves_pmaCheck_store_pte address width pbmt reservation)

private theorem load_preserves_within_clint (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_clint address width) := by
  unfold within_clint
  exact load_preserves_ite _ _ _ (load_preserves_pure _) (load_preserves_pure _)

private theorem load_preserves_within_sig (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_sig address width) := by
  unfold within_sig
  exact load_preserves_ite _ _ _ (load_preserves_pure _) (load_preserves_pure _)

private theorem load_preserves_within_htif_writable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_htif_writable address width) := by
  unfold within_htif_writable
  apply load_preserves_bind (readReg htif_tohost_base)
  · exact load_preserves_readReg htif_tohost_base
  · intro base
    cases base <;> exact load_preserves_pure _

private theorem load_preserves_within_htif_readable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_htif_readable address width) :=
  load_preserves_within_htif_writable address width

private theorem load_preserves_within_mmio_readable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_mmio_readable address width) := by
  unfold within_mmio_readable
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_bind (within_clint address width)
    · exact load_preserves_within_clint address width
    · intro _
      apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro _
        apply load_preserves_bind (within_htif_readable address width)
        · exact load_preserves_within_htif_readable address width
        · intro _
          exact load_preserves_pure _

private theorem load_preserves_sig_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (sig_load access address width) := by
  unfold sig_load
  apply load_preserves_ite
  · apply load_preserves_bind (accessFaultFromAccessType access)
    · exact accessFaultFrame
    · intro _
      exact load_preserves_pure _
  · apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_ite
      · exact load_preserves_pure _
      · apply load_preserves_bind (accessFaultFromAccessType access)
        · exact accessFaultFrame
        · intro _
          exact load_preserves_pure _

private theorem load_preserves_clint_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (clint_load access address width) := by
  unfold clint_load
  simp only [get_config_print_clint]
  apply load_preserves_ite
  · exact load_preserves_read_then_pure mip _
  · apply load_preserves_ite
    · exact load_preserves_read_then_pure mtimecmp _
    · apply load_preserves_ite
      · exact load_preserves_read_then_pure mtimecmp _
      · apply load_preserves_ite
        · exact load_preserves_read_then_pure mtimecmp _
        · apply load_preserves_ite
          · exact load_preserves_read_then_pure mtime _
          · apply load_preserves_ite
            · exact load_preserves_read_then_pure mtime _
            · apply load_preserves_ite
              · exact load_preserves_read_then_pure mtime _
              · apply load_preserves_bind (accessFaultFromAccessType access)
                · exact accessFaultFrame
                · intro _
                  exact load_preserves_pure _

private theorem load_preserves_htif_base :
    PreservesStackPointer ((do
      match (← readReg htif_tohost_base) with
      | some base => pure base
      | none => (internal_error "sys/platform.sail" 268
        "HTIF load while HTIF isn't enabled" : SailM physaddrbits)) : SailM physaddrbits) := by
  apply load_preserves_bind (readReg htif_tohost_base)
  · exact load_preserves_readReg htif_tohost_base
  · intro base
    cases base with
    | some base => exact load_preserves_pure base
    | none =>
      exact load_preserves_internal_error (α := physaddrbits)
        "sys/platform.sail" 268 "HTIF load while HTIF isn't enabled"

private theorem load_preserves_htif_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (htif_load access address width) := by
  unfold htif_load
  simp only [get_config_print_htif, Bool.false_eq_true, ↓reduceIte]
  apply load_preserves_bind (pure ())
  · exact load_preserves_pure _
  · intro _
    apply load_preserves_bind
    · exact load_preserves_htif_base
    · intro base
      apply load_preserves_ite
      · exact load_preserves_read_then_pure htif_tohost _
      · apply load_preserves_ite
        · exact load_preserves_read_then_pure htif_tohost _
        · apply load_preserves_ite
          · exact load_preserves_read_then_pure htif_tohost _
          · apply load_preserves_bind (accessFaultFromAccessType access)
            · exact accessFaultFrame
            · intro _
              exact load_preserves_pure _

private theorem load_preserves_mmio_read (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesStackPointer (accessFaultFromAccessType access)) :
    PreservesStackPointer (mmio_read access address width) := by
  unfold mmio_read
  apply load_preserves_bind (within_clint address width)
  · exact load_preserves_within_clint address width
  · intro inClint
    apply load_preserves_ite
    · exact load_preserves_clint_load access address width accessFaultFrame
    · apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro inSig
        apply load_preserves_ite
        · exact load_preserves_sig_load access address width accessFaultFrame
        · apply load_preserves_bind (within_htif_readable address width)
          · exact load_preserves_within_htif_readable address width
          · intro inHtif
            apply load_preserves_ite
            · exact load_preserves_htif_load access address width accessFaultFrame
            · apply load_preserves_bind (accessFaultFromAccessType access)
              · exact accessFaultFrame
              · intro _
                exact load_preserves_pure _

private theorem load_preserves_mmio_read_load_data (address : physaddr) (width : Nat) :
    PreservesStackPointer (mmio_read (.Load mem_payload.Data) address width) :=
  load_preserves_mmio_read (.Load mem_payload.Data) address width
    load_preserves_access_fault_load_data

private theorem load_preserves_mmio_read_load_pte (address : physaddr) (width : Nat) :
    PreservesStackPointer (mmio_read (.Load mem_payload.PageTableEntry) address width) :=
  load_preserves_mmio_read (.Load mem_payload.PageTableEntry) address width
    load_preserves_access_fault_load_pte

private theorem load_preserves_checked_mem_read_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (checked_mem_read (.Load mem_payload.Data) pbmt privilege address width
        false false false false) := by
  unfold checked_mem_read
  apply load_preserves_bind
      (phys_access_check (.Load mem_payload.Data) pbmt privilege address width false)
  · exact load_preserves_phys_access_check_load_data address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact load_preserves_pure _
    | none =>
      apply load_preserves_bind (within_mmio_readable address width)
      · exact load_preserves_within_mmio_readable address width
      · intro inMmio
        apply load_preserves_ite
        · apply load_preserves_bind (mmio_read (.Load mem_payload.Data) address width)
          · exact load_preserves_mmio_read_load_data address width
          · intro _
            exact load_preserves_pure _
        · simp only [read_kind_of_flags]
          apply load_preserves_bind (read_ram .Read_plain address width false)
          · exact load_preserves_read_ram_plain address width
          · intro _
            exact load_preserves_pure _

private theorem load_preserves_checked_mem_read_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (checked_mem_read (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false) := by
  unfold checked_mem_read
  apply load_preserves_bind
      (phys_access_check (.Load mem_payload.PageTableEntry) pbmt privilege address width false)
  · exact load_preserves_phys_access_check_load_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact load_preserves_pure _
    | none =>
      apply load_preserves_bind (within_mmio_readable address width)
      · exact load_preserves_within_mmio_readable address width
      · intro inMmio
        apply load_preserves_ite
        · apply load_preserves_bind (mmio_read (.Load mem_payload.PageTableEntry) address width)
          · exact load_preserves_mmio_read_load_pte address width
          · intro _
            exact load_preserves_pure _
        · simp only [read_kind_of_flags]
          apply load_preserves_bind (read_ram .Read_plain address width false)
          · exact load_preserves_read_ram_plain address width
          · intro _
            exact load_preserves_pure _

private theorem load_preserves_mem_read_priv_meta_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv_meta (.Load mem_payload.Data) pbmt privilege address width
        false false false false) := by
  unfold mem_read_priv_meta
  simp only
  apply load_preserves_bind
      (checked_mem_read (.Load mem_payload.Data) pbmt privilege address width
        false false false false)
  · exact load_preserves_checked_mem_read_load_data address width pbmt privilege
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_mem_read_priv_meta_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv_meta (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false) := by
  unfold mem_read_priv_meta
  simp only
  apply load_preserves_bind
      (checked_mem_read (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false)
  · exact load_preserves_checked_mem_read_load_pte address width pbmt privilege
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_mem_read_priv_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv (.Load mem_payload.Data) pbmt privilege address width false false false) := by
  unfold mem_read_priv
  apply load_preserves_bind
      (mem_read_priv_meta (.Load mem_payload.Data) pbmt privilege address width
        false false false false)
  · exact load_preserves_mem_read_priv_meta_load_data address width pbmt privilege
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_mem_read_priv_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (mem_read_priv (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false) := by
  unfold mem_read_priv
  apply load_preserves_bind
      (mem_read_priv_meta (.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false false)
  · exact load_preserves_mem_read_priv_meta_load_pte address width pbmt privilege
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_mem_read_load_data (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) :
    PreservesStackPointer
      (mem_read (.Load mem_payload.Data) pbmt address width false false false) := by
  unfold mem_read
  apply load_preserves_bind (readReg mstatus)
  · exact load_preserves_readReg mstatus
  · intro mstatusBits
    apply load_preserves_bind (readReg cur_privilege)
    · exact load_preserves_readReg cur_privilege
    · intro privilege
      apply load_preserves_bind (effectivePrivilege (.Load mem_payload.Data) mstatusBits privilege)
      · exact load_preserves_effectivePrivilege (.Load mem_payload.Data) mstatusBits privilege
      · intro effectivePrivilege
        exact load_preserves_mem_read_priv_load_data address width pbmt effectivePrivilege

private theorem load_preserves_writeByte (address : Nat) (value : BitVec 8) :
    PreservesStackPointer (PreSail.writeByte address value : SailM PUnit) := by
  intro state
  rfl

private theorem load_preserves_list_forM (values : List α) (action : α → SailM PUnit)
    (actionFrame : ∀ value, PreservesStackPointer (action value)) :
    PreservesStackPointer (values.forM action) := by
  induction values with
  | nil => exact load_preserves_pure _
  | cons value remaining induction =>
    simp only [List.forM]
    exact load_preserves_bind (action value) (fun _ => remaining.forM action)
      (actionFrame value) (fun _ => induction)

private theorem load_preserves_writeBytes (address : Nat) (value : BitVec (8 * width)) :
    PreservesStackPointer (PreSail.writeBytes address value : SailM Bool) := by
  unfold PreSail.writeBytes
  apply load_preserves_bind
  · apply load_preserves_list_forM
    intro byte
    exact load_preserves_writeByte byte.1 byte.2
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_sail_mem_write [Sail.ConcurrencyInterfaceV1.Arch]
    (request : Sail.ConcurrencyInterfaceV1.Mem_write_request n vasize (BitVec pa_size) ts Arch) :
    PreservesStackPointer (PreSail.ConcurrencyInterfaceV1.sail_mem_write request) := by
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_write
  cases hValue : request.value with
  | none =>
    exact load_preserves_pure _
  | some value =>
    apply load_preserves_bind (PreSail.writeBytes request.pa.toNat value)
    · exact load_preserves_writeBytes request.pa.toNat value
    · intro _
      exact load_preserves_pure _

private def load_write_ram_plain_request (address : physaddrbits) (width : Nat)
    (data : BitVec (8 * width)) :
    SailM (Sail.ConcurrencyInterfaceV1.Mem_write_request width 64 physaddrbits Unit
      RISCV_strong_access) := do
  let accessKind ← pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal })
  pure { access_kind := accessKind
         va := none
         pa := address
         translation := ()
         size := width
         value := some data
         tag := none }

private theorem load_preserves_write_ram_plain_request (address : physaddrbits) (width : Nat)
    (data : BitVec (8 * width)) :
    PreservesStackPointer (load_write_ram_plain_request address width data) := by
  unfold load_write_ram_plain_request
  apply load_preserves_bind (pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal }))
  · exact load_preserves_pure _
  · intro _
    exact load_preserves_pure _

private theorem load_write_ram_plain_unfold (address : physaddrbits) (width : Nat)
    (data : BitVec (8 * width)) (metadata : Unit) :
    write_ram .Write_plain (.Physaddr address) width data metadata = (do
      let request ← load_write_ram_plain_request address width data
      match ← Sail.ConcurrencyInterfaceV1.sail_mem_write request with
      | .Ok _ => pure true
      | .Err () => pure false) := by
  rfl

private theorem load_preserves_write_ram_plain (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (metadata : Unit) :
    PreservesStackPointer (write_ram .Write_plain address width data metadata) := by
  rcases address with ⟨address⟩
  rw [load_write_ram_plain_unfold]
  apply load_preserves_bind (load_write_ram_plain_request address width data)
  · exact load_preserves_write_ram_plain_request address width data
  · intro request
    apply load_preserves_bind (Sail.ConcurrencyInterfaceV1.sail_mem_write request)
    · exact load_preserves_sail_mem_write request
    · intro result
      cases result <;> exact load_preserves_pure _

private theorem load_preserves_within_mmio_writable (address : physaddr) (width : Nat) :
    PreservesStackPointer (within_mmio_writable address width) := by
  unfold within_mmio_writable
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_bind (within_clint address width)
    · exact load_preserves_within_clint address width
    · intro _
      apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro _
        apply load_preserves_bind (within_htif_writable address width)
        · exact load_preserves_within_htif_writable address width
        · intro _
          exact load_preserves_pure _

private theorem load_preserves_external_seip :
    PreservesStackPointer ((do
      let enabled ← currentlyEnabled extension.Ext_S
      if enabled then readReg sig_seip else pure 0#1) : SailM (BitVec 1)) := by
  apply load_preserves_bind (currentlyEnabled extension.Ext_S)
  · exact load_preserves_currentlyEnabled_S
  · intro enabled
    apply load_preserves_ite
    · exact load_preserves_readReg sig_seip
    · exact load_preserves_pure _

private theorem load_preserves_external_interrupts_pending :
    PreservesStackPointer (external_interrupts_pending ()) := by
  unfold external_interrupts_pending
  apply load_preserves_bind (readReg sig_meip)
  · exact load_preserves_readReg sig_meip
  · intro _
    apply load_preserves_bind
    · exact load_preserves_external_seip
    · intro _
      exact load_preserves_pure _

private theorem load_preserves_read_mip (readType : XipReadType) :
    PreservesStackPointer (read_mip readType) := by
  cases readType
  · unfold read_mip
    apply load_preserves_bind (readReg mip)
    · exact load_preserves_readReg mip
    · intro mipBits
      apply load_preserves_bind (external_interrupts_pending ())
      · exact load_preserves_external_interrupts_pending
      · intro _
        exact load_preserves_pure _
  · unfold read_mip
    exact load_preserves_readReg mip

private theorem load_preserves_csr_name_map_backwards_mip :
    PreservesStackPointer (csr_name_map_backwards "mip") := by
  unfold csr_name_map_backwards
  exact load_preserves_pure _

private theorem load_preserves_csr_name_write_callback_mip (value : BitVec 64) :
    PreservesStackPointer (csr_name_write_callback "mip" value) := by
  unfold csr_name_write_callback
  apply load_preserves_bind (csr_name_map_backwards "mip")
  · exact load_preserves_csr_name_map_backwards_mip
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_clint_dispatch_tail (oldMip : BitVec 64) (mipWasWritten : Bool) :
    PreservesStackPointer (do
      let _ ← (pure () : SailM PUnit)
      let currentMip ← readReg mip
      if (oldMip != currentMip || mipWasWritten) then do
        let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
        csr_name_write_callback "mip" mipValue
      else pure ()) := by
  apply load_preserves_bind (pure ())
  · exact load_preserves_pure _
  · intro _
    apply load_preserves_bind (readReg mip)
    · exact load_preserves_readReg mip
    · intro currentMip
      apply load_preserves_ite
      · apply load_preserves_bind (read_mip XipReadType.IncludePlatformInterrupts)
        · exact load_preserves_read_mip XipReadType.IncludePlatformInterrupts
        · intro mipValue
          exact load_preserves_csr_name_write_callback_mip mipValue
      · exact load_preserves_pure _

private theorem load_preserves_clint_dispatch (mipWasWritten : Bool) :
    PreservesStackPointer (clint_dispatch mipWasWritten) :=
  clint_dispatch_preserves_stack_pointer mipWasWritten

private theorem load_preserves_read_then_write (written : Register)
    (update : RegisterType written → RegisterType written) (notStack : x2 ≠ written) :
    PreservesStackPointer (readReg written >>= fun value => writeReg written (update value)) := by
  apply load_preserves_bind (readReg written)
  · exact load_preserves_readReg written
  · intro value
    exact load_preserves_writeReg written (update value) notStack

private theorem load_preserves_then_clint_dispatch (initial : SailM α)
    (initialFrame : PreservesStackPointer initial) (mipWasWritten : Bool) :
    PreservesStackPointer (initial >>= fun _ => clint_dispatch mipWasWritten >>= fun _ =>
      (pure (Sail.Result.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply load_preserves_bind initial
  · exact initialFrame
  · intro _
    apply load_preserves_bind (clint_dispatch mipWasWritten)
    · exact load_preserves_clint_dispatch mipWasWritten
    · intro _
      exact load_preserves_pure _

private theorem load_preserves_clint_result (mipWasWritten : Bool) :
    PreservesStackPointer (clint_dispatch mipWasWritten >>= fun _ =>
      (pure (Sail.Result.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply load_preserves_bind (clint_dispatch mipWasWritten)
  · exact load_preserves_clint_dispatch mipWasWritten
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_clint_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesStackPointer (clint_store address width data) := by
  unfold clint_store
  apply load_preserves_ite
  · apply load_preserves_bind (Sail.readReg mip)
    · exact load_preserves_readReg mip
    · intro current
      apply load_preserves_bind (Sail.writeReg mip (Sail.BitVec.updateSubrange current 3 3
        (Sail.BitVec.join1 [Sail.BitVec.access data 0])))
      · exact load_preserves_writeReg mip _ (by decide)
      · intro _
        exact load_preserves_clint_result true
  · apply load_preserves_ite
    · exact load_preserves_then_clint_dispatch (writeReg mtimecmp (zero_extend (m := 64) data))
        (load_preserves_writeReg mtimecmp _ (by decide)) false
    · apply load_preserves_ite
      · apply load_preserves_bind (readReg mtimecmp)
        · exact load_preserves_readReg mtimecmp
        · intro current
          apply load_preserves_bind (writeReg mtimecmp _)
          · exact load_preserves_writeReg mtimecmp _ (by decide)
          · intro _
            exact load_preserves_clint_result false
      · apply load_preserves_ite
        · apply load_preserves_bind (readReg mtimecmp)
          · exact load_preserves_readReg mtimecmp
          · intro current
            apply load_preserves_bind (writeReg mtimecmp _)
            · exact load_preserves_writeReg mtimecmp _ (by decide)
            · intro _
              exact load_preserves_clint_result false
        · apply load_preserves_ite
          · exact load_preserves_then_clint_dispatch (writeReg mtime data)
              (load_preserves_writeReg mtime _ (by decide)) false
          · apply load_preserves_ite
            · apply load_preserves_bind (readReg mtime)
              · exact load_preserves_readReg mtime
              · intro current
                apply load_preserves_bind (writeReg mtime _)
                · exact load_preserves_writeReg mtime _ (by decide)
                · intro _
                  exact load_preserves_clint_result false
            · apply load_preserves_ite
              · apply load_preserves_bind (readReg mtime)
                · exact load_preserves_readReg mtime
                · intro current
                  apply load_preserves_bind (writeReg mtime _)
                  · exact load_preserves_writeReg mtime _ (by decide)
                  · intro _
                    exact load_preserves_clint_result false
              · exact load_preserves_pure _

private theorem load_preserves_mip_callback_ok :
    PreservesStackPointer (read_mip XipReadType.IncludePlatformInterrupts >>= fun value =>
      csr_name_write_callback "mip" value >>= fun _ =>
        (pure (Sail.Result.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply load_preserves_bind (read_mip XipReadType.IncludePlatformInterrupts)
  · exact load_preserves_read_mip XipReadType.IncludePlatformInterrupts
  · intro value
    apply load_preserves_bind (csr_name_write_callback "mip" value)
    · exact load_preserves_csr_name_write_callback_mip value
    · intro _
      exact load_preserves_pure _

private def load_sig_after_ssi (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  let enabled ← currentlyEnabled extension.Ext_S
  if ((_get_Minterrupts_SSI interrupts == 1#1) && enabled) then do
    let current ← readReg mip
    let _ ← writeReg mip (Sail.BitVec.updateSubrange current 1 1 value)
    let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
    csr_name_write_callback "mip" mipValue
    pure (Sail.Result.Ok true)
  else do
    let _ ← (pure () : SailM PUnit)
    let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
    csr_name_write_callback "mip" mipValue
    pure (Sail.Result.Ok true)

private def load_sig_after_msi (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := if _get_Minterrupts_MSI interrupts == 1#1 then do
      let current ← readReg mip
      let _ ← writeReg mip (Sail.BitVec.updateSubrange current 3 3 value)
      load_sig_after_ssi interrupts value
    else do
      let _ ← (pure () : SailM PUnit)
      load_sig_after_ssi interrupts value

private def load_sig_after_sei (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := if _get_Minterrupts_SEI interrupts == 1#1 then do
      let _ ← writeReg sig_seip value
      load_sig_after_msi interrupts value
    else do
      let _ ← (pure () : SailM PUnit)
      load_sig_after_msi interrupts value

private def load_sig_after_mei (interrupts : BitVec 64) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := if _get_Minterrupts_MEI interrupts == 1#1 then do
      let _ ← writeReg sig_meip value
      load_sig_after_sei interrupts value
    else do
      let _ ← (pure () : SailM PUnit)
      load_sig_after_sei interrupts value

private theorem load_preserves_sig_after_ssi (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_ssi interrupts value) := by
  unfold load_sig_after_ssi
  apply load_preserves_bind (currentlyEnabled extension.Ext_S)
  · exact load_preserves_currentlyEnabled_S
  · intro enabled
    apply load_preserves_ite
    · apply load_preserves_bind (readReg mip)
      · exact load_preserves_readReg mip
      · intro current
        apply load_preserves_bind (writeReg mip _)
        · exact load_preserves_writeReg mip _ (by decide)
        · intro _
          exact load_preserves_mip_callback_ok
    · apply load_preserves_bind (pure ())
      · exact load_preserves_pure _
      · intro _
        exact load_preserves_mip_callback_ok

private theorem load_preserves_sig_after_msi (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_msi interrupts value) := by
  unfold load_sig_after_msi
  apply load_preserves_ite
  · apply load_preserves_bind (readReg mip)
    · exact load_preserves_readReg mip
    · intro current
      apply load_preserves_bind (writeReg mip _)
      · exact load_preserves_writeReg mip _ (by decide)
      · intro _
        exact load_preserves_sig_after_ssi interrupts value
  · apply load_preserves_bind (pure ())
    · exact load_preserves_pure _
    · intro _
      exact load_preserves_sig_after_ssi interrupts value

private theorem load_preserves_sig_after_sei (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_sei interrupts value) := by
  unfold load_sig_after_sei
  apply load_preserves_ite
  · apply load_preserves_bind (writeReg sig_seip value)
    · exact load_preserves_writeReg sig_seip value (by decide)
    · intro _
      exact load_preserves_sig_after_msi interrupts value
  · apply load_preserves_bind (pure ())
    · exact load_preserves_pure _
    · intro _
      exact load_preserves_sig_after_msi interrupts value

private theorem load_preserves_sig_after_mei (interrupts : BitVec 64) (value : BitVec 1) :
    PreservesStackPointer (load_sig_after_mei interrupts value) := by
  unfold load_sig_after_mei
  apply load_preserves_ite
  · apply load_preserves_bind (writeReg sig_meip value)
    · exact load_preserves_writeReg sig_meip value (by decide)
    · intro _
      exact load_preserves_sig_after_sei interrupts value
  · apply load_preserves_bind (pure ())
    · exact load_preserves_pure _
    · intro _
      exact load_preserves_sig_after_sei interrupts value

private theorem load_preserves_sig_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesStackPointer (sig_store address width data) := by
  unfold sig_store
  apply load_preserves_ite
  · exact load_preserves_pure _
  · apply load_preserves_ite
    · exact load_preserves_pure _
    · apply load_preserves_ite
      · apply load_preserves_ite
        · exact load_preserves_pure _
        · exact load_preserves_sig_after_mei (Mk_Minterrupts (zero_extend data))
            (Sail.BitVec.access data 31)
      · exact load_preserves_pure _

private theorem load_preserves_except_readReg (register : Register) :
    LoadPreservesExcept (ExceptT.lift (readReg register) : SailME ε (RegisterType register)) :=
  load_preserves_except_lift (readReg register) (load_preserves_readReg register)

private theorem load_preserves_except_writeReg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) :
    LoadPreservesExcept (ExceptT.lift (writeReg written value) : SailME ε PUnit) :=
  load_preserves_except_lift (writeReg written value)
    (load_preserves_writeReg written value notStack)

private theorem load_preserves_except_read_then_write (written : Register)
    (update : RegisterType written → RegisterType written) (notStack : x2 ≠ written) :
    LoadPreservesExcept (do
      let value ← ExceptT.lift (readReg written)
      ExceptT.lift (writeReg written (update value)) : SailME ε PUnit) := by
  apply load_preserves_except_bind
  · exact load_preserves_except_readReg written
  · intro value
    exact load_preserves_except_writeReg written (update value) notStack

private theorem load_preserves_reset_htif : PreservesStackPointer (reset_htif ()) := by
  unfold reset_htif
  apply load_preserves_bind (writeReg htif_cmd_write _)
  · exact load_preserves_writeReg htif_cmd_write _ (by decide)
  · intro _
    apply load_preserves_bind (writeReg htif_payload_writes _)
    · exact load_preserves_writeReg htif_payload_writes _ (by decide)
    · intro _
      exact load_preserves_writeReg htif_tohost _ (by decide)

private theorem load_preserves_plat_term_write (value : BitVec 8) :
    PreservesStackPointer (plat_term_write value) := by
  intro state
  rfl

private theorem load_preserves_htif_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesStackPointer (htif_store address width data) :=
  htif_store_preserves_stack_pointer address width data

private theorem load_preserves_mmio_write (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) :
    PreservesStackPointer (mmio_write address width data) := by
  unfold mmio_write
  apply load_preserves_bind (within_clint address width)
  · exact load_preserves_within_clint address width
  · intro inClint
    apply load_preserves_ite
    · exact load_preserves_clint_store address width data
    · apply load_preserves_bind (within_sig address width)
      · exact load_preserves_within_sig address width
      · intro inSig
        apply load_preserves_ite
        · exact load_preserves_sig_store address width data
        · apply load_preserves_bind (within_htif_writable address width)
          · exact load_preserves_within_htif_writable address width
          · intro inHtif
            apply load_preserves_ite
            · exact load_preserves_htif_store address width data
            · exact load_preserves_pure _

private theorem load_preserves_checked_mem_write_store_pte (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesStackPointer
      (checked_mem_write address width data (.Store mem_payload.PageTableEntry) pbmt privilege
        default_meta false false false) := by
  unfold checked_mem_write
  apply load_preserves_bind
      (phys_access_check (.Store mem_payload.PageTableEntry) pbmt privilege address width false)
  · exact load_preserves_phys_access_check_store_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact load_preserves_pure _
    | none =>
      apply load_preserves_bind (within_mmio_writable address width)
      · exact load_preserves_within_mmio_writable address width
      · intro inMmio
        apply load_preserves_ite
        · exact load_preserves_mmio_write address width data
        · simp only [write_kind_of_flags]
          apply load_preserves_bind (write_ram .Write_plain address width data default_meta)
          · exact load_preserves_write_ram_plain address width data default_meta
          · intro _
            exact load_preserves_pure _

private theorem load_preserves_mem_write_value_priv_meta_store_pte (address : physaddr)
    (width : Nat) (data : BitVec (8 * width)) (pbmt : page_based_mem_type)
    (privilege : Privilege) :
    PreservesStackPointer
      (mem_write_value_priv_meta address width data (.Store mem_payload.PageTableEntry) pbmt
        privilege default_meta false false false) := by
  unfold mem_write_value_priv_meta
  simp only
  apply load_preserves_bind
      (checked_mem_write address width data (.Store mem_payload.PageTableEntry) pbmt privilege
        default_meta false false false)
  · exact load_preserves_checked_mem_write_store_pte address width data pbmt privilege
  · intro _
    exact load_preserves_pure _

private theorem load_preserves_mem_write_value_priv_store_pte (address : physaddr)
    (width : Nat) (data : BitVec (8 * width)) (privilege : Privilege)
    (pbmt : page_based_mem_type) :
    PreservesStackPointer
      (mem_write_value_priv address width data privilege (.Store mem_payload.PageTableEntry) pbmt
        false false false) := by
  unfold mem_write_value_priv
  exact load_preserves_mem_write_value_priv_meta_store_pte address width data pbmt privilege

private theorem load_preserves_write_pte_native (address : physaddr) (width : Nat)
    (data : BitVec (width * 8)) :
    PreservesStackPointer (write_pte address width data) := by
  unfold write_pte
  exact load_preserves_mem_write_value_priv_store_pte address width _ .Supervisor .PBMT_PMA

private theorem load_preserves_pte_is_invalid (flags : BitVec 8) (extensions : BitVec 10) :
    PreservesStackPointer (pte_is_invalid flags extensions) := by
  unfold pte_is_invalid
  apply load_preserves_bind (readReg menvcfg)
  · exact load_preserves_readReg menvcfg
  · intro _
    apply load_preserves_bind (currentlyEnabled extension.Ext_Svnapot)
    · exact load_preserves_currentlyEnabled_Svnapot
    · intro _
      apply load_preserves_bind (readReg menvcfg)
      · exact load_preserves_readReg menvcfg
      · intro _
        apply load_preserves_bind (currentlyEnabled extension.Ext_Svrsw60t59b)
        · exact load_preserves_currentlyEnabled_Svrsw60t59b
        · intro _
          exact load_preserves_pure _

private theorem load_preserves_check_pte_priv_ok (privilege : Privilege) (pteU : Bool)
    (doSum : Bool) :
    LoadPreservesExcept ((match privilege with
      | .User => pure pteU
      | .Supervisor => pure ((LeanRV64DExecutable.Functions.not pteU) || (doSum && true))
      | .Machine => internal_error "sys/vmem_pte.sail" 151 "m-mode mem perm check"
      | .VirtualUser => internal_error "sys/vmem_pte.sail" 152 "Hypervisor extension not supported"
      | .VirtualSupervisor =>
        internal_error "sys/vmem_pte.sail" 153 "Hypervisor extension not supported") :
      SailME PTE_Check Bool) := by
  cases privilege with
  | User => exact load_preserves_except_pure pteU
  | Supervisor => exact load_preserves_except_pure _
  | Machine => exact load_preserves_except_lift (internal_error "sys/vmem_pte.sail" 151
      "m-mode mem perm check" : SailM Bool) (load_preserves_internal_error _ _ _)
  | VirtualUser => exact load_preserves_except_lift (internal_error "sys/vmem_pte.sail" 152
      "Hypervisor extension not supported" : SailM Bool) (load_preserves_internal_error _ _ _)
  | VirtualSupervisor => exact load_preserves_except_lift (internal_error "sys/vmem_pte.sail" 153
      "Hypervisor extension not supported" : SailM Bool) (load_preserves_internal_error _ _ _)

private theorem load_preserves_check_pte_finish_load_data (pteR pteX mxr : Bool) :
    LoadPreservesExcept (do
      let readable := pteR || (pteX && mxr)
      if LeanRV64DExecutable.Functions.not readable then
        pure (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Permission ()))
      else pure (PTE_Check.PTE_Check_Success ()) : SailME PTE_Check PTE_Check) := by
  apply load_preserves_except_ite
  · exact load_preserves_except_pure _
  · exact load_preserves_except_pure _

private theorem load_preserves_check_pte_reserved_load_data :
    LoadPreservesExcept (do
      let environment ← ExceptT.lift (readReg menvcfg)
      ExceptT.lift (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
        "sys/vmem_pte.sail:162.33-162.34")
      let shadowStackOk ← pure true
      if LeanRV64DExecutable.Functions.not shadowStackOk then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply load_preserves_except_lift_bind (readReg menvcfg)
  · exact load_preserves_readReg menvcfg
  · intro environment
    apply load_preserves_except_lift_bind
        (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
          "sys/vmem_pte.sail:162.33-162.34")
    · exact load_preserves_assert _ _
    · intro _
      apply load_preserves_except_bind
      · exact load_preserves_except_pure true
      · intro shadowStackOk
        apply load_preserves_except_ite
        · exact load_preserves_except_throw _
        · exact load_preserves_except_pure _

private theorem load_preserves_check_pte_nonreserved_load_data (flags : BitVec 8) :
    LoadPreservesExcept (do
      let shadowStack ← ExceptT.lift (is_shadow_stack_access (.Load mem_payload.Data))
      if shadowStack then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((),
          if (bit_to_bool (_get_PTE_Flags_R flags)) &&
              (LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_W flags)) &&
                LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_X flags))) then
            pte_check_failure.PTE_No_Permission ()
          else pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply load_preserves_except_lift_bind (is_shadow_stack_access (.Load mem_payload.Data))
  · exact load_preserves_is_shadow_stack_access (.Load mem_payload.Data)
  · intro shadowStack
    apply load_preserves_except_ite
    · exact load_preserves_except_throw _
    · exact load_preserves_except_pure _

private theorem load_preserves_check_PTE_permission_load_data (privilege : Privilege)
    (mxr doSum : Bool) (flags : BitVec 8) (extensions : BitVec 10) (external : Unit) :
    PreservesStackPointer
      (check_PTE_permission (.Load mem_payload.Data) privilege mxr doSum flags extensions
        external) := by
  unfold check_PTE_permission
  apply load_preserves_sailME_run
  apply load_preserves_except_lift_bind
  · exact load_preserves_assert _ _
  · intro _
    apply load_preserves_except_bind
    · exact load_preserves_check_pte_priv_ok privilege (bit_to_bool (_get_PTE_Flags_U flags)) doSum
    · intro privOk
      apply load_preserves_except_ite
      · exact load_preserves_except_pure _
      · apply load_preserves_except_ite
        · apply load_preserves_except_bind
          · exact load_preserves_check_pte_reserved_load_data
          · intro _
            exact load_preserves_check_pte_finish_load_data
              (bit_to_bool (_get_PTE_Flags_R flags)) (bit_to_bool (_get_PTE_Flags_X flags)) mxr
        · apply load_preserves_except_bind
          · exact load_preserves_check_pte_nonreserved_load_data flags
          · intro _
            exact load_preserves_check_pte_finish_load_data
              (bit_to_bool (_get_PTE_Flags_R flags)) (bit_to_bool (_get_PTE_Flags_X flags)) mxr

private theorem load_preserves_update_and_write_pte_load_data (address : physaddr) (width : Nat)
    (pte : BitVec (width * 8)) :
    PreservesStackPointer
      (update_and_write_pte address width pte (.Load mem_payload.Data)) := by
  unfold update_and_write_pte
  cases hUpdate : update_PTE_Bits pte
      (.Load mem_payload.Data) with
  | none => exact load_preserves_pure _
  | some updated =>
    apply load_preserves_bind (currentlyEnabled extension.Ext_Svadu)
    · exact load_preserves_currentlyEnabled_Svadu
    · intro _
      apply load_preserves_bind (readReg menvcfg)
      · exact load_preserves_readReg menvcfg
      · intro _
        apply load_preserves_bind (currentlyEnabled extension.Ext_Svadu)
        · exact load_preserves_currentlyEnabled_Svadu
        · intro _
          apply load_preserves_bind (currentlyEnabled extension.Ext_Svade)
          · exact load_preserves_currentlyEnabled_Svade
          · intro _
            apply load_preserves_ite
            · apply load_preserves_bind (write_pte address width updated)
              · exact load_preserves_write_pte_native address width updated
              · intro result
                cases result <;> exact load_preserves_pure _
            · exact load_preserves_pure _

private theorem load_preserves_read_pte (address : physaddr) (width : Nat) :
    PreservesStackPointer (read_pte address width) := by
  unfold read_pte
  exact load_preserves_mem_read_priv_load_pte address width .PBMT_PMA .Supervisor

private theorem load_preserves_write_TLB (index : Nat) (entry : TLB_Entry) :
    PreservesStackPointer (write_TLB index entry) := by
  unfold write_TLB
  apply load_preserves_bind (readReg tlb)
  · exact load_preserves_readReg tlb
  · intro entries
    exact load_preserves_writeReg tlb _ (by decide)

private theorem load_preserves_lookup_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12)) :
    PreservesStackPointer (lookup_TLB svWidth asid vpn) := by
  unfold lookup_TLB
  apply load_preserves_bind (readReg tlb)
  · exact load_preserves_readReg tlb
  · intro entries
    cases entry : GetElem?.getElem! entries (tlb_hash svWidth vpn) with
    | none => exact load_preserves_pure _
    | some entry =>
      apply load_preserves_ite <;> exact load_preserves_pure _

private theorem load_preserves_add_to_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (ppn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (pte : BitVec (if (svWidth == 32 : Bool) then 32 else 64)) (pteAddress : physaddr)
    (level : Nat) (global : Bool) :
    PreservesStackPointer (add_to_TLB svWidth asid vpn ppn pte pteAddress level global) := by
  unfold add_to_TLB
  apply load_preserves_bind (readReg tlb)
  · exact load_preserves_readReg tlb
  · intro entries
    apply load_preserves_bind (writeReg tlb _)
    · exact load_preserves_writeReg tlb _ (by decide)
    · intro _
      apply load_preserves_bind (readReg tlb)
      · exact load_preserves_readReg tlb
      · intro updatedEntries
        exact load_preserves_pure _

private theorem load_preserves_page_based_mem_type_forwards (bits : BitVec 2) :
    PreservesStackPointer (page_based_mem_type_forwards bits) := by
  have cases : bits.toNat = 0 ∨ bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
    omega
  rcases cases with h | h | h | h
  all_goals
    have value : bits = BitVec.ofNat 2 bits.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [value]
    simp [page_based_mem_type_forwards, h, EStateM.instMonad]
    all_goals first | exact load_preserves_pure _ | exact load_preserves_throw _

private theorem load_preserves_tlb_get_pbmt (entry : TLB_Entry) :
    PreservesStackPointer (tlb_get_pbmt entry) := by
  unfold tlb_get_pbmt
  exact load_preserves_page_based_mem_type_forwards _

private theorem load_preserves_translate_TLB_hit_load_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) (index : Nat) (entry : TLB_Entry) :
    PreservesStackPointer
      (translate_TLB_hit svWidth asid vpn (.Load mem_payload.Data) privilege mxr doSum external
        index entry) := by
  exact translate_tlb_hit_preserves_stack_pointer_of svWidth asid vpn (.Load mem_payload.Data)
    privilege mxr doSum external index entry
    (fun flags extensions =>
      load_preserves_check_PTE_permission_load_data privilege mxr doSum flags extensions external)
    (fun address width pte => load_preserves_update_and_write_pte_load_data address width pte)
    (fun index entry => load_preserves_write_TLB index entry) (load_preserves_tlb_get_pbmt entry)

private theorem load_preserves_pt_walk_load_data (svWidth : Nat) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit)
    (ptBase : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (level : Nat) (global : Bool) :
    PreservesStackPointer
      (pt_walk svWidth vpn (.Load mem_payload.Data) privilege mxr doSum ptBase level global
        external) := by
  apply pt_walk_preserves_stack_pointer_of svWidth vpn (.Load mem_payload.Data) privilege mxr doSum
    external
  · exact load_preserves_read_pte
  · exact load_preserves_pte_is_invalid
  · exact fun flags extensions =>
      load_preserves_check_PTE_permission_load_data privilege mxr doSum flags extensions external
  · exact load_preserves_currentlyEnabled_Svnapot

private theorem load_preserves_translate_TLB_miss_load_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (vpn : BitVec (svWidth - 12)) (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesStackPointer
      (translate_TLB_miss svWidth asid basePpn vpn (.Load mem_payload.Data) privilege mxr doSum
        external) := by
  apply translate_tlb_miss_preserves_stack_pointer_of svWidth asid basePpn vpn
      (.Load mem_payload.Data) privilege mxr doSum external
  · exact load_preserves_pt_walk_load_data svWidth vpn privilege mxr doSum external
  · intro address width pte
    exact load_preserves_update_and_write_pte_load_data address width pte
  · intro ppn pte pteAddress level global
    exact load_preserves_add_to_TLB svWidth asid vpn ppn pte pteAddress level global

private theorem load_preserves_translate_load_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (vpn : BitVec (svWidth - 12)) (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesStackPointer
      (translate svWidth asid basePpn vpn (.Load mem_payload.Data) privilege mxr doSum
        external) := by
  apply translate_preserves_stack_pointer_of svWidth asid basePpn vpn (.Load mem_payload.Data)
      privilege mxr doSum external
  · exact load_preserves_lookup_TLB svWidth asid vpn
  · exact load_preserves_translate_TLB_hit_load_data svWidth asid vpn privilege mxr doSum external
  · exact load_preserves_translate_TLB_miss_load_data svWidth asid basePpn vpn privilege mxr doSum
      external

private theorem load_preserves_translateAddr_load_data (vaddr : virtaddr) :
    PreservesStackPointer (translateAddr vaddr (.Load mem_payload.Data)) := by
  apply translate_addr_preserves_stack_pointer_of vaddr (.Load mem_payload.Data)
  · exact load_preserves_effectivePrivilege (.Load mem_payload.Data)
  · exact load_preserves_translationMode
  · exact load_preserves_is_shadow_stack_access (.Load mem_payload.Data)
  · exact load_preserves_satp_mode_width_forwards
  · exact load_preserves_get_satp
  · exact load_preserves_translationException_load_data
  · intro svWidth asid basePpn vpn privilege mxr doSum
    exact load_preserves_translate_load_data svWidth asid basePpn vpn privilege mxr doSum
      init_ext_ptw

private theorem load_preserves_vmem_read_misaligned_then (vaddr : virtaddr) (width : Nat) :
    LoadPreservesExcept (do
      match ← ExceptT.lift (plat_misaligned_exception (.Load mem_payload.Data) false) with
      | some .AccessFault =>
        let result ← ExceptT.lift
          (memory_exception vaddr (ExceptionType.E_Load_Access_Fault ()))
        Sail.SailME.throw (Sail.Result.Err result)
      | some .AlignmentException =>
        let result ← ExceptT.lift
          (memory_exception vaddr (ExceptionType.E_Load_Addr_Align ()))
        Sail.SailME.throw (Sail.Result.Err result)
      | none => pure () : SailME (Sail.Result (BitVec (8 * width)) ExecutionResult) PUnit) := by
  apply load_preserves_except_lift_bind
      (plat_misaligned_exception (.Load mem_payload.Data) false)
  · exact load_preserves_plat_misaligned_exception (.Load mem_payload.Data) false
  · intro result
    cases result with
    | none => exact load_preserves_except_pure _
    | some result =>
      cases result with
      | AccessFault =>
        apply load_preserves_except_lift_bind
            (memory_exception vaddr (ExceptionType.E_Load_Access_Fault ()))
        · exact load_preserves_memory_exception _ _
        · intro exception
          exact load_preserves_except_throw (Sail.Result.Err exception)
      | AlignmentException =>
        apply load_preserves_except_lift_bind
            (memory_exception vaddr (ExceptionType.E_Load_Addr_Align ()))
        · exact load_preserves_memory_exception _ _
        · intro exception
          exact load_preserves_except_throw (Sail.Result.Err exception)

private theorem load_preserves_vmem_read_addr_load_data (vaddr : virtaddr) (width : Nat) :
    PreservesStackPointer
      (vmem_read_addr vaddr width (.Load mem_payload.Data) false false false) := by
  unfold vmem_read_addr
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply load_preserves_sailME_run
  apply load_preserves_except_ite_bind
  · exact load_preserves_vmem_read_misaligned_then vaddr width
  · exact load_preserves_except_pure _
  · intro _
    apply load_preserves_except_lift_bind (split_misaligned vaddr width)
    · exact load_preserves_split_misaligned vaddr width
    · rintro ⟨n, bytes⟩
      apply load_preserves_except_bind
      · apply load_preserves_except_bind
        · apply load_preserves_untilFuelM
          · intro loopVars
            exact load_preserves_except_pure loopVars.2.1
          · rintro ⟨data, finished, i⟩
            apply load_preserves_except_lift_bind (Sail.assert true "loop dummy assert")
            · exact load_preserves_assert _ _
            · intro _
              apply load_preserves_except_bind
              · apply load_preserves_except_bind
                · exact load_preserves_except_lift _
                    (load_preserves_translateAddr_load_data _)
                · intro translation
                  cases translation with
                  | Err failure =>
                    rcases failure with ⟨failure, extensionState⟩
                    simp only
                    apply load_preserves_except_bind
                    · apply load_preserves_except_lift_bind
                        (memory_exception
                          (virtaddr.Virtaddr
                            (Sail.BitVec.addInt (bits_of_virtaddr vaddr) (i *i bytes))) failure)
                      · exact load_preserves_memory_exception _ _
                      · intro result
                        exact load_preserves_except_pure (Sail.Result.Err result)
                    · intro error
                      exact load_preserves_except_throw error
                  | Ok translation =>
                    rcases translation with ⟨address, pbmt, extensionState⟩
                    simp only
                    apply load_preserves_except_bind
                    · exact load_preserves_except_lift _
                        (load_preserves_mem_read_load_data address bytes.toNat pbmt)
                    · intro read
                      cases read with
                      | Err failure =>
                        simp only
                        apply load_preserves_except_bind
                        · apply load_preserves_except_lift_bind
                            (memory_exception
                              (virtaddr.Virtaddr
                                (Sail.BitVec.addInt
                                  (bits_of_virtaddr vaddr) (i *i bytes))) failure)
                          · exact load_preserves_memory_exception _ _
                          · intro result
                            exact load_preserves_except_pure (Sail.Result.Err result)
                        · intro error
                          exact load_preserves_except_throw error
                      | Ok value =>
                        simp only
                        apply load_preserves_except_bind
                        · exact load_preserves_except_pure ()
                        · intro _
                          exact load_preserves_except_pure _
              · intro updated
                exact load_preserves_except_pure _
        · intro loopVars
          exact (load_preserves_except_pure loopVars : LoadPreservesExcept
            (pure loopVars : SailME (Sail.Result (BitVec (8 * width)) ExecutionResult)
              (BitVec ((8 *i n) *i bytes) × Bool × Nat)))
      · rintro ⟨data, finished, i⟩
        exact load_preserves_except_pure
          (Sail.Result.Ok (BitVec.setWidth (8 * width) data) :
            Sail.Result (BitVec (8 * width)) ExecutionResult)

private theorem load_preserves_vmem_read_load_data (source : regidx) (offset : BitVec 64)
    (width : Nat) :
    PreservesStackPointer
      (vmem_read source offset width (.Load mem_payload.Data) false false false) := by
  unfold vmem_read
  apply load_preserves_sailME_run
  apply load_preserves_except_bind
  · apply load_preserves_except_bind
    · exact load_preserves_except_lift _
        (load_preserves_get_transformed_data_addr source offset (.Load mem_payload.Data) width)
    · intro transformed
      cases transformed with
      | Ext_DataAddr_Error error =>
        exact load_preserves_except_throw
          (Sail.Result.Err (ExecutionResult.Ext_DataAddr_Check_Failure error))
      | Ext_DataAddr_OK address => exact load_preserves_except_pure address
  · intro address
    exact load_preserves_except_lift _
      (load_preserves_vmem_read_addr_load_data address width)

private theorem load_preserves_wX_bits (destination : regidx) (data : BitVec 64)
    (notStack : destination ≠ stackPointer) :
    PreservesStackPointer (wX_bits destination data) := by
  intro state
  cases hAction : (wX_bits destination data).run state <;>
    simpa [hAction] using wX_bits_preserves_stack_pointer state destination data notStack

/-- A generated LOAD preserves `x2` when its destination is not the stack pointer. -/
theorem execute_LOAD_preserves_stack_pointer (immediate : BitVec 12)
    (source destination : regidx) (isUnsigned : Bool) (width : Nat)
    (notStack : destination ≠ stackPointer) :
    PreservesStackPointer (execute_LOAD immediate source destination isUnsigned width) := by
  unfold execute_LOAD
  apply load_preserves_bind (Sail.assert (width ≤b LeanRV64DExecutable.Functions.xlen_bytes)
    "extensions/I/base_insts.sail:289.28-289.29")
  · exact load_preserves_assert _ _
  · intro _
    apply load_preserves_bind
    · exact load_preserves_vmem_read_load_data source (sign_extend (m := 64) immediate) width
    · intro result
      cases result with
      | Err error => exact load_preserves_pure error
      | Ok data =>
        apply load_preserves_bind (wX_bits destination (extend_value isUnsigned data))
        · exact load_preserves_wX_bits destination _ notStack
        · intro _
          exact load_preserves_pure RETIRE_SUCCESS

/-- The generated dispatcher preserves `x2` for every LOAD outcome off the stack destination. -/
theorem executeLOADDispatchPreservesStackPointer (state : State) (immediate : BitVec 12)
    (source destination : regidx) (isUnsigned : Bool) (width : Nat)
    (notStack : destination ≠ stackPointer) :
    (match (execute (.LOAD (immediate, source, destination, isUnsigned, width))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_LOAD immediate source destination isUnsigned width).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  have frame :=
    execute_LOAD_preserves_stack_pointer immediate source destination isUnsigned width notStack
  unfold PreservesStackPointer at frame
  cases hAction : (execute_LOAD immediate source destination isUnsigned width).run state <;>
    simpa [hAction] using frame state

end BinaryFv.RISCV
