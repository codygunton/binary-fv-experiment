import BinaryFv.RiscV.Instruction.Frame.BType
import BinaryFv.RiscV.Platform.ClintFrame
import BinaryFv.RiscV.Platform.ExtensionFrame
import BinaryFv.RiscV.Platform.HtifFrame
import BinaryFv.RiscV.Platform.TranslationFrame
import Lean.Elab.Tactic.Omega

/-!
# Monadic calculus for the LOAD stack-pointer frame
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

theorem load_preserves_bind (first : SailM α) (next : α → SailM β)
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

theorem load_preserves_pure (value : α) : PreservesStackPointer (pure value : SailM α) := by
  intro state
  rfl

theorem load_preserves_throw (error : Sail.Error exception) :
    PreservesStackPointer (throw error : SailM α) := by
  intro state
  rfl

theorem load_preserves_map (action : SailM α) (function : α → β)
    (frame : PreservesStackPointer action) : PreservesStackPointer (function <$> action) :=
  load_preserves_bind action (fun value => pure (function value)) frame (fun _ =>
    load_preserves_pure _)

theorem load_preserves_ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : PreservesStackPointer whenTrue) (falseFrame : PreservesStackPointer whenFalse) :
    PreservesStackPointer (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

theorem load_preserves_readReg (register : Register) :
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

theorem load_preserves_rX_bits (source : regidx) :
    PreservesStackPointer (rX_bits source) := by
  intro state
  cases hRead : (rX_bits source).run state with
  | ok value after =>
    have projection := rX_bits_state_projection state source
    simpa [hRead] using congrArg (fun state : State => state.regs.get? x2) projection
  | error error after =>
    have projection := rX_bits_state_projection state source
    simpa [hRead] using congrArg (fun state : State => state.regs.get? x2) projection

theorem load_preserves_assert (condition : Bool) (message : String) :
    PreservesStackPointer (Sail.assert condition message) := by
  unfold Sail.assert PreSail.assert
  split <;> exact load_preserves_pure () <;> exact load_preserves_throw _

theorem load_preserves_writeReg (written : Register) (value : RegisterType written)
    (notStack : x2 ≠ written) : PreservesStackPointer (writeReg written value) := by
  intro state
  rw [writeReg_run]
  exact writeReg_read_unchanged state written x2 value notStack

def LoadPreservesExcept {ε α : Type} (action : ExceptT ε SailM α) : Prop :=
  PreservesStackPointer (ExceptT.run action)

theorem load_preserves_except_pure {ε α : Type} (value : α) :
    LoadPreservesExcept (pure value : ExceptT ε SailM α) := by
  intro state
  rfl

theorem load_preserves_except_throw {ε α : Type} (error : ε) :
    LoadPreservesExcept (Sail.SailME.throw error : SailME ε α) := by
  change PreservesStackPointer (ExceptT.run (Sail.SailME.throw error : SailME ε α))
  unfold Sail.SailME.throw PreSail.PreSailME.throw
  exact load_preserves_pure _

theorem load_preserves_except_ite {ε α : Type} (condition : Bool)
    (whenTrue whenFalse : SailME ε α) (trueFrame : LoadPreservesExcept whenTrue)
    (falseFrame : LoadPreservesExcept whenFalse) :
    LoadPreservesExcept (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

theorem load_preserves_except_lift {ε α : Type} (action : SailM α)
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

theorem load_preserves_except_lift_bind {ε α β : Type} (action : SailM α)
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

theorem load_preserves_except_bind {ε α β : Type} (action : ExceptT ε SailM α)
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

theorem load_preserves_except_ite_bind {ε α β : Type} (condition : Bool)
    (whenTrue whenFalse : SailME ε α) (next : α → SailME ε β)
    (trueFrame : LoadPreservesExcept whenTrue) (falseFrame : LoadPreservesExcept whenFalse)
    (nextFrame : ∀ value, LoadPreservesExcept (next value)) :
    LoadPreservesExcept (do
      let value ← if condition then whenTrue else whenFalse
      next value) := by
  apply load_preserves_except_ite
  · exact load_preserves_except_bind whenTrue next trueFrame nextFrame
  · exact load_preserves_except_bind whenFalse next falseFrame nextFrame

theorem load_preserves_sailME_run {α : Type} (action : SailME α α)
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

theorem load_preserves_untilFuelM {ε α : Type} (fuel : Nat)
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

theorem load_preserves_privLevel_bits_forwards (arg : BitVec 2 × BitVec 1) :
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

theorem load_preserves_effectivePrivilege (access : MemoryAccessType mem_payload)
    (mstatusBits : BitVec 64) (privilege : Privilege) :
    PreservesStackPointer (effectivePrivilege access mstatusBits privilege) := by
  unfold effectivePrivilege
  apply load_preserves_ite
  · exact load_preserves_privLevel_bits_forwards _
  · exact load_preserves_pure _

theorem load_preserves_is_pmm_applicable (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesStackPointer (is_pmm_applicable access privilege) := by
  unfold is_pmm_applicable
  apply load_preserves_bind (readReg mstatus)
  · exact load_preserves_readReg mstatus
  · intro _
    exact load_preserves_pure _

theorem load_preserves_read_senvcfg : PreservesStackPointer (read_senvcfg ()) := by
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

theorem load_preserves_currentlyEnabled_Zicsr :
    PreservesStackPointer (currentlyEnabled extension.Ext_Zicsr) :=
  currentlyEnabled_zicsr_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_S :
    PreservesStackPointer (currentlyEnabled extension.Ext_S) :=
  currentlyEnabled_s_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_Sstc :
    PreservesStackPointer (currentlyEnabled extension.Ext_Sstc) :=
  currentlyEnabled_sstc_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_Svade :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svade) :=
  currentlyEnabled_svade_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_Svadu :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svadu) :=
  currentlyEnabled_svadu_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_Sv39 :
    PreservesStackPointer (currentlyEnabled extension.Ext_Sv39) :=
  currentlyEnabled_sv39_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_Svnapot :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svnapot) :=
  currentlyEnabled_svnapot_preserves_stack_pointer

theorem load_preserves_currentlyEnabled_Svrsw60t59b :
    PreservesStackPointer (currentlyEnabled extension.Ext_Svrsw60t59b) :=
  currentlyEnabled_svrsw60t59b_preserves_stack_pointer

theorem load_preserves_internal_error (file : String) (line : Int) (message : String) :
    PreservesStackPointer (internal_error file line message : SailM α) := by
  unfold internal_error Sail.sailThrow PreSail.sailThrow
  exact load_preserves_throw _

theorem load_preserves_is_shadow_stack_access (access : MemoryAccessType mem_payload) :
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

theorem load_preserves_get_pmm (privilege : Privilege) :
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

theorem load_preserves_get_pmlen (access : MemoryAccessType mem_payload)
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

theorem load_preserves_architecture_bits_backwards (arg : BitVec 2) :
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

theorem load_preserves_architecture_supervisor :
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

theorem load_preserves_satp_mode_result (arch : Architecture) (bits : BitVec 4) :
    PreservesStackPointer (match satpMode_of_bits arch bits with
      | some mode => pure mode
      | none => internal_error "sys/vmem.sail" 263 "invalid translation mode in satp") := by
  cases hMode : satpMode_of_bits arch bits
  · exact load_preserves_internal_error _ _ _
  · exact load_preserves_pure _

theorem load_preserves_translationMode (privilege : Privilege) :
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

theorem load_preserves_satp_mode_width_forwards (mode : SATPMode) :
    PreservesStackPointer (satp_mode_width_forwards mode) := by
  cases mode <;> unfold satp_mode_width_forwards
  all_goals first
    | exact load_preserves_pure _
    | exact load_preserves_bind (Sail.assert false "Pattern match failure at unknown location")
        (fun _ => throw Sail.Error.Exit) (load_preserves_assert _ _)
        (fun _ => load_preserves_throw _)

theorem load_preserves_get_satp (svWidth : Nat) :
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

theorem load_preserves_translationException_load_data (failure : PTW_Error) :
    PreservesStackPointer (translationException (.Load mem_payload.Data) failure) := by
  unfold translationException
  cases failure <;> exact load_preserves_pure _

theorem load_preserves_transform_effective_address (address : virtaddr)
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

theorem load_preserves_ext_data_get_addr (source : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesStackPointer (ext_data_get_addr source offset access width) := by
  simp only [ext_data_get_addr]
  apply load_preserves_bind (rX_bits source)
  · exact load_preserves_rX_bits source
  · intro base
    exact load_preserves_pure _

theorem load_preserves_get_transformed_data_addr (source : regidx) (offset : BitVec 64)
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

theorem load_preserves_read_then_pure (register : Register)
    (next : RegisterType register → α) :
    PreservesStackPointer (do
      let value ← readReg register
      pure (next value)) := by
  apply load_preserves_bind (readReg register)
  · exact load_preserves_readReg register
  · intro _
    exact load_preserves_pure _

theorem load_preserves_memory_exception (address : virtaddr) (exception : ExceptionType) :
    PreservesStackPointer (memory_exception address exception) := by
  unfold memory_exception trap
  apply load_preserves_bind (readReg cur_privilege)
  · exact load_preserves_readReg cur_privilege
  · intro _
    apply load_preserves_bind (readReg PC)
    · exact load_preserves_readReg PC
    · intro _
      exact load_preserves_pure _

theorem load_preserves_plat_misaligned_exception (access : MemoryAccessType mem_payload)
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

end BinaryFv.RiscV
