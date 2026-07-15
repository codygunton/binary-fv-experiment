import BinaryFv.RISCV.EnabledFrame
import BinaryFv.RISCV.HtifFrame
import BinaryFv.RISCV.TranslationFrameAudit

namespace BinaryFv.RISCV

open PreSail
open LeanRV64DExecutable.Functions
open Register

private def PreservesX2 (action : SailM α) : Prop :=
  ∀ state,
    (match action state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2

private theorem PreservesX2.bind (first : SailM α) (next : α → SailM β)
    (firstFrame : PreservesX2 first) (nextFrame : ∀ value, PreservesX2 (next value)) :
    PreservesX2 (first >>= next) := by
  unfold PreservesX2 at *
  intro state
  have evalBind : (first >>= next) state =
      match first state with
      | .ok value afterFirst => next value afterFirst
      | .error error afterFirst => .error error afterFirst := by
    simp only [EStateM.instMonad, EStateM.bind]
    cases hFirst : first state <;> rfl
  cases hFirst : first state with
  | error error afterFirst =>
    have hAfterFirst : afterFirst.regs.get? x2 = state.regs.get? x2 := by
      simpa only [hFirst] using firstFrame state
    rw [evalBind]
    simp only [hFirst]
    exact hAfterFirst
  | ok value afterFirst =>
    have hAfterFirst : afterFirst.regs.get? x2 = state.regs.get? x2 := by
      simpa only [hFirst] using firstFrame state
    cases hNext : (next value) afterFirst with
    | error error afterNext =>
      have hAfterNext : afterNext.regs.get? x2 = afterFirst.regs.get? x2 := by
        simpa only [hNext] using nextFrame value afterFirst
      rw [evalBind]
      simp only [hFirst, hNext]
      exact hAfterNext.trans hAfterFirst
    | ok result afterNext =>
      have hAfterNext : afterNext.regs.get? x2 = afterFirst.regs.get? x2 := by
        simpa only [hNext] using nextFrame value afterFirst
      rw [evalBind]
      simp only [hFirst, hNext]
      exact hAfterNext.trans hAfterFirst

private theorem PreservesX2.pure (value : α) : PreservesX2 (pure value : SailM α) := by
  intro state
  rfl

private theorem PreservesX2.throw (error : Sail.Error exception) :
    PreservesX2 (EStateM.throw error : SailM α) := by
  intro state
  rfl

private theorem PreservesX2.writeReg (written : Register)
    (value : RegisterType written) (doesNotWriteX2 : x2 ≠ written) :
    PreservesX2 (writeReg written value) := by
  intro before
  change (match (PreSail.writeReg written value : SailM PUnit).run before with
    | .ok _ after => after.regs.get? x2
    | .error _ after => after.regs.get? x2) = before.regs.get? x2
  rw [writeReg_run]
  exact writeReg_read_unchanged before written x2 value doesNotWriteX2

private theorem PreservesX2.map (action : SailM α) (function : α → β)
    (actionFrame : PreservesX2 action) : PreservesX2 (function <$> action) := by
  exact PreservesX2.bind action (fun value => (EStateM.pure (function value) : SailM β)) actionFrame
    (fun _ => PreservesX2.pure _)

private theorem PreservesX2.ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : PreservesX2 whenTrue) (falseFrame : PreservesX2 whenFalse) :
    PreservesX2 (if condition then whenTrue else whenFalse) := by
  cases condition
  · exact falseFrame
  · exact trueFrame

private theorem preservesX2_assert (condition : Bool) (message : String) :
    PreservesX2 (PreSail.assert condition message : SailM Unit) := by
  unfold PreSail.assert
  exact PreservesX2.ite condition (EStateM.pure ())
    (EStateM.throw (Sail.Error.Assertion message)) (PreservesX2.pure _)
    (PreservesX2.throw _)

private theorem preservesX2_privLevel_bits_forwards (arg : BitVec 2 × BitVec 1) :
    PreservesX2 (privLevel_bits_forwards arg) := by
  have levelCases : arg.1.toNat = 0 ∨ arg.1.toNat = 1 ∨ arg.1.toNat = 2 ∨
      arg.1.toNat = 3 := by
    omega
  have virtualCases : arg.2.toNat = 0 ∨ arg.2.toNat = 1 := by
    omega
  rcases levelCases with hLevel | hLevel | hLevel | hLevel <;>
    rcases virtualCases with hVirtual | hVirtual
  all_goals
    have levelValue : arg.1 = BitVec.ofNat 2 arg.1.toNat := by
      rw [← BitVec.toNat_inj]
      rw [BitVec.toNat_ofNat]
      omega
    have virtualValue : arg.2 = BitVec.ofNat 1 arg.2.toNat := by
      rw [← BitVec.toNat_inj]
      rw [BitVec.toNat_ofNat]
      omega
    have argValue : arg = (BitVec.ofNat 2 arg.1.toNat, BitVec.ofNat 1 arg.2.toNat) :=
      Prod.ext levelValue virtualValue
    rw [argValue]
    simp [privLevel_bits_forwards, hLevel, hVirtual,
        internal_error, Sail.sailThrow, PreSail.sailThrow, EStateM.instMonad]
    all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

private abbrev PreservesX2E (action : SailME ε α) : Prop :=
  PreservesX2 (ExceptT.run action)

private theorem preservesStackPointer_of_preservesX2 (frame : PreservesX2 action) :
    PreservesStackPointer action := by
  simpa only [PreservesX2, PreservesStackPointer] using frame

private theorem preservesX2_of_preservesStackPointer (frame : PreservesStackPointer action) :
    PreservesX2 action := by
  simpa only [PreservesX2, PreservesStackPointer] using frame

private theorem PreservesX2E.lift (action : SailM α) (actionFrame : PreservesX2 action) :
    PreservesX2E (liftM action : SailME ε α) := by
  change PreservesX2 (ExceptT.run (liftM action : SailME ε α))
  simpa only [ExceptT.run, ExceptT.mk, MonadLift.monadLift] using
    PreservesX2.map action (fun value =>
      (Except.ok value : Except (Sail.Error exception ⊕ ε) α)) actionFrame

private theorem PreservesX2E.bind (first : SailME ε α) (next : α → SailME ε β)
    (firstFrame : PreservesX2E first) (nextFrame : ∀ value, PreservesX2E (next value)) :
    PreservesX2E (first >>= next) := by
  change PreservesX2 (ExceptT.run first >>= ExceptT.bindCont next)
  apply PreservesX2.bind
  · exact firstFrame
  · intro result
    cases result with
    | error error => exact PreservesX2.pure _
    | ok value => exact nextFrame value

private theorem PreservesX2E.pure (value : α) : PreservesX2E (pure value : SailME ε α) := by
  change PreservesX2 (ExceptT.run (ExceptT.pure value : SailME ε α))
  exact PreservesX2.pure _

private theorem PreservesX2E.throw (error : ε) :
    PreservesX2E (Sail.SailME.throw error : SailME ε α) := by
  change PreservesX2 (ExceptT.run (Sail.SailME.throw error : SailME ε α))
  unfold Sail.SailME.throw PreSail.PreSailME.throw
  exact PreservesX2.pure _

private theorem PreservesX2E.throwBind (error : ε) (next : α → SailME ε β) :
    PreservesX2E (Sail.SailME.throw error >>= next) := by
  change PreservesX2 (ExceptT.run (Sail.SailME.throw error >>= next))
  simp [Sail.SailME.throw, PreSail.PreSailME.throw, ExceptT.run]
  exact PreservesX2.pure _

private theorem PreservesX2E.ite (condition : Bool) (whenTrue whenFalse : SailME ε α)
    (trueFrame : PreservesX2E whenTrue) (falseFrame : PreservesX2E whenFalse) :
    PreservesX2E (if condition then whenTrue else whenFalse) := by
  cases condition
  · exact falseFrame
  · exact trueFrame

private theorem PreservesX2E.iteBind (condition : Bool) (whenTrue whenFalse : SailME ε α)
    (next : α → SailME ε β) (trueFrame : PreservesX2E whenTrue)
    (falseFrame : PreservesX2E whenFalse) (nextFrame : ∀ value, PreservesX2E (next value)) :
    PreservesX2E (do
      let value ← if condition then whenTrue else whenFalse
      next value) := by
  apply PreservesX2E.ite
  · exact PreservesX2E.bind whenTrue next trueFrame nextFrame
  · exact PreservesX2E.bind whenFalse next falseFrame nextFrame

private theorem preservesX2E_untilFuelM (fuel : Nat) (condition : α → SailME ε Bool)
    (initial : α) (body : α → SailME ε α)
    (conditionFrame : ∀ value, PreservesX2E (condition value))
    (bodyFrame : ∀ value, PreservesX2E (body value)) :
    PreservesX2E (untilFuelM fuel condition initial body) := by
  induction fuel generalizing initial with
  | zero =>
    simp [untilFuelM]
    exact PreservesX2E.pure _
  | succ fuel induction =>
    simp [untilFuelM]
    apply PreservesX2E.bind
    · exact bodyFrame initial
    · intro afterBody
      apply PreservesX2E.bind
      · exact conditionFrame afterBody
      · intro done
        apply PreservesX2E.ite
        · exact PreservesX2E.pure _
        · exact induction afterBody

private theorem preservesX2_sailMERun (action : SailME α α) (actionFrame : PreservesX2E action) :
    PreservesX2 (Sail.SailME.run action) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  apply PreservesX2.bind
  · exact actionFrame
  · intro result
    cases result with
    | error error =>
      cases error with
      | inl error => exact PreservesX2.throw error
      | inr error => exact PreservesX2.pure error
    | ok value => exact PreservesX2.pure value

private theorem preservesX2_readReg (register : Register) : PreservesX2 (readReg register) := by
  intro state
  cases hRead : state.regs.get? register <;>
    simp [PreSail.readReg, EStateM.bind, EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, MonadState.get,
      MonadStateOf.get, getThe, hRead] <;> rfl

private theorem preservesX2_writeByte (address : Nat) (value : BitVec 8) :
    PreservesX2 (PreSail.writeByte address value : SailM PUnit) := by
  intro state
  rfl

private theorem preservesX2_list_forM (xs : List α) (action : α → SailM PUnit)
    (actionFrame : ∀ value, PreservesX2 (action value)) : PreservesX2 (xs.forM action) := by
  induction xs with
  | nil => exact PreservesX2.pure _
  | cons value remaining induction =>
    simp only [List.forM]
    exact PreservesX2.bind (action value) (fun _ => remaining.forM action)
      (actionFrame value) (fun _ => induction)

private theorem preservesX2_writeBytes (address : Nat) (value : BitVec (8 * width)) :
    PreservesX2 (PreSail.writeBytes address value : SailM Bool) := by
  unfold PreSail.writeBytes
  apply PreservesX2.bind
  · apply preservesX2_list_forM
    intro byte
    exact preservesX2_writeByte byte.1 byte.2
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_sail_mem_write [Sail.ConcurrencyInterfaceV1.Arch]
    (request : Sail.ConcurrencyInterfaceV1.Mem_write_request n vasize (BitVec pa_size) ts Arch) :
    PreservesX2 (PreSail.ConcurrencyInterfaceV1.sail_mem_write request) := by
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_write
  cases hValue : request.value with
  | none =>
    simp only
    exact PreservesX2.pure _
  | some value =>
    simp only
    apply PreservesX2.bind
    · exact preservesX2_writeBytes request.pa.toNat value
    · intro _
      exact PreservesX2.pure _

private theorem preservesX2_write_ram (kind : write_kind) (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (metadata : Unit) :
    PreservesX2 (LeanRV64DExecutable.Functions.write_ram kind address width data metadata) := by
  unfold LeanRV64DExecutable.Functions.write_ram
  cases kind
  · apply PreservesX2.bind
    · apply PreservesX2.bind
      · exact PreservesX2.pure _
      · intro _
        exact PreservesX2.pure _
    · intro request
      apply PreservesX2.bind
      · exact preservesX2_sail_mem_write request
      · intro result
        cases result <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · apply PreservesX2.bind
      · exact PreservesX2.throw _
      · intro _
        exact PreservesX2.pure _
    · intro request
      apply PreservesX2.bind
      · exact preservesX2_sail_mem_write request
      · intro result
        cases result <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · apply PreservesX2.bind
      · exact PreservesX2.throw _
      · intro _
        exact PreservesX2.pure _
    · intro request
      apply PreservesX2.bind
      · exact preservesX2_sail_mem_write request
      · intro result
        cases result <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · apply PreservesX2.bind
      · exact PreservesX2.pure _
      · intro _
        exact PreservesX2.pure _
    · intro request
      apply PreservesX2.bind
      · exact preservesX2_sail_mem_write request
      · intro result
        cases result <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · apply PreservesX2.bind
      · exact PreservesX2.pure _
      · intro _
        exact PreservesX2.pure _
    · intro request
      apply PreservesX2.bind
      · exact preservesX2_sail_mem_write request
      · intro result
        cases result <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · apply PreservesX2.bind
      · exact PreservesX2.pure _
      · intro _
        exact PreservesX2.pure _
    · intro request
      apply PreservesX2.bind
      · exact preservesX2_sail_mem_write request
      · intro result
        cases result <;> exact PreservesX2.pure _

private theorem preservesX2_pmaCheck_store (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) :
    PreservesX2 (pmaCheck address width (MemoryAccessType.Store mem_payload.Data)
      pbmt false) := by
  unfold pmaCheck
  apply PreservesX2.bind
  · exact preservesX2_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      simp only [accessFaultFromAccessType]
      exact PreservesX2.pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply PreservesX2.bind
      · apply PreservesX2.ite
        · exact PreservesX2.pure _
        · unfold pma_misaligned_exception
          exact PreservesX2.pure _
      · intro exception
        cases exception with
        | none =>
          apply PreservesX2.bind
          · apply PreservesX2.bind
            · exact preservesX2_assert _ _
            · intro _
              exact PreservesX2.pure _
          · intro canAccess
            apply PreservesX2.ite
            · exact PreservesX2.pure _
            · apply PreservesX2.bind
              · unfold accessFaultFromAccessType
                exact PreservesX2.pure _
              · intro _
                exact PreservesX2.pure _
        | some exception =>
          cases exception
          · apply PreservesX2.bind
            · unfold accessFaultFromAccessType
              exact PreservesX2.pure _
            · intro _
              exact PreservesX2.pure _
          · apply PreservesX2.bind
            · unfold alignmentFaultFromAccessType
              exact PreservesX2.pure _
            · intro _
              exact PreservesX2.pure _

private theorem preservesX2_pmpReadAddrReg (index : Nat) :
    PreservesX2 (pmpReadAddrReg index) := by
  unfold pmpReadAddrReg
  apply PreservesX2.bind
  · exact preservesX2_readReg pmpcfg_n
  · intro config
    apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro matchType
      apply PreservesX2.bind
      · exact preservesX2_readReg pmpaddr_n
      · intro addresses
        apply PreservesX2.bind
        · exact PreservesX2.pure _
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
            all_goals split <;> exact PreservesX2.pure _

private theorem preservesX2_pmpMatchAddr (address : physaddr) (width : BitVec 64)
    (config : BitVec 8) (current previous : BitVec 64) :
    PreservesX2 (pmpMatchAddr address width config current previous) := by
  unfold pmpMatchAddr
  cases hMatch : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A config)
  · exact PreservesX2.pure _
  · apply PreservesX2.ite <;> exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_assert _ _
    · intro _
      exact PreservesX2.pure _
  · exact PreservesX2.pure _

private theorem preservesX2_pmpCheckRWX_store (config : BitVec 8) :
    PreservesX2 (pmpCheckRWX config (MemoryAccessType.Store mem_payload.Data)) := by
  unfold pmpCheckRWX
  exact PreservesX2.pure _

private def pmpLoopRange : IntRange := {
  start := 0
  stop := sys_pmp_count - 1
  step := 1
  step_pos := by omega
}

private def pmpLoopAfterPrev (address : physaddr) (width : xlenbits)
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

private def pmpLoopBody (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (index : Int) (_ : index ∈ pmpLoopRange) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let () := loopVars
  if ((index >b 0) : Bool) then do
    let previousPmpaddr ← liftM (pmpReadAddrReg (index - 1).toNat)
    pmpLoopAfterPrev address width access privilege index previousPmpaddr loopVars
  else pmpLoopAfterPrev address width access privilege index zeros loopVars

private def pmpCheckLoop (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    SailM (Option ExceptionType) := Sail.SailME.run do
  let loopVars ← IntRange.forIn' pmpLoopRange ()
    (pmpLoopBody address (to_bits width) access privilege)
  pure loopVars
  if ((privilege == .Machine) : Bool) then pure none
  else pure (some (← liftM (accessFaultFromAccessType access)))

private theorem pmpCheck_loop_eq (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) :
    pmpCheck address width access privilege = pmpCheckLoop address width access privilege := by
  unfold pmpCheck pmpCheckLoop pmpLoopRange pmpLoopBody pmpLoopAfterPrev
  simp only [sys_pmp_count]
  have countNotZero : ((16 : Int) == 0) = false := rfl
  simp only [countNotZero, Bool.false_eq_true, ↓reduceIte]
  rw [forIn_eq_forIn']
  rfl

private theorem preservesX2_accessFault_store :
    PreservesX2 (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data)) := by
  unfold accessFaultFromAccessType
  exact PreservesX2.pure _

private theorem preservesX2E_pmpLoopAfterPrev_store (address : physaddr) (width : xlenbits)
    (privilege : Privilege) (index : Int) (previousPmpaddr : BitVec 64) (loopVars : Unit) :
    PreservesX2E
      (pmpLoopAfterPrev address width (MemoryAccessType.Store mem_payload.Data) privilege index
        previousPmpaddr loopVars) := by
  unfold pmpLoopAfterPrev
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (Sail.readReg pmpcfg_n) (preservesX2_readReg pmpcfg_n)
  · intro rawConfig
    apply PreservesX2E.bind
    · exact PreservesX2E.pure _
    · intro config
      apply PreservesX2E.bind
      · exact PreservesX2E.lift (pmpReadAddrReg index.toNat)
          (preservesX2_pmpReadAddrReg index.toNat)
      · intro currentPmpaddr
        apply PreservesX2E.bind
        · exact PreservesX2E.lift
            (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
            (preservesX2_pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
        · intro matched
          cases matched with
          | PMP_NoMatch => exact PreservesX2E.pure _
          | PMP_PartialMatch =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift
                  (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data))
                  preservesX2_accessFault_store
              · intro fault
                exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault
          | PMP_Match =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift
                  (pmpCheckRWX config (MemoryAccessType.Store mem_payload.Data))
                  (preservesX2_pmpCheckRWX_store config)
              · intro permitted
                apply PreservesX2E.ite
                · exact PreservesX2E.pure none
                · apply PreservesX2E.bind
                  · exact PreservesX2E.lift
                      (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data))
                      preservesX2_accessFault_store
                  · intro fault
                    exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault

private theorem preservesX2E_pmpLoopBody_store (address : physaddr) (width : xlenbits)
    (privilege : Privilege) (index : Int) (inRange : index ∈ pmpLoopRange) (loopVars : Unit) :
    PreservesX2E
      (pmpLoopBody address width (MemoryAccessType.Store mem_payload.Data) privilege index
        inRange loopVars) := by
  unfold pmpLoopBody
  apply PreservesX2E.ite
  · apply PreservesX2E.bind
    · exact PreservesX2E.lift (pmpReadAddrReg (index - 1).toNat)
        (preservesX2_pmpReadAddrReg (index - 1).toNat)
    · intro previousPmpaddr
      exact preservesX2E_pmpLoopAfterPrev_store address width privilege index previousPmpaddr
        loopVars
  · exact preservesX2E_pmpLoopAfterPrev_store address width privilege index zeros loopVars

private theorem preservesX2E_pmpLoopInvariant
    (body : (index : Int) → index ∈ pmpLoopRange → Unit →
      SailME (Option ExceptionType) (ForInStep Unit))
    (bodyFrame : ∀ (index : Int) (inRange : index ∈ pmpLoopRange),
      PreservesX2E (body index inRange ()))
    (index : Int) (stepDiv : (index - pmpLoopRange.start) % pmpLoopRange.step = 0) :
    PreservesX2E (IntRange.forIn'.loop pmpLoopRange body () index stepDiv) := by
  unfold IntRange.forIn'.loop
  by_cases inRange : index ∈ pmpLoopRange
  · simp only [dif_pos inRange]
    apply PreservesX2E.bind
    · exact bodyFrame index inRange
    · intro result
      cases result with
      | done loopVars => exact PreservesX2E.pure _
      | yield loopVars =>
        exact preservesX2E_pmpLoopInvariant body bodyFrame
          (index + pmpLoopRange.step) (by
            rw [Int.add_comm, Int.add_sub_assoc]
            simp_all)
  · simp only [dif_neg inRange]
    exact PreservesX2E.pure _
termination_by (16 - index).toNat
decreasing_by
  change (16 - (index + 1)).toNat < (16 - index).toNat
  have bounds : (0 : Int) ≤ index ∧ index ≤ 15 := by
    simpa [pmpLoopRange, sys_pmp_count, IntRange.instMemIntRange] using inRange
  omega

private theorem preservesX2E_pmpLoop_store (address : physaddr) (width : xlenbits)
    (privilege : Privilege) :
    PreservesX2E (IntRange.forIn' pmpLoopRange ()
      (pmpLoopBody address width (MemoryAccessType.Store mem_payload.Data) privilege)) := by
  unfold IntRange.forIn'
  exact preservesX2E_pmpLoopInvariant
    (pmpLoopBody address width (MemoryAccessType.Store mem_payload.Data) privilege)
    (fun index inRange =>
      preservesX2E_pmpLoopBody_store address width privilege index inRange ())
    pmpLoopRange.start (by simp)

private theorem preservesX2_pmpCheck_store (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesX2 (pmpCheck address width (MemoryAccessType.Store mem_payload.Data) privilege) := by
  rw [pmpCheck_loop_eq]
  unfold pmpCheckLoop
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · exact preservesX2E_pmpLoop_store address (to_bits width) privilege
  · intro loopVars
    apply PreservesX2E.bind
    · exact PreservesX2E.pure loopVars
    · intro _
      apply PreservesX2E.ite
      · exact PreservesX2E.pure _
      · apply PreservesX2E.bind
        · exact PreservesX2E.lift
            (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.Data))
            preservesX2_accessFault_store
        · intro fault
          exact PreservesX2E.pure (some fault)

private theorem preservesX2_alignmentOrAccessFaultPriority (exception : ExceptionType) :
    PreservesX2 (alignmentOrAccessFaultPriority exception) := by
  cases exception <;>
    simp [alignmentOrAccessFaultPriority, internal_error, Sail.sailThrow, PreSail.sailThrow,
      EStateM.instMonad]
  all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

private theorem preservesX2_highestPriorityAlignmentOrAccessFault (left right : ExceptionType) :
    PreservesX2 (highestPriorityAlignmentOrAccessFault left right) := by
  unfold highestPriorityAlignmentOrAccessFault
  apply PreservesX2.bind
  · exact preservesX2_alignmentOrAccessFaultPriority left
  · intro leftPriority
    apply PreservesX2.bind
    · exact preservesX2_alignmentOrAccessFaultPriority right
    · intro rightPriority
      apply PreservesX2.ite <;> exact PreservesX2.pure _

private theorem preservesX2_phys_access_check_store (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
      PreservesX2
        (phys_access_check (MemoryAccessType.Store mem_payload.Data) pbmt privilege address
          width false) := by
  unfold phys_access_check
  apply PreservesX2.bind
  · exact preservesX2_pmpCheck_store address width privilege
  · intro pmpError
    apply PreservesX2.bind
    · exact preservesX2_pmaCheck_store address width pbmt
    · intro pmaError
      cases pmpError <;> cases pmaError
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · apply PreservesX2.bind
        · exact preservesX2_highestPriorityAlignmentOrAccessFault _ _
        · intro _
          exact PreservesX2.pure _

private theorem preservesX2_mem_write_ea (address : physaddr) (width : Nat) :
    PreservesX2 (mem_write_ea address width false false false) := by
  intro state
  simp [mem_write_ea, write_kind_of_flags, write_ram_ea, EStateM.bind,
    EStateM.pure, EStateM.instMonad]

private theorem preservesX2_rX_bits (source : regidx) : PreservesX2 (rX_bits source) := by
  intro state
  cases hRead : (rX_bits source).run state with
  | error error afterRead =>
    change rX_bits source state = .error error afterRead at hRead
    have hState := rX_bits_state_projection state source
    change (match rX_bits source state with
      | .ok _ state' => state'
      | .error _ state' => state') = state at hState
    have afterReadEq : afterRead = state := by
      simpa only [hRead] using hState
    subst afterRead
    simp only [hRead]
  | ok value afterRead =>
    change rX_bits source state = .ok value afterRead at hRead
    have hState := rX_bits_state_projection state source
    change (match rX_bits source state with
      | .ok _ state' => state'
      | .error _ state' => state') = state at hState
    have afterReadEq : afterRead = state := by
      simpa only [hRead] using hState
    subst afterRead
    simp only [hRead]

private theorem preservesX2_currentlyEnabled_Zicsr :
    PreservesX2 (currentlyEnabled extension.Ext_Zicsr) := by
  simp only [currentlyEnabled.eq_61]
  exact PreservesX2.pure _

private theorem preservesX2_currentlyEnabled_S :
    PreservesX2 (currentlyEnabled extension.Ext_S) := by
  rw [currentlyEnabled.eq_20]
  apply PreservesX2.bind
  · exact preservesX2_readReg misa
  · intro misaBits
    apply PreservesX2.bind
    · exact preservesX2_currentlyEnabled_Zicsr
    · intro zicsr
      exact PreservesX2.pure _

private theorem preservesX2_currentlyEnabled_Sstc :
    PreservesX2 (currentlyEnabled extension.Ext_Sstc) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_sstc_preserves_stack_pointer

private theorem preservesX2_effectivePrivilege (access : MemoryAccessType mem_payload)
    (mstatus : BitVec 64) (privilege : Privilege) :
    PreservesX2 (effectivePrivilege access mstatus privilege) := by
  unfold effectivePrivilege
  exact PreservesX2.ite _ (privLevel_bits_forwards (_get_Mstatus_MPP mstatus, 0#1))
    (EStateM.pure privilege) (preservesX2_privLevel_bits_forwards _)
    (PreservesX2.pure _)

private theorem preservesX2_is_pmm_applicable (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesX2 (is_pmm_applicable access privilege) := by
  unfold is_pmm_applicable
  apply PreservesX2.bind
  · exact preservesX2_readReg mstatus
  · intro mstatusBits
    exact PreservesX2.pure _

private theorem preservesX2_read_senvcfg : PreservesX2 (read_senvcfg ()) := by
  unfold read_senvcfg
  apply PreservesX2.bind
  · exact preservesX2_readReg senvcfg
  · intro senvcfgFirst
    apply PreservesX2.bind
    · exact preservesX2_readReg menvcfg
    · intro menvcfgBits
      apply PreservesX2.bind
      · exact preservesX2_readReg senvcfg
      · intro senvcfgSecond
        exact PreservesX2.pure _

private theorem preservesX2_internal_error (file : String) (line : Int) (message : String) :
    PreservesX2 (internal_error file line message : SailM α) := by
  unfold internal_error Sail.sailThrow PreSail.sailThrow
  exact PreservesX2.throw _

private theorem preservesX2_get_pmm (privilege : Privilege) : PreservesX2 (get_pmm privilege) := by
  cases privilege <;> unfold get_pmm
  · apply PreservesX2.bind
    · exact preservesX2_currentlyEnabled_S
    · intro enabled
      apply PreservesX2.ite
      · exact PreservesX2.bind (read_senvcfg ())
          (fun senvcfgBits => EStateM.pure (pmm_mode_backwards (_get_SEnvcfg_PMM senvcfgBits)))
          preservesX2_read_senvcfg (fun _ => PreservesX2.pure _)
      · exact PreservesX2.bind (readReg menvcfg)
          (fun menvcfgBits => EStateM.pure (pmm_mode_backwards (_get_MEnvcfg_PMM menvcfgBits)))
          (preservesX2_readReg menvcfg) (fun _ => PreservesX2.pure _)
  · exact preservesX2_internal_error _ _ _
  · apply PreservesX2.bind
    · exact preservesX2_readReg menvcfg
    · intro menvcfgBits
      exact PreservesX2.pure _
  · exact preservesX2_internal_error _ _ _
  · apply PreservesX2.bind
    · exact preservesX2_readReg mseccfg
    · intro mseccfgBits
      exact PreservesX2.pure _

private theorem preservesX2_pmm_length (pmm : PointerMaskingMode) :
    PreservesX2 (match pmm with
    | .PMM_Disabled => EStateM.pure 0
    | .PMM_PMLEN_7 => EStateM.pure 7
    | .PMM_PMLEN_16 => EStateM.pure 16
    | .PMM_Reserved =>
      (internal_error "extensions/pointer_masking/pm_utils.sail" 32
        "Invalid pointer masking mode" : SailM Unit) >>= fun (_ : Unit) => EStateM.pure 0) := by
  cases pmm
  · exact PreservesX2.pure _
  · exact PreservesX2.bind
      (internal_error "extensions/pointer_masking/pm_utils.sail" 32
        "Invalid pointer masking mode")
      (fun _ => EStateM.pure 0)
      (preservesX2_internal_error _ _ _) (fun _ => PreservesX2.pure _)
  · exact PreservesX2.pure _
  · exact PreservesX2.pure _

private theorem preservesX2_get_pmlen (access : MemoryAccessType mem_payload)
    (privilege : Privilege) : PreservesX2 (get_pmlen access privilege) := by
  unfold get_pmlen
  apply PreservesX2.bind
  · exact preservesX2_is_pmm_applicable access privilege
  · intro applicable
    apply PreservesX2.ite
    · apply PreservesX2.bind
      · exact preservesX2_get_pmm privilege
      · intro pmm
        cases pmm
        · exact PreservesX2.pure _
        · apply PreservesX2.bind
          · exact preservesX2_internal_error _ _ _
          · intro _
            exact PreservesX2.pure _
        · exact PreservesX2.pure _
        · exact PreservesX2.pure _
    · exact PreservesX2.pure _

private theorem preservesX2_architecture_bits_backwards (bits : BitVec 2) :
    PreservesX2 (architecture_bits_backwards bits) := by
  have bitCases : bits.toNat = 0 ∨ bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
    omega
  rcases bitCases with hBits | hBits | hBits | hBits
  all_goals
    have bitsValue : bits = BitVec.ofNat 2 bits.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [bitsValue]
    simp [architecture_bits_backwards, hBits, internal_error, Sail.sailThrow,
      PreSail.sailThrow, EStateM.instMonad]
    all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

private theorem preservesX2_architecture_supervisor :
    PreservesX2 (architecture Privilege.Supervisor) := by
  rw [architecture.eq_2]
  apply PreservesX2.bind
  · apply PreservesX2.bind
    · exact preservesX2_readReg mstatus
    · intro mstatusBits
      exact PreservesX2.pure _
  · intro satpArchitecture
    exact preservesX2_architecture_bits_backwards satpArchitecture

private theorem preservesX2_translation_mbits (architecture : Architecture) :
    PreservesX2 (match architecture with
    | .RV64 => do
      PreSail.assert (LeanRV64DExecutable.Functions.xlen ≥b 64) "sys/vmem.sail:254.25-254.26"
      let satpBits ← readReg satp
      EStateM.pure (_get_Satp64_Mode (Mk_Satp64 satpBits))
    | .RV32 => do
      let satpBits ← readReg satp
      EStateM.pure
        (0b000#3 ++ (_get_Satp32_Mode (Mk_Satp32 (Sail.BitVec.extractLsb satpBits 31 0))))
    | .RV128 => internal_error "sys/vmem.sail" 258 "RV128 not supported") := by
  cases architecture
  · apply PreservesX2.bind
    · exact preservesX2_readReg satp
    · intro satpBits
      exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_assert _ _
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_readReg satp
      · intro satpBits
        exact PreservesX2.pure _
  · exact preservesX2_internal_error _ _ _

private theorem preservesX2_satp_mode_result (architecture : Architecture) (bits : satp_mode) :
    PreservesX2 (match satpMode_of_bits architecture bits with
    | .some mode => EStateM.pure mode
    | none => internal_error "sys/vmem.sail" 263 "invalid translation mode in satp") := by
  cases hMode : satpMode_of_bits architecture bits
  · simpa [hMode] using
      (preservesX2_internal_error "sys/vmem.sail" 263 "invalid translation mode in satp")
  · simpa [hMode] using (PreservesX2.pure _)

private theorem preservesX2_translationMode (privilege : Privilege) :
    PreservesX2 (translationMode privilege) := by
  unfold translationMode
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_architecture_supervisor
    · intro architecture
      apply PreservesX2.bind
      · exact preservesX2_translation_mbits architecture
      · intro bits
        exact preservesX2_satp_mode_result architecture bits

private theorem preservesX2_transform_effective_address (address : virtaddr)
    (access : MemoryAccessType mem_payload) :
    PreservesX2 (transform_effective_address address access) := by
  unfold transform_effective_address
  apply PreservesX2.bind
  · exact preservesX2_readReg mstatus
  · intro mstatusBits
    apply PreservesX2.bind
    · exact preservesX2_readReg cur_privilege
    · intro privilege
      apply PreservesX2.bind
      · exact preservesX2_effectivePrivilege access mstatusBits privilege
      · intro effectivePrivilege
        apply PreservesX2.bind
        · exact preservesX2_get_pmlen access effectivePrivilege
        · intro pmlen
          apply PreservesX2.bind
          · exact preservesX2_translationMode effectivePrivilege
          · intro mode
            exact PreservesX2.ite (mode == SATPMode.Bare)
              (EStateM.pure (pm_transform_PA address pmlen.toNat))
              (EStateM.pure (pm_transform_VA address pmlen.toNat))
              (PreservesX2.pure _) (PreservesX2.pure _)

private theorem preservesX2_ext_data_get_addr (base : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesX2 (ext_data_get_addr base offset access width) := by
  unfold ext_data_get_addr
  apply PreservesX2.bind
  · exact preservesX2_rX_bits base
  · intro bits
    exact PreservesX2.pure _

private theorem preservesX2_get_transformed_data_addr (base : regidx) (offset : BitVec 64)
    (access : MemoryAccessType mem_payload) (width : Nat) :
    PreservesX2 (get_transformed_data_addr base offset access width) := by
  unfold get_transformed_data_addr
  apply PreservesX2.bind
  · exact preservesX2_ext_data_get_addr base offset access width
  · intro result
    cases result with
    | Ext_DataAddr_Error error => exact PreservesX2.pure _
    | Ext_DataAddr_OK address =>
      apply PreservesX2.bind
      · exact preservesX2_transform_effective_address address access
      · intro transformed
        exact PreservesX2.pure _

private theorem preservesX2_external_seip :
    PreservesX2 (do
      let supervisorEnabled ← currentlyEnabled extension.Ext_S
      if supervisorEnabled then readReg sig_seip else pure 0#1) := by
  apply PreservesX2.bind
  · exact preservesX2_currentlyEnabled_S
  · intro supervisorEnabled
    apply PreservesX2.ite
    · exact preservesX2_readReg sig_seip
    · exact PreservesX2.pure _

private theorem preservesX2_external_interrupts_pending :
    PreservesX2 (external_interrupts_pending ()) := by
  unfold external_interrupts_pending
  apply PreservesX2.bind
  · exact preservesX2_readReg sig_meip
  · intro meip
    apply PreservesX2.bind
    · exact preservesX2_external_seip
    · intro seip
      exact PreservesX2.pure _

private theorem preservesX2_read_mip (readType : XipReadType) :
    PreservesX2 (read_mip readType) := by
  cases readType
  · unfold read_mip
    apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro mipBits
      apply PreservesX2.bind
      · exact preservesX2_external_interrupts_pending
      · intro externalBits
        exact PreservesX2.pure _
  · unfold read_mip
    exact preservesX2_readReg mip

private theorem preservesX2_csr_name_map_backwards_mip :
    PreservesX2 (csr_name_map_backwards "mip") := by
  exact PreservesX2.pure _

private theorem preservesX2_csr_name_write_callback_mip (value : BitVec 64) :
    PreservesX2 (csr_name_write_callback "mip" value) := by
  unfold csr_name_write_callback
  apply PreservesX2.bind
  · exact preservesX2_csr_name_map_backwards_mip
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_clint_postlude (oldMip : BitVec 64) (mipWasWritten : Bool) :
    PreservesX2 (do
      pure ()
      let currentMip ← Sail.readReg mip
      if (oldMip != currentMip || mipWasWritten) then do
        let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
        csr_name_write_callback "mip" mipValue
      else pure ()) := by
  apply PreservesX2.bind
  · exact PreservesX2.pure _
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro currentMip
      apply PreservesX2.ite
      · apply PreservesX2.bind
        · exact preservesX2_read_mip XipReadType.IncludePlatformInterrupts
        · intro mipValue
          exact preservesX2_csr_name_write_callback_mip mipValue
      · exact PreservesX2.pure _

private theorem preservesX2_clint_dispatch (mipWasWritten : Bool) :
    PreservesX2 (clint_dispatch mipWasWritten) := by
  unfold clint_dispatch
  simp only [get_config_print_clint, Bool.false_eq_true, ↓reduceIte]
  apply PreservesX2.bind
  · exact preservesX2_readReg mip
  · intro oldMip
    apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro mipForTimer
      apply PreservesX2.bind
      · exact preservesX2_readReg mtimecmp
      · intro timerCompare
        apply PreservesX2.bind
        · exact preservesX2_readReg mtime
        · intro time
          apply PreservesX2.bind
          · exact PreservesX2.writeReg mip _ (by decide)
          · intro _
            apply PreservesX2.bind
            · exact preservesX2_currentlyEnabled_Sstc
            · intro supervisorTimeCompare
              apply PreservesX2.bind
              · exact preservesX2_readReg menvcfg
              · intro environmentConfig
                apply PreservesX2.ite
                · apply PreservesX2.bind
                  · exact preservesX2_readReg mip
                  · intro mipForSupervisorTimer
                    apply PreservesX2.bind
                    · exact preservesX2_readReg stimecmp
                    · intro supervisorTimerCompare
                      apply PreservesX2.bind
                      · exact preservesX2_readReg mtime
                      · intro supervisorTime
                        apply PreservesX2.bind
                        · exact PreservesX2.writeReg mip _ (by decide)
                        · intro _
                          exact preservesX2_clint_postlude oldMip mipWasWritten
                · exact preservesX2_clint_postlude oldMip mipWasWritten

private theorem preservesX2_read_then_write (written : Register)
    (update : RegisterType written → RegisterType written) (doesNotWriteX2 : x2 ≠ written) :
    PreservesX2 (readReg written >>= fun value => writeReg written (update value)) := by
  apply PreservesX2.bind
  · exact preservesX2_readReg written
  · intro value
    exact PreservesX2.writeReg written (update value) doesNotWriteX2

private theorem preservesX2_then_clint_dispatch (initial : SailM α)
    (initialFrame : PreservesX2 initial) (mipWasWritten : Bool) :
    PreservesX2 (initial >>= fun _ => clint_dispatch mipWasWritten >>= fun _ =>
      (pure (Sail.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply PreservesX2.bind
  · exact initialFrame
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_clint_dispatch mipWasWritten
    · intro _
      exact PreservesX2.pure _

private theorem preservesX2_after_clint_dispatch (mipWasWritten : Bool) :
    PreservesX2 (do
      clint_dispatch mipWasWritten
      pure (Sail.Ok true) : SailM (Sail.Result Bool ExceptionType)) := by
  apply PreservesX2.bind
  · exact preservesX2_clint_dispatch mipWasWritten
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_clint_store (app_0 : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (clint_store app_0 width data) := by
  unfold clint_store
  simp only
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro current
      apply PreservesX2.bind
      · exact PreservesX2.writeReg mip _ (by decide)
      · intro _
        exact preservesX2_after_clint_dispatch true
  · apply PreservesX2.ite
    · apply PreservesX2.bind
      · exact PreservesX2.writeReg mtimecmp _ (by decide)
      · intro _
        exact preservesX2_after_clint_dispatch false
    · apply PreservesX2.ite
      · apply PreservesX2.bind
        · exact preservesX2_readReg mtimecmp
        · intro current
          apply PreservesX2.bind
          · exact PreservesX2.writeReg mtimecmp _ (by decide)
          · intro _
            exact preservesX2_after_clint_dispatch false
      · apply PreservesX2.ite
        · apply PreservesX2.bind
          · exact preservesX2_readReg mtimecmp
          · intro current
            apply PreservesX2.bind
            · exact PreservesX2.writeReg mtimecmp _ (by decide)
            · intro _
              exact preservesX2_after_clint_dispatch false
        · apply PreservesX2.ite
          · apply PreservesX2.bind
            · exact PreservesX2.writeReg mtime _ (by decide)
            · intro _
              exact preservesX2_after_clint_dispatch false
          · apply PreservesX2.ite
            · apply PreservesX2.bind
              · exact preservesX2_readReg mtime
              · intro current
                apply PreservesX2.bind
                · exact PreservesX2.writeReg mtime _ (by decide)
                · intro _
                  exact preservesX2_after_clint_dispatch false
            · apply PreservesX2.ite
              · apply PreservesX2.bind
                · exact preservesX2_readReg mtime
                · intro current
                  apply PreservesX2.bind
                  · exact PreservesX2.writeReg mtime _ (by decide)
                  · intro _
                    exact preservesX2_after_clint_dispatch false
              · exact PreservesX2.pure _

private theorem preservesX2_mip_callback_ok :
    PreservesX2 (read_mip XipReadType.IncludePlatformInterrupts >>= fun value =>
      csr_name_write_callback "mip" value >>= fun _ =>
        (pure (Sail.Ok true) : SailM (Sail.Result Bool ExceptionType))) := by
  apply PreservesX2.bind
  · exact preservesX2_read_mip XipReadType.IncludePlatformInterrupts
  · intro value
    apply PreservesX2.bind
    · exact preservesX2_csr_name_write_callback_mip value
    · intro _
      exact PreservesX2.pure _

private def sigStoreAfterSsi (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  let supervisorEnabled ← currentlyEnabled extension.Ext_S
  if ((_get_Minterrupts_SSI interrupts == 1#1) && supervisorEnabled) then do
    let currentMip ← Sail.readReg mip
    Sail.writeReg mip (Sail.BitVec.updateSubrange currentMip 1 1 value)
  else pure ()
  let mipValue ← read_mip XipReadType.IncludePlatformInterrupts
  csr_name_write_callback "mip" mipValue
  pure (Sail.Ok true)

private theorem preservesX2_sigStoreAfterSsi (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterSsi interrupts value) := by
  unfold sigStoreAfterSsi
  apply PreservesX2.bind
  · exact preservesX2_currentlyEnabled_S
  · intro supervisorEnabled
    apply PreservesX2.ite
    · apply PreservesX2.bind
      · exact preservesX2_readReg mip
      · intro currentMip
        apply PreservesX2.bind
        · exact PreservesX2.writeReg mip _ (by decide)
        · intro _
          exact preservesX2_mip_callback_ok
    · apply PreservesX2.bind
      · exact PreservesX2.pure _
      · intro _
        exact preservesX2_mip_callback_ok

private def sigStoreAfterMsi (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  if _get_Minterrupts_MSI interrupts == 1#1 then do
    let currentMip ← Sail.readReg mip
    Sail.writeReg mip (Sail.BitVec.updateSubrange currentMip 3 3 value)
  else pure ()
  sigStoreAfterSsi interrupts value

private theorem preservesX2_sigStoreAfterMsi (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterMsi interrupts value) := by
  unfold sigStoreAfterMsi
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact preservesX2_readReg mip
    · intro currentMip
      apply PreservesX2.bind
      · exact PreservesX2.writeReg mip _ (by decide)
      · intro _
        exact preservesX2_sigStoreAfterSsi interrupts value
  · apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro _
      exact preservesX2_sigStoreAfterSsi interrupts value

private def sigStoreAfterSei (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  if _get_Minterrupts_SEI interrupts == 1#1 then
    Sail.writeReg sig_seip value
  else pure ()
  sigStoreAfterMsi interrupts value

private theorem preservesX2_sigStoreAfterSei (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterSei interrupts value) := by
  unfold sigStoreAfterSei
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact PreservesX2.writeReg sig_seip value (by decide)
    · intro _
      exact preservesX2_sigStoreAfterMsi interrupts value
  · apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro _
      exact preservesX2_sigStoreAfterMsi interrupts value

private def sigStoreAfterMei (interrupts : Minterrupts) (value : BitVec 1) :
    SailM (Sail.Result Bool ExceptionType) := do
  if _get_Minterrupts_MEI interrupts == 1#1 then
    Sail.writeReg sig_meip value
  else pure ()
  sigStoreAfterSei interrupts value

private theorem preservesX2_sigStoreAfterMei (interrupts : Minterrupts) (value : BitVec 1) :
    PreservesX2 (sigStoreAfterMei interrupts value) := by
  unfold sigStoreAfterMei
  apply PreservesX2.ite
  · apply PreservesX2.bind
    · exact PreservesX2.writeReg sig_meip value (by decide)
    · intro _
      exact preservesX2_sigStoreAfterSei interrupts value
  · apply PreservesX2.bind
    · exact PreservesX2.pure _
    · intro _
      exact preservesX2_sigStoreAfterSei interrupts value

private def sigStorePlatformAction (data : BitVec (8 * width)) :
    SailM (Sail.Result Bool ExceptionType) := do
  let value := Sail.BitVec.access data 31
  let interrupts : Minterrupts := Mk_Minterrupts (zero_extend (m := 64) data)
  if Sail.BitVec.extractLsb
      (_update_Minterrupts_SSI
        (_update_Minterrupts_MSI
          (_update_Minterrupts_SEI (_update_Minterrupts_MEI interrupts 0#1) 0#1) 0#1) 0#1)
      30 0 != zeros then
    pure (Sail.Err (ExceptionType.E_SAMO_Access_Fault ()))
  else
    sigStoreAfterMei interrupts value

private theorem preservesX2_sigStorePlatformAction (data : BitVec (8 * width)) :
    PreservesX2 (sigStorePlatformAction data) := by
  unfold sigStorePlatformAction
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · exact preservesX2_sigStoreAfterMei _ _

private theorem preservesX2_sig_store (app_0 : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (sig_store app_0 width data) := by
  unfold sig_store
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.ite
    · exact PreservesX2.pure _
    · apply PreservesX2.ite
      · exact preservesX2_sigStorePlatformAction data
      · exact PreservesX2.pure _

private theorem preservesX2_htif_store (app_0 : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (htif_store app_0 width data) := by
  intro state
  cases hStore : htif_store app_0 width data state with
  | error error after =>
    simpa [EStateM.run, hStore] using
      (htif_store_preserves_stack_pointer app_0 width data state)
  | ok value after =>
    simpa [EStateM.run, hStore] using
      (htif_store_preserves_stack_pointer app_0 width data state)

private theorem preservesX2_within_clint (address : physaddr) (width : Nat) :
    PreservesX2 (within_clint address width) := by
  unfold within_clint
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · exact PreservesX2.pure _

private theorem preservesX2_within_sig (address : physaddr) (width : Nat) :
    PreservesX2 (within_sig address width) := by
  unfold within_sig
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · exact PreservesX2.pure _

private theorem preservesX2_within_htif_writable (address : physaddr) (width : Nat) :
    PreservesX2 (within_htif_writable address width) := by
  unfold within_htif_writable
  apply PreservesX2.bind
  · exact preservesX2_readReg htif_tohost_base
  · intro base
    cases base <;> exact PreservesX2.pure _

private theorem preservesX2_mmio_write (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) : PreservesX2 (mmio_write address width data) := by
  unfold mmio_write
  apply PreservesX2.bind
  · exact preservesX2_within_clint address width
  · intro inClint
    apply PreservesX2.ite
    · exact preservesX2_clint_store address width data
    · apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro inSig
        apply PreservesX2.ite
        · exact preservesX2_sig_store address width data
        · apply PreservesX2.bind
          · exact preservesX2_within_htif_writable address width
          · intro inHtif
            apply PreservesX2.ite
            · exact preservesX2_htif_store address width data
            · exact PreservesX2.pure _

private theorem preservesX2_within_mmio_writable (address : physaddr) (width : Nat) :
    PreservesX2 (within_mmio_writable address width) := by
  unfold within_mmio_writable
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_within_clint address width
    · intro inClint
      apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro inSig
        apply PreservesX2.bind
        · exact preservesX2_within_htif_writable address width
        · intro inHtif
          exact PreservesX2.pure _

private theorem preservesX2_checked_mem_write_store (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege)
    (metadata : Unit) :
    PreservesX2 (checked_mem_write address width data (MemoryAccessType.Store mem_payload.Data)
      pbmt privilege metadata false false false) := by
  unfold checked_mem_write
  apply PreservesX2.bind
  · exact preservesX2_phys_access_check_store address width pbmt privilege
  · intro fault
    cases fault with
    | some fault => exact PreservesX2.pure _
    | none =>
      apply PreservesX2.bind
      · exact preservesX2_within_mmio_writable address width
      · intro mmioWritable
        apply PreservesX2.ite
        · exact preservesX2_mmio_write address width data
        · apply PreservesX2.bind
          · exact PreservesX2.pure _
          · intro kind
            apply PreservesX2.bind
            · exact preservesX2_write_ram kind address width data metadata
            · intro result
              exact PreservesX2.pure _

private theorem preservesX2_mem_write_value_priv_meta_store (address : physaddr) (width : Nat)
    (value : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege)
    (metadata : Unit) :
    PreservesX2 (mem_write_value_priv_meta address width value
      (MemoryAccessType.Store mem_payload.Data) pbmt privilege metadata false false false) := by
  unfold mem_write_value_priv_meta
  simp only [Bool.false_or, Bool.false_and]
  apply PreservesX2.bind
  · exact preservesX2_checked_mem_write_store address width value pbmt privilege metadata
  · intro result
    cases result <;> exact PreservesX2.pure _

private theorem preservesX2_mem_write_value_meta_store (address : physaddr) (width : Nat)
    (value : BitVec (8 * width)) (pbmt : page_based_mem_type) (metadata : Unit) :
    PreservesX2 (mem_write_value_meta address width value
      (MemoryAccessType.Store mem_payload.Data) pbmt metadata false false false) := by
  unfold mem_write_value_meta
  apply PreservesX2.bind
  · exact preservesX2_readReg mstatus
  · intro mstatusBits
    apply PreservesX2.bind
    · exact preservesX2_readReg cur_privilege
    · intro privilege
      apply PreservesX2.bind
      · exact preservesX2_effectivePrivilege (MemoryAccessType.Store mem_payload.Data)
          mstatusBits privilege
      · intro effectivePrivilege
        exact preservesX2_mem_write_value_priv_meta_store address width value pbmt
          effectivePrivilege metadata

private theorem preservesX2_mem_write_value_store (address : physaddr) (width : Nat)
    (value : BitVec (8 * width)) (pbmt : page_based_mem_type) :
    PreservesX2 (mem_write_value address width value
      (MemoryAccessType.Store mem_payload.Data) pbmt false false false) := by
  unfold mem_write_value
  exact preservesX2_mem_write_value_meta_store address width value pbmt default_meta

private theorem preservesX2_split_misaligned (address : virtaddr) (width : Nat) :
    PreservesX2 (split_misaligned address width) := by
  unfold split_misaligned
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.ite
    · exact PreservesX2.pure _
    · apply PreservesX2.bind
      · exact preservesX2_assert _ _
      · intro _
        exact PreservesX2.pure _

private theorem preservesX2_misaligned_order (count : Int) :
    PreservesX2 (misaligned_order count |> pure) := by
  unfold misaligned_order
  exact PreservesX2.pure _

private theorem preservesX2_trap (exception : sync_exception) : PreservesX2 (trap exception) := by
  unfold trap
  apply PreservesX2.bind
  · exact preservesX2_readReg cur_privilege
  · intro privilege
    apply PreservesX2.bind
    · exact preservesX2_readReg PC
    · intro pc
      exact PreservesX2.pure _

private theorem preservesX2_memory_exception (address : virtaddr) (exception : ExceptionType) :
    PreservesX2 (memory_exception address exception) := by
  unfold memory_exception
  exact preservesX2_trap _

private theorem preservesX2_plat_misaligned_exception (access : MemoryAccessType mem_payload)
    (reservation : Bool) : PreservesX2 (plat_misaligned_exception access reservation) := by
  unfold plat_misaligned_exception
  apply PreservesX2.bind
  · exact preservesX2_assert _ _
  · intro _
    exact PreservesX2.ite reservation (EStateM.pure (some plat_misaligned_access.lrsc))
      (if is_vector_access access then EStateM.pure plat_misaligned_access.vector
      else EStateM.pure plat_misaligned_access.load_store)
      (PreservesX2.pure _) (PreservesX2.ite _ _ _ (PreservesX2.pure _) (PreservesX2.pure _))

private theorem preservesX2E_vmem_write_store_misaligned_then (address : virtaddr) :
    PreservesX2E (do
      match (← plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false) with
      | some .AccessFault =>
        Sail.SailME.throw (← do
          pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))))
      | some .AlignmentException =>
        Sail.SailME.throw (← do
          pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))))
      | none => pure () : SailME (Sail.Result Bool ExecutionResult) PUnit) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift
      (plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false)
      (preservesX2_plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false)
  · intro exception
    cases exception with
    | none => exact PreservesX2E.pure _
    | some exception =>
      cases exception with
      | AccessFault =>
        apply PreservesX2E.bind
        · apply PreservesX2E.bind
          · exact PreservesX2E.lift
              (memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))
              (preservesX2_memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))
          · intro result
            exact PreservesX2E.pure (Sail.Err result)
        · intro error
          exact PreservesX2E.throw error
      | AlignmentException =>
        apply PreservesX2E.bind
        · apply PreservesX2E.bind
          · exact PreservesX2E.lift
              (memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))
              (preservesX2_memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))
          · intro result
            exact PreservesX2E.pure (Sail.Err result)
        · intro error
          exact PreservesX2E.throw error

private theorem preservesX2E_vmem_write_store_misaligned (address : virtaddr) (width : Nat) :
    PreservesX2E (if LeanRV64DExecutable.Functions.not (is_aligned_vaddr address width) then
      (do
        match (← plat_misaligned_exception (MemoryAccessType.Store mem_payload.Data) false) with
        | some .AccessFault =>
          Sail.SailME.throw (← do
            pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Access_Fault ()))) )
        | some .AlignmentException =>
          Sail.SailME.throw (← do
            pure (Sail.Err (← memory_exception address (ExceptionType.E_SAMO_Addr_Align ()))) )
        | none => pure ())
      else pure () : SailME (Sail.Result Bool ExecutionResult) PUnit) := by
  apply PreservesX2E.ite
  · exact preservesX2E_vmem_write_store_misaligned_then address
  · exact PreservesX2E.pure _

private theorem preservesX2_is_shadow_stack_access (access : MemoryAccessType mem_payload) :
    PreservesX2 (is_shadow_stack_access access) := by
  unfold is_shadow_stack_access
  cases access with
  | InstructionFetch _ => exact PreservesX2.pure _
  | Load payload =>
    cases payload <;> exact PreservesX2.pure _
  | LoadReserved payload =>
    cases payload <;> first | exact PreservesX2.pure _ | exact preservesX2_internal_error _ _ _
  | Store payload =>
    cases payload <;> exact PreservesX2.pure _
  | StoreConditional payload =>
    cases payload <;> first | exact PreservesX2.pure _ | exact preservesX2_internal_error _ _ _
  | Atomic payload =>
    rcases payload with ⟨operation, readPayload, writePayload⟩
    cases readPayload <;> cases writePayload <;>
      first | exact PreservesX2.pure _ | exact preservesX2_internal_error _ _ _
  | CacheAccess _ => exact PreservesX2.pure _

private theorem preservesX2_satp_mode_width_forwards (mode : SATPMode) :
    PreservesX2 (satp_mode_width_forwards mode) := by
  cases mode <;> unfold satp_mode_width_forwards
  all_goals first
    | exact PreservesX2.pure _
    | exact PreservesX2.bind (Sail.assert false "Pattern match failure at unknown location")
        (fun _ => EStateM.throw Sail.Error.Exit) (preservesX2_assert _ _)
        (fun _ => PreservesX2.throw _)

private theorem preservesX2_get_satp (svWidth : Nat) :
    PreservesX2 (get_satp svWidth) := by
  unfold get_satp
  apply PreservesX2.bind
      (Sail.assert ((svWidth == 32) || (LeanRV64DExecutable.Functions.xlen == 64))
        "sys/vmem.sail:395.30-395.31")
  · exact preservesX2_assert _ _
  · intro _
    by_cases hWidth : svWidth = 32
    · subst svWidth
      simp
      apply PreservesX2.bind (readReg satp)
      · exact preservesX2_readReg satp
      · intro _
        exact PreservesX2.pure _
    · have hWidthBool : (svWidth == 32) = false := beq_eq_false_iff_ne.mpr hWidth
      rw [hWidthBool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply PreservesX2.bind (readReg satp)
      · exact preservesX2_readReg satp
      · intro _
        exact PreservesX2.pure _

private theorem preservesX2_translationException_store_data (failure : PTW_Error) :
    PreservesX2 (translationException (MemoryAccessType.Store mem_payload.Data) failure) := by
  unfold translationException
  cases failure <;> exact PreservesX2.pure _

private theorem preservesX2_currentlyEnabled_Svade :
    PreservesX2 (currentlyEnabled extension.Ext_Svade) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svade_preserves_stack_pointer

private theorem preservesX2_currentlyEnabled_Svadu :
    PreservesX2 (currentlyEnabled extension.Ext_Svadu) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svadu_preserves_stack_pointer

private theorem preservesX2_currentlyEnabled_Svnapot :
    PreservesX2 (currentlyEnabled extension.Ext_Svnapot) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svnapot_preserves_stack_pointer

private theorem preservesX2_currentlyEnabled_Svrsw60t59b :
    PreservesX2 (currentlyEnabled extension.Ext_Svrsw60t59b) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    currentlyEnabled_svrsw60t59b_preserves_stack_pointer

private theorem preservesX2_pte_is_invalid (flags : BitVec 8) (extensions : BitVec 10) :
    PreservesX2 (pte_is_invalid flags extensions) := by
  unfold pte_is_invalid
  apply PreservesX2.bind
  · exact preservesX2_readReg menvcfg
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_currentlyEnabled_Svnapot
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_readReg menvcfg
      · intro _
        apply PreservesX2.bind
        · exact preservesX2_currentlyEnabled_Svrsw60t59b
        · intro _
          exact PreservesX2.pure _

private theorem preservesX2E_check_pte_priv_ok_store_data (privilege : Privilege) (pteU : Bool)
    (doSum : Bool) :
    PreservesX2E ((match privilege with
      | .User => pure pteU
      | .Supervisor => pure ((LeanRV64DExecutable.Functions.not pteU) || (doSum && true))
      | .Machine => internal_error "sys/vmem_pte.sail" 151 "m-mode mem perm check"
      | .VirtualUser => internal_error "sys/vmem_pte.sail" 152 "Hypervisor extension not supported"
      | .VirtualSupervisor =>
        internal_error "sys/vmem_pte.sail" 153 "Hypervisor extension not supported") :
      SailME PTE_Check Bool) := by
  cases privilege with
  | User => exact PreservesX2E.pure pteU
  | Supervisor => exact PreservesX2E.pure _
  | Machine =>
    exact PreservesX2E.lift (internal_error "sys/vmem_pte.sail" 151 "m-mode mem perm check")
      (preservesX2_internal_error _ _ _)
  | VirtualUser =>
    exact PreservesX2E.lift
      (internal_error "sys/vmem_pte.sail" 152 "Hypervisor extension not supported")
      (preservesX2_internal_error _ _ _)
  | VirtualSupervisor =>
    exact PreservesX2E.lift
      (internal_error "sys/vmem_pte.sail" 153 "Hypervisor extension not supported")
      (preservesX2_internal_error _ _ _)

private theorem preservesX2E_check_pte_finish_store_data (pteW : Bool) :
    PreservesX2E (do
      let writable := pteW
      if LeanRV64DExecutable.Functions.not writable then
        pure (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Permission ()))
      else pure (PTE_Check.PTE_Check_Success ()) : SailME PTE_Check PTE_Check) := by
  apply PreservesX2E.ite
  · exact PreservesX2E.pure _
  · exact PreservesX2E.pure _

private theorem preservesX2E_check_pte_reserved_store_data :
    PreservesX2E (do
      let environment ← ExceptT.lift (readReg menvcfg)
      ExceptT.lift (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
        "sys/vmem_pte.sail:162.33-162.34")
      let shadowStackOk ← pure false
      if LeanRV64DExecutable.Functions.not shadowStackOk then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((), pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (readReg menvcfg) (preservesX2_readReg menvcfg)
  · intro environment
    apply PreservesX2E.bind
    · exact PreservesX2E.lift
        (Sail.assert (bool_bit_backwards (_get_MEnvcfg_SSE environment))
          "sys/vmem_pte.sail:162.33-162.34")
        (preservesX2_assert _ _)
    · intro _
      apply PreservesX2E.bind
      · exact PreservesX2E.pure false
      · intro shadowStackOk
        apply PreservesX2E.ite
        · exact PreservesX2E.throw _
        · exact PreservesX2E.pure _

private theorem preservesX2E_check_pte_nonreserved_store_data (flags : BitVec 8) :
    PreservesX2E (do
      let shadowStack ← ExceptT.lift
        (is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
      if shadowStack then
        Sail.SailME.throw (PTE_Check.PTE_Check_Failure ((),
          if (bit_to_bool (_get_PTE_Flags_R flags)) &&
              (LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_W flags)) &&
                LeanRV64DExecutable.Functions.not (bit_to_bool (_get_PTE_Flags_X flags))) then
            pte_check_failure.PTE_No_Permission ()
          else pte_check_failure.PTE_No_Access ()))
      else pure () : SailME PTE_Check PUnit) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift
      (is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
      (preservesX2_is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
  · intro shadowStack
    apply PreservesX2E.ite
    · exact PreservesX2E.throw _
    · exact PreservesX2E.pure _

private theorem preservesX2_check_PTE_permission_store_data (privilege : Privilege)
    (mxr doSum : Bool) (flags : BitVec 8) (extensions : BitVec 10) (external : Unit) :
    PreservesX2
      (check_PTE_permission (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum flags
        extensions external) := by
  unfold check_PTE_permission
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (Sail.assert _ _) (preservesX2_assert _ _)
  · intro _
    apply PreservesX2E.bind
    · exact preservesX2E_check_pte_priv_ok_store_data privilege
        (bit_to_bool (_get_PTE_Flags_U flags)) doSum
    · intro privOk
      apply PreservesX2E.ite
      · exact PreservesX2E.pure _
      · apply PreservesX2E.ite
        · apply PreservesX2E.bind
          · exact preservesX2E_check_pte_reserved_store_data
          · intro _
            exact preservesX2E_check_pte_finish_store_data (bit_to_bool (_get_PTE_Flags_W flags))
        · apply PreservesX2E.bind
          · exact preservesX2E_check_pte_nonreserved_store_data flags
          · intro _
            exact preservesX2E_check_pte_finish_store_data (bit_to_bool (_get_PTE_Flags_W flags))

private theorem preservesX2_readByte (address : Nat) :
    PreservesX2 (PreSail.readByte address : SailM (BitVec 8)) := by
  intro state
  unfold PreSail.readByte
  simp only [EStateM.instMonad, EStateM.bind, instMonadStateOfMonadStateOf,
    EStateM.instMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe]
  unfold EStateM.get
  simp only
  cases hRead : state.mem.get? address <;> rfl

private theorem preservesX2_readBytes (size address : Nat) :
    PreservesX2 (PreSail.readBytes size address) := by
  induction size generalizing address with
  | zero => exact PreservesX2.pure _
  | succ size ih =>
    cases size with
    | zero =>
      simp only [PreSail.readBytes]
      apply PreservesX2.bind (PreSail.readByte address)
      · exact preservesX2_readByte address
      · intro _
        exact PreservesX2.pure _
    | succ size =>
      simp only [PreSail.readBytes]
      apply PreservesX2.bind (PreSail.readByte address)
      · exact preservesX2_readByte address
      · intro _
        apply PreservesX2.bind (PreSail.readBytes (size + 1) (address + 1))
        · exact ih (address := address + 1)
        · intro _
          exact PreservesX2.pure _

private def storeReadRamPlainRequest (address : physaddrbits) (width : Nat) :
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

private theorem preservesX2_storeReadRamPlainRequest (address : physaddrbits) (width : Nat) :
    PreservesX2 (storeReadRamPlainRequest address width) := by
  unfold storeReadRamPlainRequest
  apply PreservesX2.bind (pure (Sail.ConcurrencyInterfaceV1.AK_explicit
    { variety := Sail.ConcurrencyInterfaceV1.AV_plain
      strength := Sail.ConcurrencyInterfaceV1.AS_normal }))
  · exact PreservesX2.pure _
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_plain_sail_mem_read
    (request : Sail.ConcurrencyInterfaceV1.Mem_read_request width 64 physaddrbits Unit
      RISCV_strong_access) :
    PreservesX2 (Sail.ConcurrencyInterfaceV1.sail_mem_read request) := by
  delta Sail.ConcurrencyInterfaceV1.sail_mem_read
  unfold PreSail.ConcurrencyInterfaceV1.sail_mem_read
  apply PreservesX2.bind (PreSail.readBytes width request.pa.toNat)
  · exact preservesX2_readBytes width request.pa.toNat
  · intro _
    exact PreservesX2.pure _

private theorem storeReadRamPlainUnfold (address : physaddrbits) (width : Nat) :
    read_ram .Read_plain (.Physaddr address) width false = (do
      let request ← storeReadRamPlainRequest address width
      match ← Sail.ConcurrencyInterfaceV1.sail_mem_read request with
      | .Ok (value, _) => pure (value, default_meta)
      | .Err () => EStateM.throw Sail.Error.Exit) := by
  rfl

private theorem preservesX2_read_ram_plain (address : physaddr) (width : Nat) :
    PreservesX2 (read_ram .Read_plain address width false) := by
  rcases address with ⟨address⟩
  rw [storeReadRamPlainUnfold]
  apply PreservesX2.bind (storeReadRamPlainRequest address width)
  · exact preservesX2_storeReadRamPlainRequest address width
  · intro request
    apply PreservesX2.bind (Sail.ConcurrencyInterfaceV1.sail_mem_read request)
    · exact preservesX2_plain_sail_mem_read request
    · intro result
      cases result with
      | Ok value => exact PreservesX2.pure _
      | Err error => exact PreservesX2.throw _

private theorem preservesX2_accessFault_load_pte :
    PreservesX2 (accessFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact PreservesX2.pure _

private theorem preservesX2_accessFault_store_pte :
    PreservesX2
      (accessFaultFromAccessType
        (MemoryAccessType.Store mem_payload.PageTableEntry)) := by
  unfold accessFaultFromAccessType
  exact PreservesX2.pure _

private theorem preservesX2_alignmentFault_load_pte :
    PreservesX2
      (alignmentFaultFromAccessType
        (MemoryAccessType.Load mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact PreservesX2.pure _

private theorem preservesX2_alignmentFault_store_pte :
    PreservesX2
      (alignmentFaultFromAccessType
        (MemoryAccessType.Store mem_payload.PageTableEntry)) := by
  unfold alignmentFaultFromAccessType
  exact PreservesX2.pure _

private theorem preservesX2_pmpCheckRWX_load_pte (config : BitVec 8) :
    PreservesX2 (pmpCheckRWX config (MemoryAccessType.Load mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact PreservesX2.pure _

private theorem preservesX2_pmpCheckRWX_store_pte (config : BitVec 8) :
    PreservesX2 (pmpCheckRWX config (MemoryAccessType.Store mem_payload.PageTableEntry)) := by
  unfold pmpCheckRWX
  exact PreservesX2.pure _

private theorem preservesX2E_pmpLoopAfterPrev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2E
      (pmpLoopAfterPrev address width access privilege index previousPmpaddr loopVars) := by
  unfold pmpLoopAfterPrev
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (Sail.readReg pmpcfg_n) (preservesX2_readReg pmpcfg_n)
  · intro rawConfig
    apply PreservesX2E.bind
    · exact PreservesX2E.pure _
    · intro config
      apply PreservesX2E.bind
      · exact PreservesX2E.lift (pmpReadAddrReg index.toNat)
          (preservesX2_pmpReadAddrReg index.toNat)
      · intro currentPmpaddr
        apply PreservesX2E.bind
        · exact PreservesX2E.lift
            (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
            (preservesX2_pmpMatchAddr address width config currentPmpaddr previousPmpaddr)
        · intro matched
          cases matched with
          | PMP_NoMatch => exact PreservesX2E.pure _
          | PMP_PartialMatch =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift (accessFaultFromAccessType access) accessFaultFrame
              · intro fault
                exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault
          | PMP_Match =>
            apply PreservesX2E.bind
            · apply PreservesX2E.bind
              · exact PreservesX2E.lift (pmpCheckRWX config access) (rwxFrame config)
              · intro permitted
                apply PreservesX2E.ite
                · exact PreservesX2E.pure none
                · apply PreservesX2E.bind
                  · exact PreservesX2E.lift (accessFaultFromAccessType access) accessFaultFrame
                  · intro fault
                    exact PreservesX2E.pure (some fault)
            · intro fault
              exact PreservesX2E.throw fault

private theorem preservesX2E_pmpLoopBody (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege) (index : Int)
    (inRange : index ∈ pmpLoopRange) (loopVars : Unit)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2E (pmpLoopBody address width access privilege index inRange loopVars) := by
  unfold pmpLoopBody
  apply PreservesX2E.ite
  · apply PreservesX2E.bind
    · exact PreservesX2E.lift (pmpReadAddrReg (index - 1).toNat)
        (preservesX2_pmpReadAddrReg (index - 1).toNat)
    · intro previousPmpaddr
      exact preservesX2E_pmpLoopAfterPrev address width access privilege index previousPmpaddr
        loopVars accessFaultFrame rwxFrame
  · exact preservesX2E_pmpLoopAfterPrev address width access privilege index zeros loopVars
      accessFaultFrame rwxFrame

private theorem preservesX2E_pmpLoop (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2E
      (IntRange.forIn' pmpLoopRange () (pmpLoopBody address width access privilege)) := by
  unfold IntRange.forIn'
  exact preservesX2E_pmpLoopInvariant
    (pmpLoopBody address width access privilege)
    (fun index inRange =>
      preservesX2E_pmpLoopBody address width access privilege index inRange () accessFaultFrame
        rwxFrame)
    pmpLoopRange.start (by simp)

private theorem preservesX2_pmpCheck (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (privilege : Privilege)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access))
    (rwxFrame : ∀ config, PreservesX2 (pmpCheckRWX config access)) :
    PreservesX2 (pmpCheck address width access privilege) := by
  rw [pmpCheck_loop_eq]
  unfold pmpCheckLoop
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · exact preservesX2E_pmpLoop address (to_bits width) access privilege accessFaultFrame rwxFrame
  · intro loopVars
    apply PreservesX2E.bind
    · exact PreservesX2E.pure loopVars
    · intro _
      apply PreservesX2E.ite
      · exact PreservesX2E.pure _
      · apply PreservesX2E.bind
        · exact PreservesX2E.lift (accessFaultFromAccessType access) accessFaultFrame
        · intro fault
          exact PreservesX2E.pure (some fault)

private theorem preservesX2_pmpCheck_load_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesX2 (pmpCheck address width (MemoryAccessType.Load mem_payload.PageTableEntry)
      privilege) :=
  preservesX2_pmpCheck address width (MemoryAccessType.Load mem_payload.PageTableEntry) privilege
    preservesX2_accessFault_load_pte preservesX2_pmpCheckRWX_load_pte

private theorem preservesX2_pmpCheck_store_pte (address : physaddr) (width : Nat)
    (privilege : Privilege) :
    PreservesX2 (pmpCheck address width (MemoryAccessType.Store mem_payload.PageTableEntry)
      privilege) :=
  preservesX2_pmpCheck address width (MemoryAccessType.Store mem_payload.PageTableEntry) privilege
    preservesX2_accessFault_store_pte preservesX2_pmpCheckRWX_store_pte

private theorem preservesX2_pmaCheck_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesX2 (pmaCheck address width (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt
      reservation) := by
  unfold pmaCheck
  apply PreservesX2.bind
  · exact preservesX2_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      simp only
      apply PreservesX2.bind
        (accessFaultFromAccessType
          (MemoryAccessType.Load mem_payload.PageTableEntry))
      · exact preservesX2_accessFault_load_pte
      · intro _
        exact PreservesX2.pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply PreservesX2.bind
      · apply PreservesX2.ite
        · exact PreservesX2.pure _
        · unfold pma_misaligned_exception
          exact PreservesX2.pure _
      · intro exception
        cases exception with
        | none =>
          apply PreservesX2.bind
          · apply PreservesX2.bind (Sail.assert _ _)
            · exact preservesX2_assert _ _
            · intro _
              exact PreservesX2.pure _
          · intro canAccess
            apply PreservesX2.ite
            · exact PreservesX2.pure _
            · apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry))
              · exact preservesX2_accessFault_load_pte
              · intro _
                exact PreservesX2.pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry))
            · exact preservesX2_accessFault_load_pte
            · intro _
              exact PreservesX2.pure _
          | AlignmentException =>
            apply PreservesX2.bind
                (alignmentFaultFromAccessType (MemoryAccessType.Load mem_payload.PageTableEntry))
            · exact preservesX2_alignmentFault_load_pte
            · intro _
              exact PreservesX2.pure _

private theorem preservesX2_pmaCheck_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (reservation : Bool) :
    PreservesX2 (pmaCheck address width (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt
      reservation) := by
  unfold pmaCheck
  apply PreservesX2.bind
  · exact preservesX2_readReg pma_regions
  · intro regions
    cases hPma : matching_pma_region regions address width with
    | none =>
      simp only
      apply PreservesX2.bind
          (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
      · exact preservesX2_accessFault_store_pte
      · intro _
        exact PreservesX2.pure _
    | some region =>
      rcases region with ⟨base, size, attributes, includeInDeviceTree⟩
      apply PreservesX2.bind
      · apply PreservesX2.ite
        · exact PreservesX2.pure _
        · unfold pma_misaligned_exception
          exact PreservesX2.pure _
      · intro exception
        cases exception with
        | none =>
          apply PreservesX2.bind
          · apply PreservesX2.bind (Sail.assert _ _)
            · exact preservesX2_assert _ _
            · intro _
              exact PreservesX2.pure _
          · intro canAccess
            apply PreservesX2.ite
            · exact PreservesX2.pure _
            · apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
              · exact preservesX2_accessFault_store_pte
              · intro _
                exact PreservesX2.pure _
        | some exception =>
          cases exception with
          | AccessFault =>
            apply PreservesX2.bind
                (accessFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
            · exact preservesX2_accessFault_store_pte
            · intro _
              exact PreservesX2.pure _
          | AlignmentException =>
            apply PreservesX2.bind
                (alignmentFaultFromAccessType (MemoryAccessType.Store mem_payload.PageTableEntry))
            · exact preservesX2_alignmentFault_store_pte
            · intro _
              exact PreservesX2.pure _

private theorem preservesX2_phys_access_check (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (privilege : Privilege)
    (reservation : Bool) (pmpFrame : PreservesX2 (pmpCheck address width access privilege))
    (pmaFrame : PreservesX2 (pmaCheck address width access pbmt reservation)) :
    PreservesX2 (phys_access_check access pbmt privilege address width reservation) := by
  unfold phys_access_check
  apply PreservesX2.bind
  · exact pmpFrame
  · intro pmpError
    apply PreservesX2.bind
    · exact pmaFrame
    · intro pmaError
      cases pmpError <;> cases pmaError
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · exact PreservesX2.pure _
      · apply PreservesX2.bind
        · exact preservesX2_highestPriorityAlignmentOrAccessFault _ _
        · intro _
          exact PreservesX2.pure _

private theorem preservesX2_phys_access_check_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesX2
      (phys_access_check (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width reservation) :=
  preservesX2_phys_access_check address width (MemoryAccessType.Load mem_payload.PageTableEntry)
    pbmt privilege reservation (preservesX2_pmpCheck_load_pte address width privilege)
    (preservesX2_pmaCheck_load_pte address width pbmt reservation)

private theorem preservesX2_phys_access_check_store_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) (reservation : Bool) :
    PreservesX2
      (phys_access_check (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt privilege address
        width reservation) :=
  preservesX2_phys_access_check address width (MemoryAccessType.Store mem_payload.PageTableEntry)
    pbmt privilege reservation (preservesX2_pmpCheck_store_pte address width privilege)
    (preservesX2_pmaCheck_store_pte address width pbmt reservation)

private theorem preservesX2_read_then_pure (register : Register)
    (next : RegisterType register → α) :
    PreservesX2 (do
      let value ← readReg register
      pure (next value)) := by
  apply PreservesX2.bind (readReg register)
  · exact preservesX2_readReg register
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_within_htif_readable (address : physaddr) (width : Nat) :
    PreservesX2 (within_htif_readable address width) := by
  exact preservesX2_within_htif_writable address width

private theorem preservesX2_within_mmio_readable (address : physaddr) (width : Nat) :
    PreservesX2 (within_mmio_readable address width) := by
  unfold within_mmio_readable
  apply PreservesX2.ite
  · exact PreservesX2.pure _
  · apply PreservesX2.bind
    · exact preservesX2_within_clint address width
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro _
        apply PreservesX2.bind
        · exact preservesX2_within_htif_readable address width
        · intro _
          exact PreservesX2.pure _

private theorem preservesX2_sig_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access)) :
    PreservesX2 (sig_load access address width) := by
  unfold sig_load
  apply PreservesX2.ite
  · apply PreservesX2.bind (accessFaultFromAccessType access)
    · exact accessFaultFrame
    · intro _
      exact PreservesX2.pure _
  · apply PreservesX2.ite
    · exact PreservesX2.pure _
    · apply PreservesX2.ite
      · exact PreservesX2.pure _
      · apply PreservesX2.bind (accessFaultFromAccessType access)
        · exact accessFaultFrame
        · intro _
          exact PreservesX2.pure _

private theorem preservesX2_clint_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access)) :
    PreservesX2 (clint_load access address width) := by
  unfold clint_load
  simp only [get_config_print_clint]
  apply PreservesX2.ite
  · exact preservesX2_read_then_pure mip _
  · apply PreservesX2.ite
    · exact preservesX2_read_then_pure mtimecmp _
    · apply PreservesX2.ite
      · exact preservesX2_read_then_pure mtimecmp _
      · apply PreservesX2.ite
        · exact preservesX2_read_then_pure mtimecmp _
        · apply PreservesX2.ite
          · exact preservesX2_read_then_pure mtime _
          · apply PreservesX2.ite
            · exact preservesX2_read_then_pure mtime _
            · apply PreservesX2.ite
              · exact preservesX2_read_then_pure mtime _
              · apply PreservesX2.bind (accessFaultFromAccessType access)
                · exact accessFaultFrame
                · intro _
                  exact PreservesX2.pure _

private theorem preservesX2_htif_load (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat) :
    PreservesX2 (htif_load access address width) := by
  simpa only [PreservesX2, PreservesStackPointer] using
    htif_load_preserves_stack_pointer access address width

private theorem preservesX2_mmio_read (access : MemoryAccessType mem_payload)
    (address : physaddr) (width : Nat)
    (accessFaultFrame : PreservesX2 (accessFaultFromAccessType access)) :
    PreservesX2 (mmio_read access address width) := by
  unfold mmio_read
  apply PreservesX2.bind
  · exact preservesX2_within_clint address width
  · intro inClint
    apply PreservesX2.ite
    · exact preservesX2_clint_load access address width accessFaultFrame
    · apply PreservesX2.bind
      · exact preservesX2_within_sig address width
      · intro inSig
        apply PreservesX2.ite
        · exact preservesX2_sig_load access address width accessFaultFrame
        · apply PreservesX2.bind
          · exact preservesX2_within_htif_readable address width
          · intro inHtif
            apply PreservesX2.ite
            · exact preservesX2_htif_load access address width
            · apply PreservesX2.bind (accessFaultFromAccessType access)
              · exact accessFaultFrame
              · intro _
                exact PreservesX2.pure _

private theorem preservesX2_mmio_read_load_pte (address : physaddr) (width : Nat) :
    PreservesX2 (mmio_read (MemoryAccessType.Load mem_payload.PageTableEntry) address width) :=
  preservesX2_mmio_read (MemoryAccessType.Load mem_payload.PageTableEntry) address width
    preservesX2_accessFault_load_pte

private theorem preservesX2_checked_mem_read_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false) := by
  unfold checked_mem_read
  apply PreservesX2.bind
      (phys_access_check (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false)
  · exact preservesX2_phys_access_check_load_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact PreservesX2.pure _
    | none =>
      apply PreservesX2.bind
      · exact preservesX2_within_mmio_readable address width
      · intro inMmio
        apply PreservesX2.ite
        · apply PreservesX2.bind
            (mmio_read (MemoryAccessType.Load mem_payload.PageTableEntry) address width)
          · exact preservesX2_mmio_read_load_pte address width
          · intro _
            exact PreservesX2.pure _
        · simp only [read_kind_of_flags]
          apply PreservesX2.bind (read_ram .Read_plain address width false)
          · exact preservesX2_read_ram_plain address width
          · intro _
            exact PreservesX2.pure _

private theorem preservesX2_mem_read_priv_meta_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (mem_read_priv_meta (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false) := by
  unfold mem_read_priv_meta
  simp only
  apply PreservesX2.bind
      (checked_mem_read (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false)
  · exact preservesX2_checked_mem_read_load_pte address width pbmt privilege
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_mem_read_priv_load_pte (address : physaddr) (width : Nat)
    (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (mem_read_priv (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address width
        false false false) := by
  unfold mem_read_priv
  apply PreservesX2.bind
      (mem_read_priv_meta (MemoryAccessType.Load mem_payload.PageTableEntry) pbmt privilege address
        width false false false false)
  · exact preservesX2_mem_read_priv_meta_load_pte address width pbmt privilege
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_read_pte (address : physaddr) (width : Nat) :
    PreservesX2 (read_pte address width) := by
  unfold read_pte
  exact preservesX2_mem_read_priv_load_pte address width .PBMT_PMA .Supervisor

private theorem preservesX2_checked_mem_write_store_pte (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (pbmt : page_based_mem_type) (privilege : Privilege) :
    PreservesX2
      (checked_mem_write address width data (MemoryAccessType.Store mem_payload.PageTableEntry)
        pbmt privilege default_meta false false false) := by
  unfold checked_mem_write
  apply PreservesX2.bind
      (phys_access_check (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt privilege address
        width false)
  · exact preservesX2_phys_access_check_store_pte address width pbmt privilege false
  · intro exception
    cases exception with
    | some exception => exact PreservesX2.pure _
    | none =>
      apply PreservesX2.bind
      · exact preservesX2_within_mmio_writable address width
      · intro inMmio
        apply PreservesX2.ite
        · exact preservesX2_mmio_write address width data
        · simp only [write_kind_of_flags]
          apply PreservesX2.bind (write_ram .Write_plain address width data default_meta)
          · exact preservesX2_write_ram .Write_plain address width data default_meta
          · intro _
            exact PreservesX2.pure _

private theorem preservesX2_mem_write_value_priv_meta_store_pte (address : physaddr)
    (width : Nat) (data : BitVec (8 * width)) (pbmt : page_based_mem_type)
    (privilege : Privilege) :
      PreservesX2
        (mem_write_value_priv_meta address width data
          (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt privilege default_meta
          false false false) := by
  unfold mem_write_value_priv_meta
  simp only
  apply PreservesX2.bind
      (checked_mem_write address width data (MemoryAccessType.Store mem_payload.PageTableEntry)
        pbmt privilege default_meta false false false)
  · exact preservesX2_checked_mem_write_store_pte address width data pbmt privilege
  · intro _
    exact PreservesX2.pure _

private theorem preservesX2_mem_write_value_priv_store_pte (address : physaddr) (width : Nat)
    (data : BitVec (8 * width)) (privilege : Privilege) (pbmt : page_based_mem_type) :
    PreservesX2
      (mem_write_value_priv address width data privilege
        (MemoryAccessType.Store mem_payload.PageTableEntry) pbmt false false false) := by
  unfold mem_write_value_priv
  exact preservesX2_mem_write_value_priv_meta_store_pte address width data pbmt privilege

private theorem preservesX2_write_pte (address : physaddr) (width : Nat)
    (data : BitVec (width * 8)) :
    PreservesX2 (write_pte address width data) := by
  unfold write_pte
  exact preservesX2_mem_write_value_priv_store_pte address width _ .Supervisor .PBMT_PMA

private theorem preservesX2_update_and_write_pte_store_data (address : physaddr) (width : Nat)
    (pte : BitVec (width * 8)) :
    PreservesX2
      (update_and_write_pte address width pte (MemoryAccessType.Store mem_payload.Data)) := by
  unfold update_and_write_pte
  cases hUpdate : update_PTE_Bits pte (MemoryAccessType.Store mem_payload.Data) with
  | none => exact PreservesX2.pure _
  | some updated =>
    apply PreservesX2.bind (currentlyEnabled extension.Ext_Svadu)
    · exact preservesX2_currentlyEnabled_Svadu
    · intro _
      apply PreservesX2.bind (readReg menvcfg)
      · exact preservesX2_readReg menvcfg
      · intro _
        apply PreservesX2.bind (currentlyEnabled extension.Ext_Svadu)
        · exact preservesX2_currentlyEnabled_Svadu
        · intro _
          apply PreservesX2.bind (currentlyEnabled extension.Ext_Svade)
          · exact preservesX2_currentlyEnabled_Svade
          · intro _
            apply PreservesX2.ite
            · apply PreservesX2.bind (write_pte address width updated)
              · exact preservesX2_write_pte address width updated
              · intro result
                cases result <;> exact PreservesX2.pure _
            · exact PreservesX2.pure _

private theorem preservesX2_write_TLB (index : Nat) (entry : TLB_Entry) :
    PreservesX2 (write_TLB index entry) := by
  unfold write_TLB
  apply PreservesX2.bind
  · exact preservesX2_readReg tlb
  · intro entries
    exact PreservesX2.writeReg tlb _ (by decide)

private theorem preservesX2_lookup_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12)) :
    PreservesX2 (lookup_TLB svWidth asid vpn) := by
  unfold lookup_TLB
  apply PreservesX2.bind
  · exact preservesX2_readReg tlb
  · intro entries
    cases entry : GetElem?.getElem! entries (tlb_hash svWidth vpn) with
    | none => exact PreservesX2.pure _
    | some entry =>
      apply PreservesX2.ite <;> exact PreservesX2.pure _

private theorem preservesX2_add_to_TLB (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (ppn : BitVec (if (svWidth == 32 : Bool) then 22 else 44))
    (pte : BitVec (if (svWidth == 32 : Bool) then 32 else 64)) (pteAddress : physaddr)
    (level : Nat) (global : Bool) :
    PreservesX2 (add_to_TLB svWidth asid vpn ppn pte pteAddress level global) := by
  unfold add_to_TLB
  apply PreservesX2.bind
  · exact preservesX2_readReg tlb
  · intro entries
    apply PreservesX2.bind
    · exact PreservesX2.writeReg tlb _ (by decide)
    · intro _
      apply PreservesX2.bind
      · exact preservesX2_readReg tlb
      · intro updatedEntries
        exact PreservesX2.pure _

private theorem preservesX2_page_based_mem_type_forwards (bits : BitVec 2) :
    PreservesX2 (page_based_mem_type_forwards bits) := by
  have cases : bits.toNat = 0 ∨ bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
    omega
  rcases cases with h | h | h | h
  all_goals
    have value : bits = BitVec.ofNat 2 bits.toNat := by
      rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      omega
    rw [value]
    simp [page_based_mem_type_forwards, h, EStateM.instMonad]
    all_goals first | exact PreservesX2.pure _ | exact PreservesX2.throw _

private theorem preservesX2_tlb_get_pbmt (entry : TLB_Entry) :
    PreservesX2 (tlb_get_pbmt entry) := by
  unfold tlb_get_pbmt
  exact preservesX2_page_based_mem_type_forwards _

private theorem preservesX2_translate_TLB_hit_store_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) (index : Nat) (entry : TLB_Entry) :
    PreservesX2
      (translate_TLB_hit svWidth asid vpn (MemoryAccessType.Store mem_payload.Data) privilege mxr
        doSum external index entry) := by
  apply preservesX2_of_preservesStackPointer
  exact translate_tlb_hit_preserves_stack_pointer_of svWidth asid vpn
    (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum external index entry
    (fun flags extensions =>
      preservesStackPointer_of_preservesX2
        (preservesX2_check_PTE_permission_store_data privilege mxr doSum flags extensions external))
    (fun address width pte =>
      preservesStackPointer_of_preservesX2
        (preservesX2_update_and_write_pte_store_data address width pte))
    (fun index entry =>
      preservesStackPointer_of_preservesX2 (preservesX2_write_TLB index entry))
    (preservesStackPointer_of_preservesX2 (preservesX2_tlb_get_pbmt entry))

private theorem preservesX2_pt_walk_store_data (svWidth : Nat) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit)
    (ptBase : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (level : Nat) (global : Bool) :
      PreservesX2
        (pt_walk svWidth vpn (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum
          ptBase level global external) := by
  apply preservesX2_of_preservesStackPointer
  apply pt_walk_preserves_stack_pointer_of svWidth vpn (MemoryAccessType.Store mem_payload.Data)
      privilege mxr doSum external
  · intro address width
    exact preservesStackPointer_of_preservesX2 (preservesX2_read_pte address width)
  · intro flags extensions
    exact preservesStackPointer_of_preservesX2 (preservesX2_pte_is_invalid flags extensions)
  · intro flags extensions
    exact preservesStackPointer_of_preservesX2
      (preservesX2_check_PTE_permission_store_data privilege mxr doSum flags extensions external)
  · exact preservesStackPointer_of_preservesX2 preservesX2_currentlyEnabled_Svnapot

private theorem preservesX2_translate_TLB_miss_store_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesX2
      (translate_TLB_miss svWidth asid basePpn vpn (MemoryAccessType.Store mem_payload.Data)
        privilege mxr doSum external) := by
  apply preservesX2_of_preservesStackPointer
  apply translate_tlb_miss_preserves_stack_pointer_of svWidth asid basePpn vpn
      (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum external
  · intro ptBase level global
    exact preservesStackPointer_of_preservesX2
      (preservesX2_pt_walk_store_data svWidth vpn privilege mxr doSum external ptBase level global)
  · intro address width pte
    exact preservesStackPointer_of_preservesX2
      (preservesX2_update_and_write_pte_store_data address width pte)
  · intro ppn pte pteAddress level global
    exact preservesStackPointer_of_preservesX2
      (preservesX2_add_to_TLB svWidth asid vpn ppn pte pteAddress level global)

private theorem preservesX2_translate_store_data (svWidth : Nat)
    (asid : BitVec (if (64 == 32 : Bool) then 9 else 16))
    (basePpn : BitVec (if (svWidth == 32 : Bool) then 22 else 44)) (vpn : BitVec (svWidth - 12))
    (privilege : Privilege) (mxr doSum : Bool) (external : Unit) :
    PreservesX2
      (translate svWidth asid basePpn vpn (MemoryAccessType.Store mem_payload.Data) privilege mxr
        doSum external) := by
  apply preservesX2_of_preservesStackPointer
  apply translate_preserves_stack_pointer_of svWidth asid basePpn vpn
      (MemoryAccessType.Store mem_payload.Data) privilege mxr doSum external
  · exact preservesStackPointer_of_preservesX2 (preservesX2_lookup_TLB svWidth asid vpn)
  · intro index entry
    exact preservesStackPointer_of_preservesX2
      (preservesX2_translate_TLB_hit_store_data svWidth asid vpn privilege mxr doSum external
        index entry)
  · exact preservesStackPointer_of_preservesX2
      (preservesX2_translate_TLB_miss_store_data svWidth asid basePpn vpn privilege mxr doSum
        external)

private theorem preservesX2_translateAddr_store_data (vaddr : virtaddr) :
    PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data)) := by
  apply preservesX2_of_preservesStackPointer
  apply translate_addr_preserves_stack_pointer_of vaddr (MemoryAccessType.Store mem_payload.Data)
  · intro mstatusBits privilege
    exact preservesStackPointer_of_preservesX2
      (preservesX2_effectivePrivilege
        (MemoryAccessType.Store mem_payload.Data) mstatusBits privilege)
  · intro privilege
    exact preservesStackPointer_of_preservesX2 (preservesX2_translationMode privilege)
  · exact preservesStackPointer_of_preservesX2
      (preservesX2_is_shadow_stack_access (MemoryAccessType.Store mem_payload.Data))
  · intro mode
    exact preservesStackPointer_of_preservesX2 (preservesX2_satp_mode_width_forwards mode)
  · intro svWidth
    exact preservesStackPointer_of_preservesX2 (preservesX2_get_satp svWidth)
  · intro failure
    exact preservesStackPointer_of_preservesX2
      (preservesX2_translationException_store_data failure)
  · intro svWidth asid basePpn vpn privilege mxr doSum
    exact preservesStackPointer_of_preservesX2
      (preservesX2_translate_store_data svWidth asid basePpn vpn privilege mxr doSum init_ext_ptw)

private theorem preservesX2E_throw_memory_exception (address : virtaddr)
    (exception : ExceptionType) :
    PreservesX2E (do
      let result ← liftM (memory_exception address exception)
      let error ← pure (Sail.Err result)
      Sail.SailME.throw error : SailME (Sail.Result Bool ExecutionResult) α) := by
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (memory_exception address exception)
      (preservesX2_memory_exception address exception)
  · intro result
    apply PreservesX2E.bind
    · exact PreservesX2E.pure (Sail.Err result)
    · intro error
      exact PreservesX2E.throw error

private def vmemWriteStoreStep (bytes last step : Int) (baseVaddr : BitVec 64)
    (data : BitVec (8 * width)) (state : Bool × Nat × Bool) :
    SailME (Sail.Result Bool ExecutionResult) (Bool × Nat × Bool) :=
  (fun (finished, index, writeSuccess) => do
    liftM (Sail.assert true "loop dummy assert")
    let offset := index
    let vaddr := Sail.BitVec.addInt baseVaddr (offset *i bytes)
    let writeSuccess ← ((do
        match
          (← translateAddr (virtaddr.Virtaddr vaddr)
            (MemoryAccessType.Store mem_payload.Data)) with
      | .Err (exception, _) =>
        Sail.SailME.throw (← do
          pure (Sail.Err (← memory_exception (virtaddr.Virtaddr vaddr) exception)))
      | .Ok (paddr, pbmt, _) =>
        (do
          liftM (Sail.assert (false == false) "sys/vmem_utils.sail:197.50-197.51")
          (do
            match (← mem_write_ea paddr bytes false false false) with
            | .Err exception =>
              Sail.SailME.throw (← do
                pure (Sail.Err (← memory_exception (virtaddr.Virtaddr vaddr) exception)))
            | .Ok () =>
              (do
                let writeValue := Sail.BitVec.extractLsb data
                  (((8 *i (offset +i 1)) *i bytes) -i 1) ((8 *i offset) *i bytes)
                match (← mem_write_value paddr bytes writeValue
                    (MemoryAccessType.Store mem_payload.Data) pbmt false false false) with
                | .Err exception =>
                  Sail.SailME.throw (← do
                    pure (Sail.Err (← memory_exception (virtaddr.Virtaddr vaddr) exception)))
                | .Ok success => pure (writeSuccess && success))))) : SailME
        (Sail.Result Bool ExecutionResult) Bool)
    let (finished, index) : Bool × Nat :=
      if ((offset == last) : Bool)
      then
        (let finished : Bool := true
        (finished, index))
      else
        (let index : Nat := offset +i step
        (finished, index))
    pure (finished, index, writeSuccess)) state

private theorem preservesX2E_vmemWriteStoreStep (bytes last step : Int) (baseVaddr : BitVec 64)
    (data : BitVec (8 * width)) (state : Bool × Nat × Bool)
    (translateFrame : ∀ address,
      PreservesX2 (translateAddr address (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2E (vmemWriteStoreStep bytes last step baseVaddr data state) := by
  unfold vmemWriteStoreStep
  apply PreservesX2E.bind
  · exact PreservesX2E.lift (PreSail.assert true "loop dummy assert")
      (preservesX2_assert true "loop dummy assert")
  · intro _
    apply PreservesX2E.bind
    · apply PreservesX2E.bind
      · exact PreservesX2E.lift
          (translateAddr (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
            (MemoryAccessType.Store mem_payload.Data))
          (translateFrame _)
      · intro translation
        cases translation with
        | Err failure =>
          apply PreservesX2E.bind
          · apply PreservesX2E.bind
            · exact PreservesX2E.lift
                (memory_exception
                  (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes))) failure.1)
                (preservesX2_memory_exception
                  (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes))) failure.1)
            · intro result
              exact PreservesX2E.pure (Sail.Err result)
          · intro error
            exact PreservesX2E.throw error
        | Ok translation =>
          rcases translation with ⟨paddr, pbmt, extensionState⟩
          apply PreservesX2E.bind
          · exact PreservesX2E.lift
              (PreSail.assert (false == false) "sys/vmem_utils.sail:197.50-197.51")
              (preservesX2_assert (false == false) "sys/vmem_utils.sail:197.50-197.51")
          · intro _
            apply PreservesX2E.bind
            · exact PreservesX2E.lift (mem_write_ea paddr bytes false false false)
                (preservesX2_mem_write_ea paddr bytes)
            · intro writeEa
              cases writeEa with
              | Err exception =>
                apply PreservesX2E.bind
                · apply PreservesX2E.bind
                  · exact PreservesX2E.lift
                      (memory_exception
                        (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                        exception)
                      (preservesX2_memory_exception
                        (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                        exception)
                  · intro result
                    exact PreservesX2E.pure (Sail.Err result)
                · intro error
                  exact PreservesX2E.throw error
              | Ok _ =>
                apply PreservesX2E.bind
                · exact PreservesX2E.lift
                    (mem_write_value paddr bytes
                      (Sail.BitVec.extractLsb data
                        (((8 *i (state.2.1 +i 1)) *i bytes) -i 1)
                        ((8 *i state.2.1) *i bytes))
                      (MemoryAccessType.Store mem_payload.Data) pbmt false false false)
                    (preservesX2_mem_write_value_store paddr bytes _ pbmt)
                · intro writeResult
                  cases writeResult with
                  | Err exception =>
                    apply PreservesX2E.bind
                    · apply PreservesX2E.bind
                      · exact PreservesX2E.lift
                          (memory_exception
                            (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                            exception)
                          (preservesX2_memory_exception
                            (virtaddr.Virtaddr (Sail.BitVec.addInt baseVaddr (state.2.1 *i bytes)))
                            exception)
                      · intro result
                        exact PreservesX2E.pure (Sail.Err result)
                    · intro error
                      exact PreservesX2E.throw error
                  | Ok success =>
                    exact PreservesX2E.pure _
    · intro writeSuccess
      exact PreservesX2E.pure _

private theorem preservesX2_vmem_write_addr_store_of_translate (address : virtaddr) (width : Nat)
    (data : BitVec (8 * width))
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2 (vmem_write_addr address width data
      (MemoryAccessType.Store mem_payload.Data) false false false) := by
  unfold vmem_write_addr
  simp only [is_store_conditional, Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  apply preservesX2_sailMERun
  apply PreservesX2E.iteBind
  · exact preservesX2E_vmem_write_store_misaligned_then address
  · exact PreservesX2E.pure _
  · intro _
    apply PreservesX2E.bind
    · exact PreservesX2E.lift (split_misaligned address width)
        (preservesX2_split_misaligned address width)
    · rintro ⟨n, bytes⟩
      apply PreservesX2E.bind
      · apply PreservesX2E.bind
        · exact preservesX2E_untilFuelM n.toNat
            (fun state : Bool × Nat × Bool => pure state.1)
            (false, (misaligned_order n).1.toNat, true)
            (vmemWriteStoreStep bytes (misaligned_order n).2.1 (misaligned_order n).2.2
              (bits_of_virtaddr address) data)
            (fun _ => PreservesX2E.pure _)
            (fun state => preservesX2E_vmemWriteStoreStep bytes (misaligned_order n).2.1
              (misaligned_order n).2.2 (bits_of_virtaddr address) data state translateFrame)
        · intro loopVars
          exact PreservesX2E.pure loopVars
      · rintro ⟨finished, index, writeSuccess⟩
        exact PreservesX2E.pure (Sail.Ok writeSuccess)

private theorem preservesX2_vmem_write_store_of_translate (base : regidx) (offset : BitVec 64)
    (width : Nat) (data : BitVec (8 * width))
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2 (vmem_write base offset width data
      (MemoryAccessType.Store mem_payload.Data) false false false) := by
  unfold vmem_write
  apply preservesX2_sailMERun
  apply PreservesX2E.bind
  · apply PreservesX2E.bind
    · exact PreservesX2E.lift
        (get_transformed_data_addr base offset (MemoryAccessType.Store mem_payload.Data) width)
        (preservesX2_get_transformed_data_addr base offset
          (MemoryAccessType.Store mem_payload.Data) width)
    · intro transformed
      cases transformed with
      | Ext_DataAddr_Error error =>
        exact PreservesX2E.throw (Sail.Err (ExecutionResult.Ext_DataAddr_Check_Failure error))
      | Ext_DataAddr_OK address => exact PreservesX2E.pure address
  · intro address
    exact PreservesX2E.lift
      (vmem_write_addr address width data (MemoryAccessType.Store mem_payload.Data)
        false false false)
      (preservesX2_vmem_write_addr_store_of_translate address width data translateFrame)

private theorem preservesX2_execute_STORE_of_translate (immediate : BitVec 12)
    (sourceData sourceAddress : regidx) (width : Nat)
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    PreservesX2 (execute_STORE immediate sourceData sourceAddress width) := by
  unfold execute_STORE
  apply PreservesX2.bind
  · exact preservesX2_assert _ _
  · intro _
    apply PreservesX2.bind
    · exact preservesX2_rX_bits sourceData
    · intro bits
      apply PreservesX2.bind
      · exact PreservesX2.pure (Sail.BitVec.extractLsb bits ((width *i 8) -i 1) 0)
      · intro data
        apply PreservesX2.bind
        · exact preservesX2_vmem_write_store_of_translate sourceAddress
            (sign_extend (m := 64) immediate) width data translateFrame
        · intro writeResult
          cases writeResult <;> exact PreservesX2.pure _

private theorem execute_STORE_dispatch_preservesX2_of_translate (state : State)
    (immediate : BitVec 12) (sourceData sourceAddress : regidx) (width : Nat)
    (translateFrame : ∀ vaddr,
      PreservesX2 (translateAddr vaddr (MemoryAccessType.Store mem_payload.Data))) :
    (match (execute (.STORE (immediate, sourceData, sourceAddress, width))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  change (match (execute_STORE immediate sourceData sourceAddress width).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2
  cases hStore : execute_STORE immediate sourceData sourceAddress width state with
  | error error after =>
    simpa [EStateM.run, hStore] using
      (preservesX2_execute_STORE_of_translate immediate sourceData sourceAddress width
        translateFrame state)
  | ok value after =>
    simpa [EStateM.run, hStore] using
      (preservesX2_execute_STORE_of_translate immediate sourceData sourceAddress width
        translateFrame state)

/-- The generated STORE action preserves `x2` on normal and error outcomes. -/
theorem execute_STORE_preserves_stack_pointer (immediate : BitVec 12)
    (sourceData sourceAddress : regidx) (width : Nat) :
    PreservesStackPointer (execute_STORE immediate sourceData sourceAddress width) := by
  apply preservesStackPointer_of_preservesX2
  exact preservesX2_execute_STORE_of_translate immediate sourceData sourceAddress width
    (fun vaddr => preservesX2_translateAddr_store_data vaddr)

/-- The generated dispatcher preserves `x2` for every STORE instruction outcome. -/
theorem executeSTOREDispatchPreservesStackPointer (state : State) (immediate : BitVec 12)
    (sourceData sourceAddress : regidx) (width : Nat) :
    (match (execute (.STORE (immediate, sourceData, sourceAddress, width))).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  exact execute_STORE_dispatch_preservesX2_of_translate
    state immediate sourceData sourceAddress width
    (fun vaddr => preservesX2_translateAddr_store_data vaddr)

private theorem mem_write_ea_preserves_stack_pointer (state : State) (address : physaddr)
    (width : Nat) :
    (match (mem_write_ea address width false false false).run state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2 := by
  simp [mem_write_ea, write_kind_of_flags, write_ram_ea, EStateM.run, EStateM.bind,
    EStateM.pure, EStateM.instMonad]

end BinaryFv.RISCV
