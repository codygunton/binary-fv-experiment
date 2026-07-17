import BinaryFv.RiscV.Platform.ExtensionFrame
import BinaryFv.RiscV.Platform.HtifFrame
import BinaryFv.RiscV.Platform.TranslationFrame

/-!
# The `PreservesX2` calculus

The monadic calculus for 'this action leaves `x2` alone', over `SailM`, `ExceptT`, and `SailME`,
plus the primitive frames it is assembled from.
-/

namespace BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

def PreservesX2 (action : SailM α) : Prop :=
  ∀ state,
    (match action state with
    | .ok _ state' => state'.regs.get? x2
    | .error _ state' => state'.regs.get? x2) = state.regs.get? x2

theorem PreservesX2.bind (first : SailM α) (next : α → SailM β)
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

theorem PreservesX2.pure (value : α) : PreservesX2 (pure value : SailM α) := by
  intro state
  rfl

theorem PreservesX2.throw (error : Sail.Error exception) :
    PreservesX2 (EStateM.throw error : SailM α) := by
  intro state
  rfl

theorem PreservesX2.writeReg (written : Register)
    (value : RegisterType written) (doesNotWriteX2 : x2 ≠ written) :
    PreservesX2 (writeReg written value) := by
  intro before
  change (match (PreSail.writeReg written value : SailM PUnit).run before with
    | .ok _ after => after.regs.get? x2
    | .error _ after => after.regs.get? x2) = before.regs.get? x2
  rw [writeReg_run]
  exact writeReg_read_unchanged before written x2 value doesNotWriteX2

theorem PreservesX2.map (action : SailM α) (function : α → β)
    (actionFrame : PreservesX2 action) : PreservesX2 (function <$> action) := by
  exact PreservesX2.bind action (fun value => (EStateM.pure (function value) : SailM β)) actionFrame
    (fun _ => PreservesX2.pure _)

theorem PreservesX2.ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : PreservesX2 whenTrue) (falseFrame : PreservesX2 whenFalse) :
    PreservesX2 (if condition then whenTrue else whenFalse) := by
  cases condition
  · exact falseFrame
  · exact trueFrame

theorem preservesX2_assert (condition : Bool) (message : String) :
    PreservesX2 (PreSail.assert condition message : SailM Unit) := by
  unfold PreSail.assert
  exact PreservesX2.ite condition (EStateM.pure ())
    (EStateM.throw (Sail.Error.Assertion message)) (PreservesX2.pure _)
    (PreservesX2.throw _)

theorem preservesX2_privLevel_bits_forwards (arg : BitVec 2 × BitVec 1) :
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

abbrev PreservesX2E (action : SailME ε α) : Prop :=
  PreservesX2 (ExceptT.run action)

theorem preservesStackPointer_of_preservesX2 (frame : PreservesX2 action) :
    PreservesStackPointer action := by
  simpa only [PreservesX2, PreservesStackPointer] using frame

theorem preservesX2_of_preservesStackPointer (frame : PreservesStackPointer action) :
    PreservesX2 action := by
  simpa only [PreservesX2, PreservesStackPointer] using frame

theorem PreservesX2E.lift (action : SailM α) (actionFrame : PreservesX2 action) :
    PreservesX2E (liftM action : SailME ε α) := by
  change PreservesX2 (ExceptT.run (liftM action : SailME ε α))
  simpa only [ExceptT.run, ExceptT.mk, MonadLift.monadLift] using
    PreservesX2.map action (fun value =>
      (Except.ok value : Except (Sail.Error exception ⊕ ε) α)) actionFrame

theorem PreservesX2E.bind (first : SailME ε α) (next : α → SailME ε β)
    (firstFrame : PreservesX2E first) (nextFrame : ∀ value, PreservesX2E (next value)) :
    PreservesX2E (first >>= next) := by
  change PreservesX2 (ExceptT.run first >>= ExceptT.bindCont next)
  apply PreservesX2.bind
  · exact firstFrame
  · intro result
    cases result with
    | error error => exact PreservesX2.pure _
    | ok value => exact nextFrame value

theorem PreservesX2E.pure (value : α) : PreservesX2E (pure value : SailME ε α) := by
  change PreservesX2 (ExceptT.run (ExceptT.pure value : SailME ε α))
  exact PreservesX2.pure _

theorem PreservesX2E.throw (error : ε) :
    PreservesX2E (Sail.SailME.throw error : SailME ε α) := by
  change PreservesX2 (ExceptT.run (Sail.SailME.throw error : SailME ε α))
  unfold Sail.SailME.throw PreSail.PreSailME.throw
  exact PreservesX2.pure _

theorem PreservesX2E.throwBind (error : ε) (next : α → SailME ε β) :
    PreservesX2E (Sail.SailME.throw error >>= next) := by
  change PreservesX2 (ExceptT.run (Sail.SailME.throw error >>= next))
  simp [Sail.SailME.throw, PreSail.PreSailME.throw, ExceptT.run]
  exact PreservesX2.pure _

theorem PreservesX2E.ite (condition : Bool) (whenTrue whenFalse : SailME ε α)
    (trueFrame : PreservesX2E whenTrue) (falseFrame : PreservesX2E whenFalse) :
    PreservesX2E (if condition then whenTrue else whenFalse) := by
  cases condition
  · exact falseFrame
  · exact trueFrame

theorem PreservesX2E.iteBind (condition : Bool) (whenTrue whenFalse : SailME ε α)
    (next : α → SailME ε β) (trueFrame : PreservesX2E whenTrue)
    (falseFrame : PreservesX2E whenFalse) (nextFrame : ∀ value, PreservesX2E (next value)) :
    PreservesX2E (do
      let value ← if condition then whenTrue else whenFalse
      next value) := by
  apply PreservesX2E.ite
  · exact PreservesX2E.bind whenTrue next trueFrame nextFrame
  · exact PreservesX2E.bind whenFalse next falseFrame nextFrame

theorem preservesX2E_untilFuelM (fuel : Nat) (condition : α → SailME ε Bool)
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

theorem preservesX2_sailMERun (action : SailME α α) (actionFrame : PreservesX2E action) :
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

theorem preservesX2_readReg (register : Register) : PreservesX2 (readReg register) := by
  intro state
  cases hRead : state.regs.get? register <;>
    simp [PreSail.readReg, EStateM.bind, EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, MonadState.get,
      MonadStateOf.get, getThe, hRead] <;> rfl

theorem preservesX2_writeByte (address : Nat) (value : BitVec 8) :
    PreservesX2 (PreSail.writeByte address value : SailM PUnit) := by
  intro state
  rfl

theorem preservesX2_list_forM (xs : List α) (action : α → SailM PUnit)
    (actionFrame : ∀ value, PreservesX2 (action value)) : PreservesX2 (xs.forM action) := by
  induction xs with
  | nil => exact PreservesX2.pure _
  | cons value remaining induction =>
    simp only [List.forM]
    exact PreservesX2.bind (action value) (fun _ => remaining.forM action)
      (actionFrame value) (fun _ => induction)

theorem preservesX2_writeBytes (address : Nat) (value : BitVec (8 * width)) :
    PreservesX2 (PreSail.writeBytes address value : SailM Bool) := by
  unfold PreSail.writeBytes
  apply PreservesX2.bind
  · apply preservesX2_list_forM
    intro byte
    exact preservesX2_writeByte byte.1 byte.2
  · intro _
    exact PreservesX2.pure _

theorem preservesX2_sail_mem_write [Sail.ConcurrencyInterfaceV1.Arch]
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

theorem preservesX2_write_ram (kind : write_kind) (address : physaddr) (width : Nat)
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

end BinaryFv.RiscV
