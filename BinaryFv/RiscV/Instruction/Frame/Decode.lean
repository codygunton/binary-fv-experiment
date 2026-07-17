import BinaryFv.RiscV.Logic.ReadFrame

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open extension

private def StateProjection (action : SailM α) : Prop :=
  ∀ (state : State),
    (match action state with
    | .ok _ state' => state'
    | .error _ state' => state') = state

private theorem stateProjection_pure (value : α) : StateProjection (pure value : SailM α) := by
  intro state
  rfl

private theorem stateProjection_throw (error : Sail.Error exception) :
    StateProjection (throw error : SailM α) := by
  intro state
  rfl

private theorem stateProjection_bind (first : SailM α) (next : α → SailM β)
    (firstFrame : StateProjection first) (nextFrame : ∀ value, StateProjection (next value)) :
    StateProjection (first >>= next) := by
  intro state
  cases hFirst : first state with
  | error error middle =>
    simpa [EStateM.bind, EStateM.instMonad, hFirst] using firstFrame state
  | ok value middle =>
    have hMiddle : middle = state := by simpa [hFirst] using firstFrame state
    subst middle
    cases hNext : next value state with
    | error error after =>
      simpa [EStateM.bind, EStateM.instMonad, hFirst, hNext] using nextFrame value state
    | ok result after =>
      simpa [EStateM.bind, EStateM.instMonad, hFirst, hNext] using nextFrame value state

private theorem stateProjection_ite (condition : Bool) (whenTrue whenFalse : SailM α)
    (trueFrame : StateProjection whenTrue) (falseFrame : StateProjection whenFalse) :
    StateProjection (if condition then whenTrue else whenFalse) := by
  cases condition <;> assumption

private theorem stateProjection_assert (condition : Bool) (message : String) :
    StateProjection (PreSail.assert condition message : SailM Unit) := by
  unfold PreSail.assert
  apply stateProjection_ite
  · exact stateProjection_pure _
  · exact stateProjection_throw _

private theorem stateProjection_patternFailure (message : String) :
    StateProjection (do
      assert false message
      throw Sail.Error.Exit : SailM α) := by
  apply stateProjection_bind
  · exact stateProjection_assert _ _
  · intro _
    exact stateProjection_throw _

private theorem encdec_reg_state_projection (bits : BitVec 5) :
    StateProjection (encdec_reg_backwards bits) := by
  unfold encdec_reg_backwards
  apply stateProjection_ite
  · exact stateProjection_pure _
  · apply stateProjection_bind
    · exact stateProjection_assert _ _
    · intro _
      exact stateProjection_throw _

private theorem encdec_uop_state_projection (bits : BitVec 7) :
    StateProjection (encdec_uop_backwards bits) := by
  unfold encdec_uop_backwards
  split <;> first | exact stateProjection_pure _ | exact stateProjection_patternFailure _

private theorem encdec_bop_state_projection (bits : BitVec 3) :
    StateProjection (encdec_bop_backwards bits) := by
  unfold encdec_bop_backwards
  split <;> first | exact stateProjection_pure _ | exact stateProjection_patternFailure _

private theorem encdec_iop_state_projection (bits : BitVec 3) :
    StateProjection (encdec_iop_backwards bits) := by
  unfold encdec_iop_backwards
  split <;> first | exact stateProjection_pure _ | exact stateProjection_patternFailure _

private theorem encdec_sop_state_projection (bits : BitVec 3) :
    StateProjection (encdec_sop_backwards bits) := by
  unfold encdec_sop_backwards
  split <;> first | exact stateProjection_pure _ | exact stateProjection_patternFailure _

private theorem encdec_mul_op_state_projection (bits : BitVec 3) :
    StateProjection (encdec_mul_op_backwards bits) := by
  unfold encdec_mul_op_backwards
  split <;> first | exact stateProjection_pure _ | exact stateProjection_patternFailure _

private theorem readReg_stateProjection (register : Register) :
    StateProjection (readReg register : SailM (RegisterType register)) := by
  intro state
  cases hRead : state.regs.get? register <;>
    simp [PreSail.readReg, EStateM.bind, EStateM.get, EStateM.pure,
      EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, MonadState.get,
      MonadStateOf.get, getThe, hRead] <;> rfl

private theorem currentlyEnabled_m_state_projection :
    StateProjection (currentlyEnabled Ext_M) := by
  rw [currentlyEnabled.eq_59]
  apply stateProjection_bind
  · exact readReg_stateProjection misa
  · intro _
    exact stateProjection_pure _

private theorem currentlyEnabled_zicsr_state_projection :
    StateProjection (currentlyEnabled Ext_Zicsr) := by
  rw [currentlyEnabled.eq_61]
  all_goals try simp
  exact stateProjection_pure _

private theorem currentlyEnabled_s_state_projection :
    StateProjection (currentlyEnabled Ext_S) := by
  rw [currentlyEnabled.eq_20]
  apply stateProjection_bind
  · exact readReg_stateProjection misa
  · intro _
    apply stateProjection_bind
    · exact currentlyEnabled_zicsr_state_projection
    · intro _
      exact stateProjection_pure _

private theorem currentlyEnabled_zmmul_state_projection :
    StateProjection (currentlyEnabled Ext_Zmmul) := by
  rw [currentlyEnabled.eq_60]
  apply stateProjection_bind
  · exact currentlyEnabled_m_state_projection
  · intro _
    exact stateProjection_pure _

private theorem currentlyEnabled_sv32_state_projection :
    StateProjection (currentlyEnabled Ext_Sv32) := by
  rw [currentlyEnabled.eq_23]
  apply stateProjection_bind
  · exact currentlyEnabled_s_state_projection
  · intro _
    exact stateProjection_pure _

private theorem currentlyEnabled_sv39_state_projection :
    StateProjection (currentlyEnabled Ext_Sv39) := by
  rw [currentlyEnabled.eq_24]
  apply stateProjection_bind
  · exact currentlyEnabled_s_state_projection
  · intro _
    exact stateProjection_pure _

private theorem currentlyEnabled_sv48_state_projection :
    StateProjection (currentlyEnabled Ext_Sv48) := by
  rw [currentlyEnabled.eq_25]
  apply stateProjection_bind
  · exact currentlyEnabled_s_state_projection
  · intro _
    exact stateProjection_pure _

private theorem currentlyEnabled_sv57_state_projection :
    StateProjection (currentlyEnabled Ext_Sv57) := by
  rw [currentlyEnabled.eq_26]
  apply stateProjection_bind
  · exact currentlyEnabled_s_state_projection
  · intro _
    exact stateProjection_pure _

private theorem virtualMemorySupported_state_projection :
    StateProjection (virtual_memory_supported ()) := by
  unfold virtual_memory_supported
  apply stateProjection_bind
  · exact currentlyEnabled_sv32_state_projection
  · intro _
    apply stateProjection_bind
    · exact currentlyEnabled_sv39_state_projection
    · intro _
      apply stateProjection_bind
      · exact currentlyEnabled_sv48_state_projection
      · intro _
        apply stateProjection_bind
        · exact currentlyEnabled_sv57_state_projection
        · intro _
          exact stateProjection_pure _

private theorem readSenvcfg_state_projection : StateProjection (read_senvcfg ()) := by
  unfold read_senvcfg
  apply stateProjection_bind
  · exact readReg_stateProjection senvcfg
  · intro _
    apply stateProjection_bind
    · exact readReg_stateProjection menvcfg
    · intro _
      apply stateProjection_bind
      · exact readReg_stateProjection senvcfg
      · intro _
        exact stateProjection_pure _

private theorem internalError_state_projection (file : String) (line : Int) (message : String) :
    StateProjection (internal_error file line message : SailM α) := by
  unfold internal_error Sail.sailThrow PreSail.sailThrow
  exact stateProjection_throw _

private theorem getXLPE_state_projection (privilege : Privilege) :
    StateProjection (get_xLPE privilege) := by
  cases privilege
  · rw [get_xLPE.eq_3]
    apply stateProjection_bind
    · exact currentlyEnabled_s_state_projection
    · intro _
      apply stateProjection_ite
      · apply stateProjection_bind
        · exact readSenvcfg_state_projection
        · intro _
          exact stateProjection_pure _
      · apply stateProjection_bind
        · exact readReg_stateProjection menvcfg
        · intro _
          exact stateProjection_pure _
  · rw [get_xLPE.eq_5]
    exact internalError_state_projection _ _ _
  · rw [get_xLPE.eq_2]
    apply stateProjection_bind
    · exact readReg_stateProjection menvcfg
    · intro _
      exact stateProjection_pure _
  · rw [get_xLPE.eq_4]
    exact internalError_state_projection _ _ _
  · rw [get_xLPE.eq_1]
    apply stateProjection_bind
    · exact readReg_stateProjection mseccfg
    · intro _
      exact stateProjection_pure _

private theorem currentlyEnabled_zicfilp_state_projection :
    StateProjection (currentlyEnabled Ext_Zicfilp) := by
  rw [currentlyEnabled.eq_49]
  apply stateProjection_bind
  · exact currentlyEnabled_zicsr_state_projection
  · intro _
    apply stateProjection_bind
    · exact readReg_stateProjection cur_privilege
    · intro privilege
      apply stateProjection_bind
      · exact getXLPE_state_projection privilege
      · intro _
        exact stateProjection_pure _

private theorem extDecode_stateProjection (word : BitVec 32) :
    StateProjection (ext_decode word) := by
  unfold ext_decode encdec_backwards
  apply stateProjection_bind
  · apply stateProjection_bind
    · exact currentlyEnabled_zicfilp_state_projection
    · intro _
      apply stateProjection_ite
      · exact stateProjection_pure _
      · apply stateProjection_ite
        · apply stateProjection_bind
          · exact encdec_reg_state_projection _
          · intro _
            apply stateProjection_bind
            · exact encdec_uop_state_projection _
            · intro _
              exact stateProjection_pure _
        · exact stateProjection_pure _
  · intro decoded
    cases decoded with
    | some _ => exact stateProjection_pure _
    | none =>
      repeat' first
      | exact virtualMemorySupported_state_projection
      | exact currentlyEnabled_m_state_projection
      | exact currentlyEnabled_zmmul_state_projection
      | apply stateProjection_bind
      | apply stateProjection_ite
      | exact encdec_reg_state_projection _
      | exact encdec_uop_state_projection _
      | exact encdec_bop_state_projection _
      | exact encdec_iop_state_projection _
      | exact encdec_sop_state_projection _
      | exact encdec_mul_op_state_projection _
      | exact stateProjection_pure _
      | (intro value; cases value)

/-- The generated external decoder leaves the concrete generated state unchanged. -/
theorem ext_decode_state_projection (state : State) (word : BitVec 32) :
    (match (ext_decode word).run state with
    | .ok _ state' => state'
    | .error _ state' => state') = state := by
  change (match ext_decode word state with
    | .ok _ state' => state'
    | .error _ state' => state') = state
  have frame := extDecode_stateProjection word
  cases hAction : ext_decode word state <;> simpa [hAction] using frame state

end BinaryFv.RiscV
