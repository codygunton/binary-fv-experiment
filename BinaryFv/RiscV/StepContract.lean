import BinaryFv.RiscV.Framing

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The hart-state selector used verbatim by generated `try_step`. -/
def activeHartStep (stepNo : Nat) (exitWait : Bool) : SailM Step := do
  match (← Sail.readReg hart_state) with
  | .HART_WAITING (reason, bits) => run_hart_waiting stepNo reason bits exitWait
  | .HART_ACTIVE () => run_hart_active stepNo

/-- `activeHartStep` is definitionally the generated selector immediately before its postlude. -/
theorem activeHartStep_eq_generated_action (stepNo : Nat) (exitWait : Bool) :
    (do
      match (← Sail.readReg hart_state) with
      | .HART_WAITING (reason, bits) => run_hart_waiting stepNo reason bits exitWait
      | .HART_ACTIVE () => run_hart_active stepNo : SailM Step) =
        activeHartStep stepNo exitWait := by
  rfl

/-- `activeHartStep` is definitionally the generated selector immediately before its postlude. -/
theorem activeHartStep_eq_generated (stepNo : Nat) (exitWait : Bool) (state : State) :
    (do
      match (← Sail.readReg hart_state) with
      | .HART_WAITING (reason, bits) => run_hart_waiting stepNo reason bits exitWait
      | .HART_ACTIVE () => run_hart_active stepNo : SailM Step).run state =
        (activeHartStep stepNo exitWait).run state := by
  rfl

/-- Lift a generated active-hart step contract through the selector used by `try_step`. -/
theorem activeHartStep_active (stepNo : Nat) (exitWait : Bool) (before after : State)
    (result : Step) (hHart : before.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hActive : Runs (run_hart_active stepNo) before after result) :
    Runs (activeHartStep stepNo exitWait) before after result := by
  unfold Runs at hActive ⊢
  simp only [activeHartStep, EStateM.run, EStateM.bind, EStateM.instMonad,
    PreSail.readReg, EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hHart]
  exact hActive

/-- Lift a normal generated active-hart retirement through the authoritative `try_step` postlude. -/
theorem tryStepRetires (stepNo : Nat) (before afterInc afterActive afterPc afterRetired : State)
    (privilege : Privilege) (retired : BitVec 64) (instbits : BitVec 32)
    (hPrivilege : before.regs.get? cur_privilege = some privilege)
    (hShouldInc : Runs (should_inc_minstret privilege) before before true)
    (hInc : Runs (Sail.writeReg minstret_increment true) before afterInc PUnit.unit)
    (hHartPre : afterInc.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hActive : Runs (run_hart_active stepNo) afterInc afterActive
      (.Step_Execute (.Retire_Success (), instbits)))
    (hHartPost : afterActive.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hTick : Runs (tick_pc ()) afterActive afterPc ())
    (hIncrement : afterPc.regs.get? minstret_increment = some true)
    (hRetired : afterPc.regs.get? minstret = some retired)
    (hWriteRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      afterPc afterRetired PUnit.unit) :
    Runs (try_step stepNo false) before afterRetired false := by
  have hReadPrivilege : Runs (Sail.readReg cur_privilege) before before privilege := by
    unfold Runs
    simp only [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.instMonad,
      EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hPrivilege]
  have hSelected : Runs (activeHartStep stepNo false) afterInc afterActive
      (.Step_Execute (.Retire_Success (), instbits)) :=
    activeHartStep_active stepNo false afterInc afterActive _ hHartPre hActive
  change Runs (do
    let currentPrivilege ← Sail.readReg cur_privilege
    let shouldIncrement ← should_inc_minstret currentPrivilege
    Sail.writeReg minstret_increment shouldIncrement
    let stepValue ← activeHartStep stepNo false
    _) before afterRetired false
  apply Runs.bind hReadPrivilege
  apply Runs.bind hShouldInc
  apply Runs.bind hInc
  apply Runs.bind hSelected
  simp only
  have hReadHart : Runs (Sail.readReg hart_state) afterActive afterActive (.HART_ACTIVE ()) := by
    unfold Runs
    simp only [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.instMonad,
      EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hHartPost]
  have hAssert : Runs (Sail.assert (hart_is_active (.HART_ACTIVE ()))
      "postlude/step.sail:219.74-219.75") afterActive afterActive () := by
    unfold Runs
    simp [Sail.assert, PreSail.assert, EStateM.run, EStateM.instMonad, EStateM.pure,
      hart_is_active]
  have hReadIncrement : Runs (Sail.readReg minstret_increment) afterPc afterPc true := by
    unfold Runs
    simp only [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.instMonad,
      EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hIncrement]
  have hReadRetired : Runs (Sail.readReg minstret) afterPc afterPc retired := by
    unfold Runs
    simp only [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.instMonad,
      EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hRetired]
  apply Runs.bind hReadHart
  apply Runs.bind hAssert
  apply Runs.bind hReadHart
  apply Runs.bind hTick
  apply Runs.bind hReadIncrement
  simp
  apply Runs.bind hReadRetired
  apply Runs.bind hWriteRetired
  unfold Runs
  simp [get_config_rvfi, EStateM.run, EStateM.instMonad, EStateM.pure]

end BinaryFv.RiscV
