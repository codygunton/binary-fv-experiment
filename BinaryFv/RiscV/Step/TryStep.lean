import BinaryFv.RiscV.Logic.Framing

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
  unfold activeHartStep
  exact Runs.bind (readReg_run before hart_state (.HART_ACTIVE ()) hHart) hActive

/--
The authoritative `try_step` postlude for a **retiring** step, taking the hart-state selector's own
run as a premise.

This is `tryStepRetires` with its two active-hart hypotheses replaced by the one fact they were only
ever used to build. Nothing after the selector inspects *which* branch produced the retirement, so
the postlude is genuinely branch-agnostic: the wait-wakeup branch (`run_hart_waiting` returning
`Retire_Success` after clearing `hart_state`) retires through exactly this lemma.
-/
theorem tryStepRetiresOfSelected (stepNo : Nat)
    (before afterInc afterActive afterPc afterRetired : State)
    (privilege : Privilege) (retired : BitVec 64) (instbits : BitVec 32)
    (hPrivilege : before.regs.get? cur_privilege = some privilege)
    (hShouldInc : Runs (should_inc_minstret privilege) before before true)
    (hInc : Runs (Sail.writeReg minstret_increment true) before afterInc PUnit.unit)
    (hSelected : Runs (activeHartStep stepNo false) afterInc afterActive
      (.Step_Execute (.Retire_Success (), instbits)))
    (hHartPost : afterActive.regs.get? hart_state = some (.HART_ACTIVE ()))
    (hTick : Runs (tick_pc ()) afterActive afterPc ())
    (hIncrement : afterPc.regs.get? minstret_increment = some true)
    (hRetired : afterPc.regs.get? minstret = some retired)
    (hWriteRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      afterPc afterRetired PUnit.unit) :
    Runs (try_step stepNo false) before afterRetired false := by
  have hReadPrivilege : Runs (Sail.readReg cur_privilege) before before privilege := by
    exact readReg_run before cur_privilege privilege hPrivilege
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
    exact readReg_run afterActive hart_state (.HART_ACTIVE ()) hHartPost
  have hAssert : Runs (Sail.assert (hart_is_active (.HART_ACTIVE ()))
      "postlude/step.sail:219.74-219.75") afterActive afterActive () := by
    unfold Runs
    change EStateM.pure () afterActive = EStateM.Result.ok () afterActive
    rfl
  have hReadIncrement : Runs (Sail.readReg minstret_increment) afterPc afterPc true := by
    exact readReg_run afterPc minstret_increment true hIncrement
  have hReadRetired : Runs (Sail.readReg minstret) afterPc afterPc retired := by
    exact readReg_run afterPc minstret retired hRetired
  apply Runs.bind hReadHart
  apply Runs.bind hAssert
  apply Runs.bind hReadHart
  apply Runs.bind hTick
  apply Runs.bind hReadIncrement
  simp
  apply Runs.bind hReadRetired
  apply Runs.bind hWriteRetired
  unfold Runs
  change EStateM.pure false afterRetired = EStateM.Result.ok false afterRetired
  rfl

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
    Runs (try_step stepNo false) before afterRetired false :=
  tryStepRetiresOfSelected stepNo before afterInc afterActive afterPc afterRetired privilege
    retired instbits hPrivilege hShouldInc hInc
    (activeHartStep_active stepNo false afterInc afterActive _ hHartPre hActive)
    hHartPost hTick hIncrement hRetired hWriteRetired

end BinaryFv.RiscV
