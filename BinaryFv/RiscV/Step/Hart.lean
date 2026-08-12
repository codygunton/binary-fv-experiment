import BinaryFv.RiscV.Logic.Framing

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Run an ordinary generated Sail action before a `SailME` continuation. -/
theorem exceptTRunLiftBind {α : Type} (action : SailM α) (next : α → SailME Step Step) :
    ExceptT.run (do
      let current ← liftM action
      next current) = (do
        let current ← action
        ExceptT.run (next current)) := by
  change ExceptT.run ((ExceptT.lift action) >>= next) = _
  funext state
  change EStateM.bind (EStateM.map Except.ok action) (ExceptT.bindCont next) state =
    EStateM.bind action (fun current => ExceptT.run (next current)) state
  unfold EStateM.bind EStateM.map
  cases hAction : action state <;> rfl

/-- Eliminate the generated `SailME.run` wrapper around an ordinary Sail-action bind. -/
theorem sailMERunLiftBind {α : Type} (action : SailM α) (next : α → SailME Step Step) :
    Sail.SailME.run (do
      let current ← liftM action
      next current) = (do
        let current ← action
        Sail.SailME.run (next current)) := by
  unfold Sail.SailME.run PreSail.PreSailME.run
  rw [exceptTRunLiftBind]
  funext state
  simp

/-- Compose an ordinary generated Sail-action contract with a `SailME` continuation contract. -/
theorem runsSailMELift {α : Type} (action : SailM α) (next : α → SailME Step Step)
    (before middle after : State) (value : α) (result : Step)
    (hAction : Runs action before middle value)
    (hNext : Runs (Sail.SailME.run (next value)) middle after result) :
    Runs (Sail.SailME.run (do
      let current ← liftM action
      next current)) before after result := by
  rw [sailMERunLiftBind]
  exact Runs.bind hAction hNext

/-- Compose the generated no-interrupt, base-instruction, non-landing-pad retirement path. -/
theorem runHartActiveBaseRetires (stepNo : Nat) (before afterFetch afterNext afterExec : State)
    (privilege : Privilege) (word : BitVec 32) (instruction : instruction) (pc : BitVec 64)
    (hPrivilege : before.regs.get? cur_privilege = some privilege)
    (hDispatch : Runs (dispatchInterrupt privilege) before before none)
    (hFetch : Runs (fetch ()) before afterFetch (.F_Base word))
    (hDecode : Runs (ext_decode word) afterFetch afterFetch instruction)
    (hNoLandingPad : Runs (is_landing_pad_expected ()) afterFetch afterFetch false)
    (hPc : afterFetch.regs.get? PC = some pc)
    (hNextPc : Runs (Sail.writeReg nextPC (Sail.BitVec.addInt pc 4))
      afterFetch afterNext PUnit.unit)
    (hExecute : Runs (execute instruction) afterNext afterExec (.Retire_Success ())) :
    Runs (run_hart_active stepNo) before afterExec
      (.Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) := by
  have hReadPrivilege : Runs (Sail.readReg cur_privilege) before before privilege := by
    exact readReg_run before cur_privilege privilege hPrivilege
  have hReadPc : Runs (Sail.readReg PC) afterFetch afterFetch pc := by
    exact readReg_run afterFetch PC pc hPc
  unfold run_hart_active
  refine runsSailMELift (action := Sail.readReg cur_privilege) (next := ?_)
    (before := before) (middle := before) (after := afterExec) (value := privilege)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word))
    hReadPrivilege ?_
  refine runsSailMELift (action := dispatchInterrupt privilege) (next := ?_)
    (before := before) (middle := before) (after := afterExec) (value := none)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hDispatch ?_
  simp [ext_fetch_hook, get_config_print_instr]
  refine runsSailMELift (action := fetch ()) (next := ?_)
    (before := before) (middle := afterFetch) (after := afterExec) (value := .F_Base word)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hFetch ?_
  simp only
  refine runsSailMELift (action := ext_decode word) (next := ?_)
    (before := afterFetch) (middle := afterFetch) (after := afterExec) (value := instruction)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hDecode ?_
  refine runsSailMELift (action := is_landing_pad_expected ()) (next := ?_)
    (before := afterFetch) (middle := afterFetch) (after := afterExec) (value := false)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hNoLandingPad ?_
  simp
  refine runsSailMELift (action := Sail.readReg PC) (next := ?_)
    (before := afterFetch) (middle := afterFetch) (after := afterExec) (value := pc)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hReadPc ?_
  refine runsSailMELift
    (action := Sail.writeReg nextPC (Sail.BitVec.addInt pc 4)) (next := ?_)
    (before := afterFetch) (middle := afterNext) (after := afterExec) (value := PUnit.unit)
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hNextPc ?_
  refine runsSailMELift (action := execute instruction) (next := ?_)
    (before := afterNext) (middle := afterExec) (after := afterExec)
    (value := .Retire_Success ())
    (result := .Step_Execute (.Retire_Success (), zero_extend (m := 32) word)) hExecute ?_
  simp
  unfold Runs Sail.SailME.run PreSail.PreSailME.run
  simp

/-- The generated `nextPC` write has the standard register-update contract. -/
theorem writeNextPc_run (state : State) (pc : BitVec 64) :
    Runs (Sail.writeReg nextPC (Sail.BitVec.addInt pc 4)) state
      { state with regs := state.regs.insert nextPC (Sail.BitVec.addInt pc 4) } PUnit.unit := by
  exact writeReg_run state nextPC (Sail.BitVec.addInt pc 4)

end BinaryFv.RiscV
