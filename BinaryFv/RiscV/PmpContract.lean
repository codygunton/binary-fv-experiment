import BinaryFv.RiscV.FetchContract

namespace BinaryFv.RiscV

open PreSail
open Sail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType

/-- The exact finite range traversed by the generated PMP checker. -/
private def pmpLoopRange : IntRange := {
  start := 0
  stop := sys_pmp_count - 1
  step := 1
  step_pos := by omega
}

/-- The generated PMP-loop body after its preceding-address read. -/
private def pmpLoopAfterPrev (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (priv : Privilege) (index : Int)
    (previousPmpaddr : BitVec 64) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let rawConfig ← liftM (Sail.readReg pmpcfg_n)
  let config ← pure (GetElem?.getElem! rawConfig index)
  let currentPmpaddr ← liftM (pmpReadAddrReg index.toNat)
  match (← liftM (pmpMatchAddr address width config currentPmpaddr previousPmpaddr)) with
  | .PMP_NoMatch => pure ()
  | .PMP_PartialMatch =>
    SailME.throw (← do pure (some (← liftM (accessFaultFromAccessType access))))
  | .PMP_Match =>
    SailME.throw (← do
      if (((← liftM (pmpCheckRWX config access)) ||
          ((priv == .Machine) && LeanRV64DExecutable.Functions.not (pmpLocked config))) : Bool) then
        pure none
      else pure (some (← liftM (accessFaultFromAccessType access))))
  pure PUnit.unit
  pure (.yield loopVars)

/-- The generated PMP-loop body, with its exact preceding-address branch. -/
private def pmpLoopBody (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (priv : Privilege)
    (index : Int) (_ : index ∈ pmpLoopRange) (loopVars : Unit) :
    SailME (Option ExceptionType) (ForInStep Unit) := do
  let () := loopVars
  if ((index >b 0) : Bool) then do
    let previousPmpaddr ← liftM (pmpReadAddrReg (index - 1).toNat)
    pmpLoopAfterPrev address width access priv index previousPmpaddr loopVars
  else pmpLoopAfterPrev address width access priv index zeros loopVars

/-- A definitionally exact factorization of the generated Machine-mode PMP loop. -/
private def pmpCheckMachineLoop (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) : SailM (Option ExceptionType) :=
  SailME.run do
    let loopVars ← IntRange.forIn' pmpLoopRange ()
      (pmpLoopBody address (to_bits width) access .Machine)
    pure loopVars
    if ((.Machine : Privilege) == .Machine) then pure none
    else pure (some (← liftM (accessFaultFromAccessType access)))

private theorem pmpCheck_machine_loop_eq (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) :
    pmpCheck address width access .Machine = pmpCheckMachineLoop address width access := by
  unfold pmpCheck pmpCheckMachineLoop pmpLoopRange pmpLoopBody pmpLoopAfterPrev
  simp only [sys_pmp_count]
  have countNotZero : ((16 : Int) == 0) = false := rfl
  have machineEq : ((.Machine : Privilege) == .Machine) = true := rfl
  simp only [countNotZero, Bool.false_eq_true, ↓reduceIte, machineEq]
  rw [forIn_eq_forIn']
  rfl

private theorem defaultPmpCfgEntry (index : Nat) :
    ((default : Vector (BitVec 8) 64)[index]!) = (0 : BitVec 8) := by
  change (Vector.replicate 64 (0 : BitVec 8))[index]! = (0 : BitVec 8)
  rw [LawfulGetElem.getElem!_def, Vector.getElem?_replicate]
  split <;> simp_all <;> rfl

private theorem defaultPmpCfgEntryInt (index : Int) :
    ((default : Vector (BitVec 8) 64)[index]!) = (0 : BitVec 8) := by
  change ((default : Vector (BitVec 8) 64)[index.toNat]!) = (0 : BitVec 8)
  exact defaultPmpCfgEntry index.toNat

private theorem defaultPmpAddrEntry (index : Nat) :
    ((default : Vector (BitVec 64) 64)[index]!) = (0 : BitVec 64) := by
  change (Vector.replicate 64 (0 : BitVec 64))[index]! = (0 : BitVec 64)
  rw [LawfulGetElem.getElem!_def, Vector.getElem?_replicate]
  split <;> simp_all <;> rfl

private theorem pmpReadAddrReg_default (state : State) (index : Nat)
    (configRead : state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64))
    (addressRead : state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)) :
    Runs (pmpReadAddrReg index) state state (0 : BitVec 64) := by
  have matchType : Sail.BitVec.access (_get_Pmpcfg_ent_A 0#8) 1 = 0#1 := rfl
  unfold Runs pmpReadAddrReg
  simp [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, sys_pmp_grain, configRead, addressRead,
    defaultPmpCfgEntry, defaultPmpAddrEntry]
  rw [matchType]
  rfl

private theorem runsExceptTLift {ε α β : Type} (action : SailM α)
    (next : α → ExceptT ε SailM β) (before middle after : State) (value : α) (result : Except ε β)
    (hAction : Runs action before middle value)
    (hNext : Runs (ExceptT.run (next value)) middle after result) :
    Runs (ExceptT.run (do
      let current ← liftM action
      next current)) before after result := by
  change Runs (ExceptT.run ((ExceptT.lift action) >>= next)) before after result
  have runEq : ExceptT.run ((ExceptT.lift action) >>= next) = (do
      let current ← action
      ExceptT.run (next current)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.lift, ExceptT.mk,
      ExceptT.run, EStateM.instMonad]
    funext state
    cases hAction' : action state <;>
      simp [EStateM.bind, EStateM.map, ExceptT.bindCont, hAction']
  rw [runEq]
  exact Runs.bind hAction hNext

private theorem runsExceptTBind {ε α β : Type} (action : ExceptT ε SailM α)
    (next : α → ExceptT ε SailM β) (before middle after : State) (value : α) (result : Except ε β)
    (hAction : Runs (ExceptT.run action) before middle (.ok value))
    (hNext : Runs (ExceptT.run (next value)) middle after result) :
    Runs (ExceptT.run (action >>= next)) before after result := by
  have runEq : ExceptT.run (action >>= next) = (do
      let current ← ExceptT.run action
      match current with
      | .ok value => ExceptT.run (next value)
      | .error error => pure (.error error)) := by
    simp only [ExceptT.instMonad, Monad.toBind, ExceptT.bind, ExceptT.run, ExceptT.mk,
      EStateM.instMonad]
    rfl
  rw [runEq]
  exact Runs.bind hAction hNext

private theorem pmpLoopAfterPrev_default (state : State) (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (index : Int) (previousPmpaddr : BitVec 64)
    (loopVars : Unit)
    (configRead : state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64))
    (addressRead : state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)) :
    Runs (ExceptT.run
      (pmpLoopAfterPrev address width access .Machine index previousPmpaddr loopVars))
      state state (.ok (.yield loopVars)) := by
  have configRun : Runs (Sail.readReg pmpcfg_n) state state (default : Vector (BitVec 8) 64) :=
    readReg_run state pmpcfg_n _ configRead
  have currentRun : Runs (pmpReadAddrReg index.toNat) state state (0 : BitVec 64) :=
    pmpReadAddrReg_default state index.toNat configRead addressRead
  have matchRun : Runs (pmpMatchAddr address width 0#8 0#64 previousPmpaddr)
      state state .PMP_NoMatch := by
    unfold Runs pmpMatchAddr
    rfl
  unfold pmpLoopAfterPrev
  refine runsExceptTLift (action := Sail.readReg pmpcfg_n) (next := ?_)
    (before := state) (middle := state) (after := state)
    (value := (default : Vector (BitVec 8) 64))
    (result := (Except.ok (ForInStep.yield loopVars) :
      Except (Sail.Error exception ⊕ Option ExceptionType) (ForInStep Unit))) configRun ?_
  rw [defaultPmpCfgEntryInt index]
  simp
  refine runsExceptTLift (action := pmpReadAddrReg index.toNat) (next := ?_)
    (before := state) (middle := state) (after := state) (value := (0 : BitVec 64))
    (result := (Except.ok (ForInStep.yield loopVars) :
      Except (Sail.Error exception ⊕ Option ExceptionType) (ForInStep Unit))) currentRun ?_
  refine runsExceptTLift
    (action := pmpMatchAddr address width 0#8 0#64 previousPmpaddr) (next := ?_)
    (before := state) (middle := state) (after := state) (value := .PMP_NoMatch)
    (result := (Except.ok (ForInStep.yield loopVars) :
      Except (Sail.Error exception ⊕ Option ExceptionType) (ForInStep Unit))) matchRun ?_
  simp
  rfl

private theorem pmpLoopBody_default (state : State) (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload) (index : Int) (inRange : index ∈ pmpLoopRange)
    (loopVars : Unit)
    (configRead : state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64))
    (addressRead : state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)) :
    Runs (ExceptT.run (pmpLoopBody address width access .Machine index inRange loopVars))
      state state (.ok (.yield loopVars)) := by
  cases loopVars
  unfold pmpLoopBody
  by_cases positive : ((index >b 0) : Bool) = true
  · simp only [positive]
    refine runsExceptTLift (action := pmpReadAddrReg (index - 1).toNat) (next := ?_)
      (before := state) (middle := state) (after := state) (value := (0 : BitVec 64))
      (result := (Except.ok (ForInStep.yield ()) :
        Except (Sail.Error exception ⊕ Option ExceptionType) (ForInStep Unit)))
      (pmpReadAddrReg_default state (index - 1).toNat configRead addressRead) ?_
    exact pmpLoopAfterPrev_default state address width access index 0#64 () configRead addressRead
  · simp only [positive]
    exact pmpLoopAfterPrev_default state address width access index 0#64 () configRead addressRead

/-- The recursive invariant for each suffix of the exact generated sixteen-entry PMP loop. -/
private theorem loopInvariant
    (body : (index : Int) → index ∈ pmpLoopRange → Unit →
      SailME (Option ExceptionType) (ForInStep Unit))
    (state : State)
    (bodyRun : ∀ (index : Int) (inRange : index ∈ pmpLoopRange),
      Runs (ExceptT.run (body index inRange ())) state state (.ok (.yield ())))
    (index : Int) (stepDiv : (index - pmpLoopRange.start) % pmpLoopRange.step = 0) :
    Runs (ExceptT.run (IntRange.forIn'.loop pmpLoopRange body () index stepDiv))
      state state (.ok ()) := by
  unfold IntRange.forIn'.loop
  by_cases inRange : index ∈ pmpLoopRange
  · simp only [dif_pos inRange]
    refine runsExceptTBind (action := body index inRange ()) (next := ?_)
      (before := state) (middle := state) (after := state) (value := .yield ())
      (result := (Except.ok () :
        Except (Sail.Error exception ⊕ Option ExceptionType) Unit))
      (bodyRun index inRange) ?_
    exact loopInvariant body state bodyRun (index + pmpLoopRange.step) (by
      rw [Int.add_comm, Int.add_sub_assoc]
      simp_all)
  · simp only [dif_neg inRange]
    rfl
termination_by (16 - index).toNat
decreasing_by
  change (16 - (index + 1)).toNat < (16 - index).toNat
  have bounds : (0 : Int) ≤ index ∧ index ≤ 15 := by
    simpa [pmpLoopRange, sys_pmp_count, IntRange.instMemIntRange] using inRange
  omega

private theorem pmpLoop_default (state : State) (address : physaddr) (width : xlenbits)
    (access : MemoryAccessType mem_payload)
    (configRead : state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64))
    (addressRead : state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)) :
    Runs (ExceptT.run (IntRange.forIn' pmpLoopRange ()
      (pmpLoopBody address width access .Machine))) state state (.ok ()) := by
  unfold IntRange.forIn'
  exact loopInvariant (pmpLoopBody address width access .Machine) state
    (fun index inRange => pmpLoopBody_default state address width access index inRange ()
      configRead addressRead) pmpLoopRange.start (by simp)

private theorem runsSailMERunOfOk {α : Type} (action : SailME α α)
    (before after : State) (result : α)
    (hAction : Runs (ExceptT.run action) before after (.ok result)) :
    Runs (SailME.run action) before after result := by
  unfold Runs at hAction
  unfold Runs Sail.SailME.run PreSail.PreSailME.run
  simp only [EStateM.instMonad]
  unfold EStateM.bind
  unfold EStateM.run at hAction ⊢
  dsimp
  rw [hAction]
  rfl

private theorem pmpCheckMachineLoop_default (state : State) (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload)
    (configRead : state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64))
    (addressRead : state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)) :
    Runs (pmpCheckMachineLoop address width access) state state none := by
  unfold pmpCheckMachineLoop
  apply runsSailMERunOfOk
  refine runsExceptTBind
    (action := IntRange.forIn' pmpLoopRange ()
      (pmpLoopBody address (to_bits width) access .Machine))
    (next := ?_)
    (before := state) (middle := state) (after := state)
    (value := ())
    (result := (Except.ok none :
      Except (Sail.Error exception ⊕ Option ExceptionType) (Option ExceptionType)))
    (pmpLoop_default state address (to_bits width) access configRead addressRead) ?_
  rfl

/-- Default PMP registers make the generated Machine-mode PMP check succeed without a fault. -/
theorem pmpCheck_machine_of_disabled (state : State) (address : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload) (disabled : FetchPmpDisabled state) :
    Runs (pmpCheck address width access .Machine) state state none := by
  rcases disabled with ⟨configRead, addressRead⟩
  rw [pmpCheck_machine_loop_eq]
  exact pmpCheckMachineLoop_default state address width access configRead addressRead

end BinaryFv.RiscV
