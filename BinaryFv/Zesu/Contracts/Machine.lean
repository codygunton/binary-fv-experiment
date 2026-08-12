import BinaryFv

/-!
# Machine traces and relational contracts for the SSZ proof root

The historical target-specific trace stack is not a dependency of the replacement proof root. This
file keeps the required interface small: actual Sail `try_step` execution, exact PC confinement, a
positive bounded trace, an allowed semantic outcome, and a machine exit relation.
-/

namespace BinaryFv.Zesu

open PreSail LeanRV64DExecutable.Functions Register

abbrev MachineState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def MachineStep (stepNo : Nat) (before after : MachineState) : Prop :=
  (try_step stepNo false).run before = .ok false after

def MachinePc (state : MachineState) : Option (BitVec 64) :=
  state.regs.get? PC

/-- A sequence of steps whose pre-step PCs all belong to `region`. The state and step relation are
parameters because the linked endpoint combines Sail instruction steps with explicit Linux syscalls. -/
inductive ConfinedTrace {State : Type} (stepRelation : Nat → State → State → Prop)
    (statePc : State → Option (BitVec 64)) (region : BitVec 64 → Prop) :
    Nat → Nat → State → State → Prop where
  | refl (fromStep : Nat) (state : State) :
      ConfinedTrace stepRelation statePc region fromStep 0 state state
  | step (fromStep count : Nat) (pc : BitVec 64) (before middle after : State)
      (atPc : statePc before = some pc)
      (inside : region pc)
      (machineStep : stepRelation fromStep before middle)
      (rest : ConfinedTrace stepRelation statePc region (fromStep + 1) count middle after) :
      ConfinedTrace stepRelation statePc region fromStep (count + 1) before after

theorem ConfinedTrace.weaken {State : Type} {stepRelation : Nat → State → State → Prop}
    {statePc : State → Option (BitVec 64)} {narrow wide : BitVec 64 → Prop}
    (subset : ∀ pc, narrow pc → wide pc) {fromStep count : Nat} {before after : State}
    (trace : ConfinedTrace stepRelation statePc narrow fromStep count before after) :
    ConfinedTrace stepRelation statePc wide fromStep count before after := by
  induction trace with
  | refl => exact .refl _ _
  | step fromStep count pc before middle after atPc inside machineStep rest ih =>
      exact .step fromStep count pc before middle after atPc (subset pc inside) machineStep ih

theorem ConfinedTrace.append {State : Type} {stepRelation : Nat → State → State → Prop}
    {statePc : State → Option (BitVec 64)} {region : BitVec 64 → Prop}
    {fromStep firstCount secondCount : Nat} {before middle after : State}
    (first : ConfinedTrace stepRelation statePc region fromStep firstCount before middle)
    (second : ConfinedTrace stepRelation statePc region (fromStep + firstCount) secondCount
      middle after) :
    ConfinedTrace stepRelation statePc region fromStep (firstCount + secondCount) before after := by
  induction first with
  | refl => simpa using second
  | step fromStep count pc before next middle atPc inside machineStep rest ih =>
      have second' :
          ConfinedTrace stepRelation statePc region ((fromStep + 1) + count) secondCount
            middle after := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ConfinedTrace.step fromStep (count + secondCount) pc before next after atPc inside
          machineStep (ih second')

/-- A compiled instance whose reviewed semantics permits a fixed relation of outcomes. -/
structure RelationalMachineContract (State Args Outcome : Type) where
  allows : Args → Outcome → Prop
  entry : Args → State → Prop
  exit : Args → Outcome → State → State → Prop
  stepBound : Args → Nat

/-- The machine implementation obligation used by a Level N contract assumption. -/
def RelationalMachineContract.Implements {State Args Outcome : Type}
    (stepRelation : Nat → State → State → Prop) (statePc : State → Option (BitVec 64))
    (region exitPc : BitVec 64 → Prop) (contract : RelationalMachineContract State Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (before : State),
    contract.entry args before →
      ∃ (count : Nat) (after : State) (outcome : Outcome),
        0 < count ∧
        count ≤ contract.stepBound args ∧
        ConfinedTrace stepRelation statePc region fromStep count before after ∧
        (∃ pc, statePc after = some pc ∧ exitPc pc) ∧
        contract.allows args outcome ∧
        contract.exit args outcome before after

/-- Exact membership in generated half-open four-byte PC ranges. -/
def pcInRanges (ranges : List (Nat × Nat)) (pc : BitVec 64) : Prop :=
  ∃ range ∈ ranges, range.1 ≤ pc.toNat ∧ pc.toNat < range.2

/-- Exact membership in a generated finite PC list. -/
def pcInList (pcs : List Nat) (pc : BitVec 64) : Prop :=
  pc.toNat ∈ pcs

end BinaryFv.Zesu
