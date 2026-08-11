import BinaryFv

/-!
# Machine traces and relational contracts for the SSZ proof root

The historical target-specific trace stack is not a dependency of the replacement proof root. This
file keeps the required interface small: actual Sail `try_step` execution, exact PC confinement, a
positive bounded trace, an allowed semantic outcome, and a machine exit relation.
-/

namespace BinaryFv.Ssz

open PreSail LeanRV64DExecutable.Functions Register

abbrev MachineState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def MachineStep (stepNo : Nat) (before after : MachineState) : Prop :=
  (try_step stepNo false).run before = .ok false after

/-- A sequence of actual Sail steps whose pre-step PCs all belong to `region`. -/
inductive ConfinedTrace (region : BitVec 64 → Prop) :
    Nat → Nat → MachineState → MachineState → Prop where
  | refl (fromStep : Nat) (state : MachineState) :
      ConfinedTrace region fromStep 0 state state
  | step (fromStep count : Nat) (pc : BitVec 64) (before middle after : MachineState)
      (atPc : before.regs.get? PC = some pc)
      (inside : region pc)
      (machineStep : MachineStep fromStep before middle)
      (rest : ConfinedTrace region (fromStep + 1) count middle after) :
      ConfinedTrace region fromStep (count + 1) before after

/-- A compiled instance whose reviewed semantics permits a fixed relation of outcomes. -/
structure RelationalMachineContract (Args Outcome : Type) where
  allows : Args → Outcome → Prop
  entry : Args → MachineState → Prop
  exit : Args → Outcome → MachineState → MachineState → Prop
  stepBound : Args → Nat

/-- The machine implementation obligation used by a Level N contract assumption. -/
def RelationalMachineContract.Implements {Args Outcome : Type}
    (region exitPc : BitVec 64 → Prop) (contract : RelationalMachineContract Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (before : MachineState),
    contract.entry args before →
      ∃ (count : Nat) (after : MachineState) (outcome : Outcome),
        0 < count ∧
        count ≤ contract.stepBound args ∧
        ConfinedTrace region fromStep count before after ∧
        (∃ pc, after.regs.get? PC = some pc ∧ exitPc pc) ∧
        contract.allows args outcome ∧
        contract.exit args outcome before after

/-- Exact membership in generated half-open four-byte PC ranges. -/
def pcInRanges (ranges : List (Nat × Nat)) (pc : BitVec 64) : Prop :=
  ∃ range ∈ ranges, range.1 ≤ pc.toNat ∧ pc.toNat < range.2

end BinaryFv.Ssz
