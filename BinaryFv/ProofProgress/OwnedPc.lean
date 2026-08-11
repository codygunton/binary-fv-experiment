import BinaryFv.RiscV.Elfling.SequentialSplice

/-!
# Deciding literal PC ownership against generated program tables

This target-neutral authoring tactic stays outside `BinaryFv.RiscV` because it evaluates a concrete
generated target with `native_decide`; generic RISC-V theorems themselves must not do that.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail LeanRV64DExecutable.Functions Register
open BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV

/-- Prove literal membership in a generated function's ranges, or literal nonmembership in its exits. -/
macro "owned_pc" : tactic =>
  `(tactic|
    first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | (simp only [functionInstanceExitPred, FunctionInstance.isExit] <;> native_decide)
    | fail "owned_pc: goal is not a decidable generated execution-range or exit predicate")

namespace ConfinedPrefix

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}

/-- One owned retired instruction, with literal generated-table checks supplied by `owned_pc`. -/
theorem ownStep' {a : Nat} {s s' : State} {pc : BitVec 64}
    (atPc : s.regs.get? PC = some pc)
    (step : Runs (try_step a false) s s' false)
    (inRegion : own pc := by owned_pc)
    (notExit : ¬ exit pc := by owned_pc) :
    ConfinedPrefix own exit childSummary a 1 s s' :=
  ConfinedPrefix.ownStep atPc inRegion notExit step

end ConfinedPrefix
end BinaryFv.RiscV.Elfling
