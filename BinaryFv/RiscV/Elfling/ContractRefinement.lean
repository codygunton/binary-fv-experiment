import BinaryFv.RiscV.Elfling.Contract

/-!
# Refining one machine-region contract into another

A proof decomposition is a choice, so its contracts need an explicit refinement relation. This
module records the simplest resolution change: a finer contract for the same machine region implies a
coarser contract. The argument types may differ; `liftArgs` reconstructs the fine interface from the
coarse one.

Nothing here mentions source functions, DWARF, or a calling convention. An ABI-shaped entry predicate
is appropriate only when the selected region starts at a real machine call boundary.
-/

namespace BinaryFv.RiscV.Elfling

open BinaryFv.RiscV

/--
Evidence that `fine` is strong enough to discharge `coarse` on the same machine region.

The four fields are deliberately directional:

- a coarse invocation supplies fine arguments and establishes the fine entry predicate;
- the fine meaning and exit fact establish the coarse exit fact;
- the fine step budget fits inside the coarse budget.
-/
structure ContractRefinement {FineArgs CoarseArgs Outcome : Type}
    (fine : FunctionInstanceContract FineArgs Outcome)
    (coarse : FunctionInstanceContract CoarseArgs Outcome) where
  liftArgs : CoarseArgs → FineArgs
  entry : ∀ (args : CoarseArgs) (state : State),
    coarse.binding.entry args state → fine.binding.entry (liftArgs args) state
  exit : ∀ (args : CoarseArgs) (before after : State),
    fine.binding.exit (liftArgs args) (fine.spec.meaning (liftArgs args)) before after →
      coarse.binding.exit args (coarse.spec.meaning args) before after
  stepBound : ∀ args, fine.binding.stepBound (liftArgs args) ≤ coarse.binding.stepBound args

namespace ContractRefinement

variable {FineArgs CoarseArgs Outcome : Type}
  {fine : FunctionInstanceContract FineArgs Outcome}
  {coarse : FunctionInstanceContract CoarseArgs Outcome}

/-- A finer contract on a region discharges a coarser contract on that same region. -/
theorem implements {region exit : BitVec 64 → Prop} {entryPc : BitVec 64}
    (refinement : ContractRefinement fine coarse)
    (fineImplements : fine.Implements region exit entryPc) :
    coarse.Implements region exit entryPc := by
  intro args fromStep state coarseEntry
  obtain ⟨count, after, fineBound, trace, fineExit⟩ :=
    fineImplements (refinement.liftArgs args) fromStep state
      (refinement.entry args state coarseEntry)
  exact
    ⟨count, after, Nat.le_trans fineBound (refinement.stepBound args), trace,
      refinement.exit args state after fineExit⟩

/--
If the coarse entry predicate has a witness, the refinement supplies a witness for the fine entry
predicate. This prevents a refinement proof from hiding a contradictory fine precondition.
-/
theorem preSatisfiable (refinement : ContractRefinement fine coarse)
    (coarseSatisfiable : coarse.PreSatisfiable) : fine.PreSatisfiable := by
  obtain ⟨args, state, entry⟩ := coarseSatisfiable
  exact ⟨refinement.liftArgs args, state, refinement.entry args state entry⟩

end ContractRefinement

end BinaryFv.RiscV.Elfling
