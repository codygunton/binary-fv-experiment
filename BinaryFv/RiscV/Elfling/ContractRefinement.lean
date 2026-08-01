import BinaryFv.RiscV.Elfling.Contract

/-!
# Reusing an implementation proof for another contract

This module gives sufficient conditions for transferring an `OccurrenceContract.Implements` proof
from one contract to another over the same machine region. Suppose `fine.Implements` is already known
and `coarse.Implements` is required. A `ContractRefinement fine coarse` supplies:

- `liftArgs`, which translates each `coarse` argument into a `fine` argument;
- an implication from the `coarse` entry predicate to the translated `fine` entry predicate;
- an implication from the resulting `fine` exit predicate to the `coarse` exit predicate; and
- a proof that the `fine` step bound does not exceed the `coarse` step bound.

The execution trace produced by `fine.Implements` then also witnesses `coarse.Implements`. This
relation changes only the contract placed on an execution; it does not change the region, entry PC,
exit set, instruction semantics, or trace.
-/

namespace BinaryFv.RiscV.Elfling

open BinaryFv.RiscV

/--
Evidence that an implementation of `fine` also implements `coarse` on the same machine region.

The four fields are deliberately directional:

- `liftArgs` translates the arguments expected by `coarse` into arguments accepted by `fine`;
- `entry` shows that every valid `coarse` starting state is also a valid `fine` starting state;
- `exit` shows that the `fine` result satisfies the exit condition required by `coarse`;
- `stepBound` shows that the trace allowed by `fine` fits within the limit allowed by `coarse`.
-/
structure ContractRefinement {FineArgs CoarseArgs Outcome : Type}
    (fine : OccurrenceContract FineArgs Outcome)
    (coarse : OccurrenceContract CoarseArgs Outcome) where
  liftArgs : CoarseArgs → FineArgs
  entry : ∀ (args : CoarseArgs) (state : State),
    coarse.binding.entry args state → fine.binding.entry (liftArgs args) state
  exit : ∀ (args : CoarseArgs) (before after : State),
    fine.binding.exit (liftArgs args) (fine.spec.meaning (liftArgs args)) before after →
      coarse.binding.exit args (coarse.spec.meaning args) before after
  stepBound : ∀ args, fine.binding.stepBound (liftArgs args) ≤ coarse.binding.stepBound args

namespace ContractRefinement

variable {FineArgs CoarseArgs Outcome : Type}
  {fine : OccurrenceContract FineArgs Outcome}
  {coarse : OccurrenceContract CoarseArgs Outcome}

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
