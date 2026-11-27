import ZesuExec.Fn.F1.Vc

/-!
# F1's bound is the longest feasible path (plan Verification item 6)

Own steps at each feasible leaf of the runs in `ZesuExec.Fn.F1.Vc` along a path, plus the
callee bounds on that path (`remap` = F0 9, `alloc` 53, `memcpy` 3, `free` 42). The runs after
`remap` continue the entry run's step count; the join runs start from 0. The maximum equals
`F1.bound`, so the bound is not padded.
-/

namespace ZesuExec.Test.Budget
open ZesuExec.Fn.F1

def f1PathCosts : List Nat :=
  [ (runE_leaves[0]!).S.steps,                                  -- no growth
    (runE_leaves[2]!).S.steps + 53 + (runJ2_leaves[1]!).S.steps, -- capacity 0, alloc null
    (runE_leaves[2]!).S.steps + 53 + (runJ2_leaves[0]!).S.steps + 3 +
      (runJ3_leaves[0]!).S.steps + (runJ4_leaves[0]!).S.steps,   -- capacity 0, alloc, memcpy
    (runR_leaves[1]!).S.steps + 9 + 53 + (runJ2_leaves[1]!).S.steps, -- remap, alloc null
    (runR_leaves[1]!).S.steps + 9 + 53 + (runJ2_leaves[0]!).S.steps + 3 +
      (runJ3_leaves[1]!).S.steps + 42 + (runJ4_leaves[0]!).S.steps ] -- remap, alloc, memcpy, free

theorem f1PathCosts_eq : f1PathCosts = [29, 112, 123, 137, 197] := by decide +kernel

theorem f1_budget_tight : f1PathCosts.foldl max 0 = bound := by decide +kernel

end ZesuExec.Test.Budget
