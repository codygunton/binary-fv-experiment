import ZesuExec.Fn.F1.Vc

/-!
# F1's bound is the longest feasible path (plan Verification item 6)

Own steps at each feasible leaf of the runs in `ZesuExec.Fn.F1.Vc` along a path, plus the
callee bounds on that path (`alloc` 53, `memcpy` 3, `free` 42). `remap`'s bound (F0, 9) is part of
the steps of the entry leaves that continue through its call (`runWith`); the join runs start
from 0. The maximum equals `F1.bound`, so the bound is not padded.
-/

namespace ZesuExec.Test.Budget
open ZesuExec.Fn.F1

def f1PathCosts : List Nat :=
  [ (runE_leaves[0]!).leaf.S.steps,                                  -- no growth
    (runE_leaves[2]!).leaf.S.steps + 53 + (runJ2_leaves[1]!).leaf.S.steps, -- capacity 0, alloc null
    (runE_leaves[2]!).leaf.S.steps + 53 + (runJ2_leaves[0]!).leaf.S.steps + 3 +
      (runJ3_leaves[0]!).leaf.S.steps + (runJ4_leaves[0]!).leaf.S.steps,   -- capacity 0, alloc, memcpy
    (runE_leaves[5]!).leaf.S.steps + 53 + (runJ2_leaves[1]!).leaf.S.steps, -- remap, alloc null
    (runE_leaves[5]!).leaf.S.steps + 53 + (runJ2_leaves[0]!).leaf.S.steps + 3 +
      (runJ3_leaves[1]!).leaf.S.steps + 42 + (runJ4_leaves[0]!).leaf.S.steps ] -- remap, alloc, memcpy, free

theorem f1PathCosts_eq : f1PathCosts = [29, 112, 123, 137, 197] := by decide +kernel

theorem f1_budget_tight : f1PathCosts.foldl max 0 = bound := by decide +kernel

end ZesuExec.Test.Budget
