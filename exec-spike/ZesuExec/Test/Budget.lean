import ZesuExec.Fn.F1.Runs

/-!
# F1's bound is the longest feasible path (plan Verification item 6)

Own steps at each feasible return leaf of the runs in `ZesuExec.Fn.F1.Runs`, plus the callee
bounds on that path (`remap` = F0 9, `alloc` 53, `memcpy` 3, `free` 42). The maximum equals
`F1.bound`, so the bound is not padded.
-/

namespace ZesuExec.Test.Budget
open ZesuExec.Fn.F1

def f1PathCosts : List Nat :=
  [ (run0_leaves[0]!).S.steps,                    -- no growth
    (run2a_leaves[1]!).S.steps + 53,              -- capacity 0, alloc null
    (run3a_leaves[0]!).S.steps + 53 + 3,          -- capacity 0, alloc, memcpy
    (run2b_leaves[1]!).S.steps + 9 + 53,          -- remap, alloc null
    (run4b_leaves[0]!).S.steps + 9 + 53 + 3 + 42 ] -- remap, alloc, memcpy, free

theorem f1PathCosts_eq : f1PathCosts = [29, 112, 123, 137, 197] := by decide +kernel

theorem f1_budget_tight : f1PathCosts.foldl max 0 = bound := by decide +kernel

end ZesuExec.Test.Budget
