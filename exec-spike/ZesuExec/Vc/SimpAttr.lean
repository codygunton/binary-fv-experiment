import Lean

/-!
# `zesu_simp` (programme plan S4 step 5)

Simp set for per-function normal-form lemmas (an `Env`'s variables as machine registers, a
cut's definitions unfolded, region bases). `leaf_auto`, `leaf_infeasible` and `region_tac` use it.
-/

register_simp_attr zesu_simp
