import ZesuExec.Fn.F2.Vc

/-!
# F2 proof: `f2_spec : Spec zesuImage 0x800d6960 75 Pre Post`

From `F2.reach` (`Fn/F2/Vc.lean`) at the entry cut, whose assertion is `Pre` of the entry
machine and whose budget is `bound`.
-/

namespace ZesuExec.Fn.F2
open ZesuExec ZesuExec.Vc

theorem f2_spec : Spec zesuImage entry bound Pre Post :=
  fun m hpc hpre => F2.reach cE (by simp [F2.plan, vcPlan]) m m ⟨rfl, hpc, hpre⟩

/--
info: 'ZesuExec.Fn.F2.f2_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f2_spec

end ZesuExec.Fn.F2
