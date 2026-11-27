import ZesuExec.Fn.F6.Vc

/-!
# F6 proof: `f6_spec : Spec zesuImage 0x800d5cb8 2178 Pre Post`

From `F6.reach` (`Fn/F6/Vc.lean`) at the entry cut, whose assertion is `Pre` of the entry
machine and whose budget is 2178.
-/

namespace ZesuExec.Fn.F6
open ZesuExec ZesuExec.Vc

theorem f6_spec : Spec zesuImage entry 2178 Pre Post :=
  fun m hpc hpre => F6.reach cE (by simp [F6.plan, vcPlan]) m m ⟨rfl, hpc, hpre⟩

/--
info: 'ZesuExec.Fn.F6.f6_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f6_spec

end ZesuExec.Fn.F6
