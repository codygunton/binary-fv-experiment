import ZesuExec.Fn.F1.Vc

/-!
# F1 proof: `f1_spec : Spec zesuImage 0x800cb40c 197 (Pre A L items) (Post A L items)`

From `F1.reach` (`Fn/F1/Vc.lean`) at the entry cut, whose assertion is `Pre` of the entry
machine and whose budget is `bound`.
-/

namespace ZesuExec.Fn.F1
open ZesuExec ZesuExec.Vc

/-- F1 meets its contract, given the allocator's assumed contracts. -/
theorem f1_spec (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (items : List Byte) :
    Spec zesuImage entry bound (Pre A L items) (Post A L items) :=
  fun m hpc hpre => F1.reach cE (by simp [F1.plan, vcPlan]) ⟨A, L, items, m⟩ m ⟨rfl, hpc, hpre⟩

/--
info: 'ZesuExec.Fn.F1.f1_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f1_spec

end ZesuExec.Fn.F1
