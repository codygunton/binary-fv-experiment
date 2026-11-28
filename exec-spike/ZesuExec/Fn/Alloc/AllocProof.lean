import ZesuExec.Fn.Alloc.AllocE
import ZesuExec.Fn.Alloc.AllocJ
import ZesuExec.Fn.Alloc.AllocLeaves
import ZesuExec.Sail.Run

/-!
# `AllocF.allocf_spec`: `alt_fl_alloc.alloc` meets its contract over the free-list invariant

`zesu_assemble AllocF` takes the 9 cut theorems and 43 leaf theorems and gives `AllocF.reach`
on `allocImage`; `runsIn_text` moves the run to `zesuImage`. `AllocF.allocf_sail`: the same at
the Sail level. (The end theorems sit in the plan's namespace, named after it, so that
`zesu-status` finds them and their `pre_nonvacuous` and `post_snapshot` beside them.)
-/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Vc ZesuExec.SailLink

zesu_assemble AllocF

theorem AllocF.allocf_spec (L : List (Word × Nat)) :
    Spec zesuImage allocEntry 53 (AllocPre L) (AllocPost L) := fun m hpc hpre => by
  obtain ⟨k, m', hk, hr, hq⟩ :=
    AllocF.reach cE (by simp [AllocF.plan, allocPlan]) ⟨L, m⟩ m ⟨rfl, hpc, hpre⟩
  exact ⟨k, m', hk, runsIn_text hr, hq⟩

theorem AllocF.allocf_sail (L : List (Word × Nat)) {m : Machine} {s : BinaryFv.RiscV.State}
    (h : Rel zesuImage m s) (hpc : m.pc.toNat = allocEntry) (hpre : AllocPre L m) :
    SailReaches zesuImage 53 (fun s' => ∃ m', Rel zesuImage m' s' ∧ AllocPost L m m') s :=
  sail_reaches h (AllocF.allocf_spec L m hpc hpre)

/--
info: 'ZesuExec.Fn.Alloc.AllocF.allocf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AllocF.allocf_spec

end ZesuExec.Fn.Alloc
