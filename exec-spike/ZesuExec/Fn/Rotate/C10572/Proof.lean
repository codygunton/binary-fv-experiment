import ZesuExec.Fn.Rotate.C10572.Leaves
import ZesuExec.Fn.Rotate.C10572.Snaps
import ZesuExec.Sail.Run

/-!
# `mem.rotate__anon_10572`: `r10572_spec` and `r10572_sail`

`R10572.reach` (`zesu_assemble`) at the entry cut, whose assertion is `Pre` of the entry machine
and whose budget is `bound`; `sail_reaches` lifts it to the Sail model.
-/

namespace ZesuExec.Fn.Rotate.C10572
open ZesuExec ZesuExec.Vc ZesuExec.SailLink ZesuExec.Fn.Rotate

theorem r10572_spec : Spec zesuImage entry bound (Pre cfg) (Post cfg) :=
  fun m hpc hpre => R10572.reach cE (by simp [R10572.plan, vcPlan]) m m ⟨rfl, hpc, hpre⟩

theorem r10572_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre cfg m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post cfg m m') s :=
  sail_reaches h (r10572_spec m hpc hpre)

/-- Contract rule (a): `Pre` holds of a concrete machine (two elements, rotated by one). -/
theorem pre_nonvacuous : ∃ m, Pre cfg m := ⟨_, pre_witness cfg (n := 2) (a := 1) (by decide) (by decide) (by decide) (by decide)⟩

/-- Contract rule (b): `Post` holds on the Unicorn snapshots `test/snapshots/R10572` (lengths 0–8,
every amount class), evaluated by `decide`. -/
theorem post_snapshot : snaps.all (SnapOk cfg) = true := by decide +kernel

end ZesuExec.Fn.Rotate.C10572
