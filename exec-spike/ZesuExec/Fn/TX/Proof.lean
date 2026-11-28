import ZesuExec.Fn.TX.Calls
import ZesuExec.Fn.TX.Done

/-!
# TX assembled (programme plan S6 step 7): `tx_spec : Spec zesuImage 0x80000000 bound Pre Post`

`zesu_assemble TX` collects the leaf theorems `zesu_auto TX` proved (it runs in `Facts.lean`,
after the `@[zesu_fact]` lemmas), the cut lemmas and leaf theorems of `Vc.lean`, `Ret.lean`,
`Store.lean` and the leaf modules into `TX.reach`. At the entry cut the assertion is `Pre` of
the entry machine and the budget `32 · len + 424`, at most `bound` since the input lies in the
input buffer or RAM.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

zesu_assemble TX

/-- The input of a `Pre` machine has at most `2^30` bytes. -/
theorem len_le {A : AllocContract zesuImage} {g : Params} {m : Machine} (hpre : Pre A g m) :
    (wordAt m (m.reg 12 + 8)).toNat ≤ 2 ^ 30 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, harea, -⟩ := hpre
  unfold InputArea at harea
  rcases harea with ⟨h1, h2⟩ | h
  · simp only [Layout.inputLo, Layout.inputHi] at h1 h2; omega
  · simp only [RamRange, Layout.ramLo, Layout.ramHi] at h; omega

/-- TX meets its contract for any allocator meeting `AllocContract` (DTF calls this). -/
theorem tx_spec_of (A : AllocContract zesuImage) (g : Params) :
    Spec zesuImage entry bound (Pre A g) (Post A g) :=
  fun m hpc hpre => (TX.reach cutEntry (by simp [TX.plan, vcPlan]) ⟨A, g, m⟩ m
    ⟨rfl, hpc, hpre⟩).mono (by
      show 32 * (wordAt m (m.reg 12 + 8)).toNat + 424 ≤ bound
      have := len_le hpre; unfold bound; omega) fun _ h => h

/-- TX meets its contract over the proved allocator. -/
theorem tx_spec (g : Params) :
    Spec zesuImage entry bound (Pre Alloc.contract g) (Post Alloc.contract g) :=
  tx_spec_of Alloc.contract g

/--
info: 'ZesuExec.Fn.TX.tx_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tx_spec

end ZesuExec.Fn.TX
