import ZesuExec.Fn.Sha256.Pro
import ZesuExec.Fn.Sha256.Out

/-!
# `zkvm_sha256`: the end theorem

The prologue (`pro`, 27 steps), the whole blocks (`blocks`, at most `22 + 10 ⌊n / 64⌋`), the
tail (`tail_p`, 14), the padding blocks (`pad`, at most 33) and the output (`out_post`, 96):
`192 + 10 ⌊n / 64⌋ ≤ bound n` steps for an input of `n` bytes.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Machine ZesuExec.Fn

theorem sha256_spec (n : Nat) :
    Spec zesuImage entry (bound n) (fun m => Pre m ∧ (m.reg 11).toNat = n) Post := by
  intro m hpc ⟨hpre, hn⟩
  obtain ⟨m1, hr1, hpc1, hmid1, hst1, h10, h11⟩ := pro hpre hpc
  obtain ⟨k2, m2, hr2, hk2, hT⟩ := blocks hpre hpc1 ⟨hmid1, h10, h11⟩ hst1
  obtain ⟨m3, hr3, hP⟩ := tail_p hpre hT
  obtain ⟨k4, m4, hr4, hk4, hO⟩ := pad hpre hP
  obtain ⟨m5, hr5, hpost⟩ := out_post hpre hO
  refine ⟨27 + (k2 + (14 + (k4 + 96))), m5, ?_, hr1.trans (hr2.trans (hr3.trans (hr4.trans hr5))),
    hpost⟩
  unfold bound; rw [← hn]; omega

end ZesuExec.Fn.Sha256
