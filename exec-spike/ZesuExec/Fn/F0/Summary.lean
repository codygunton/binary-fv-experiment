import ZesuExec.Fn.F0.Proof
import ZesuExec.Sym.Summary

/-!
# F0 `alt_fl_alloc.remap` as a `runWith` summary (programme plan S5 probe 2)

`summary`: at most `bound` (9) instructions, the ABI's caller-saved registers clobbered, `a0 = 0`,
no caller bytes written. `callPost` turns `f0_spec`'s `Post` into the `CallPost` a caller's
`CallHyp` must give at a call recorded with this summary: the callee's only footprint is its
16-byte frame below the caller's `sp`, which the caller must place inside its `X` and outside its
regions.

Not used by F1 yet: F1's proof is a `Vc.Plan`, and `vc_sound` runs `run`, not `runWith`; the
change is recorded in `LOG.md` (S5-p2).
-/

namespace ZesuExec.Fn.F0
open ZesuExec ZesuExec.Sym

def summary : Summary := ⟨bound, abiClobbers, some (.lit 0), []⟩

/-- `f0_spec`'s postcondition gives `CallPost` for a call recorded with `summary`. -/
theorem callPost {img : Image} {X : Word → Prop} {c : CallRec} {env : Env} {m₁ m₂ : Machine}
    (hk : c.keptB = true) (hres : c.result = some (.lit 0)) (hwr : c.wr = [])
    (hra : (m₁.reg 1 &&& ~~~(1 : Word)).toNat = c.ret) (hpost : Post m₁ m₂)
    (hstk : StackOk m₁ 16) (hro : RoLoaded img m₁)
    (hfr : ∀ r j, r < c.S.regions.length → j < env.size r →
      ¬ InRange (m₁.reg 2 - 16) 16 (env.base r + BitVec.ofNat 64 j))
    (hX : ∀ a, InRange (m₁.reg 2 - 16) 16 a → X a) :
    CallPost img X c env m₁ m₂ := by
  obtain ⟨hret, h10, hso⟩ := hpost
  have hcov : ∀ r j, Ranges.covers c.wr r j = false := fun r j => by simp [hwr, Ranges.covers]
  refine ⟨(by rw [hret.1, hra]), CallRec.keep_of_returns hk hret,
    (fun v hv => by rw [hres] at hv; cases hv; simp [h10, Sym.eval]), (fun r j hr hj _ => ?_),
    (fun r j _ _ h => by rw [hcov] at h; cases h),
    (fun a ha => hso a fun h => ha (.inr (hX a h))), (fun a b hlo hhi hb => ?_)⟩
  · exact hso _ (hfr r j hr hj)
  · rw [hso _ fun h => ?_]
    · exact hro a b hlo hhi hb
    · obtain ⟨-, hsplo, -⟩ := hstk
      unfold InRange at h
      have h16 : (m₁.reg 2 - 16).toNat = (m₁.reg 2).toNat - 16 := by
        rw [BitVec.toNat_sub]; simp; omega
      rw [h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold Layout.rodataHi at hhi; omega)] at h
      unfold Layout.rodataHi at hhi; unfold Layout.ramLo at hsplo; omega

end ZesuExec.Fn.F0
