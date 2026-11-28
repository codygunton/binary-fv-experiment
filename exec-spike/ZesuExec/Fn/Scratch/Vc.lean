import ZesuExec.Fn.Scratch.Runs
import ZesuExec.Fn.Scratch.Spec
import ZesuExec.Fn.Alloc.AllocCuts

/-!
# `scratch_arena.free` and `scratch_arena.remap` in the obligation framework

Plans `FS` and `RS` over `allocImage`, `σ = Machine` (the entry machine). Two cut points each:
the entry, and the instruction after the null test of `chunks`, where the machine is the entry's
but for the register holding the chunk (`a0` in `free`, `a3` in `remap`).
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc ZesuExec.Fn.Alloc

def envS (sh : Machine → Shape) (_ : Machine) (m : Machine) : Env := entryEnv m ((sh m).map (·.1))

theorem envS_var (sh : Machine → Shape) (e m : Machine) (i : Fin 32) :
    (envS sh e m).vars i.val = m.reg i := by simp [envS, entryEnv]

theorem cutOK_S {P : Plan Machine allocImage} {pc : Nat} {ov : Nat → Option Sym}
    {rs : List Region} {A : Machine → Machine → Prop} {sh : Machine → Shape}
    {bud : Machine → Machine → Nat}
    (hrs : ∀ m, (sh m).map (·.2) = rs)
    (h : ∀ g m, A g m → (∀ p ∈ sh m, RegionOk p) ∧ ((sh m).map (·.1)).Pairwise Fn.Disjoint ∧
      (∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
        s.eval (entryEnv m ((sh m).map (·.1))) = m.reg i) ∧
      (∀ r j, r < rs.length → j < (entryEnv m ((sh m).map (·.1))).size r →
        (m.mem ((entryEnv m ((sh m).map (·.1))).base r + BitVec.ofNat 64 j)).isSome) ∧
      m.pc.toNat = pc) :
    CutOK P (⟨pc, Fn.entryState ov rs [], A, envS sh, bud⟩ : Cut Machine) := by
  intro g m hA
  obtain ⟨hok, hd, hov, hpres, hpc⟩ := h g m hA
  have hwf := entry_wf (m := m) (ov := ov) (ks := []) (sh m) hok hd
  have hmt := entry_match (m := m) (regs := (sh m).map (·.1)) (ov := ov) (rs := rs) (ks := [])
    hov hpres (by simp)
  rw [hrs m] at hwf
  exact ⟨hwf, hmt, rodata_allocImage m, hpc⟩

theorem regionOk_cap {b : Word} (hlo : Layout.ramLo ≤ b.toNat) (hhi : b.toNat + 16 ≤ Layout.ramHi) :
    RegionOk ((b, 16), capR) := by
  refine ⟨by simp [capR], by simp [capR, Nat.mod_one], ?_⟩
  simp [capR, writable, inRange]; omega

theorem stack_same {e m : Machine} (h : StackOk e 16) (h2 : m.reg 2 = e.reg 2)
    (hm : m.mem = e.mem) : StackOk m 16 := by
  unfold StackOk at *; rw [h2, hm]; exact h

theorem load_same {e m : Machine} (hm : m.mem = e.mem) (a : Word) (n : Nat) :
    m.load a n = e.load a n := by unfold Machine.load; rw [hm]

/-- The word a run reads at offset `off` of region `r` of an entry state, as the machine holds
it. -/
theorem word_cst {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S) (hm : Match env S m)
    {r off : Nat} {R : Region} (hR : S.regions[r]? = some R) (hb : off + 8 ≤ env.size r) :
    word m (env.base r + BitVec.ofNat 64 off) = (readConst S r off 8).eval env := by
  unfold word; rw [load_cst hwf hm hR hb]; rfl

/-- The callee-saved registers other than `sp`, and `ra`. -/
def keepS : List Nat := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem returns_S {e m' : Machine} {env : Env} {S : SState} (hm' : Match env S m')
    (hkeep : ∀ i ∈ keepS, S.reg i = .var i) (hv : ∀ i : Fin 32, i.val ∈ keepS → env.vars i = e.reg i)
    (h2 : m'.reg 2 = e.reg 2)
    (hpc : m'.pc = (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env) : Returns e m' := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hpc]; simp only [Sym.eval_bin, Sym.eval_lit, Sym.eval_var, BinOp.eval, notOne]
    rw [show env.vars 1 = e.reg 1 from hv 1 (by decide)]
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | hi
  · exact h2
  · have hk : i.val ∈ keepS := by
      simp only [keepS, List.mem_cons, List.mem_nil_iff, or_false]
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reg_var hm' i (hkeep i.val hk)).trans (hv i hk)

theorem ret_oblig_S {env : Env} {e : Machine} (hv : env.vars 1 = e.reg 1) (h : RetAligned e) :
    (Oblig.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4).holds env := by
  simp only [Oblig.holds, Sym.eval_bin, Sym.eval_lit, Sym.eval_var, BinOp.eval, notOne, hv]; exact h

theorem inRange_add {b : Word} {n j : Nat} (hb : b.toNat + n < 2 ^ 64) (hj : j < n) :
    InRange b n (b + BitVec.ofNat 64 j) := by
  unfold InRange; rw [toNat_add_ofNat (by omega)]; omega

/-! ## Entry cut (both functions): region 0 is `ctx.chunks` -/

def shapeE (m : Machine) : Shape := [((m.reg 10 + 16, 8), wordR)]

theorem cutE {P : Plan Machine allocImage} {pc : Nat} {A : Machine → Machine → Prop}
    {bud : Machine → Machine → Nat}
    (hA : ∀ g m, A g m → CtxOk m ∧ m.pc.toNat = pc) :
    CutOK P (⟨pc, SE, A, envS shapeE, bud⟩ : Cut Machine) :=
  cutOK_S (sh := shapeE) (fun _ => rfl) fun g m h => by
    obtain ⟨⟨hR, hP⟩, hpc⟩ := hA g m h
    refine ⟨by simp only [shapeE, List.mem_singleton, forall_eq]; exact regionOk_word hR.1 hR.2,
      by simp [shapeE], fun i hi s hs => ?_, fun r j hr hj => ?_, hpc⟩
    · simp only [ovE] at hs; split at hs
      · next h => cases hs; have : i = 10 := Fin.ext h; subst this
                  show m.reg 10 + 16 + BitVec.ofInt 64 (-16) = m.reg 10; simp; bv_omega
      · simp at hs
    · simp only [List.length_singleton, Nat.lt_one_iff] at hr; subst hr
      have hj8 : j < 8 := by simpa [Env.size, entryEnv, shapeE] using hj
      simpa [Env.base, entryEnv, shapeE] using hP j hj8

theorem chunks_eval {e : Machine} {S : SState} (hS : S = SE) (hwf : Env.WF (envS shapeE e e) S)
    (hm : Match (envS shapeE e e) S e) : (Sym.init 0 0 8).eval (envS shapeE e e) = chunks e := by
  subst hS
  have := word_cst hwf hm (r := 0) (off := 0) (R := wordR) rfl (by show 0 + 8 ≤ 8; decide)
  rw [show (envS shapeE e e).base 0 + BitVec.ofNat 64 0 = e.reg 10 + 16 by simp [envS, entryEnv,
    Env.base, shapeE]] at this
  exact this.symm

end ZesuExec.Fn.Scratch
