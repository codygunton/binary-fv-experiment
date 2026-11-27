import ZesuExec.Vc.Sound
import ZesuExec.Sym.Summary

/-!
# Obligation framework with callee summaries (programme plan S5 probe 2)

`PlanW` is a `Plan` whose runs are `runWith` runs: `sums` gives the summarised callees, `F0` the
first fresh variable, `wleaves` the `runWith` leaves per cut point. `X g m` is the memory the
summarised callees may change outside the caller's writable regions (for the cut machine `m`),
`Qc g m` the fact each `CallHyp` records about a call (`True` by default).

Goals:
* a leaf without summarised calls has the plain `LeafGoal` of `P.toPlan` on its `Leaf` (so leaves
  of plans without summaries keep their statements);
* a leaf with calls has `LeafGoalC`: under the cut's assertion, for every `env'` that agrees with
  the cut's `Env` below `F0` and outside the written ranges, its obligations and budget, and given
  the calls' `CallFact`s, the `ExitGoal` of the machine at its end (footprint `FootW`);
* each distinct call record of a cut's leaves has `CallGoal` (`CallHyp` under the assertion).

`vc_soundW` is `vc_sound` with `runWith_sound` in place of `run_sound`.
-/

namespace ZesuExec.Vc
open ZesuExec ZesuExec.Sym

structure PlanW (σ : Type) (img : Image) extends Plan σ img where
  sums : Nat → Option Summary
  F0 : Nat := 64
  X : σ → Machine → Word → Prop := fun _ _ _ => False
  Qc : σ → Machine → CallRec → Machine → Machine → Prop := fun _ _ _ _ _ => True
  wleaves : Nat → List LeafW

variable {σ : Type} {img : Image}

/-- The distinct summarised calls of the leaves of the cut point at `pc`. -/
def PlanW.callsAt (P : PlanW σ img) (pc : Nat) : List CallRec :=
  ((P.wleaves pc).flatMap (·.calls)).eraseDups

def CallGoal (P : PlanW σ img) (c : Cut σ) (call : CallRec) : Prop :=
  ∀ g m, c.A g m → CallHyp img (P.X g m) (P.Qc g m) (c.env g m) c.S m P.F0 call

def LeafGoalC (P : PlanW σ img) (c : Cut σ) (l : LeafW) : Prop :=
  ∀ g m, c.A g m → ∀ env', Env.Agree (c.env g m) env' P.F0 l.wr →
    (∀ b ∈ l.leaf.conds, b.eval env' = true) →
    (∀ o ∈ l.leaf.obligs, o.holds env') ∧ l.leaf.S.steps - c.S.steps ≤ c.budget g m ∧
    ((∀ call ∈ l.calls, CallFact img (P.X g m) (P.Qc g m) (c.env g m) P.F0 env' l.wr call) →
      ∀ k m', RunsIn img k m m' → Match env' l.leaf.S m' → ExitOk env' l.leaf.exit m' →
        SameOutside (FootW (c.env g m) c.S (P.X g m)) m m' →
        ExitGoal P.toPlan g m' (c.budget g m - (l.leaf.S.steps - c.S.steps)) l.leaf.exit)

def LeafGoalW (P : PlanW σ img) (c : Cut σ) (l : LeafW) : Prop :=
  if l.calls = [] then LeafGoal P.toPlan c l.leaf else LeafGoalC P c l

theorem LeafGoalW.of_plain {P : PlanW σ img} {c : Cut σ} {l : LeafW} (h : l.calls = [])
    (hg : LeafGoal P.toPlan c l.leaf) : LeafGoalW P c l := by
  unfold LeafGoalW; rw [if_pos h]; exact hg

theorem LeafGoalW.of_calls {P : PlanW σ img} {c : Cut σ} {l : LeafW} (h : l.calls ≠ [])
    (hg : LeafGoalC P c l) : LeafGoalW P c l := by
  unfold LeafGoalW; rw [if_neg h]; exact hg

theorem vc_soundW (P : PlanW σ img)
    (hruns : ∀ c ∈ P.cuts,
      runWith img P.sums (P.cuts.map (·.pc)) P.F0 P.fuel c.pc c.S = some (P.wleaves c.pc))
    (hpos : ∀ c ∈ P.cuts, ∀ l ∈ P.wleaves c.pc, c.S.steps < l.leaf.S.steps)
    (hcut : ∀ c ∈ P.cuts, CutOK P.toPlan c)
    (hcall : ∀ c ∈ P.cuts, ∀ call ∈ P.callsAt c.pc, CallGoal P c call)
    (hleaf : ∀ c ∈ P.cuts, ∀ l ∈ P.wleaves c.pc, LeafGoalW P c l) :
    ∀ c ∈ P.cuts, ∀ g m, c.A g m → Reaches img (c.budget g m) (P.Post g) m := by
  suffices H : ∀ n, ∀ c ∈ P.cuts, ∀ g m, c.A g m → c.budget g m = n →
      Reaches img n (P.Post g) m from
    fun c hc g m hA => H _ c hc g m hA rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c hc g m hA hb
  obtain ⟨hwf, hm, hro, hpc⟩ := hcut c hc g m hA
  have hcalls : ∀ l ∈ P.wleaves c.pc, ∀ call ∈ l.calls,
      CallHyp img (P.X g m) (P.Qc g m) (c.env g m) c.S m P.F0 call :=
    fun l hl call hcl => hcall c hc call
      (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨l, hl, hcl⟩)) g m hA
  obtain ⟨l, hl, env', hag, henv, hconds, hrun⟩ := runWith_sound (hruns c hc) hcalls hwf hm hpc hro
  have hp := hpos c hc l hl
  obtain ⟨s, hs0, hsn, m', k, hk, hr, hx⟩ : ∃ s, 0 < s ∧ s ≤ n ∧ ∃ m' k, k ≤ s ∧
      RunsIn img k m m' ∧ ExitGoal P.toPlan g m' (n - s) l.leaf.exit := by
    have hlw := hleaf c hc l hl
    unfold LeafGoalW at hlw
    split at hlw
    · next h0 =>
      have he := henv h0
      subst he
      obtain ⟨hob, hbud, hexit⟩ := hlw g m hA hconds
      obtain ⟨-, k, m', hk, hr, hm', hex, -, hpl⟩ := hrun hob
      exact ⟨l.leaf.S.steps - c.S.steps, by omega, by omega, m', k, hk, hr, by
        rw [← hb]; exact hexit m' hm' hex (hpl h0)⟩
    · obtain ⟨hob, hbud, hexit⟩ := hlw g m hA env' hag hconds
      obtain ⟨hf, k, m', hk, hr, hm', hex, hfo, -⟩ := hrun hob
      exact ⟨l.leaf.S.steps - c.S.steps, by omega, by omega, m', k, hk, hr, by
        rw [← hb]; exact hexit hf k m' hr hm' hex hfo⟩
  have done : ∀ k₂ m₂, RunsIn img k₂ m' m₂ → k₂ ≤ n - s → P.Post g m₂ →
      Reaches img n (P.Post g) m :=
    fun k₂ m₂ hk₂ hle hQ => ⟨k + k₂, m₂, by omega, hr.trans hk₂, hQ⟩
  have atCut : ∀ c' ∈ P.cuts, ∀ m₁, c'.A g m₁ → ∀ k₀, RunsIn img k₀ m' m₁ →
      k₀ + c'.budget g m₁ ≤ n - s → Reaches img n (P.Post g) m := by
    intro c' hc' m₁ hA' k₀ hk₀ hle
    obtain ⟨k₂, m₂, hk₂, hr₂, hQ⟩ := ih (c'.budget g m₁) (by omega) c' hc' g m₁ hA' rfl
    exact done (k₀ + k₂) m₂ (hk₀.trans hr₂) (by omega) hQ
  have call : ∀ r, (∃ k, P.callee r = some k ∧ m'.pc.toNat = k.entry ∧ k.Pre g m' ∧
      ∀ m'', k.Post g m' m'' → ∃ c' ∈ P.cuts, c'.pc = r ∧ m''.pc.toNat = r ∧ c'.A g m'' ∧
        k.bound + c'.budget g m'' ≤ n - s) → Reaches img n (P.Post g) m := by
    rintro r ⟨kc, -, hpc', hpre, hpost⟩
    obtain ⟨k₁, m₁, hk₁, hr₁, hP⟩ := kc.spec g m' hpc' hpre
    obtain ⟨c', hc', -, -, hA', hle⟩ := hpost m₁ hP
    exact atCut c' hc' m₁ hA' k₁ hr₁ (by omega)
  cases hE : l.leaf.exit with
  | ret t => rw [hE] at hx; exact done 0 m' .refl (Nat.zero_le _) hx
  | «at» pc =>
    rw [hE] at hx
    obtain ⟨c', hc', -, hA', hle⟩ := hx
    exact atCut c' hc' m' hA' 0 .refl (by omega)
  | jumpInd t =>
    rw [hE] at hx
    obtain ⟨c', hc', -, hA', hle⟩ := hx
    exact atCut c' hc' m' hA' 0 .refl (by omega)
  | call t r => rw [hE] at hx; exact call r hx
  | callInd t r => rw [hE] at hx; exact call r hx

end ZesuExec.Vc
