import ZesuExec.Vc.Goals
import ZesuExec.Sym.Sound

/-!
# Obligation framework: soundness (programme plan S2 step 3)

`vc_sound`: if every run of the plan is the one `sym_run` evaluated, every leaf takes at least
one step, every cut's assertion gives `CutOK` and every leaf goal holds, then from every cut
point the machine reaches the postcondition within the cut's budget. Strong induction on the
budget: each leaf spends at least one instruction and hands a smaller budget to the next cut.

`AllL` and `forall_mem_of_idx` let `zesu_assemble` prove `∀ x ∈ l, Q x` from one proof per
index of `l`.
-/

namespace ZesuExec.Vc
open ZesuExec ZesuExec.Sym

variable {σ : Type} {img : Image}

theorem vc_sound (P : Plan σ img)
    (hruns : ∀ c ∈ P.cuts, run img (P.cuts.map (·.pc)) P.fuel c.pc c.S = some (P.leaves c.pc))
    (hpos : ∀ c ∈ P.cuts, ∀ l ∈ P.leaves c.pc, c.S.steps < l.S.steps)
    (hcut : ∀ c ∈ P.cuts, CutOK P c)
    (hleaf : ∀ c ∈ P.cuts, ∀ l ∈ P.leaves c.pc, LeafGoal P c l) :
    ∀ c ∈ P.cuts, ∀ g m, c.A g m → Reaches img (c.budget g m) (P.Post g) m := by
  suffices H : ∀ n, ∀ c ∈ P.cuts, ∀ g m, c.A g m → c.budget g m = n →
      Reaches img n (P.Post g) m from
    fun c hc g m hA => H _ c hc g m hA rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c hc g m hA hb
  obtain ⟨hwf, hm, hro, hpc⟩ := hcut c hc g m hA
  obtain ⟨l, hl, hconds, hrun⟩ := run_sound (hruns c hc) hwf hm hpc hro
  obtain ⟨hob, hbud, hexit⟩ := hleaf c hc l hl g m hA hconds
  obtain ⟨m', hr, hm', he, hso⟩ := hrun hob
  have hp := hpos c hc l hl
  have hx := hexit m' hm' he hso
  rw [hb] at hbud hx
  generalize hs : l.S.steps - c.S.steps = s at hr hbud hx
  have hs0 : 0 < s := by omega
  have done : ∀ k m₂, RunsIn img k m' m₂ → k ≤ n - s → P.Post g m₂ →
      Reaches img n (P.Post g) m :=
    fun k m₂ hk hle hQ => ⟨s + k, m₂, by omega, hr.trans hk, hQ⟩
  have atCut : ∀ c' ∈ P.cuts, ∀ m₁, c'.A g m₁ → ∀ k₀, RunsIn img k₀ m' m₁ →
      k₀ + c'.budget g m₁ ≤ n - s → Reaches img n (P.Post g) m := by
    intro c' hc' m₁ hA' k₀ hk₀ hle
    obtain ⟨k, m₂, hk, hr₂, hQ⟩ := ih (c'.budget g m₁) (by omega) c' hc' g m₁ hA' rfl
    exact done (k₀ + k) m₂ (hk₀.trans hr₂) (by omega) hQ
  have call : ∀ r, (∃ k x, P.callee r = some k ∧ m'.pc.toNat = k.entry ∧ k.Pre g x m' ∧
      ∀ m'', k.Post g x m' m'' → ∃ c' ∈ P.cuts, c'.pc = r ∧ m''.pc.toNat = r ∧ c'.A g m'' ∧
        k.bound + c'.budget g m'' ≤ n - s) → Reaches img n (P.Post g) m := by
    rintro r ⟨k, x, -, hpc', hpre, hpost⟩
    obtain ⟨k₁, m₁, hk₁, hr₁, hP⟩ := k.spec g x m' hpc' hpre
    obtain ⟨c', hc', -, -, hA', hle⟩ := hpost m₁ hP
    exact atCut c' hc' m₁ hA' k₁ hr₁ (by omega)
  cases hE : l.exit with
  | ret t => rw [hE] at hx; exact done 0 m' .refl (Nat.zero_le _) hx
  | «at» pc =>
    rw [hE] at hx
    cases ht : P.tail pc with
    | some k =>
      simp only [ExitGoal, ht] at hx
      obtain ⟨x, hpc', hpre, hbd, hpost⟩ := hx
      obtain ⟨k₁, m₁, hk₁, hr₁, hP⟩ := k.spec g x m' hpc' hpre
      exact done k₁ m₁ hr₁ (by omega) (hpost m₁ hP)
    | none =>
      simp only [ExitGoal, ht] at hx
      obtain ⟨c', hc', -, hA', hle⟩ := hx
      exact atCut c' hc' m' hA' 0 .refl (by omega)
  | jumpInd t =>
    rw [hE] at hx
    obtain ⟨c', hc', -, hA', hle⟩ := hx
    exact atCut c' hc' m' hA' 0 .refl (by omega)
  | call t r => rw [hE] at hx; exact call r hx
  | callInd t r => rw [hE] at hx; exact call r hx

/-- `Q` holds for every element of the list. -/
def AllL {α : Type} (Q : α → Prop) : List α → Prop
  | [] => True
  | a :: l => Q a ∧ AllL Q l

theorem AllL.forall {α : Type} {Q : α → Prop} : ∀ {l : List α}, AllL Q l → ∀ x ∈ l, Q x
  | [], _, _, hx => by simp at hx
  | a :: l, ⟨ha, hl⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact AllL.forall hl x hx

/-- `Q` at index `i` of `l`. -/
def idxQ {α : Type} [Inhabited α] (Q : α → Prop) (l : List α) (i : Nat) : Prop := Q l[i]!

theorem forall_mem_of_idx {α : Type} [Inhabited α] {Q : α → Prop} (l : List α)
    (h : AllL (idxQ Q l) (List.range l.length)) : ∀ x ∈ l, Q x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have := AllL.forall h i (List.mem_range.mpr hi)
  simpa [idxQ, getElem!_pos l i hi] using this

/-- For hand-written leaf theorems: the `i`-th leaf is a leaf of the run. -/
theorem getElem!_mem {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!_pos l i h]; exact List.getElem_mem h

end ZesuExec.Vc
