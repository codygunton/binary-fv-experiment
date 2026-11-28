import ZesuExec.Vc.Sound

/-!
# Obligation framework: recursion (programme plan S15)

`PlanR` is a `Plan` whose leaves are listed by cut *index* (`leaves i` for `cuts[i]`), so a plan
may list several cuts at one pc (one per value of a register a run needs as a literal, e.g. an
index into a rodata table). Two more call exits:

* a call into the plan itself (`SelfGoal`): at the call, the assertion of some cut `c₀` of the
  plan holds for parameters `g'` the leaf chooses; after any run of at most `c₀`'s budget to a
  machine satisfying `Post g'`, the assertion of a cut of the caller holds at the return address,
  and the two budgets fit what is left;
* a call to a `CalleeD` (`DGoal`): a callee whose budget depends on the caller's parameters and
  the callee index (e.g. `sparseRoot` from `progressiveRootAt`).

Both hand the caller the callee's run (`RunsIn`), so the caller may use what every run keeps
(`Fn.Preserved`).

`vc_sound_rec`: the strong induction of `vc_sound` on the budget. The induction hypothesis
covers every cut for every parameter with a smaller budget, so a self-call whose callee budget is
at most the remaining budget is one more case of the same induction.
-/

namespace ZesuExec.Vc
open ZesuExec ZesuExec.Sym

/-- A callee whose budget depends on the caller's parameters and the callee index. -/
structure CalleeD (σ : Type) (img : Image) where
  X     : Type := Unit
  entry : Nat
  bound : σ → X → Nat
  Pre   : σ → X → Machine → Prop
  Post  : σ → X → Machine → Machine → Prop
  spec  : ∀ g x, Spec img entry (bound g x) (Pre g x) (Post g x)

/-- A recursive plan. `leaves i` are the leaves of `cuts[i]` (by index, not by pc); `dcallee`
gives `CalleeD`s by return address. -/
structure PlanR (σ : Type) (img : Image) extends Plan σ img where
  dcallee : Nat → Option (CalleeD σ img) := fun _ => none

variable {σ : Type} {img : Image}

/-- A call into the plan: `m'` satisfies the assertion of a cut `c₀` for parameters `g'`; every
run from `m'` of at most `c₀`'s budget ending in `Post g'` ends at the return address `r` in the
assertion of a cut, within `rem`. -/
def SelfGoal (P : PlanR σ img) (g : σ) (m' : Machine) (rem r : Nat) : Prop :=
  ∃ c₀ ∈ P.cuts, ∃ g', c₀.A g' m' ∧ c₀.budget g' m' ≤ rem ∧
    ∀ k m'', RunsIn img k m' m'' → k ≤ c₀.budget g' m' → P.Post g' m'' →
      ∃ c' ∈ P.cuts, m''.pc.toNat = r ∧ c'.A g m'' ∧ c₀.budget g' m' + c'.budget g m'' ≤ rem

/-- A call to the `CalleeD` at return address `r`. -/
def DGoal (P : PlanR σ img) (g : σ) (m' : Machine) (rem r : Nat) : Prop :=
  ∃ k, P.dcallee r = some k ∧ m'.pc.toNat = k.entry ∧ ∃ x, k.Pre g x m' ∧
    ∀ n m'', RunsIn img n m' m'' → n ≤ k.bound g x → k.Post g x m' m'' →
      ∃ c' ∈ P.cuts, m''.pc.toNat = r ∧ c'.A g m'' ∧ k.bound g x + c'.budget g m'' ≤ rem

def ExitGoalR (P : PlanR σ img) (g : σ) (m' : Machine) (rem : Nat) (e : Exit) : Prop :=
  ExitGoal P.toPlan g m' rem e ∨
    match e with
    | .call _ r | .callInd _ r => SelfGoal P g m' rem r ∨ DGoal P g m' rem r
    | _ => False

def LeafGoalR (P : PlanR σ img) (c : Cut σ) (l : Leaf) : Prop :=
  ∀ g m, c.A g m → (∀ b ∈ l.conds, b.eval (c.env g m) = true) →
    (∀ o ∈ l.obligs, o.holds (c.env g m)) ∧
    l.S.steps - c.S.steps ≤ c.budget g m ∧
    ∀ m', Match (c.env g m) l.S m' → ExitOk (c.env g m) l.exit m' →
      SameOutside (InWritable (c.env g m) c.S) m m' →
      ExitGoalR P g m' (c.budget g m - (l.S.steps - c.S.steps)) l.exit

/-- A leaf goal of the plain form is a recursive one. -/
theorem LeafGoalR.of_leafGoal {P : PlanR σ img} {c : Cut σ} {l : Leaf}
    (h : LeafGoal P.toPlan c l) : LeafGoalR P c l := by
  intro g m hA hc
  obtain ⟨h1, h2, h3⟩ := h g m hA hc
  exact ⟨h1, h2, fun m' hm he hs => .inl (h3 m' hm he hs)⟩

theorem ExitGoalR.self {P : PlanR σ img} {g : σ} {m' : Machine} {rem t r : Nat}
    (h : SelfGoal P g m' rem r) : ExitGoalR P g m' rem (.call t r) := .inr (.inl h)

theorem ExitGoalR.dcall {P : PlanR σ img} {g : σ} {m' : Machine} {rem t r : Nat}
    (h : DGoal P g m' rem r) : ExitGoalR P g m' rem (.call t r) := .inr (.inr h)

theorem vc_sound_rec (P : PlanR σ img)
    (hruns : ∀ i (h : i < P.cuts.length),
      run img (P.cuts.map (·.pc)) P.fuel P.cuts[i].pc P.cuts[i].S = some (P.leaves i))
    (hpos : ∀ i (h : i < P.cuts.length), ∀ l ∈ P.leaves i, P.cuts[i].S.steps < l.S.steps)
    (hcut : ∀ c ∈ P.cuts, CutOK P.toPlan c)
    (hleaf : ∀ i (h : i < P.cuts.length), ∀ l ∈ P.leaves i, LeafGoalR P P.cuts[i] l) :
    ∀ c ∈ P.cuts, ∀ g m, c.A g m → Reaches img (c.budget g m) (P.Post g) m := by
  suffices H : ∀ n, ∀ c ∈ P.cuts, ∀ g m, c.A g m → c.budget g m = n →
      Reaches img n (P.Post g) m from
    fun c hc g m hA => H _ c hc g m hA rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c hc g m hA hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨hwf, hm, hro, hpc⟩ := hcut _ hc g m hA
  obtain ⟨l, hl, hconds, hrun⟩ := run_sound (hruns i hi) hwf hm hpc hro
  obtain ⟨hob, hbud, hexit⟩ := hleaf i hi l hl g m hA hconds
  obtain ⟨m', hr, hm', he, hso⟩ := hrun hob
  have hp := hpos i hi l hl
  have hx := hexit m' hm' he hso
  rw [hb] at hbud hx
  generalize hs : l.S.steps - P.cuts[i].S.steps = s at hr hbud hx
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
  have self : ∀ r, SelfGoal P g m' (n - s) r → Reaches img n (P.Post g) m := by
    rintro r ⟨c₀, hc₀, g', hA₀, hb₀, hpost⟩
    obtain ⟨k₁, m₁, hk₁, hr₁, hP⟩ := ih (c₀.budget g' m') (by omega) c₀ hc₀ g' m' hA₀ rfl
    obtain ⟨c', hc', -, hA', hle⟩ := hpost k₁ m₁ hr₁ hk₁ hP
    exact atCut c' hc' m₁ hA' k₁ hr₁ (by omega)
  have dcall : ∀ r, DGoal P g m' (n - s) r → Reaches img n (P.Post g) m := by
    rintro r ⟨k, -, hpc', x, hpre, hpost⟩
    obtain ⟨k₁, m₁, hk₁, hr₁, hP⟩ := k.spec g x m' hpc' hpre
    obtain ⟨c', hc', -, hA', hle⟩ := hpost k₁ m₁ hr₁ hk₁ hP
    exact atCut c' hc' m₁ hA' k₁ hr₁ (by omega)
  rcases hx with hx | hx
  · cases hE : l.exit with
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
  · cases hE : l.exit with
    | call t r => rw [hE] at hx; exact hx.elim (self r) (dcall r)
    | callInd t r => rw [hE] at hx; exact hx.elim (self r) (dcall r)
    | ret t => rw [hE] at hx; exact hx.elim
    | «at» pc => rw [hE] at hx; exact hx.elim
    | jumpInd t => rw [hE] at hx; exact hx.elim

end ZesuExec.Vc
