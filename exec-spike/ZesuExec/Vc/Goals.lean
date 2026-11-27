import ZesuExec.Vc.Types

/-!
# Obligation framework: goals (programme plan S2 step 2)

`CutOK P c`: the assertion of `c` gives what `run_sound` needs at its start.
`LeafGoal P c l`: under the assertion of `c` and the conditions of `l`, the obligations of `l`
hold, `l` fits the budget, and the machine at the end of `l` satisfies `ExitGoal`: the
postcondition (return), the assertion of the next cut with a smaller budget (cut or indirect
jump), the tail callee's precondition with every callee result satisfying the postcondition
(jump to a tail callee's entry), or the callee's precondition and, after any callee result, the
assertion at the return cut (call).
-/

namespace ZesuExec.Vc
open ZesuExec ZesuExec.Sym

variable {σ : Type} {img : Image}

def CutOK (_P : Plan σ img) (c : Cut σ) : Prop :=
  ∀ g m, c.A g m → Env.WF (c.env g m) c.S ∧ Match (c.env g m) c.S m ∧ RodataLoaded img m ∧
    m.pc.toNat = c.pc

/-- What the machine `m'` at the end of a leaf with exit `e` must satisfy, with `rem`
instructions of the budget left. -/
def ExitGoal (P : Plan σ img) (g : σ) (m' : Machine) (rem : Nat) : Exit → Prop
  | .ret _ => P.Post g m'
  | .at pc =>
    match P.tail pc with
    | some k => ∃ x, m'.pc.toNat = k.entry ∧ k.Pre g x m' ∧ k.bound ≤ rem ∧
        ∀ m'', k.Post g x m' m'' → P.Post g m''
    | none => ∃ c' ∈ P.cuts, m'.pc.toNat = c'.pc ∧ c'.A g m' ∧ c'.budget g m' ≤ rem
  | .jumpInd _ =>
    ∃ c' ∈ P.cuts, m'.pc.toNat = c'.pc ∧ c'.A g m' ∧ c'.budget g m' ≤ rem
  | .call _ r | .callInd _ r =>
    ∃ k x, P.callee r = some k ∧ m'.pc.toNat = k.entry ∧ k.Pre g x m' ∧
      ∀ m'', k.Post g x m' m'' →
        ∃ c' ∈ P.cuts, c'.pc = r ∧ m''.pc.toNat = r ∧ c'.A g m'' ∧ k.bound + c'.budget g m'' ≤ rem

def LeafGoal (P : Plan σ img) (c : Cut σ) (l : Leaf) : Prop :=
  ∀ g m, c.A g m → (∀ b ∈ l.conds, b.eval (c.env g m) = true) →
    (∀ o ∈ l.obligs, o.holds (c.env g m)) ∧
    l.S.steps - c.S.steps ≤ c.budget g m ∧
    ∀ m', Match (c.env g m) l.S m' → ExitOk (c.env g m) l.exit m' →
      SameOutside (InWritable (c.env g m) c.S) m m' →
      ExitGoal P g m' (c.budget g m - (l.S.steps - c.S.steps)) l.exit

/-- A jump to a cut point (no tail callee at `pc`). -/
theorem ExitGoal.at_cut {P : Plan σ img} {g : σ} {m' : Machine} {rem pc : Nat}
    (h : P.tail pc = none)
    (hc : ∃ c' ∈ P.cuts, m'.pc.toNat = c'.pc ∧ c'.A g m' ∧ c'.budget g m' ≤ rem) :
    ExitGoal P g m' rem (.at pc) := by
  simp only [ExitGoal, h]; exact hc

/-- A tail call: a jump to the entry of the tail callee `k` at `pc`. -/
theorem ExitGoal.at_tail {P : Plan σ img} {g : σ} {m' : Machine} {rem pc : Nat}
    {k : Callee σ img} (h : P.tail pc = some k)
    (hc : ∃ x, m'.pc.toNat = k.entry ∧ k.Pre g x m' ∧ k.bound ≤ rem ∧
      ∀ m'', k.Post g x m' m'' → P.Post g m'') :
    ExitGoal P g m' rem (.at pc) := by
  simp only [ExitGoal, h]; exact hc

end ZesuExec.Vc
