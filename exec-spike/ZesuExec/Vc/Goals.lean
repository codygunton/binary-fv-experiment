import ZesuExec.Vc.Types

/-!
# Obligation framework: goals (programme plan S2 step 2)

`CutOK P c`: the assertion of `c` gives what `run_sound` needs at its start.
`LeafGoal P c l`: under the assertion of `c` and the conditions of `l`, the obligations of `l`
hold, `l` fits the budget, and the machine at the end of `l` satisfies `ExitGoal`: the
postcondition (return), the assertion of the next cut with a smaller budget (cut or indirect
jump), or the callee's precondition and, after any callee result, the assertion at the return
cut (call).
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
  | .at _ | .jumpInd _ =>
    ∃ c' ∈ P.cuts, m'.pc.toNat = c'.pc ∧ c'.A g m' ∧ c'.budget g m' ≤ rem
  | .call _ r | .callInd _ r =>
    ∃ k, P.callee r = some k ∧ m'.pc.toNat = k.entry ∧ k.Pre g m' ∧
      ∀ m'', k.Post g m' m'' →
        ∃ c' ∈ P.cuts, c'.pc = r ∧ m''.pc.toNat = r ∧ c'.A g m'' ∧ k.bound + c'.budget g m'' ≤ rem

def LeafGoal (P : Plan σ img) (c : Cut σ) (l : Leaf) : Prop :=
  ∀ g m, c.A g m → (∀ b ∈ l.conds, b.eval (c.env g m) = true) →
    (∀ o ∈ l.obligs, o.holds (c.env g m)) ∧
    l.S.steps - c.S.steps ≤ c.budget g m ∧
    ∀ m', Match (c.env g m) l.S m' → ExitOk (c.env g m) l.exit m' →
      SameOutside (InWritable (c.env g m) c.S) m m' →
      ExitGoal P g m' (c.budget g m - (l.S.steps - c.S.steps)) l.exit

end ZesuExec.Vc
