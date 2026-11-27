import Lean
import ZesuExec.Sym.Summary

/-!
# Assertion facts for leaf automation (programme plan S4b)

`@[zesu_fact]` tags a proved lemma `∀ xs, H₁ → … → Hₙ → Q` that derives a fact `Q` from a cut's
assertion (a function's `Pre`, an assertion definition, …). The tactic `zesu_facts` forward-chains
these lemmas over the local context: for each tagged lemma, every propositional premise is matched
against a hypothesis (by unification, which also fixes the lemma's other arguments); when all
premises match and the conclusion is closed, it is added as a hypothesis unless one with the same
type exists. Two rounds, so a fact may use a fact. The tactic only applies proved lemmas: it adds
hypotheses, never changes the goal, and guesses nothing (programme plan rule 6).

`SBool.conds_agree` moves a leaf's conditions from an extended `Env` back to the cut's when they
mention neither fresh variables nor written bytes (`SBool.okB`), as `leafc_auto` needs.
-/

namespace ZesuExec.Vc
open Lean Meta Elab Tactic
open ZesuExec.Sym

initialize zesuFactAttr : TagAttribute ←
  registerTagAttribute `zesu_fact "a lemma deriving a fact from a cut's assertion, for `zesu_facts`"

/-- Every `@[zesu_fact]` lemma: imported modules, then this one. -/
def zesuFacts (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    out := out ++ zesuFactAttr.ext.getModuleEntries env i
  out ++ (zesuFactAttr.ext.getState env).toArray

/-- Instantiate `n`'s premises from the local context; the closed conclusion and its proof. -/
def factFrom (n : Name) : MetaM (Option (Expr × Expr)) := do
  let s ← saveState
  try
    let e ← mkConstWithFreshMVarLevels n
    let (mvs, _, concl) ← forallMetaTelescope (← inferType e)
    for mv in mvs do
      if (← instantiateMVars mv).isMVar then
        let ty ← instantiateMVars (← inferType mv)
        if ← isProp ty then
          let mut found := false
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let s' ← saveState
            if ← isDefEq ty d.type then
              mv.mvarId!.assign d.toExpr
              found := true
              break
            s'.restore
          unless found do s.restore; return none
    let concl ← instantiateMVars concl
    let prf ← instantiateMVars (mkAppN e mvs)
    if concl.hasMVar || prf.hasMVar then s.restore; return none
    return some (concl, prf)
  catch _ =>
    s.restore; return none

syntax (name := zesuFactsCmd) "zesu_facts" : tactic

/-- Forward-chain the `@[zesu_fact]` lemmas; the number of hypotheses added. -/
def addFacts : TacticM Nat := do
  let names := zesuFacts (← getEnv)
  let mut added := 0
  for _ in [0:2] do
    for n in names do
      let new ← withMainContext do
        let some (ty, prf) ← factFrom n | return false
        for d in ← getLCtx do
          if !d.isImplementationDetail && (← withReducible (isDefEq d.type ty)) then return false
        let g ← getMainGoal
        let (_, g') ← (← g.assert (Name.mkSimple s!"fact_{n.getString!}") ty prf).intro1P
        replaceMainGoal [g']
        return true
      if new then added := added + 1
  return added

@[tactic zesuFactsCmd] def evalZesuFacts : Tactic := fun _ => do discard addFacts

theorem SBool.conds_agree {env env' : Env} {F : Nat} {wr : Ranges} {cs : List SBool}
    (hag : Env.Agree env env' F wr) (hok : cs.all (SBool.okB F wr) = true)
    (hc : ∀ b ∈ cs, b.eval env' = true) : ∀ b ∈ cs, b.eval env = true := fun b hb => by
  rw [← SBool.eval_agree hag b (List.all_eq_true.mp hok b hb)]; exact hc b hb

end ZesuExec.Vc
