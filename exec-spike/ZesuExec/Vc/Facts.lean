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

/-! ## Backward lemmas for obligations -/

initialize zesuObligAttr : TagAttribute ←
  registerTagAttribute `zesu_oblig
    "a lemma proving an obligation (`Oblig.holds env o`) from assertion facts, for `zesu_apply`"

def zesuObligs (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    out := out ++ zesuObligAttr.ext.getModuleEntries env i
  out ++ (zesuObligAttr.ext.getState env).toArray

/-- A conjunct of `t : ty` (nested `∧`, definitions unfolded) whose type is `goal`. -/
partial def conjOf (goal t ty : Expr) : MetaM (Option Expr) := do
  if ← isDefEq ty goal then return some t
  let ty ← whnf ty
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    if let some p ← conjOf goal (mkApp3 (mkConst ``And.left) a b t) a then return some p
    conjOf goal (mkApp3 (mkConst ``And.right) a b t) b
  else return none

/-- Close `g` by a hypothesis or a conjunct of one. -/
def closeByConj (g : MVarId) : MetaM Bool := g.withContext do
  let goal ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let s ← saveState
    if let some p ← conjOf goal d.toExpr (← instantiateMVars d.type) then
      g.assign p
      return true
    s.restore
  return false

syntax (name := zesuApplyCmd) "zesu_apply" : tactic

/-- The head constant of the `Env` in a type `… → Oblig.holds env o`. -/
def obligEnvHead? (ty : Expr) : Option Name :=
  let c := ty.getForallBody
  if c.isAppOfArity ``Oblig.holds 2 then c.appFn!.appArg!.getAppFn.constName? else none

/-- Close the goal by a `@[zesu_oblig]` lemma whose premises are hypotheses or conjuncts of
hypotheses (the lemma's arguments come from unifying its conclusion with the goal). A lemma whose
`Env` has another head constant than the goal's (another function's `Env`) is skipped without
unifying, so a goal no lemma is about fails at once. -/
@[tactic zesuApplyCmd] def evalZesuApply : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let gHead := obligEnvHead? (← instantiateMVars (← g.getType))
  for n in zesuObligs (← getEnv) do
    if let (some a, some b) := (gHead, obligEnvHead? (← getConstInfo n).type) then
      if a != b then continue
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels n)
      let mut ok := true
      for g' in gs do
        unless ← g'.isAssigned do
          unless ← closeByConj g' do ok := false
      if ok then
        replaceMainGoal []
        return
    catch _ => pure ()
    s.restore
  throwError "zesu_apply: no @[zesu_oblig] lemma closes the goal"

theorem SBool.conds_agree {env env' : Env} {F : Nat} {wr : Ranges} {cs : List SBool}
    (hag : Env.Agree env env' F wr) (hok : cs.all (SBool.okB F wr) = true)
    (hc : ∀ b ∈ cs, b.eval env' = true) : ∀ b ∈ cs, b.eval env = true := fun b hb => by
  rw [← SBool.eval_agree hag b (List.all_eq_true.mp hok b hb)]; exact hc b hb

end ZesuExec.Vc
