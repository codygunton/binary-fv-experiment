import Lean
import ZesuExec.Vc.Assemble
import ZesuExec.Vc.Regions
import ZesuExec.Sym.Tactic
import ZesuExec.Sym.Join
import ZesuExec.Vc.Facts

/-!
# Sound automation for leaf and cut goals (programme plan S4 steps 1, 2, 4)

Tactics only build proofs the kernel checks; they guess no assertion, invariant or cut point.

* `leaf_intro`, `cut_intro`: replace the goal's `F.plan.cuts[i]!` by the cut's definition and the
  leaf `(F.plan.leaves pc)[j]!` by its value (computed with compiled code; the kernel checks the
  replacement by evaluation, as for `sym_run`).
* `sym_show`: prints the goal's leaf with `Leaf.pp` (registers that changed since the cut).
* `match_regs h`: from `h : Match env S m` with a literal `S`, adds `m.reg i = …` for every
  register `S` does not leave as `var i`.
* `leaf_infeasible`: closes a goal whose hypotheses contradict, after normalising the leaf's
  conditions (`SBool.eval`, `Sym.eval`, `zesu_simp`) and turning `BitVec` comparisons into `Nat`
  ones: `omega`, then `bv_omega`.
* `exit_intro`: for `ExitGoal P g m' rem e` with a literal exit, picks the cut at the exit's
  address (or the callee at the return address) and leaves its fields as goals.
* `leaf_auto`, `cut_auto` (the `macro_rules` added to the placeholders of `Vc.Assemble`):
  the plan's step 4; they fail unless the goal is closed. `leaf_auto` is one rule (S11): facts,
  then the infeasible path or `oblig_auto`, `budget_auto` and the exit goal; `leaf_diag` runs the
  same stages in one pass for `zesu_auto` and names the first one left open. A join cut
  (programme plan S5 probe 1: `Env` `joinEnv K F Ss E`, state `generalise F Ss K`) is closed by
  `JoinIn.ok` when its assertion has the conjuncts `JoinIn K Ss E m`, `RodataLoaded img m` and the
  pc equation.
* `conj_assumption`: closes the goal with a hypothesis or a conjunct of one (nested `∧`, defined
  propositions unfolded), compared up to reducible unfolding.
* S11 decision procedures: `budget_auto` (a budget inequality: the budget evaluated at the
  literal cut by `measure_norm`, measure facts, `omega`) and `oblig_auto` (memory obligations of
  the grammar in its doc comment: `@[zesu_oblig]` lemmas, else region values in normal form,
  `sym_rw`, `omega`/`bv_omega`/`region_arith`, opened assertions by `assert_open`).
-/

namespace ZesuExec.Vc
open Lean Elab Tactic Meta
open ZesuExec ZesuExec.Sym

theorem Plan.getElem!_mem {σ : Type} {img : Image} (P : Plan σ img) {i : Nat}
    (h : i < P.cuts.length) : P.cuts[i]! ∈ P.cuts := by
  rw [getElem!_pos P.cuts i h]; exact List.getElem_mem h

/-- A register index written `⟨n % 32, _⟩` as `Fin.ofNat`, which simp reduces for literals. -/
theorem Machine.reg_mod (m : Machine) (n : Nat) (h : n % 32 < 32) :
    m.reg ⟨n % 32, h⟩ = m.reg (Fin.ofNat 32 n) := rfl

theorem Match.reg_of {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (i : Fin 32)
    (s : Sym) (h : S.reg i.val = s) : m.reg i = s.eval env := by
  rw [← hm.regs i, h]

/-- The register indices as a literal list (`simp only [AllL, regIdx]` splits a goal per register). -/
def regIdx : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31]

/-- `Match.regs` from one goal per register. -/
theorem regs_of_all {env : Env} {S : SState} {m : Machine}
    (h : AllL (fun i => (S.reg i).eval env = m.reg (Fin.ofNat 32 i)) regIdx) :
    ∀ i : Fin 32, (S.reg i.val).eval env = m.reg i := by
  intro i
  have := AllL.forall h i.val
    (by rw [show regIdx = List.range 32 from rfl]; exact List.mem_range.mpr i.isLt)
  simpa [Fin.ofNat, Nat.mod_eq_of_lt i.isLt] using this

/-- The value of a closed term, computed with compiled code. -/
unsafe def evalClosed (α : Type) [ToExpr α] (ty e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar then throwError "zesu: {e} is not closed"
  return toExpr (← evalExpr α ty e)

syntax (name := leafIntroCmd) "leaf_intro" : tactic
syntax (name := cutIntroCmd) "cut_intro" : tactic

/-- The cut `c` as a structure, its symbolic state evaluated to a literal. -/
unsafe def unfoldCut (c : Expr) : MetaM Expr := do
  let c' ← whnf c
  unless c'.isAppOfArity ``Cut.mk 6 do throwError "zesu: cut {c} does not unfold to a structure"
  let a := c'.getAppArgs
  let S ← evalClosed SState (mkConst ``SState) a[2]!
  return mkAppN c'.getAppFn #[a[0]!, a[1]!, S, a[3]!, a[4]!, a[5]!]

/-- `LeafGoal σ img P c l` with the cut unfolded to its structure and the leaf to its value. -/
@[tactic leafIntroCmd] unsafe def evalLeafIntro : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``LeafGoal 5 do throwError "leaf_intro: goal is not `LeafGoal`"
  let a := t.getAppArgs
  let c ← unfoldCut a[3]!
  let l ← evalClosed Leaf (mkConst ``Leaf) a[4]!
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN (mkConst ``LeafGoal) #[a[0]!, a[1]!, a[2]!, c, l])]

/-- `CutOK σ img P c` with the cut unfolded to its structure. -/
@[tactic cutIntroCmd] unsafe def evalCutIntro : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``CutOK 4 do throwError "cut_intro: goal is not `CutOK`"
  let a := t.getAppArgs
  let c ← unfoldCut a[3]!
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN (mkConst ``CutOK) #[a[0]!, a[1]!, a[2]!, c])]

/-- The first closed subterm of type `ty`. -/
def findClosedOf (ty : Expr) (e : Expr) : MetaM (Option Expr) := do
  for x in collect e do
    if !x.hasLooseBVars && !x.hasFVar && !x.hasMVar then
      if (← observing? (do guard (← isDefEq (← inferType x) ty))).isSome then return some x
  return none
where
  collect (e : Expr) : Array Expr :=
    let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
      let acc := acc.push e
      match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b | .proj _ _ b => go b acc
      | _ => acc
    go e #[]

syntax (name := symShowCmd) "sym_show" : tactic

/-- Print the goal's leaf: against its cut's state when the goal is `LeafGoal`, else in full. -/
@[tactic symShowCmd] unsafe def evalSymShow : Tactic := fun _ => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let (S, l) ← if t.isAppOfArity ``LeafGoal 5 then
      let a := t.getAppArgs
      pure (some (mkApp2 (mkConst ``Cut.S) a[0]! a[3]!), some a[4]!)
    else pure (none, ← findClosedOf (mkConst ``Leaf) t)
  let some l := l | throwError "sym_show: no closed leaf in the goal"
  let lv ← evalExpr Leaf (mkConst ``Leaf) l
  let Sv ← match S with
    | some S => evalExpr SState (mkConst ``SState) S
    | none => pure default
  logInfo (Leaf.pp Sv lv)

syntax (name := matchRegsCmd) "match_regs " ident : tactic

/-- From `h : Match env S m` with a literal `S`, add `m.reg i = (S.reg i).eval env` for every
register whose term is not `var i`, as hypotheses `h_r<i>`. -/
@[tactic matchRegsCmd] unsafe def evalMatchRegs : Tactic := fun stx => withMainContext do
  let h ← getFVarId stx[1]
  let ht ← whnfR (← instantiateMVars (← h.getType))
  unless ht.isAppOfArity ``Match 3 do throwError "match_regs: not a `Match` hypothesis"
  let a := ht.getAppArgs
  let S ← evalExpr SState (mkConst ``SState) a[1]!
  let mut g ← getMainGoal
  for i in [1:32] do
    let s := S.reg i
    let fin ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 32)) i
    let se := toExpr s
    let prf := mkAppN (mkConst ``Match.reg_of) #[a[0]!, a[1]!, a[2]!, .fvar h, fin, se,
      ← mkEqRefl se]
    let ty := mkAppN (mkConst ``Eq [1]) #[mkConst ``Word,
      mkApp2 (mkConst ``Machine.reg) a[2]! fin, mkApp2 (mkConst ``Sym.eval) a[0]! se]
    let (_, g') ← (← g.assert (Name.mkSimple s!"{(← h.getDecl).userName}_r{i}") ty prf).intro1P
    g := g'
  replaceMainGoal [g]

/-- Conditions and obligations as `BitVec` facts, then as `Nat` facts. -/
syntax "leaf_norm" : tactic
macro_rules
  | `(tactic| leaf_norm) => `(tactic| (
      try simp only [List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, SBool.eval,
        Oblig.holds, Sym.eval_lit, Sym.eval_var, Sym.eval_ptr, Sym.eval_bin, Sym.eval_sext,
        BinOp.eval, ExitOk, Machine.reg_mod, Fin.reduceOfNat, Fin.isValue, zesu_simp] at *
      try simp only [BitVec.ult, bne_iff_ne, beq_iff_eq, ne_eq, Bool.not_eq_true,
        Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_not] at *))

/-- Close the goal from contradictory leaf conditions (and the other hypotheses). -/
syntax "leaf_infeasible" : tactic
macro_rules
  | `(tactic| leaf_infeasible) => `(tactic| (
      exfalso
      leaf_norm
      first | omega | bv_omega))

syntax (name := exitIntroCmd) "exit_intro" : tactic

/-- `ExitGoal P g m' rem e` with a literal exit: for `.at pc`, the cut at `pc`; for a call, the
callee at the return address and, after `intro m'' hpost`, the cut at the return address.
Leaves the cut's fields as goals. -/
@[tactic exitIntroCmd] unsafe def evalExitIntro : Tactic := fun _ => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOfArity ``ExitGoal 7 do throwError "exit_intro: goal is not `ExitGoal`"
  let a := t.getAppArgs
  let (σ, img, P) := (a[0]!, a[1]!, a[2]!)
  let pcs ← evalExpr (List Nat) (← mkAppM ``List #[mkConst ``Nat])
    (← mkAppM ``List.map #[mkApp (mkConst ``Cut.pc) σ, mkAppN (mkConst ``Plan.cuts) #[σ, img, P]])
  let cutsE := mkAppN (mkConst ``Plan.cuts) #[σ, img, P]
  -- the cut at index `i`, unfolded, as syntax for `refine`
  let cutStx (i : Nat) : TacticM Term := do
    let mut l := cutsE
    for _ in [0:i] do
      let l' ← whnf l
      unless l'.isAppOfArity ``List.cons 3 do throwError "exit_intro: cut list not literal"
      l := l'.appArg!
    let l' ← whnf l
    unless l'.isAppOfArity ``List.cons 3 do throwError "exit_intro: cut list not literal"
    Term.exprToSyntax (← unfoldCut l'.appFn!.appArg!)
  let e ← whnf a[6]!
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Exit.at, #[pcE] =>
    let pc ← evalExpr Nat (mkConst ``Nat) pcE
    let isTail ← evalExpr Bool (mkConst ``Bool)
      (← mkAppM ``Option.isSome #[mkApp2 (mkAppN (mkConst ``Plan.tail) #[σ, img]) P pcE])
    if isTail then
      evalTactic (← `(tactic| (
        refine ExitGoal.at_tail (by rfl) ⟨?x, ?_, ?_, ?_, fun m'' hpost => ?_⟩
        try (case x => exact ()))))
    else
    let some i := pcs.idxOf? pc | throwError "exit_intro: no cut at {pc}"
    let c ← cutStx i
    evalTactic (← `(tactic| (
      refine ExitGoal.at_cut (by rfl)
        ⟨$c, (Plan.getElem!_mem _ (i := $(quote i)) (by decide) : $c ∈ _), ?_, ?_, ?_⟩)))
  | some ``Exit.ret, _ =>
    -- `P.Post g m'` with `P.Post` unfolded to its definition
    let post ← whnf (mkApp3 (mkConst ``Plan.Post) σ img P)
    let g ← getMainGoal
    replaceMainGoal [← g.replaceTargetDefEq (mkApp2 post a[3]! a[4]!).headBeta]
  | some ``Exit.call, #[_, rE] | some ``Exit.callInd, #[_, rE] =>
    let r ← evalExpr Nat (mkConst ``Nat) rE
    let some i := pcs.idxOf? r | throwError "exit_intro: no cut at the return address {r}"
    let c ← cutStx i
    evalTactic (← `(tactic| (
      simp only [ExitGoal]
      refine ⟨_, ?x, rfl, ?_, ?_, fun m'' hpost =>
        ⟨$c, (Plan.getElem!_mem _ (i := $(quote i)) (by decide) : $c ∈ _), rfl, ?_, ?_, ?_⟩⟩
      try (case x => exact ()))))
  | _, _ => throwError "exit_intro: exit {e} has no literal target"

/-! ## S11: measures, region values, opened assertions

Normalisations that `budget_auto`, `oblig_auto` and `field_auto` run before linear arithmetic.
Every change they make is definitional (`change`) or a case split of a hypothesis; the kernel
checks the result. -/

/-- A definition `measure_norm` and `assert_open` may unfold: a non-recursive definition outside
the core library (`Init`, `Std`, `Lean`) that is not an instance, `match`, projection or
auxiliary recursor. -/
def unfoldable (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | return false
  if (← isInstance n) || (← isMatcher n) || isAuxRecursor env n || isNoConfusion env n then
    return false
  if (← getProjectionFnInfo? n).isSome then return false
  if let some idx := env.getModuleIdxFor? n then
    if [`Init, `Std, `Lean].contains (env.header.moduleNames[idx.toNat]!).getRoot then
      return false
  return !(d.value.find? fun e => match e with
    | .const c _ => c == n || c == ``WellFounded.fix || c == n ++ `_unary ||
        (match c with | .str _ s => s == "brecOn" | _ => false)
    | _ => false).isSome

/-- A numeral: a raw literal, `OfNat.ofNat _ n _`, or `BitVec.ofNat w n` of numerals. -/
def isNumeral (x : Expr) : Bool :=
  x.isRawNatLit || x.nat?.isSome ||
    (x.isAppOfArity ``OfNat.ofNat 3 && x.appFn!.appArg!.isRawNatLit) ||
    (x.isAppOfArity ``BitVec.ofNat 2 && x.appFn!.appArg!.nat?.isSome && x.appArg!.nat?.isSome)

/-- The numeral of a closed `Nat` or `BitVec w` term that is not one, computed with compiled
code (the kernel re-checks the replacement by evaluation, as for `sym_run`). -/
unsafe def closedNumeral? (x : Expr) : MetaM (Option Expr) := do
  if x.hasFVar || x.hasMVar || x.hasLooseBVars || isNumeral x then return none
  let ty ← whnfR (← inferType x)
  try
    if ty.isConstOf ``Nat then
      return some (mkNatLit (← evalExpr Nat (mkConst ``Nat) x))
    if ty.isAppOfArity ``BitVec 1 then
      let some w := ty.appArg!.nat? | return none
      let n ← evalExpr Nat (mkConst ``Nat) (mkApp2 (mkConst ``BitVec.toNat) ty.appArg! x)
      return some (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit n))
    return none
  catch _ => return none

/-- `e` with `unfoldable` definitions at its head unfolded (at most 16 times). -/
def unfoldHead (e : Expr) : MetaM Expr := do
  let mut s := e
  for _ in [0:16] do
    let .const c _ := s.getAppFn | break
    unless ← unfoldable c do break
    let some s' ← delta? s (· == c) | break
    s := s'.headBeta
  return s

/-- Element `k` of the list `l`, its cells exposed by `whnfD`; `none` past the end. -/
def listGet? (l : Expr) (k : Nat) : MetaM (Option Expr) := do
  let mut l := l
  for _ in [0:k] do
    let l' ← whnfD l
    unless l'.isAppOfArity ``List.cons 3 do return none
    l := l'.appArg!
  let l' ← whnfD l
  if l'.isAppOfArity ``List.cons 3 then return some l'.appFn!.appArg! else return none

/-- One rewrite of `measure_norm` at the subterm `x`. -/
unsafe def measureStep (x : Expr) : MetaM TransformStep := do
  if let some v ← closedNumeral? x then return .done v
  let .const n _ := x.getAppFn | return .continue
  let args := x.getAppArgs
  if n == ``List.getD && args.size == 4 then
    let some k := args[2]!.nat? | return .continue
    if let some a ← listGet? args[1]! k then return .visit a
    return .continue
  if (n == ``ite || n == ``dite) && args.size == 5 && !args[1]!.hasFVar && !args[1]!.hasMVar then
    let d ← whnfD args[2]!
    if d.isAppOf ``Decidable.isTrue then
      return .visit (if n == ``ite then args[3]! else mkApp args[3]! d.appArg!).headBeta
    if d.isAppOf ``Decidable.isFalse then
      return .visit (if n == ``ite then args[4]! else mkApp args[4]! d.appArg!).headBeta
    return .continue
  if let some info ← getProjectionFnInfo? n then
    if h : info.numParams < args.size then
      let s ← unfoldHead args[info.numParams]
      let x' ← whnfR (mkAppN x.getAppFn (args.set info.numParams s))
      if x' != x then return .visit x'.headBeta
    return .continue
  if ← isMatcher n then
    if let ReduceMatcherResult.reduced x' ← reduceMatcher? x then return .visit x'.headBeta
    return .continue
  unless ← unfoldable n do return .continue
  unless n == ``Env.base || (← whnfR (← inferType x)).isConstOf ``Nat do return .continue
  let some x' ← delta? x (· == n) | return .continue
  return .visit x'.headBeta

unsafe def measureNorm (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do try measureStep x catch _ => return .continue)

/-- The hypotheses `measure_norm at *` rewrites: arithmetic and propositional connectives. -/
def arithProp (ty : Expr) : Bool :=
  match ty.getAppFn.constName? with
  | some n => [``Eq, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Ne, ``Not, ``And, ``Or, ``Iff].contains n
  | none => false

/-- `measure_norm` (`at *`: also in the arithmetic hypotheses): a budget or region value as
arithmetic on its atoms. Unfolds `Nat`-valued applications of `unfoldable` definitions (a cut's
budget, its measures) and `Env.base`; reduces projections of `unfoldable` definitions' values
(an `Env`'s regions and variables), `List.getD` at a numeral, `if` on a closed condition and
`match` on a constructor; replaces closed `Nat` and `BitVec` terms by numerals (a budget table
at a literal cut address). -/
syntax (name := measureNormCmd) "measure_norm" (" at" " *")? : tactic

@[tactic measureNormCmd] unsafe def evalMeasureNorm : Tactic := fun stx => withMainContext do
  let mut g ← getMainGoal
  if !stx[1].isNone then
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless arithProp ty do continue
      let ty' ← measureNorm ty
      if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  let t ← instantiateMVars (← g.getType)
  let t' ← measureNorm t
  if t' != t then g ← g.replaceTargetDefEq t'
  replaceMainGoal [g]

syntax (name := symRwCmd) "sym_rw" : tactic

/-- `sym_rw`: rewrite the goal with every hypothesis `Sym.eval env t = u` (a value the cut's
assertion or a fact fixes). -/
@[tactic symRwCmd] def evalSymRw : Tactic := fun _ => withMainContext do
  let mut thms : SimpTheorems := {}
  let mut any := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Eq 3 && ty.appFn!.appArg!.isAppOf ``Sym.eval then
      thms ← thms.add (.fvar d.fvarId) #[] d.toExpr
      any := true
  unless any do return
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  match ← simpGoal (← getMainGoal) ctx (simplifyTarget := true) (fvarIdsToSimp := #[]) with
  | (none, _) => replaceMainGoal []
  | (some (_, g), _) => replaceMainGoal [g]

/-- Open the hypotheses: unfold `Prop`-valued `unfoldable` definitions at their head, split `∧`,
`∃` and single-constructor non-recursive structures (`fuel` rounds of structures, at most 400
hypotheses). -/
partial def openHyps (g : MVarId) (fuel : Nat) : MetaM MVarId := do
  if fuel = 0 then return g
  g.withContext do
    let lctx ← getLCtx
    if lctx.size > 400 then return g
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      let .const c _ := ty.getAppFn | continue
      if c == ``And || c == ``Exists then
        let #[s] ← g.cases d.fvarId | return g
        return ← openHyps s.mvarId fuel
      if ← unfoldable c then
        let some ty' ← delta? ty (· == c) | continue
        return ← openHyps (← g.replaceLocalDeclDefEq d.fvarId ty'.headBeta) fuel
      if let some (.inductInfo i) := (← getEnv).find? c then
        if i.ctors.length == 1 && !i.isRec && i.numIndices == 0 && c != ``Eq && c != ``HEq &&
            c != ``True then
          let #[s] ← g.cases d.fvarId | return g
          return ← openHyps s.mvarId (fuel - 1)
    return g

/-- `assert_open`: the facts inside the hypotheses (a cut's assertion, its invariant's fields) as
separate hypotheses (`openHyps`). -/
syntax (name := assertOpenCmd) "assert_open" : tactic

@[tactic assertOpenCmd] def evalAssertOpen : Tactic := fun _ => withMainContext do
  replaceMainGoal [← openHyps (← getMainGoal) 3]

/-- Each field of a conjunction: hypothesis, normalisation and arithmetic, `region_tac`, and a
budget inequality between `Nat`s (`measure_norm`, then `omega`). (No `rfl`/`decide` and only
reducible `assumption`: on `Word` goals full unfolding expands 64-bit literals until the
recursion limit.) -/
syntax "field_auto" : tactic
macro_rules
  | `(tactic| field_auto) => `(tactic| first
      | with_reducible assumption
      | (leaf_norm; first | (simp_all [zesu_simp]; done) | omega | bv_omega)
      | region_tac
      | (guard_target =~ (_ : Nat) ≤ _
         leaf_norm; measure_norm at *; first | omega | (split <;> omega)))

macro_rules
  | `(tactic| cut_auto) => `(tactic| (
      cut_intro
      intro g m hA
      try dsimp only at hA ⊢
      refine ⟨?_, ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_⟩
      · region_tac
      · refine regs_of_all ?_
        simp only [AllL, regIdx]
        and_intros
        all_goals
          first
            | (simp [SState.reg, Machine.reg, Sym.eval, zesu_simp] at *; done)
            | (leaf_norm; simp_all [zesu_simp]; done)
      · intro r j hr hj
        simp at hr
        all_goals (leaf_norm; simp_all [zesu_simp])
      · simp
      · first | assumption | (simp_all [zesu_simp]; done)
      · first | assumption | (leaf_norm; simp_all [zesu_simp]; done) | (leaf_norm; omega)))

/-- A conjunct of `t : ty` (nested `∧`, definitions unfolded) whose type is `goal`. -/
partial def findConj (goal t ty : Expr) : MetaM (Option Expr) := do
  if ← withReducible (isDefEq ty goal) then return some t
  let ty ← whnf ty
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    if let some p ← findConj goal (mkApp3 (mkConst ``And.left) a b t) a then return some p
    findConj goal (mkApp3 (mkConst ``And.right) a b t) b
  else return none

syntax (name := conjAssumption) "conj_assumption" : tactic

@[tactic conjAssumption] def evalConjAssumption : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let goal ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some p ← findConj goal d.toExpr (← instantiateMVars d.type) then
      g.assign p
      replaceMainGoal []
      return
  throwError "conj_assumption: no hypothesis or conjunct of one is the goal"

macro_rules
  | `(tactic| cut_auto) => `(tactic| (
      cut_intro
      intro g m hA
      try dsimp only at hA ⊢
      refine ⟨(JoinIn.ok (by decide) (by decide) ?hJ).1, (JoinIn.ok (by decide) (by decide) ?hJ).2,
        ?_, ?_⟩
      all_goals conj_assumption))

/-! ## S11: `oblig_auto`, `budget_auto`, `leaf_auto` -/

/-- An obligation by region arithmetic: `leaf_norm`; the region values in normal form
(`measure_norm` on the goal and the arithmetic hypotheses: the `Env`'s region list and
variables as machine terms, closed masks as numerals); the goal rewritten with the values the
facts fix (`sym_rw`); then a hypothesis, `omega`, `bv_omega` or `region_arith`; last, the same
with the cut's assertion opened (`assert_open`: an invariant's bounds). -/
syntax "oblig_region" : tactic
macro_rules
  | `(tactic| oblig_region) => `(tactic| (
      leaf_norm
      measure_norm at *
      sym_rw
      measure_norm
      first
        | assumption
        | omega
        | bv_omega
        | region_arith
        | (assert_open; measure_norm at *; first | omega | bv_omega)))

/-- Each memory obligation of a leaf (`Oblig.holds env o` after the leaf's conditions and the
`@[zesu_fact]` facts of the cut's assertion are hypotheses).

Goal grammar, read off the manual `oblig` leaves (S11: TX `068_0` `068_1` `0d8_0` `0d8_1` `10c_0`
.. `10c_3` `15c_0` `15c_1` `1a0_0` .. `1a0_3` `1f8_0` `25c_0` `340_0` `3d4_1` `4a0_0` `4a0_1`;
DTF `80000634_0`, `800006f4_0` (byte loops), `80000a00_2`, `80000bec_2` (call arguments), the
return leaf; F6's loop heads):

    O ::= aligned (bin and (init r off 8) (lit c)) n   -- return through the saved `ra`
        | aligned (bin and (var i) (lit c)) n            -- the same, `ra` held in a variable
        | inBounds r off (var i) scale n                 -- read at an index (loop cursor,
                                                         --   offset into a decoded payload)
    holds env (aligned x n)          ↔ (x.eval env).toNat % n = 0
    holds env (inBounds r off i s n) ↔ off + s * (env.vars i).toNat + n ≤ env.size r

`env` is the cut's `Env`: a definition whose regions are a literal list of (base, size) pairs
of machine terms and whose variables are machine terms. Closed by a `@[zesu_oblig]` lemma
(`zesu_apply`), else `oblig_region` (alignment: the saved `ra` equals the entry `ra`, whose
alignment is a fact; bounds: linear arithmetic over the region sizes and the facts, including
the invariant's fields), else normalisation and `field_auto`. Not closed: bounds that follow
only from per-function semantics outside the assertion (the payload length of a decoded item:
TX `10c_3`, `1a0_3`). -/
syntax "oblig_auto" : tactic
macro_rules
  | `(tactic| oblig_auto) => `(tactic| (
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
        false_implies, implies_true, and_true]
      try and_intros
      all_goals first | oblig_region | zesu_apply | (leaf_norm; and_intros <;> field_auto)))

/-- A budget inequality `steps ≤ c.budget g m` (or one between two cuts' budgets): the budget
evaluated at the literal cut (`measure_norm`: the cut's budget definition and its measures
unfolded, a budget table read at the literal address), the `@[zesu_fact]` measure facts among
the hypotheses normalised the same way, then `omega`, splitting the budget's `if`s first if
needed. -/
syntax "budget_auto" : tactic
macro_rules
  | `(tactic| budget_auto) => `(tactic| (
      leaf_norm
      all_goals (measure_norm at *
                 first | omega | (split <;> omega) | (split <;> split <;> omega))))

/-- `leaf_auto`: the cut's assertion facts (`zesu_facts`), then either the leaf is infeasible
(the conditions and facts normalised, `False` by `omega`, `bv_omega` or `simp_all`; or the
conditions in `simp` normal form rewritten with the facts) or its main path closes:
`oblig_auto`, `budget_auto`, and the exit goal (`exit_intro`, each conjunct by `field_auto`).
One rule, so a leaf that fails runs each stage once. -/
macro_rules
  | `(tactic| leaf_auto) => `(tactic| (
      leaf_intro
      intro g m hA hc
      try dsimp only at hA hc ⊢
      zesu_facts
      first
        | (exfalso
           first
             | (leaf_norm; first | omega | bv_omega | (simp_all [zesu_simp]; done))
             | (sym_simp at hc
                try simp only [zesu_simp] at hc
                simp at hc
                simp only [*] at hc
                first | (simp at hc; done) | (simp_all; done)))
        | (refine ⟨?_, ?_, fun m' hm' he hso => ?_⟩
           · oblig_auto
           · budget_auto
           · try dsimp only at he
             match_regs hm'
             exit_intro
             all_goals (try dsimp only)
             all_goals leaf_norm
             all_goals (and_intros <;> field_auto))))

/-- `leaf_diag` (syntax in `Vc/Assemble`): `leaf_auto` in one pass that names what failed. It
runs `leaf_auto`'s stages and closes the goal when they all close; otherwise it fails at the
first stage that does not close, with its class: `oblig`, `budget`, `exit` (no cut or callee for
the exit), then by exit kind `post` (return), `cut` (assertion at the next cut), `tail` (tail
callee), `callee-pre` (callee entry and precondition), `return-cut` (assertion after the call),
followed by the head symbol of the first conjunct `field_auto` does not close. `zesu_auto` uses
it, so a leaf that fails runs each stage once and stops at its first open conjunct. -/
@[tactic leafDiagCmd] unsafe def evalLeafDiag : Tactic := fun _ => withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOfArity ``LeafGoal 5 do throwError "class other: not a LeafGoal"
  let a := t.getAppArgs
  let l ← evalExpr Leaf (mkConst ``Leaf) a[4]!
  let tailOf := mkAppN (mkConst ``Plan.tail) #[a[0]!, a[1]!, a[2]!]
  let kind ← match l.exit with
    | .ret _ => pure "post"
    | .at pc => do
      let isTail ← evalExpr Bool (mkConst ``Bool)
        (← mkAppM ``Option.isSome #[mkApp tailOf (mkNatLit pc)])
      pure (if isTail then "tail" else "cut")
    | .jumpInd _ => pure "cut"
    | .call _ _ | .callInd _ _ => pure "callee"
  let headOf (g : MVarId) : TacticM String := do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    return match ty.getAppFn.constName? with
      | some n => n.toString
      | none => "?"
  -- `tac` at `g`: the goals it leaves, or `none` when it fails
  let run (tac : TSyntax `tactic) (g : MVarId) : TacticM (Option (List MVarId)) := do
    let s ← saveState
    try some <$> evalTacticAt tac g catch _ => s.restore; pure none
  -- `tac` closes `g`, else the class `c` with the head of `g`
  let close (tac : TSyntax `tactic) (g : MVarId) (c : String) : TacticM Unit := do
    match ← run tac g with
    | some [] => pure ()
    | _ => throwError "class {c} {← headOf g}"
  evalTactic (← `(tactic| (leaf_intro; intro g m hA hc; try dsimp only at hA hc ⊢; zesu_facts)))
  let g ← getMainGoal
  if let some [] ← run (← `(tactic| (
      exfalso
      first
        | (leaf_norm; first | omega | bv_omega | (simp_all [zesu_simp]; done))
        | (sym_simp at hc
           try simp only [zesu_simp] at hc
           simp at hc
           simp only [*] at hc
           first | (simp at hc; done) | (simp_all; done))))) g then
    replaceMainGoal []
    return
  evalTactic (← `(tactic| refine ⟨?_, ?_, fun m' hm' he hso => ?_⟩))
  let [gO, gB, gE] ← getGoals | throwError "class other: leaf goal shape"
  close (← `(tactic| oblig_auto)) gO "oblig"
  close (← `(tactic| budget_auto)) gB "budget"
  let some gs ← run (← `(tactic| ((try dsimp only at he); match_regs hm'; exit_intro))) gE
    | throwError "class exit"
  let mut i := 0
  for g in gs do
    let c := if kind == "callee" then (if i < 2 then "callee-pre" else "return-cut") else kind
    let some gs' ← run (← `(tactic| ((try dsimp only); leaf_norm))) g
      | throwError "class {c} {← headOf g}"
    for g' in gs' do
      let some cs ← run (← `(tactic| and_intros)) g' | throwError "class {c} {← headOf g'}"
      for c' in cs do close (← `(tactic| field_auto)) c' c
    i := i + 1
  replaceMainGoal []

end ZesuExec.Vc
