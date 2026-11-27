import Lean
import ZesuExec.Vc.Assemble
import ZesuExec.Vc.Regions
import ZesuExec.Sym.Tactic

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
  the plan's step 4; they fail unless the goal is closed.
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
    let some i := pcs.idxOf? pc | throwError "exit_intro: no cut at {pc}"
    let c ← cutStx i
    evalTactic (← `(tactic| (
      simp only [ExitGoal]
      refine ⟨$c, (Plan.getElem!_mem _ (i := $(quote i)) (by decide) : $c ∈ _), ?_, ?_, ?_⟩)))
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
      refine ⟨_, rfl, ?_, ?_, fun m'' hpost =>
        ⟨$c, (Plan.getElem!_mem _ (i := $(quote i)) (by decide) : $c ∈ _), rfl, ?_, ?_, ?_⟩⟩)))
  | _, _ => throwError "exit_intro: exit {e} has no literal target"

/-- Each field of a conjunction: hypothesis, normalisation and arithmetic, `region_tac`.
(No `rfl`/`decide` and only reducible `assumption`: on `Word` goals full unfolding expands
64-bit literals until the recursion limit.) -/
syntax "field_auto" : tactic
macro_rules
  | `(tactic| field_auto) => `(tactic| first
      | with_reducible assumption
      | (leaf_norm; first | (simp_all [zesu_simp]; done) | omega | bv_omega)
      | region_tac)

macro_rules
  | `(tactic| leaf_auto) => `(tactic| (
      leaf_intro
      intro g m hA hc
      try dsimp only at hA hc ⊢
      first
        | leaf_infeasible
        | (refine ⟨?_, ?_, fun m' hm' he hso => ?_⟩
           · leaf_norm
             all_goals (and_intros <;> field_auto)
           · leaf_norm
             all_goals omega
           · try dsimp only at he
             match_regs hm'
             exit_intro
             all_goals (try dsimp only)
             all_goals leaf_norm
             all_goals (and_intros <;> field_auto))))

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

end ZesuExec.Vc
