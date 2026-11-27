import ZesuExec.Vc.Assemble
import ZesuExec.Vc.SoundW
import ZesuExec.Vc.Tactics

/-!
# Obligation framework commands for plans with callee summaries

`zesu_planw`, `zesu_autow` and `zesu_assemblew` are `zesu_plan`, `zesu_auto` and `zesu_assemble`
for a `PlanW` (runs by `runWith`). The items and their statements:

* `F.cut_<pc> : CutOK F.plan.toPlan F.plan.cuts[i]!`;
* `F.leaf_<pc>_<j>` for a leaf without summarised calls:
  `LeafGoal F.plan.toPlan F.plan.cuts[i]! ((F.plan.wleaves <pc>)[j]!).leaf`, for a leaf with calls:
  `LeafGoalC F.plan F.plan.cuts[i]! (F.plan.wleaves <pc>)[j]!`;
* `F.call_<pc>_<k> : CallGoal F.plan F.plan.cuts[i]! (F.plan.callsAt <pc>)[k]!`.

`F.reach_from` / `F.reach` come from `vc_soundW`; the run equations are checked by `Eq.refl`, or
by the theorem `F.run_<pc>` when it exists (`runProof?`), and `hpos` and the call-free test of
each leaf by kernel `decide`. `zesu_autow` tries `cut_auto`
and, on leaves without calls, `leaf_auto`. `unsafe` only evaluates the plan to list its items.
-/

namespace ZesuExec.Vc
open Lean Elab Command Meta
open ZesuExec.Sym

def callItem (fn : Name) (pc k : Nat) : Name := fn ++ Name.mkSimple s!"call_{hexNat pc}_{k}"

def planTxt (fn : Name) : String := rootTxt (fn ++ `plan)

def cutGoalTxtW (fn : Name) (i : Nat) : String :=
  s!"ZesuExec.Vc.CutOK {planTxt fn}.toPlan {cutTxt fn i}"

def leafGoalTxtW (fn : Name) (i pc j : Nat) (plain : Bool) : String :=
  if plain then
    s!"ZesuExec.Vc.LeafGoal {planTxt fn}.toPlan {cutTxt fn i} ((({planTxt fn}.wleaves {pc})[{j}]!).leaf)"
  else
    s!"ZesuExec.Vc.LeafGoalC {planTxt fn} {cutTxt fn i} (({planTxt fn}.wleaves {pc})[{j}]!)"

def callGoalTxt (fn : Name) (i pc k : Nat) : String :=
  s!"ZesuExec.Vc.CallGoal {planTxt fn} {cutTxt fn i} (({planTxt fn}.callsAt {pc})[{k}]!)"

/-- Per cut point: pc, whether each leaf is free of summarised calls, the number of distinct calls. -/
structure CutW where
  pc : Nat
  plain : Array Bool
  calls : Nat
  deriving Inhabited

unsafe def evalCutsW (fn : Name) : TermElabM (Array CutW × Array CutInfo) := do
  let p := planTxt fn
  let ty ← inferType (mkConst (fn ++ `plan))
  unless (← whnfR ty).isAppOfArity ``PlanW 2 do throwError "zesu: {fn}.plan is not a PlanW"
  let natNat ← elabClosed "List (Nat × Nat)"
  let cs ← evalExpr (List (Nat × Nat)) natNat
    (← elabClosed s!"{p}.cuts.map (fun c => (c.pc, c.S.steps))" natNat)
  let leafTy ← elabClosed "List ZesuExec.Sym.LeafW"
  let callTy ← elabClosed "List ZesuExec.Sym.CallRec"
  let mut ws : Array CutW := #[]
  let mut infos : Array CutInfo := #[]
  for (pc, s0) in cs do
    if infos.any (·.pc == pc) then throwError "zesu: two cut points at 0x{hexNat pc}"
    let ls ← evalExpr (List LeafW) leafTy (← elabClosed s!"{p}.wleaves {pc}" leafTy)
    let calls ← evalExpr (List CallRec) callTy (← elabClosed s!"{p}.callsAt {pc}" callTy)
    ws := ws.push { pc, plain := ls.toArray.map (·.calls.isEmpty), calls := calls.length }
    infos := infos.push { pc, leaves := ls.toArray.map fun lw =>
      let l := lw.leaf
      let (e, t, ts) := exitInfo l.exit
      { exit := e, target := t, targetSym := ts, steps := l.S.steps - s0,
        conds := l.conds.length, obligs := l.obligs.length : LeafInfo } }
  pure (ws, infos)

/-- `leaf_auto` for a leaf through summarised calls (`LeafGoalC`); rules below and in
function files. Placeholder: fails. -/
syntax (name := leafcAuto) "leafc_auto" : tactic
macro_rules | `(tactic| leafc_auto) => `(tactic| fail "leafc_auto: no rule closed the goal")

syntax (name := zesuPlanWCmd) "zesu_planw " ident " := " term : command
syntax (name := zesuAutoWCmd) "zesu_autow " ident : command
syntax (name := zesuAssembleWCmd) "zesu_assemblew " ident : command

@[command_elab zesuPlanWCmd]
unsafe def elabZesuPlanW : CommandElab := fun stx => do
  let fn ← fnName stx[1]
  if (planOf? (← getEnv) fn).isSome then throwError "zesu_planw: {fn} already has a plan"
  let pid := mkIdent (`_root_ ++ fn ++ `plan)
  elabCommand (← `(command| def $pid := $(⟨stx[3]⟩)))
  let (ws, cuts) ← liftTermElabM (evalCutsW fn)
  modifyEnv (zesuExt.addEntry · (.plan fn cuts))
  let mut msg := s!"{fn}: {cuts.size} cut points"
  for c in ws do
    msg := msg ++ s!"\n  0x{hexNat c.pc}: {c.plain.size} leaves \
      ({(c.plain.filter (!·)).size} through summarised calls), {c.calls} calls"
  logInfo msg

@[command_elab zesuAutoWCmd]
unsafe def elabZesuAutoW : CommandElab := fun stx => do
  let fn ← fnName stx[1]
  unless (planOf? (← getEnv) fn).isSome do throwError "zesu_autow: no plan for {fn}"
  let (ws, _) ← liftTermElabM (evalCutsW fn)
  let mut nAuto := 0
  let mut nTried := 0
  for h : i in [0:ws.size] do
    let c := ws[i]
    let cn := cutItem fn c.pc
    unless (← getEnv).contains cn do
      nTried := nTried + 1
      tryItem fn cn (cutGoalTxtW fn i) (← `(tactic| cut_auto))
      if (← getEnv).contains cn then nAuto := nAuto + 1
    for h : j in [0:c.plain.size] do
      let ln := leafItem fn c.pc j
      if !(← getEnv).contains ln then
        nTried := nTried + 1
        if c.plain[j] then
          tryItem fn ln (leafGoalTxtW fn i c.pc j true) (← `(tactic| leaf_auto))
          if (← getEnv).contains ln then nAuto := nAuto + 1
          else tryItem fn ln (leafGoalTxtW fn i c.pc j true) (← `(tactic| leaf_diag))
        else
          tryItem fn ln (leafGoalTxtW fn i c.pc j false) (← `(tactic| leafc_auto))
          if (← getEnv).contains ln then nAuto := nAuto + 1
  logInfo s!"{fn}: zesu_autow closed {nAuto} of {nTried} items"

/-- A kernel `decide` proof of the proposition `txt`. -/
def decideTxt (txt : String) : TermElabM Expr := do
  let p ← elabClosed txt (mkSort .zero)
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  pure (mkApp3 (mkConst ``of_decide_eq_true) p inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)))

@[command_elab zesuAssembleWCmd]
unsafe def elabZesuAssembleW : CommandElab := fun stx => do
  let fn ← fnName stx[1]
  unless (planOf? (← getEnv) fn).isSome do throwError "zesu_assemblew: no plan for {fn}"
  let (ws, _) ← liftTermElabM (evalCutsW fn)
  let env ← getEnv
  let autos : Array Name := (zesuEntries env).filterMap fun
    | .attempt f n true _ => if f == fn then some n else none
    | _ => none
  let mut items : Array (Name × Name × String) := #[]
  for h : i in [0:ws.size] do
    let c := ws[i]
    let cn := cutItem fn c.pc
    items := items.push (cn, Name.mkSimple cn.getString!, cutGoalTxtW fn i)
    for h : j in [0:c.plain.size] do
      let ln := leafItem fn c.pc j
      items := items.push (ln, Name.mkSimple ln.getString!, leafGoalTxtW fn i c.pc j c.plain[j])
    for k in [0:c.calls] do
      let kn := callItem fn c.pc k
      items := items.push (kn, Name.mkSimple kn.getString!, callGoalTxt fn i c.pc k)
  let mut manual := #[]
  let mut opens := #[]
  for (n, _, txt) in items do
    match env.find? n with
    | some ci =>
      let ok ← liftTermElabM do
        let ty ← elabClosed txt (mkSort .zero)
        isDefEq ci.type ty
      unless ok do throwError "zesu_assemblew: {n} does not state `{txt}`"
      unless autos.contains n do manual := manual.push n
    | none => opens := opens.push n
  let openName := fn ++ `Open
  let fields := items.filter (opens.contains ·.1) |>.map fun (_, f, txt) => s!"\n  {f} : {txt}"
  let structTxt := s!"structure {rootTxt openName} : Prop" ++
    (if fields.isEmpty then "" else " where" ++ String.join fields.toList)
  elabCommand (← liftCoreM (parseTxt `command structTxt))
  liftTermElabM do
    let P := mkConst (fn ++ `plan)
    let pty ← whnfR (← inferType P)
    let #[σ, img] := pty.getAppArgs | throwError "zesu_assemblew: {fn}.plan is not a PlanW"
    let vc := mkApp3 (mkConst ``vc_soundW) σ img P
    let vcTy ← inferType vc
    let cutTy := mkApp (mkConst ``Cut) σ
    let cutsE ← elabClosed s!"{planTxt fn}.cuts"
    let n := ws.size
    let cutE (i : Nat) : TermElabM Expr := elabClosed (cutTxt fn i)
    let predOf (t : Expr) : TermElabM Expr :=
      forallBoundedTelescope t (some 2) fun xs b => mkLambdaFVars #[xs[0]!] b
    let b1 := vcTy.bindingBody!
    let b2 := b1.bindingBody!
    let b3 := b2.bindingBody!
    let b4 := b3.bindingBody!
    let hrunsTy := vcTy.bindingDomain!
    let hposTy := b1.bindingDomain!
    let hcutTy := b2.bindingDomain!
    let hcallTy := b3.bindingDomain!
    let hleafTy := b4.bindingDomain!
    let leafListTy := mkApp (mkConst ``List [0]) (mkConst ``LeafW)
    let hruns ← allOfIdx cutTy (← predOf hrunsTy) cutsE n fun i => do
      match ← runProof? fn ws[i]!.pc ((← predOf hrunsTy).beta #[← cutE i]) with
      | some p => pure p
      | none =>
        let ls ← elabClosed s!"{planTxt fn}.wleaves {ws[i]!.pc}"
        pure (mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) leafListTy)
          (mkApp2 (mkConst ``Option.some [0]) leafListTy ls))
    let hposInst ← synthInstance (mkApp (mkConst ``Decidable) hposTy)
    let hpos := mkApp3 (mkConst ``of_decide_eq_true) hposTy hposInst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    withLocalDeclD `o (mkConst openName) fun o => do
      let proofOf (name : Name) : Expr :=
        if opens.contains name then mkApp (mkConst (openName ++ Name.mkSimple name.getString!)) o
        else mkConst name
      let hcut ← allOfIdx cutTy (← predOf hcutTy) cutsE n fun i =>
        pure (proofOf (cutItem fn ws[i]!.pc))
      let hcall ← allOfIdx cutTy (← predOf hcallTy) cutsE n fun i => do
        let c := ws[i]!
        let ci ← cutE i
        let Q ← withLocalDeclD `x (mkConst ``CallRec) fun x => do
          mkLambdaFVars #[x] (mkAppN (mkConst ``CallGoal) #[σ, img, P, ci, x])
        let cs ← elabClosed s!"{planTxt fn}.callsAt {c.pc}"
        allOfIdx (mkConst ``CallRec) Q cs c.calls fun k => pure (proofOf (callItem fn c.pc k))
      let hleaf ← allOfIdx cutTy (← predOf hleafTy) cutsE n fun i => do
        let c := ws[i]!
        let ci ← cutE i
        let Q ← withLocalDeclD `l (mkConst ``LeafW) fun l => do
          mkLambdaFVars #[l] (mkAppN (mkConst ``LeafGoalW) #[σ, img, P, ci, l])
        let ls ← elabClosed s!"{planTxt fn}.wleaves {c.pc}"
        allOfIdx (mkConst ``LeafW) Q ls c.plain.size fun j => do
          let pf := proofOf (leafItem fn c.pc j)
          let lj := s!"(({planTxt fn}.wleaves {c.pc})[{j}]!)"
          if c.plain[j]! then
            mkAppM ``LeafGoalW.of_plain #[← decideTxt s!"{lj}.calls = []", pf]
          else
            mkAppM ``LeafGoalW.of_calls #[← decideTxt s!"{lj}.calls ≠ []", pf]
      let concl := b4.bindingBody!
      let val ← mkLambdaFVars #[o] (mkApp5 vc hruns hpos hcut hcall hleaf)
      let ty ← mkForallFVars #[o] concl
      addDecl (.thmDecl { name := fn ++ `reach_from, levelParams := [], type := ty, value := val })
      if opens.isEmpty then
        let v := mkApp (mkConst (fn ++ `reach_from)) (mkConst (openName ++ `mk))
        addDecl (.thmDecl { name := fn ++ `reach, levelParams := [], type := concl, value := v })
  modifyEnv (zesuExt.addEntry · (.assembled fn manual opens))
  logInfo s!"{fn}: {items.size} items, {items.size - manual.size - opens.size} auto, \
    {manual.size} manual, {opens.size} open"

open Lean.Elab.Tactic in
/-- `leafc_intro`: `LeafGoalC σ img P c l` with the cut unfolded and the leaf evaluated. -/
syntax (name := leafcIntroCmd) "leafc_intro" : tactic

open Lean.Elab.Tactic in
/-- `call_intro`: `CallGoal σ img P c call` with the cut unfolded and the call evaluated. -/
syntax (name := callIntroCmd) "call_intro" : tactic

open Lean.Elab.Tactic in
@[tactic leafcIntroCmd] unsafe def evalLeafCIntro : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``LeafGoalC 5 do throwError "leafc_intro: goal is not `LeafGoalC`"
  let a := t.getAppArgs
  let c ← unfoldCut a[3]!
  let l ← evalClosed LeafW (mkConst ``LeafW) a[4]!
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN (mkConst ``LeafGoalC) #[a[0]!, a[1]!, a[2]!, c, l])]

open Lean.Elab.Tactic in
@[tactic callIntroCmd] unsafe def evalCallIntro : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``CallGoal 5 do throwError "call_intro: goal is not `CallGoal`"
  let a := t.getAppArgs
  let c ← unfoldCut a[3]!
  let k ← evalClosed CallRec (mkConst ``CallRec) a[4]!
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN (mkConst ``CallGoal) #[a[0]!, a[1]!, a[2]!, c, k])]

/-- An infeasible leaf through summarised calls: move its conditions back to the cut's `Env`
(`SBool.conds_agree`, checked by `decide`), then as `leaf_auto`'s facts rule. -/
macro_rules
  | `(tactic| leafc_auto) => `(tactic| (
      leafc_intro
      intro g m hA env' hag hc0
      try dsimp only at hA hag hc0 ⊢
      have hc := SBool.conds_agree hag (by decide) hc0
      clear hc0
      exfalso
      zesu_facts
      first
        | (leaf_norm; first | omega | bv_omega | (simp_all [zesu_simp]; done))
        | (sym_simp at hc
           try simp only [zesu_simp] at hc
           simp at hc
           simp only [*] at hc
           first | (simp at hc; done) | (simp_all; done))))

end ZesuExec.Vc
