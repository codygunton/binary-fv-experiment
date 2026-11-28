import Lean
import ZesuExec.Vc.Sound

/-!
# Obligation framework: commands (programme plan S2 step 4)

* `zesu_plan F := P` adds `def F.plan := P` (a `Plan σ img`), evaluates its cut points and the
  leaves of each with compiled code, and records them in `zesuExt`.
* `zesu_auto F` tries `cut_auto` on `CutOK` of every cut point and `leaf_diag` (`leaf_auto`'s
  stages in one pass that names the first stage left open) on `LeafGoal` of every leaf that has
  no theorem yet; a success becomes the theorem `F.cut_<pc>` or `F.leaf_<pc>_<i>` (`pc` in
  lower-case hex) and is recorded `auto`; a failure is recorded with the number of remaining goals
  and the head symbol of the first, or the tactic's error (for a leaf, its residual class).
* `zesu_assemble F` takes the theorems `F.cut_<pc>` / `F.leaf_<pc>_<i>` that exist (hand-written
  ones are `manual`), makes the missing ones the fields of `structure F.Open : Prop`, and adds
  `theorem F.reach_from (o : F.Open)` by `vc_sound`, and `theorem F.reach` when nothing is missing.

The statements are fixed: `F.cut_<pc> : CutOK F.plan F.plan.cuts[i]!` and
`F.leaf_<pc>_<j> : LeafGoal F.plan F.plan.cuts[i]! (F.plan.leaves <pc>)[j]!` where `i` is the
index of the cut point at `pc`. The run equations `run … = some (F.plan.leaves pc)` are
re-checked by the kernel with `Eq.refl`, as `sym_run` does, unless a theorem `F.run_<pc>` exists:
then that theorem is the proof (`runProof?`; its `run` arguments and leaf list must match the
conjunct's by `isDefEq` on the arguments, never by unfolding `run`, else assembly fails naming
the cut), so the kernel compares arguments instead of evaluating every run again in one
declaration; `hpos` by kernel `decide`.
`unsafe` is confined to the evaluation of the plan's cut points and leaves; nothing it computes
is trusted.
-/

namespace ZesuExec.Vc
open Lean Elab Command Meta
open ZesuExec.Sym

/-- One leaf of a recorded plan, for `zesu-status`. `steps` counts from the cut point; `target`
is the exit address when it is a literal, `targetSym` the symbolic target otherwise. -/
structure LeafInfo where
  exit : String
  target : Option Nat
  targetSym : Option String
  steps : Nat
  conds : Nat
  obligs : Nat
  deriving Inhabited, Repr

structure CutInfo where
  pc : Nat
  leaves : Array LeafInfo
  deriving Inhabited, Repr

inductive Entry
  /-- a plan registered by `zesu_plan` for the function `fn` -/
  | plan (fn : Name) (cuts : Array CutInfo)
  /-- a `zesu_auto` attempt on the item `item` (a constant name) -/
  | attempt (fn item : Name) (ok : Bool) (residual : String)
  /-- `zesu_assemble`: items taken from hand-written theorems, and the open items -/
  | assembled (fn : Name) (manual opens : Array Name)
  deriving Inhabited, Repr

initialize zesuExt : SimplePersistentEnvExtension Entry Unit ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ _ => ()
    addImportedFn := fun _ => () }

/-- Every entry: imported modules in order, then this module's. -/
def zesuEntries (env : Environment) : Array Entry := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    out := out ++ zesuExt.getModuleEntries env i
  out ++ (zesuExt.getEntries env).reverse.toArray

def planOf? (env : Environment) (fn : Name) : Option (Array CutInfo) :=
  (zesuEntries env).findSome? fun | .plan f cs => if f == fn then some cs else none | _ => none

def hexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def cutItem (fn : Name) (pc : Nat) : Name := fn ++ Name.mkSimple s!"cut_{hexNat pc}"
def leafItem (fn : Name) (pc j : Nat) : Name := fn ++ Name.mkSimple s!"leaf_{hexNat pc}_{j}"

/-- Fully qualified source text of a name. -/
def rootTxt (n : Name) : String := "_root_." ++ n.toString

def cutTxt (fn : Name) (i : Nat) : String := s!"({rootTxt (fn ++ `plan)}.cuts[{i}]!)"

def cutGoalTxt (fn : Name) (i : Nat) : String :=
  s!"ZesuExec.Vc.CutOK {rootTxt (fn ++ `plan)} {cutTxt fn i}"

def leafGoalTxt (fn : Name) (i pc j : Nat) : String :=
  s!"ZesuExec.Vc.LeafGoal {rootTxt (fn ++ `plan)} {cutTxt fn i} (({rootTxt (fn ++ `plan)}.leaves {pc})[{j}]!)"

/-- Placeholder until plan S4: fails, leaving the goal open. S4 adds `macro_rules`. -/
syntax (name := leafAuto) "leaf_auto" : tactic
/-- Placeholder until plan S4: fails, leaving the goal open. S4 adds `macro_rules`. -/
syntax (name := cutAuto) "cut_auto" : tactic
macro_rules | `(tactic| leaf_auto) => `(tactic| fail "leaf_auto: no automation before plan S4")
macro_rules | `(tactic| cut_auto) => `(tactic| fail "cut_auto: no automation before plan S4")
/-- `leaf_auto`'s stages in one pass (implemented in `Vc/Tactics`): closes the goal when they all
close, else fails with the residual class of the first stage left open as its message. -/
syntax (name := leafDiagCmd) "leaf_diag" : tactic

def parseTxt (cat : Name) (s : String) : CoreM Syntax := do
  match Parser.runParserCategory (← getEnv) cat s with
  | .ok stx => pure stx
  | .error e => throwError "zesu: cannot parse `{s}`: {e}"

def elabClosed (s : String) (ty? : Option Expr := none) : TermElabM Expr := do
  let e ← Term.elabTerm (← parseTxt `term s) ty?
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "zesu: `{s}` has metavariables"
  pure e

def exitInfo : Exit → String × Option Nat × Option String
  | .at pc => ("at", some pc, none)
  | .call t _ => ("call", some t, none)
  | .callInd t _ => ("callInd", none, some (reprStr t))
  | .ret t => ("ret", none, some (reprStr t))
  | .jumpInd t => ("jumpInd", none, some (reprStr t))

syntax (name := zesuPlanCmd) "zesu_plan " ident " := " term : command
syntax (name := zesuAutoCmd) "zesu_auto " ident : command
syntax (name := zesuAssembleCmd) "zesu_assemble " ident : command

/-- The function id `F` named in the current namespace. -/
def fnName (id : Syntax) : CommandElabM Name := return (← getCurrNamespace) ++ id.getId

@[command_elab zesuPlanCmd]
unsafe def elabZesuPlan : CommandElab := fun stx => do
  let fn ← fnName stx[1]
  if (planOf? (← getEnv) fn).isSome then throwError "zesu_plan: {fn} already has a plan"
  let pid := mkIdent (`_root_ ++ fn ++ `plan)
  elabCommand (← `(command| def $pid := $(⟨stx[3]⟩)))
  let p := rootTxt (fn ++ `plan)
  let cuts ← liftTermElabM do
    let ty ← inferType (mkConst (fn ++ `plan))
    unless (← whnfR ty).isAppOfArity ``Plan 2 do throwError "zesu_plan: {fn}.plan is not a Plan"
    let natNat ← elabClosed "List (Nat × Nat)"
    let cs ← evalExpr (List (Nat × Nat)) natNat
      (← elabClosed s!"{p}.cuts.map (fun c => (c.pc, c.S.steps))" natNat)
    let leafTy ← elabClosed "List ZesuExec.Sym.Leaf"
    let mut out : Array CutInfo := #[]
    for (pc, s0) in cs do
      if out.any (·.pc == pc) then throwError "zesu_plan: two cut points at 0x{hexNat pc}"
      let ls ← evalExpr (List Leaf) leafTy (← elabClosed s!"{p}.leaves {pc}" leafTy)
      let infos := ls.toArray.map fun l =>
        let (e, t, ts) := exitInfo l.exit
        { exit := e, target := t, targetSym := ts, steps := l.S.steps - s0,
          conds := l.conds.length,
          obligs := l.obligs.length : LeafInfo }
      out := out.push { pc, leaves := infos }
    pure out
  modifyEnv (zesuExt.addEntry · (.plan fn cuts))
  let mut msg := s!"{fn}: {cuts.size} cut points"
  for c in cuts do
    msg := msg ++ s!"\n  0x{hexNat c.pc}: {c.leaves.size} leaves"
  logInfo msg

/-- Try `tac` on the goal `goalTxt`; on success add theorem `name`. A proof with a placeholder (an
error recovered inside the tactic) is a failure. A failure leaves no messages and records the
remaining goals' count and the first one's head symbol, or the tactic's error. -/
def tryItem (fn name : Name) (goalTxt : String) (tac : Syntax) : CommandElabM Unit := do
  let (ok, residual) ← liftTermElabM do
    let ty ← elabClosed goalTxt (mkSort .zero)
    let mv ← mkFreshExprMVar ty
    let saved ← saveState
    let msgs := (← getThe Core.State).messages
    let fail (r : String) : TermElabM (Bool × String) := do
      saved.restore; modifyThe Core.State ({ · with messages := msgs }); return (false, r)
    let res ← try
        let gs ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! <|
          Tactic.withoutRecover (Tactic.evalTactic tac)
        pure (Except.ok gs)
      catch e => pure (Except.error e)
    match res with
    | .ok [] =>
      let v ← instantiateMVars mv
      if v.hasMVar || v.hasSorry then return ← fail "1 goal; incomplete proof"
      addDecl (.thmDecl { name, levelParams := [], type := ty, value := v })
      return (true, "")
    | .ok (g :: gs) =>
      let head ← ppExpr ((← instantiateMVars (← g.getType)).getAppFn)
      fail s!"{gs.length + 1} goals; head {head}"
    | .error e =>
      let msg := ((← e.toMessageData.toString).splitOn "\n").headD ""
      fail s!"1 goal; head {← ppExpr ty.getAppFn}; {String.ofList (msg.toList.take 160)}"
  modifyEnv (zesuExt.addEntry · (.attempt fn name ok residual))

@[command_elab zesuAutoCmd]
def elabZesuAuto : CommandElab := fun stx => do
  let fn ← fnName stx[1]
  let some cuts := planOf? (← getEnv) fn | throwError "zesu_auto: no plan for {fn}"
  let mut nAuto := 0
  let mut nTried := 0
  for h : i in [0:cuts.size] do
    let c := cuts[i]
    let cn := cutItem fn c.pc
    unless (← getEnv).contains cn do
      nTried := nTried + 1
      tryItem fn cn (cutGoalTxt fn i) (← `(tactic| cut_auto))
      if (← getEnv).contains cn then nAuto := nAuto + 1
    for j in [0:c.leaves.size] do
      let ln := leafItem fn c.pc j
      unless (← getEnv).contains ln do
        nTried := nTried + 1
        tryItem fn ln (leafGoalTxt fn i c.pc j) (← `(tactic| leaf_diag))
        if (← getEnv).contains ln then nAuto := nAuto + 1
  logInfo s!"{fn}: zesu_auto closed {nAuto} of {nTried} items"

/-- A proof of `∀ x ∈ l, Q x` (by `forall_mem_of_idx`) from the proofs `pf i : Q l[i]!` for
`i < n`, where `n` is the length of `l`; the kernel checks that the length is `n`. -/
def allOfIdx (α Q l : Expr) (n : Nat) (pf : Nat → TermElabM Expr) : TermElabM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Inhabited [1]) α)
  let Qi := mkApp4 (mkConst ``idxQ) α inst Q l
  let natTy := mkConst ``Nat
  let mut chain := mkConst ``True.intro
  for k' in [0:n] do
    let k := n - 1 - k'
    let tail ← mkListLit natTy ((List.range' (k + 1) (n - k - 1)).map mkNatLit)
    let rest := mkApp2 (mkConst ``AllL) natTy Qi
    chain := mkApp4 (mkConst ``And.intro) (mkApp Qi (mkNatLit k)) (mkApp rest tail) (← pf k) chain
  pure (mkApp5 (mkConst ``forall_mem_of_idx) α inst Q l chain)

/-- The proof of the run equation `want` of the cut at `pc` by the theorem `fn.run_<pc>`, if it
exists. Both statements must be `f a₁ … aₙ = some l` with the same head `f` (`run` or
`runWith`); the arguments and `l` are compared by `isDefEq`, `f` itself is never unfolded. -/
def runProof? (fn : Name) (pc : Nat) (want : Expr) : TermElabM (Option Expr) := do
  let rn := fn ++ Name.mkSimple s!"run_{hexNat pc}"
  let some ci := (← getEnv).find? rn | return none
  let parts (e : Expr) : TermElabM (Option (Expr × Array Expr × Expr)) := do
    let e ← instantiateMVars (← whnfR e)
    let some (_, lhs, rhs) := e.eq? | return none
    let some (_, l) := (← whnfR rhs).app2? ``Option.some | return none
    return some (lhs.getAppFn, lhs.getAppArgs, l)
  let fail : TermElabM (Option Expr) :=
    throwError "zesu_assemble: {rn} does not state the run equation of the cut at 0x{hexNat pc} \
      (same function, arguments and leaves)"
  let some (f₁, as₁, l₁) ← parts want | fail
  let some (f₂, as₂, l₂) ← parts ci.type | fail
  unless f₁.isConst && f₁ == f₂ && as₁.size == as₂.size do return ← fail
  for (a, b) in as₁.zip as₂ do
    unless ← isDefEq a b do return ← fail
  unless ← isDefEq l₁ l₂ do return ← fail
  return some (mkConst rn)

@[command_elab zesuAssembleCmd]
def elabZesuAssemble : CommandElab := fun stx => do
  let fn ← fnName stx[1]
  let some cuts := planOf? (← getEnv) fn | throwError "zesu_assemble: no plan for {fn}"
  let env ← getEnv
  let autos : Array Name := (zesuEntries env).filterMap fun
    | .attempt f n true _ => if f == fn then some n else none
    | _ => none
  -- items: (name, field, statement text)
  let mut items : Array (Name × Name × String) := #[]
  for h : i in [0:cuts.size] do
    let c := cuts[i]
    let cn := cutItem fn c.pc
    items := items.push (cn, Name.mkSimple cn.getString!, cutGoalTxt fn i)
    for j in [0:c.leaves.size] do
      let ln := leafItem fn c.pc j
      items := items.push (ln, Name.mkSimple ln.getString!, leafGoalTxt fn i c.pc j)
  -- check the statements of existing theorems
  let mut manual := #[]
  let mut opens := #[]
  for (n, _, txt) in items do
    match env.find? n with
    | some ci =>
      let ok ← liftTermElabM do
        let ty ← elabClosed txt (mkSort .zero)
        isDefEq ci.type ty
      unless ok do throwError "zesu_assemble: {n} does not state `{txt}`"
      unless autos.contains n do manual := manual.push n
    | none => opens := opens.push n
  -- the structure of open items
  let openName := fn ++ `Open
  let fields := items.filter (opens.contains ·.1) |>.map fun (_, f, txt) => s!"\n  {f} : {txt}"
  let structTxt := s!"structure {rootTxt openName} : Prop" ++
    (if fields.isEmpty then "" else " where" ++ String.join fields.toList)
  elabCommand (← liftCoreM (parseTxt `command structTxt))
  liftTermElabM do
    let P := mkConst (fn ++ `plan)
    let pty ← whnfR (← inferType P)
    let #[σ, img] := pty.getAppArgs | throwError "zesu_assemble: {fn}.plan is not a Plan"
    let vc := mkApp3 (mkConst ``vc_sound) σ img P
    let vcTy ← inferType vc
    let cutTy := mkApp (mkConst ``Cut) σ
    let cutsE := mkApp3 (mkConst ``Plan.cuts) σ img P
    let n := cuts.size
    let cutE (i : Nat) : TermElabM Expr := elabClosed (cutTxt fn i)
    -- the predicate of `∀ c ∈ P.cuts, Q c` in each hypothesis of `vc_sound`
    let predOf (t : Expr) : TermElabM Expr :=
      forallBoundedTelescope t (some 2) fun xs b => mkLambdaFVars #[xs[0]!] b
    let hrunsTy := vcTy.bindingDomain!
    let hposTy := vcTy.bindingBody!.bindingDomain!
    let hcutTy := vcTy.bindingBody!.bindingBody!.bindingDomain!
    let hleafTy := vcTy.bindingBody!.bindingBody!.bindingBody!.bindingDomain!
    let leafListTy := mkApp (mkConst ``List [0]) (mkConst ``Leaf)
    let hruns ← allOfIdx cutTy (← predOf hrunsTy) cutsE n fun i => do
      match ← runProof? fn cuts[i]!.pc ((← predOf hrunsTy).beta #[← cutE i]) with
      | some p => pure p
      | none =>
        let ls ← elabClosed s!"{rootTxt (fn ++ `plan)}.leaves {cuts[i]!.pc}"
        pure (mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) leafListTy)
          (mkApp2 (mkConst ``Option.some [0]) leafListTy ls))
    let hposInst ← synthInstance (mkApp (mkConst ``Decidable) hposTy)
    let hpos := mkApp3 (mkConst ``of_decide_eq_true) hposTy hposInst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    let openTy := mkConst openName
    withLocalDeclD `o openTy fun o => do
      let proofOf (name : Name) : Expr :=
        if opens.contains name then mkApp (mkConst (openName ++ Name.mkSimple name.getString!)) o
        else mkConst name
      let hcut ← allOfIdx cutTy (← predOf hcutTy) cutsE n fun i =>
        pure (proofOf (cutItem fn cuts[i]!.pc))
      let hleaf ← allOfIdx cutTy (← predOf hleafTy) cutsE n fun i => do
        let c := cuts[i]!
        let ci ← cutE i
        let Q ← withLocalDeclD `l (mkConst ``Leaf) fun l => do
          mkLambdaFVars #[l] (mkAppN (mkConst ``LeafGoal) #[σ, img, P, ci, l])
        let ls ← elabClosed s!"{rootTxt (fn ++ `plan)}.leaves {c.pc}"
        allOfIdx (mkConst ``Leaf) Q ls c.leaves.size fun j => pure (proofOf (leafItem fn c.pc j))
      let concl := vcTy.bindingBody!.bindingBody!.bindingBody!.bindingBody!
      let val ← mkLambdaFVars #[o] (mkApp4 vc hruns hpos hcut hleaf)
      let ty ← mkForallFVars #[o] concl
      addDecl (.thmDecl { name := fn ++ `reach_from, levelParams := [], type := ty, value := val })
      if opens.isEmpty then
        let v := mkApp (mkConst (fn ++ `reach_from)) (mkConst (openName ++ `mk))
        addDecl (.thmDecl { name := fn ++ `reach, levelParams := [], type := concl, value := v })
  modifyEnv (zesuExt.addEntry · (.assembled fn manual opens))
  logInfo s!"{fn}: {items.size} items, {items.size - manual.size - opens.size} auto, \
    {manual.size} manual, {opens.size} open"

end ZesuExec.Vc
