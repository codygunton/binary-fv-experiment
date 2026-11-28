import ZesuExec.Vc.Assemble
import ZesuExec.Vc.Facts
import ZesuExec.Vc.Legacy

/-!
# `zesu-status` (programme plan S2 step 5, S10.2)

Imports the built `ZesuExec` environment and prints `zmap.status.v1` JSON: every function with a
plan (`zesu_plan`; test plans under `ZesuExec.Test` are skipped) with its cut points and leaves and
the state of each item, then the spike functions of `legacyFns` with `"legacy": true`.

Per function: `id` (`f_<entry hex>`, the static map's id), `fn` (Lean namespace or spike id),
`entry` (integer), `legacy`, `assembled` (`F.reach_from` exists), `cuts`, `open` (open items of
the last `zesu_assemble`), `theorems` (`reach`, `spec`, `sail`, `compliance`: the constants
exist) and `names` (the constants looked up). An item is `auto` when `zesu_auto` proved it,
`manual` when its theorem exists otherwise, `open` else; `residual` (manual and open items) is
the last failed `zesu_auto` attempt's message: for a leaf the `leaf_diag` class (`class <c>
<head>`), else the remaining-goal count and head symbol. Leaf `target` is the exit address
(integer) when it is literal, else `null` with `target_sym` holding the symbolic target; `steps`
counts from the cut point.

Facts measured for the tracking (plan S10.2), per function:

* per cut lemma and leaf, `thm`: the theorem name, `file` (its module's source path), `lines`
  (declaration range, `null` for theorems `zesu_auto` added) and `rule`: `manual`, or
  `auto:<rule>` read from the proof term: `auto:join` (uses `JoinIn.ok`), `auto:cut`,
  `auto:infeasible` (the leaf proof is `False.elim` under the binders), `auto:path`; `+facts`
  when it uses a `@[zesu_fact]` lemma. `null` for open items.
* `hashes`: 64-bit hashes (hex) of the elaborated statements: `spec` (the end theorem's type),
  `pre`, `post` (its `Spec` arguments, abstracted over the theorem's binders), and for plans
  `cuts`, `callees` (fields `callee`, `tail` and, for `PlanW`, `sums`). A hash covers every
  constant of this package the statement mentions, transitively (definitions by value,
  theorems by type); constants of `Init`, `Std` and `Lean` by name.
* `hyps`: the end theorem's binders that are hypotheses, not `Pre`: a proposition, or a
  structure with a propositional field (a bundle of assumptions such as `AllocAssumptions`);
  each `{name, type, spec_entries}`, `spec_entries` the entries of the `Spec`s it assumes (the
  hypothesis itself or its fields): the functions the theorem rests on.
* `nonvacuity`, `snapshot`: the constants `pre_nonvacuous` and `post_snapshot` in the end
  theorem's namespace, when they exist (the registration convention), else `null`.
* `post_consts`: the constants of this package outside the function's own namespace that its
  `Post` mentions, unfolding the function's own definitions. `zmap merge` joins them with the
  model constants in `map/reviews.json` (`meaning_link`).
* `spec_callees` (functions of `legacyFns` without a plan): the entries of the other functions
  whose end theorems (a plan's `reach`, `reach_from` or end theorem; a legacy end theorem) the
  end theorem's proof uses, through this package's constants; another function's end theorem is
  not entered. `zmap merge` takes them as the proof callees (a plan's come from its leaves).
-/

namespace ZesuExec.Vc
open Lean Meta

/-! ## Measured facts -/

def libModule (m : Name) : Bool := m.getRoot ∈ [`Init, `Std, `Lean, `Lake]

/-- A constant of this package (or a dependency outside the Lean distribution). -/
def userConst (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => !libModule (env.header.moduleNames[i.toNat]?.getD .anonymous)
  | none => true

abbrev HashM := StateM (Std.HashMap Name UInt64)

mutual
  /-- Structural hash of `e` mixed with the deep hashes of the package constants it uses. -/
  partial def deepHash (env : Environment) (e : Expr) : HashM UInt64 := do
    let mut h := e.hash
    for c in e.getUsedConstants do
      if userConst env c then h := mixHash h (← constHash env c)
    return h

  partial def constHash (env : Environment) (c : Name) : HashM UInt64 := do
    if let some h := (← get)[c]? then return h
    modify (·.insert c (hash c))  -- a recursive reference sees the name only
    let body ← match env.find? c with
      | some (.thmInfo i) => deepHash env i.type
      | some (.defnInfo i) => return mixHash (← deepHash env i.type) (← deepHash env i.value)
      | some ci => deepHash env ci.type
      | none => pure 0
    let h := mixHash (hash c) body
    modify (·.insert c h)
    return h
end

def hex64 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- Package constants `e` mentions outside `ns`, unfolding the definitions under `ns`. -/
partial def mentions (env : Environment) (ns : Name) (e : Expr) : StateM NameSet Unit := do
  for c in e.getUsedConstants do
    if (← get).contains c || !userConst env c then continue
    modify (·.insert c)
    if ns.isPrefixOf c then
      if let some (.defnInfo i) := env.find? c then mentions env ns i.value

/-- `e` with its head constants unfolded until it is an application of the constructor `ctor`. -/
partial def unfoldTo (env : Environment) (ctor : Name) (e : Expr) (fuel : Nat := 32) :
    Option Expr :=
  let e := e.headBeta
  match e.getAppFn with
  | .const c ls =>
    if c == ctor then some e
    else match fuel, env.find? c with
      | n + 1, some (.defnInfo i) =>
        unfoldTo env ctor ((i.value.instantiateLevelParams i.levelParams ls).beta e.getAppArgs) n
      | _, _ => none
  | .mdata _ b => unfoldTo env ctor b fuel
  | _ => none

/-- The fields of a structure instance `e` of `S`, parents flattened: `[(field, value)]`. -/
partial def structFields (env : Environment) (S : Name) (e : Expr) : List (Name × Expr) :=
  match getStructureInfo? env S, (getStructureCtor env S |>.name) with
  | some info, ctor =>
    match unfoldTo env ctor e with
    | some app =>
      let args := app.getAppArgs.toList.drop (getStructureCtor env S).numParams
      (info.fieldNames.toList.zip args).flatMap fun (f, v) =>
        match isSubobjectField? env S f with
        | some P => structFields env P v
        | none => [(f, v)]
    | none => []
  | none, _ => []

/-- The rule that closed an auto item, from its proof term. -/
def autoRule (env : Environment) (isCut : Bool) (v : Expr) : String :=
  let cs := v.getUsedConstants
  let facts := if cs.any (zesuFactAttr.hasTag env) then "+facts" else ""
  if cs.contains `ZesuExec.Vc.JoinIn.ok then "auto:join" ++ facts
  else if isCut then "auto:cut" ++ facts
  else
    -- `id T (fun g m hA hc => id P body)`: the body's head
    let rec body (e : Expr) (n : Nat) : Expr :=
      match n, e with
      | n + 1, .lam _ _ b _ => body b n
      | n + 1, .mdata _ b => body b n
      | n + 1, e => if e.isAppOfArity ``id 2 then body e.appArg! n else e
      | 0, e => e
    let b := body v 16
    if b.isAppOf ``False.elim || b.isAppOf ``absurd then "auto:infeasible" ++ facts
    else "auto:path" ++ facts

def moduleFile (env : Environment) (n : Name) : Option String :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?.map fun m =>
    (System.FilePath.mk ("/".intercalate (m.components.map (·.toString))) |>.addExtension
      "lean").toString

/-- `thm` of an item: name, file, lines, rule; `null` when the theorem does not exist. -/
def thmJson (env : Environment) (isCut : Bool) (state : String) (n : Name) : MetaM Json := do
  let some ci := env.find? n | return Json.null
  let rule := if state == "auto" then autoRule env isCut ci.value! else "manual"
  let lines := match ← findDeclarationRanges? n with
    | some r => toJson [r.range.pos.line, r.range.endPos.line]
    | none => Json.null
  return Json.mkObj [("name", toJson n.toString), ("file", toJson (moduleFile env n)),
    ("lines", lines), ("rule", toJson rule)]

/-- The entry of `t` when it is `∀ …, Spec img entry bound P Q` with a closed entry. -/
def specEntry? (t : Expr) : MetaM (Option Nat) :=
  forallTelescope t fun _ b => do
    unless b.isAppOfArity `ZesuExec.Spec 5 do return none
    let e ← whnf (b.getArg! 1)
    match e with
    | .lit (.natVal n) => return some n
    | _ => return (← evalNat e)

/-- A binder that is a hypothesis: a proposition, or a structure with a propositional field.
`some entries` (the entries of the `Spec`s it assumes: the binder itself or its fields), `none`
when it is no hypothesis. -/
def hypEntries? (x : Expr) : MetaM (Option (List Nat)) := do
  let t ← inferType x
  if ← isProp t then return some ((← specEntry? t).toList)
  let .const S _ := (← whnf t).getAppFn | return none
  unless isStructure (← getEnv) S do return none
  let mut hyp := false
  let mut entries := []
  for f in getStructureFields (← getEnv) S do
    try
      let ft ← inferType (← mkProjection x f)
      if ← isProp ft then
        hyp := true
        if let some e ← specEntry? ft then entries := entries ++ [e]
    catch _ => pure ()
  return if hyp then some entries else none

/-- Facts from the end theorem `spec`: hashes, non-`Pre` hypotheses, `Post`'s package constants. -/
def specFacts (spec : Name) : MetaM (List (String × Json)) := do
  let env ← getEnv
  let some ci := env.find? spec | return []
  let ns := spec.getPrefix
  forallTelescope ci.type fun xs body => do
    let hyps ← xs.toList.filterMapM fun x => do
      if let some es ← hypEntries? x then
        return some (Json.mkObj [("name", toJson (← x.fvarId!.getUserName).toString),
          ("type", toJson (toString (← ppExpr (← inferType x)))), ("spec_entries", toJson es)])
      return none
    let (specH, s) := (constHash env spec).run {}
    let mut out := [("hyps", Json.arr hyps.toArray), ("spec", toJson (hex64 specH))]
    if body.isAppOfArity `ZesuExec.Spec 5 then
      let pre ← mkLambdaFVars xs (body.getArg! 3)
      let post ← mkLambdaFVars xs (body.getArg! 4)
      let ((preH, postH), _) := (do return (← deepHash env pre, ← deepHash env post)).run s
      let ((), consts) := (mentions env ns post).run {}
      out := out ++ [("pre", toJson (hex64 preH)), ("post", toJson (hex64 postH)),
        ("post_consts", toJson ((consts.toList.filter (!ns.isPrefixOf ·)).map (·.toString)
          |>.toArray.qsort (· < ·)))]
    return out

/-- Hashes of a plan's cut points and callee fields. -/
def planHashes (env : Environment) (fn : Name) : List (String × Json) :=
  match env.find? (fn ++ `plan) with
  | none => []
  | some ci =>
  let S := if (ci.type.getAppFn.constName?) == some `ZesuExec.Vc.PlanW then `ZesuExec.Vc.PlanW
    else `ZesuExec.Vc.Plan
  let fs := structFields env S ci.value!
  if fs.isEmpty then [] else
  let pick (names : List Name) : HashM UInt64 := do
    let mut h : UInt64 := 7
    for (f, v) in fs do
      if names.contains f then h := mixHash h (← deepHash env v)
    return h
  let ((cutsH, calleeH), _) := (do return (← pick [`cuts], ← pick [`callee, `tail, `sums])).run {}
  [("cuts", toJson (hex64 cutsH)), ("callees", toJson (hex64 calleeH))]

/-- Every S10.2 fact of a function whose end theorem is `spec`. -/
def factsJson (env : Environment) (spec : Name) (plan : Option Name) : MetaM (List (String × Json)) := do
  let sf ← specFacts spec
  let hashes := (sf.filter (·.1 ∈ ["spec", "pre", "post"])) ++ (plan.map (planHashes env)).getD []
  let ns := spec.getPrefix
  let reg (s : String) : Json :=
    let n := ns ++ Name.mkSimple s
    if env.contains n then toJson n.toString else Json.null
  return [("hashes", Json.mkObj hashes), ("hyps", (sf.lookup "hyps").getD (Json.arr #[])),
    ("nonvacuity", reg "pre_nonvacuous"), ("snapshot", reg "post_snapshot"),
    ("post_consts", (sf.lookup "post_consts").getD (Json.arr #[]))]

/-! ## Status JSON -/

def itemJson (entries : Array Entry) (env : Environment) (fn item : Name) : String × String :=
  let tried := entries.filterMap fun
    | .attempt f n ok r => if f == fn && n == item then some (ok, r) else none
    | _ => none
  if tried.any (·.1) then ("auto", "")
  else if env.contains item then ("manual", (tried.back?.map (·.2)).getD "")
  else ("open", (tried.back?.map (·.2)).getD "not attempted")

def theoremsJson (env : Environment) (reach : Option Name) (spec sail : Name)
    (compliance : Option Name) : Json × Json :=
  let has (n : Name) := Json.bool (env.contains n)
  let hasO (n : Option Name) := (n.map has).getD (Json.bool false)
  (Json.mkObj [("reach", hasO reach), ("spec", has spec), ("sail", has sail),
      ("compliance", hasO compliance)],
    Json.mkObj [("reach", toJson (reach.map (·.toString))), ("spec", toJson spec.toString),
      ("sail", toJson sail.toString), ("compliance", toJson (compliance.map (·.toString)))])

/-- `n` in the namespace of `fn` if it exists there, else in its parent. -/
def nearName (env : Environment) (fn : Name) (s : String) : Name :=
  let n := fn ++ Name.mkSimple s
  if env.contains n then n else fn.getPrefix ++ Name.mkSimple s

/-- The compliance theorem `s` of `fn = ZesuExec.Fn.X.X`: `nearName`, else
`ZesuExec.Compliance.X.s` (where the compliance modules put it). -/
def complianceName (env : Environment) (fn : Name) (s : String) : Name :=
  let n := nearName env fn s
  if env.contains n then n
  else `ZesuExec.Compliance ++ Name.mkSimple fn.getPrefix.getString! ++ Name.mkSimple s

/-- The end theorem of plan `fn` with entry `entry`: the legacy table's name for a converted spike
function, else `<fn lowercase>_spec` (`nearName`). -/
def planSpec (env : Environment) (fn : Name) (entry : Nat) : Name :=
  match legacyFns.find? (·.entry == entry) with
  | some l => l.spec
  | none => nearName env fn s!"{fn.getString!.toLower}_spec"

def planJson (entries : Array Entry) (env : Environment) (fn : Name) (cuts : Array CutInfo) :
    MetaM Json := do
  let entry := (cuts[0]?.map (·.pc)).getD 0
  let opens := (entries.filterMap fun
    | .assembled f _ os => if f == fn then some os else none
    | _ => none).back?.getD #[]
  let cutsJ ← cuts.toList.mapM fun c => do
    let cn := cutItem fn c.pc
    let (st, res) := itemJson entries env fn cn
    let leaves ← ((List.range c.leaves.size).zip c.leaves.toList).mapM fun (j, l) => do
      let ln := leafItem fn c.pc j
      let (ls, lr) := itemJson entries env fn ln
      return Json.mkObj [("i", toJson j), ("exit", toJson l.exit), ("target", toJson l.target),
        ("target_sym", toJson l.targetSym), ("steps", toJson l.steps), ("conds", toJson l.conds),
        ("obligs", toJson l.obligs), ("state", toJson ls), ("residual", toJson lr),
        ("thm", ← thmJson env false ls ln)]
    return Json.mkObj [("pc", toJson c.pc), ("cut_lemma", toJson st), ("residual", toJson res),
      ("thm", ← thmJson env true st cn), ("leaves", Json.arr leaves.toArray)]
  -- a spike function converted to a plan keeps the legacy table's theorem names
  let spec := planSpec env fn entry
  let (th, names) := match legacyFns.find? (·.entry == entry) with
    | some l => theoremsJson env (some (fn ++ `reach)) l.spec l.sail l.compliance
    | none =>
      let f := fn.getString!.toLower
      theoremsJson env (some (fn ++ `reach)) spec (nearName env fn s!"{f}_sail")
        (some (complianceName env fn s!"{f}_compliance"))
  return Json.mkObj ([("id", toJson s!"f_{hexNat entry}"), ("fn", toJson fn.toString),
    ("entry", toJson entry), ("legacy", toJson false),
    ("assembled", toJson (env.contains (fn ++ `reach_from))), ("cuts", Json.arr cutsJ.toArray),
    ("open", toJson (opens.map (·.toString))), ("theorems", th), ("names", names)] ++
    (← factsJson env spec (some fn)))

/-- The entries of the functions other than `own` whose end theorems (`ends`) the proof of
`spec` uses, through this package's constants; another function's end theorem is not entered. -/
def specCallees (env : Environment) (ends : Std.HashMap Name Nat) (spec : Name) (own : Nat) :
    Array Nat := Id.run do
  let mut stack : Array Name := #[spec]
  let mut seen : Std.HashSet Name := {}
  let mut out : Std.HashSet Nat := {}
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c || !userConst env c then continue
    seen := seen.insert c
    if c != spec then
      if let some e := ends[c]? then
        if e != own then out := out.insert e
        continue
    let some ci := env.find? c | continue
    for d in ci.type.getUsedConstants ++ ((ci.value?.map (·.getUsedConstants)).getD #[]) do
      unless seen.contains d do stack := stack.push d
  return out.toArray.qsort (· < ·)

def legacyJson (env : Environment) (ends : Std.HashMap Name Nat) (l : LegacyFn) : MetaM Json := do
  let (th, names) := theoremsJson env none l.spec l.sail l.compliance
  return Json.mkObj ([("id", toJson s!"f_{hexNat l.entry}"), ("fn", toJson l.fn),
    ("entry", toJson l.entry), ("legacy", toJson true), ("assembled", toJson false),
    ("cuts", Json.arr #[]), ("open", Json.arr #[]), ("theorems", th), ("names", names),
    ("spec_callees", toJson (specCallees env ends l.spec l.entry))] ++
    (← factsJson env l.spec none))

/-- Plan functions, then the legacy functions that have no plan. -/
def statusJson : MetaM Json := do
  let env ← getEnv
  let entries := zesuEntries env
  let plans := entries.filterMap fun
    | .plan fn cs => if (`ZesuExec.Test).isPrefixOf fn then none else some (fn, cs)
    | _ => none
  let planEntries := plans.map fun (_, cs) => (cs[0]?.map (·.pc)).getD 0
  let legacy := legacyFns.filter (!planEntries.contains ·.entry)
  -- every function's end theorems
  let ends : Std.HashMap Name Nat := legacyFns.foldl (fun m l => m.insert l.spec l.entry) <|
    (plans.zip planEntries).foldl (fun m ((fn, _), e) =>
      [fn ++ `reach, fn ++ `reach_from, planSpec env fn e].foldl (·.insert · e) m) {}
  let ps ← plans.mapM fun (fn, cs) => planJson entries env fn cs
  let ls ← legacy.mapM (legacyJson env ends)
  return Json.mkObj [("schema", toJson "zmap.status.v1"), ("functions", Json.arr (ps ++ ls.toArray))]

end ZesuExec.Vc

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `ZesuExec }] {} (trustLevel := 1024)
  let ctx : Lean.Core.Context :=
    { fileName := "zesu-status", fileMap := default, maxHeartbeats := 0 }
  let (j, _) ← (ZesuExec.Vc.statusJson.run' {} {}).toIO ctx { env := env }
  IO.println j.pretty
  return 0
