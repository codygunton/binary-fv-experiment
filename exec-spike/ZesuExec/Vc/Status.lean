import ZesuExec.Vc.Assemble
import ZesuExec.Vc.Legacy

/-!
# `zesu-status` (programme plan S2 step 5)

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
-/

namespace ZesuExec.Vc
open Lean

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

def planJson (entries : Array Entry) (env : Environment) (fn : Name) (cuts : Array CutInfo) : Json :=
  let entry := (cuts[0]?.map (·.pc)).getD 0
  let opens := (entries.filterMap fun
    | .assembled f _ os => if f == fn then some os else none
    | _ => none).back?.getD #[]
  let cutsJ := cuts.toList.map fun c =>
    let (st, res) := itemJson entries env fn (cutItem fn c.pc)
    let leaves := (List.range c.leaves.size).zip c.leaves.toList |>.map fun (j, l) =>
      let (ls, lr) := itemJson entries env fn (leafItem fn c.pc j)
      Json.mkObj [("i", toJson j), ("exit", toJson l.exit), ("target", toJson l.target),
        ("target_sym", toJson l.targetSym), ("steps", toJson l.steps), ("conds", toJson l.conds),
        ("obligs", toJson l.obligs), ("state", toJson ls), ("residual", toJson lr)]
    Json.mkObj [("pc", toJson c.pc), ("cut_lemma", toJson st), ("residual", toJson res),
      ("leaves", Json.arr leaves.toArray)]
  -- a spike function converted to a plan keeps the legacy table's theorem names
  let (th, names) := match legacyFns.find? (·.entry == entry) with
    | some l => theoremsJson env (some (fn ++ `reach)) l.spec l.sail l.compliance
    | none =>
      let f := fn.getString!.toLower
      theoremsJson env (some (fn ++ `reach)) (nearName env fn s!"{f}_spec")
        (nearName env fn s!"{f}_sail") (some (complianceName env fn s!"{f}_compliance"))
  Json.mkObj [("id", toJson s!"f_{hexNat entry}"), ("fn", toJson fn.toString),
    ("entry", toJson entry), ("legacy", toJson false),
    ("assembled", toJson (env.contains (fn ++ `reach_from))), ("cuts", Json.arr cutsJ.toArray),
    ("open", toJson (opens.map (·.toString))), ("theorems", th), ("names", names)]

def legacyJson (env : Environment) (l : LegacyFn) : Json :=
  let (th, names) := theoremsJson env none l.spec l.sail l.compliance
  Json.mkObj [("id", toJson s!"f_{hexNat l.entry}"), ("fn", toJson l.fn), ("entry", toJson l.entry),
    ("legacy", toJson true), ("assembled", toJson false), ("cuts", Json.arr #[]),
    ("open", Json.arr #[]), ("theorems", th), ("names", names)]

/-- Plan functions, then the legacy functions that have no plan. -/
def statusJson (env : Environment) : Json :=
  let entries := zesuEntries env
  let plans := entries.filterMap fun
    | .plan fn cs => if (`ZesuExec.Test).isPrefixOf fn then none else some (fn, cs)
    | _ => none
  let planEntries := plans.map fun (_, cs) => (cs[0]?.map (·.pc)).getD 0
  let legacy := legacyFns.filter (!planEntries.contains ·.entry)
  Json.mkObj [("schema", toJson "zmap.status.v1"),
    ("functions", Json.arr (plans.map (fun (fn, cs) => planJson entries env fn cs) ++
      (legacy.map (legacyJson env)).toArray))]

end ZesuExec.Vc

def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `ZesuExec }] {} (trustLevel := 1024)
  IO.println (ZesuExec.Vc.statusJson env).pretty
  return 0
