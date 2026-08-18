import BinaryFv.Zesu.Root
import Lean.DeclarationRange
import Lean.Util.FoldConsts

/-! Emit the project-local declaration dependency graph below `root_compliance`. -/

open Lean

private def sourceDeclaration (env : Environment) (name : Name) : Bool :=
  let text := name.toString
  !text.contains "._native" && !text.contains "._proof" && !text.contains "._auto" &&
    (env.getModuleIdxFor? name |>.any fun index =>
      env.header.moduleNames[index]!.toString.startsWith "BinaryFv.")

private partial def visit (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (reported : NameSet := {})
    (edges : Array (Name × Name) := #[]) : NameSet × Array (Name × Name) :=
  match todo with
  | [] => (reported, edges)
  | name :: rest =>
      if seen.contains name then visit env rest seen reported edges
      else
        let seen := seen.insert name
        let dependencies :=
          match env.find? name with
          | some info => info.getUsedConstantsAsSet.toList.filter (sourceDeclaration env)
          | none => []
        let reported := dependencies.foldl (fun names dependency => names.insert dependency)
          (reported.insert name)
        let edges := dependencies.foldl (fun edges dependency => edges.push (name, dependency)) edges
        visit env (dependencies ++ rest) seen reported edges

private def emit : IO Unit := do
  let env ← importModules #[{ module := `BinaryFv.Zesu.Root }] {}
  let (declarations, edges) := visit env [`BinaryFv.Zesu.root_compliance]
  for name in declarations.toList.mergeSort Name.quickLt do
    let moduleName := env.getModuleIdxFor? name |>.map (env.header.moduleNames[·]!)
    let range := declRangeExt.find? (level := .exported) env name
    IO.println s!"declaration\t{name}\t{moduleName.getD `_unknown}\t{range.map (·.range.pos.line) |>.getD 0}\t{range.map (·.range.endPos.line) |>.getD 0}"
  for (parent, dependency) in edges.qsort (fun a b =>
      Name.quickLt a.1 b.1 || (a.1 == b.1 && Name.quickLt a.2 b.2)) do
    IO.println s!"edge\t{parent}\t{dependency}"

#eval emit
