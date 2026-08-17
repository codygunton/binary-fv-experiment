import BinaryFv.Zesu.Root
import Lean.Util.FoldConsts

/-! Emit the project-local declaration dependency graph below `root_compliance`. -/

open Lean

private def projectDeclaration (name : Name) : Bool :=
  name.toString.startsWith "BinaryFv."

private partial def visit (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (edges : NameSet := {}) : NameSet × NameSet :=
  match todo with
  | [] => (seen, edges)
  | name :: rest =>
      if seen.contains name then visit env rest seen edges
      else
        let seen := seen.insert name
        let dependencies :=
          match env.find? name with
          | some info => info.getUsedConstantsAsSet.toList.filter projectDeclaration
          | none => []
        let edges := dependencies.foldl (fun edges dependency =>
          edges.insert (Name.str (Name.str .anonymous name.toString) dependency.toString)) edges
        visit env (dependencies ++ rest) seen edges

private def emit : IO Unit := do
  let env ← importModules #[{ module := `BinaryFv.Zesu.Root }] {}
  let (declarations, edges) := visit env [`BinaryFv.Zesu.root_compliance]
  for name in declarations.toList.mergeSort Name.quickLt do
    let moduleName := env.getModuleIdxFor? name |>.map (env.header.moduleNames[·]!)
    IO.println s!"declaration\t{name}\t{moduleName.getD `_unknown}"
  for edge in edges.toList.mergeSort Name.quickLt do
    let parent := edge.getPrefix.getString!
    let dependency := edge.getString!
    IO.println s!"edge\t{parent}\t{dependency}"

#eval emit
