import Lean
import ZesuExec.Sym.Summary
import ZesuExec.Sym.Pretty

/-!
# `sym_runw`: `sym_run` for `runWith`

`sym_runw name := runWith img sums cuts F0 fuel pc S` evaluates the term with the compiler, adds
`def name_leaves : List LeafW` holding the value and `theorem name : … = some name_leaves` by
`Eq.refl` (the kernel re-evaluates `runWith`), and logs one line per leaf with its summarised
calls (callee entry, return address). As for `sym_run`, nothing the compiler computes is
trusted; `unsafe` is confined to this elaborator.
-/

namespace ZesuExec.Sym
open Lean Elab Command Meta

syntax (name := symRunWCmd) "sym_runw " ident " := " term : command

@[command_elab symRunWCmd]
unsafe def elabSymRunW : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    let lty := mkApp (mkConst ``List [0]) (mkConst ``LeafW)
    let ty := mkApp (mkConst ``Option [0]) lty
    let t ← Term.elabTermEnsuringType stx[3] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    if t.hasMVar then throwError "sym_runw: term has metavariables"
    let v ← evalExpr (Option (List LeafW)) ty t
    let some ls := v | throwError "sym_runw: runWith returned none"
    let lname := name.appendAfter "_leaves"
    let dv : DefinitionVal :=
      { name := lname, levelParams := [], type := lty, value := toExpr ls,
        hints := .regular 0, safety := .safe }
    addAndCompile (Declaration.defnDecl dv)
    enableRealizationsForConst lname
    let e := mkApp2 (mkConst ``Option.some [0]) lty (mkConst lname)
    let stmt ← mkEq t e
    let prf ← mkEqRefl e
    addDecl (Declaration.thmDecl { name, levelParams := [], type := stmt, value := prf })
    enableRealizationsForConst name
    let mut i := 0
    let mut msg := s!"{name}: {ls.length} leaves"
    for lw in ls do
      let l := lw.leaf
      let first := match l.conds with | c :: _ => s!" (first: {c.pp})" | [] => ""
      let hex (n : Nat) := String.ofList (Nat.toDigits 16 n)
      let calls := lw.calls.map fun c => s!"{hex c.target}→{hex c.ret}"
      msg := msg ++ s!"\n  [{i}] {l.exit.pp} steps {l.S.steps} conds {l.conds.length}{first} obligs {l.obligs.length} calls {calls}"
      i := i + 1
    logInfo msg

end ZesuExec.Sym
