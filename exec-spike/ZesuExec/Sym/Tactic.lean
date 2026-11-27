import Lean
import ZesuExec.Sym.Exec

/-!
# `sym_run`: evaluate `run` with compiled code, let the kernel re-check

`sym_run name := run img cuts fuel pc S` evaluates the term with the compiler (`evalExpr`),
quotes the value with `ToExpr`, adds `def name_leaves : List Leaf` holding it and
`theorem name : run img cuts fuel pc S = some name_leaves` proved by `Eq.refl`: the kernel
re-evaluates `run` to check it. It logs one line per leaf (index, exit, steps, conditions,
obligations). `unsafe` is confined to this
elaborator; nothing it computes is trusted.
-/

namespace ZesuExec.Sym
open Lean Elab Command Meta

syntax (name := symRunCmd) "sym_run " ident " := " term : command

@[command_elab symRunCmd]
unsafe def elabSymRun : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    let ty := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``Leaf))
    let t ← Term.elabTermEnsuringType stx[3] ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    if t.hasMVar then throwError "sym_run: term has metavariables"
    let v ← evalExpr (Option (List Leaf)) ty t
    let some ls := v | throwError "sym_run: run returned none"
    let lname := name.appendAfter "_leaves"
    let lty := mkApp (mkConst ``List [0]) (mkConst ``Leaf)
    let dv : DefinitionVal :=
      { name := lname, levelParams := [], type := lty, value := toExpr ls,
        hints := .regular 0, safety := .safe }
    addDecl (Declaration.defnDecl dv)
    let e := mkApp2 (mkConst ``Option.some [0]) lty (mkConst lname)
    let stmt ← mkEq t e
    let prf ← mkEqRefl e
    addDecl (Declaration.thmDecl { name, levelParams := [], type := stmt, value := prf })
    let mut i := 0
    let mut msg := s!"{name}: {ls.length} leaves"
    for l in ls do
      msg := msg ++ s!"\n  [{i}] {reprStr l.exit} steps {l.S.steps} conds {l.conds.length} obligs {l.obligs.length}"
      i := i + 1
    logInfo msg

end ZesuExec.Sym
