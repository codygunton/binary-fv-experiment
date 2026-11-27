import Lean
import ZesuExec.Sym.Exec

/-!
# `sym_run`: evaluate `run` with compiled code, let the kernel re-check

`sym_run name := run img cuts fuel pc S` evaluates the term with the compiler (`evalExpr`),
quotes the value with `ToExpr`, and adds `theorem name : run img cuts fuel pc S = some …`
proved by `Eq.refl`: the kernel re-evaluates `run` to check it. `unsafe` is confined to this
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
    if v.isNone then throwError "sym_run: run returned none"
    let e := toExpr v
    let stmt ← mkEq t e
    let prf ← mkEqRefl e
    addDecl (Declaration.thmDecl { name, levelParams := [], type := stmt, value := prf })

end ZesuExec.Sym
