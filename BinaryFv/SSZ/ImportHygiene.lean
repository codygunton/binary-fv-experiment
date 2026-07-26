import Lean
import BinaryFv.SSZ.Root

/-!
# Import hygiene, mechanically enforced

The `Validation/` modules are **falsification evidence, never proof premises**. They run
`native_decide` agreement checks of the handwritten meanings against the pinned oracle and against a
corpus; a root theorem that transitively imported one would be quoting its own probe as a hypothesis.
This module makes that impossible to do accidentally: the check runs at build time, from
`BinaryFv.lean`, so a leak fails `lake build BinaryFv` rather than waiting for review.

## Why this is not a duplicate of the `nix/proof.nix` grep

`nix/proof.nix` already greps for `^import BinaryFv\..*\.Validation\.` in any file outside
`Validation/`. That check is real and it fires — verified by injecting a leak into `Root.lean` and
watching it trip. It is kept. But it and this one pin **different things**, in the same way the
textual `sorry` grep and `AxiomHygiene`'s sorry-site scan pin different things:

* the grep pins **where an import is written** — every edge in the source, whether or not that file is
  reachable from any theorem. It is broader than the root and catches a leak in a module nothing
  imports yet.
* this pins **what the root actually depends on** — the module set Lean itself resolved for
  `BinaryFv.SSZ.Root`. It is narrower in scope and stronger in kind: it cannot be fooled by an import
  the grep's pattern does not happen to match, because it does not read source text at all.

Neither subsumes the other, and the cheap one is not the one that would survive a refactor of how
imports are spelled.

## Anti-vacuity

A guard whose scan set is empty passes forever, so the check **also fails when it is looking at the
wrong thing**. The exact condition is that `BinaryFv.SSZ.Root` is itself in the scanned closure: if
this module ever stops importing the root, the leak scan becomes vacuous and the guard says so
instead of passing. That is a direct test of the premise rather than a threshold, so it cannot drift
as the module count changes — an earlier version used a count floor, which sat 9 modules above the
true count of 59 and would have started false-alarming on any real pruning.

The count is still printed on success, for the reason a bare `0` is never evidence: "0 leaks out of
59 modules" can be checked by a reader, "0 leaks" cannot.

This matters more here than almost anywhere else in the project: the whole point of the guard is to
stop validation evidence entering the proof, so a version of it that could not fail would be the most
damaging possible instance of the defect this row keeps finding.
-/

open Lean

namespace BinaryFv.SSZ.ImportHygiene

/-- The module-name components, as strings. -/
private def parts (n : Name) : List String := n.toString.splitOn "."

/-- A module of *this project* living under a `Validation` namespace. Restricted to `BinaryFv` so an
unrelated upstream module that happens to contain the component is not reported. -/
def isProjectValidationModule (n : Name) : Bool :=
  let ps := parts n
  ps.head? == some "BinaryFv" && ps.contains "Validation"

/-- The module whose import closure this guard is *about*. Checked to be present, so the scan cannot
silently become vacuous. -/
def anchorModule : Name := `BinaryFv.SSZ.Root

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let project := modules.filter fun n => (parts n).head? == some "BinaryFv"
  let leaks := modules.filter isProjectValidationModule
  if !leaks.isEmpty then
    throwError "import hygiene: `BinaryFv.SSZ.Root`'s import closure contains Validation \
      modules, which are falsification evidence and must never be proof premises: {leaks.toList}"
  else if !modules.contains anchorModule then
    throwError "import hygiene: {anchorModule} is not in the scanned closure, so the leak scan is \
      vacuous — it is reported as a failure rather than a pass. Most likely this module stopped \
      importing the root."
  else
    logInfo m!"import hygiene OK: {anchorModule} present, {project.size} project modules in its \
      closure, 0 under Validation"

end BinaryFv.SSZ.ImportHygiene
