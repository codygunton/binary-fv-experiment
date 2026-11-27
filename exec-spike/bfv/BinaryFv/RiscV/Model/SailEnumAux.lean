import LeanRV64DExecutable.Defs
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Enums

/-!
# Shared realization of the Sail enum auxiliaries used by `bv_decide`

Whenever `bv_decide` meets a goal mentioning an enum inductive, its enum preprocessing pass
(`Lean.Elab.Tactic.BVDecide.Frontend.Normalize`) *lazily realizes* two reserved auxiliary constants
for that enum -- for example, for `Register` (a 176-constructor enum from the Sail-generated
`LeanRV64DExecutable.Defs`):

* `Register.enumToBitVec : Register → BitVec 8` — the constructor-index mapping, built as a
  `Register.recOn` chain `fun x => Register.recOn x 0#8 1#8 … 175#8`;
* `Register.eq_iff_enumToBitVec_eq : ∀ x y : Register, x = y ↔ x.enumToBitVec = y.enumToBitVec` —
  proved from an explicit inverse via `BitVec.eq_iff_eq_of_inv`.

Realization is *per-module*: the constants are recorded in the `.olean` of whichever module first
triggered the pass.  Two sibling modules that each run `bv_decide` on a goal mentioning the same
enum therefore each realize their own copy, and importing both into one environment fails with

```
environment already contains 'Register.enumToBitVec' from SomeModule
```

which is exactly what blocks two such sibling contract modules from co-elaborating.  The
tree-wide cumulative import test is what detects this class of failure; per-module builds cannot.

This module fixes that by realizing the auxiliaries *once*, deliberately, in a single common
ancestor of every `bv_decide`-using module that mentions these enums.  Downstream modules then find
them already present in the environment, so `realizeConst` reuses the imported declarations instead
of building fresh, colliding ones, and any set of those modules can be imported side by side.

`enums` below lists every Sail enum this stack's `bv_decide` goals currently mention.  `Register`
and `Privilege` were each realized independently by both `MemcpyContract` and `CallStepContract` --
a live collision.  `mem_payload` is realized today only by `MemcpyContract`, and is included so that
a second `bv_decide` site mentioning it cannot reintroduce the same failure.

This is a build-hygiene shim only.  It invokes the very same toolchain API that `bv_decide` would
have invoked anyway (`getEqIffEnumToBitVecEqFor`, which realizes `getEnumToBitVecFor` in passing),
so the resulting declarations are exactly the ones the tactic built before; both are ordinary
kernel-checked declarations and neither adds an axiom.  Nothing here is a proof step or a semantic
assumption: no theorem statement depends on this module, only the ability to import its dependents
side by side.
-/

namespace BinaryFv.RiscV.Model.SailEnumAux

/-- The Sail enums appearing in this stack's `bv_decide` goals, whose `bv_decide` auxiliaries must
be realized once in this shared ancestor rather than per-module. -/
def enums : List Lean.Name := [``Register, ``Privilege, ``mem_payload]

end BinaryFv.RiscV.Model.SailEnumAux

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for e in BinaryFv.RiscV.Model.SailEnumAux.enums do
    discard <| Lean.Elab.Tactic.BVDecide.Frontend.Normalize.getEqIffEnumToBitVecEqFor e

/-- Confirms the shared realizations landed in *this* module, so that every downstream `bv_decide`
on a goal mentioning these enums reuses them rather than realizing colliding copies. -/
example : (∀ x y : Register, x = y ↔ x.enumToBitVec = y.enumToBitVec)
    ∧ (∀ x y : Privilege, x = y ↔ x.enumToBitVec = y.enumToBitVec)
    ∧ (∀ x y : mem_payload, x = y ↔ x.enumToBitVec = y.enumToBitVec) :=
  ⟨Register.eq_iff_enumToBitVec_eq, Privilege.eq_iff_enumToBitVec_eq,
    mem_payload.eq_iff_enumToBitVec_eq⟩
