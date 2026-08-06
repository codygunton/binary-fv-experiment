import BinaryFv.RiscV.Elfling.SequentialSplice

/-!
# Deciding pc ownership against the generated program tables

`owned_pc` and `ConfinedPrefix.ownStep'` live here rather than beside the rest of `ConfinedPrefix`
in `RiscV/Elfling/SequentialSplice.lean` for a layering reason that CI enforces: they decide their
side conditions by evaluating the *generated* program tables, and `nix/proof.nix` permits that
evaluation only outside `BinaryFv/RiscV/` and `BinaryFv/Binary/`.

    native_decide is not permitted in the generic RISC-V/Binary layers.

The gate greps for the string, so even a docstring mentioning it in those layers fails the build.
That is deliberate: the fixed-artifact exception covers closed facts about the pinned ELF, and such
facts are target facts by construction, so no generic module may state one.

Everything in `ConfinedPrefix` that is genuinely generic -- `reindex`, `trans'`, `consume`, and the
`confined_steps` fold -- stays in the RISC-V layer, where it belongs and where it costs nothing.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV

/--
Discharge one pc-literal side condition of a confined step against the generated program data.

Two goal shapes are handled, both decidable checks on the generated tables:

* `functionInstanceExecutionPcs program functionInstance pc` — the address is inside the function
  instance's execution ranges, decided through `functionInstanceExecutionPcs_iff_ranges` and
  `RegionPcs.iff_inRanges`;
* `¬ functionInstanceExitPred functionInstance pc` — the address is not one of the generated exit
  pcs, decided by unfolding `FunctionInstance.isExit` to array membership.

This is a decision procedure over the generated image, not a search: on an address outside the
region the `native_decide` evaluates to `false` and the tactic *fails*. It therefore cannot be used
to claim ownership of an address the generator did not attribute to the function instance.
-/
macro "owned_pc" : tactic =>
  `(tactic|
    first
    | (apply functionInstanceExecutionPcs_iff_ranges.mpr
       apply RegionPcs.iff_inRanges.mpr
       native_decide)
    | (simp only [functionInstanceExitPred, FunctionInstance.isExit] <;> native_decide)
    | fail "owned_pc: the goal is neither a provable `functionInstanceExecutionPcs …` membership \
            nor a provable `¬ functionInstanceExitPred …`; check the address against the \
            generated ranges and exit pcs")

namespace ConfinedPrefix

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}

/-- One retired owned instruction as a confined prefix, with the two pc-literal side conditions
discharged by `owned_pc` unless the caller supplies them. Same statement as `ownStep`, same
premises; only the two decidable checks move from the call site into the default. -/
theorem ownStep' {a : Nat} {s s' : State} {pc : BitVec 64}
    (atPc : s.regs.get? PC = some pc)
    (step : Runs (try_step a false) s s' false)
    (inRegion : own pc := by owned_pc)
    (notExit : ¬ exit pc := by owned_pc) :
    ConfinedPrefix own exit childSummary a 1 s s' :=
  ConfinedPrefix.ownStep atPc inRegion notExit step

end ConfinedPrefix

end BinaryFv.RiscV.Elfling
