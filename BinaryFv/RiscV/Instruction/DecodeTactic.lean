import BinaryFv.RiscV.Logic.BlockStep

/-!
# The shared `decode_run` tactic

`decode_run` discharges "this generated Sail decode step runs and retires" by unfolding `Runs`,
rewriting through the generated extension decoder, and reducing the `EStateM` plumbing.

It lives in its own module because sibling machine-execution modules each need it and Lean rejects
two identical `macro` declarations of the same name in one environment. Duplicating it made
`BinaryFv.Zesu` — which imports both siblings — fail to elaborate. Keeping it here also preserves the
rule that sibling function modules avoid umbrella imports, so Lake can still compile them
concurrently: they depend on this leaf, not on each other.
-/

namespace BinaryFv.RiscV

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

macro "decode_run" : tactic =>
  `(tactic|
    (unfold Runs
     rw [extDecode_eq]
     simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
       PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
       EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, getThe,
       MonadState.get, MonadStateOf.get, *]
     rfl))

end BinaryFv.RiscV
