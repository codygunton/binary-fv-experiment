import BinaryFv.RiscV.Logic.BlockStep

/-!
# The shared `decode_run` tactic

`decode_run` discharges "this generated Sail decode step runs and retires" by unfolding `Runs`,
rewriting through the generated extension decoder, and reducing the `EStateM` plumbing.

It lives in its own module because sibling target modules otherwise duplicate the same macro and
Lean rejects duplicate declarations in one environment.
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
