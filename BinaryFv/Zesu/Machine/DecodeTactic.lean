import BinaryFv.RiscV.Logic.BlockStep

/-!
# The shared `decode_run` tactic

`decode_run` discharges "this generated Sail decode step runs and retires" by unfolding `Runs`,
rewriting through the generated extension decoder, and reducing the `EStateM` plumbing.

Ported unchanged from `d0f50581:BinaryFv/Zesu/MachineExecution/DecodeTactic.lean`. It kept its own
module then for a reason that still applies: sibling machine-execution modules each need it, and
Lean rejects two identical `macro` declarations of one name in a single environment, so duplicating
it makes any module importing both siblings fail to elaborate. Keeping it a leaf also lets Lake
compile those siblings concurrently.
-/

namespace BinaryFv.Zesu.Machine

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

end BinaryFv.Zesu.Machine
