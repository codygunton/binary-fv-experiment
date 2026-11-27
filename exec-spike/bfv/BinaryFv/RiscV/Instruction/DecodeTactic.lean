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
       PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map,
       EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
       EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
       EStateM.instMonadExceptOfOfBacktrackable, getThe,
       MonadState.get, MonadStateOf.get, *]
     rfl))

/-- Derive the configured post-increment reads and run one concrete decode. -/
macro "configured_decode " configured:term : tactic =>
  `(tactic|
    (obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        ($configured).decodeRunsContext
     decode_run))

/-- Derive the configured post-increment reads for a concrete store decode. -/
macro "configured_store_decode " configured:term : tactic =>
  `(tactic|
    (obtain ⟨seccfgBits, privilegeAfter, seccfgAfter⟩ :=
        ($configured).storeDecodeRunsContext
     decode_run))

end BinaryFv.RiscV
