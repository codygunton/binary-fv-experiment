import BinaryFv.RiscV.HartContract

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- The generated external decoder is definitionally the generated instruction decoder. -/
theorem extDecode_eq (word : BitVec 32) :
    ext_decode word = encdec_backwards word := by
  rfl

/-- An `elp` register configured with no landing-pad expectation. -/
def LandingPadNotExpected (state : State) : Prop :=
  state.regs.get? elp =
    some (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED)

/-- The generated landing-pad check is false when `elp` carries no expectation. -/
theorem landingPad_notExpected (state : State) (notExpected : LandingPadNotExpected state) :
    Runs (is_landing_pad_expected ()) state state false := by
  unfold LandingPadNotExpected at notExpected
  unfold Runs
  simp [is_landing_pad_expected, landing_pad_bits_backwards, PreSail.readReg, EStateM.run,
    EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    notExpected]

/-- The generated `nextPC` write has the standard register-update contract. -/
theorem writeNextPc_run (state : State) (pc : BitVec 64) :
    Runs (Sail.writeReg nextPC (Sail.BitVec.addInt pc 4)) state
      { state with regs := state.regs.insert nextPC (Sail.BitVec.addInt pc 4) } PUnit.unit := by
  exact writeReg_run state nextPC (Sail.BitVec.addInt pc 4)

end BinaryFv.RiscV
