import BinaryFv.RiscV.Step.Hart

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

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

end BinaryFv.RiscV
