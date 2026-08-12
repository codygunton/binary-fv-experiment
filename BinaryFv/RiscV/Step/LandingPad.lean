import BinaryFv.RiscV.Step.Hart

/-!
# The `elp` register and the generated Zicfilp update

Two facts about the same register: that no landing pad is expected, and that the update a `jalr`
performs on it is a no-op. The second is a premise of every control-flow rule
(`Instruction/Execute/ControlFlow.lean`'s `helpElp`), and it is discharged here rather than assumed.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open extension

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
    Bind.bind, Pure.pure, Functor.map,
    EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
    instMonadStateOfMonadStateOf, MonadState.get, MonadStateOf.get,
    EStateM.instMonadExceptOfOfBacktrackable, getThe,
    notExpected]

/--
**The generated Zicfilp landing-pad update is a no-op, for every link register.**

`update_elp_state r` is `if (← currentlyEnabled Ext_Zicfilp) then writeReg elp … else pure ()`, and in
the generated model the gate is
`currentlyEnabled Ext_Zicsr && hartSupports Ext_Zicfilp && get_xLPE (← readReg cur_privilege)`.

The reason it is false here is **not** the `mseccfg` `MLPE` bit: `mseccfgBits` is universally
quantified below, so the value is irrelevant. It is that the generated `currentlyEnabled` match has
**no `Ext_Zicsr` arm at all** and falls through its `_ => pure false` default, which makes the
conjunction false at every state. `hartSupports Ext_Zicfilp` is `true` in this configuration, so
reading the gate off `hartSupports` alone would give the wrong answer.

The two register reads are still real: the gate reads `cur_privilege` and then, at Machine, `mseccfg`
through `get_xLPE`, and an absent register makes the generated read throw rather than return. So the
hypotheses are exactly the two reads that must succeed — no more, and no fact about their values
beyond the privilege level that selects the `mseccfg` branch.

This is the `helpElp` premise of `tryStepRetRetires`, and `r` is left free rather than fixed to `x1`
so that a caller returning through any link register uses the same lemma.
-/
theorem updateElpState_run (state : State) (r : regidx) (mseccfgBits : BitVec 64)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (seccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (update_elp_state r) state state () := by
  have gate : Runs (currentlyEnabled Ext_Zicfilp) state state false := by
    unfold Runs
    simp [currentlyEnabled, hartSupports, get_xLPE, PreSail.readReg, EStateM.run,
      Bind.bind, Pure.pure, Functor.map, EStateM.bind,
      EStateM.get, EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf,
      instMonadStateOfMonadStateOf, MonadState.get, MonadStateOf.get,
      EStateM.instMonadExceptOfOfBacktrackable, getThe,
      privilegeRead, seccfgRead]
  unfold update_elp_state
  exact Runs.bind gate rfl

/-- **The reads above are load-bearing, not defensive.** Drop `cur_privilege` and the conclusion is
not merely unprovable — it is false, because the generated read throws. A "no-op" premise that held
at every state whatsoever would be a sign the statement had lost contact with the model. -/
theorem not_updateElpState_run_of_privilege_absent (state : State) (r : regidx)
    (absent : state.regs.get? cur_privilege = none) :
    ¬ Runs (update_elp_state r) state state () := by
  intro run
  unfold Runs update_elp_state at run
  simp [currentlyEnabled, PreSail.readReg, EStateM.run, Bind.bind, Pure.pure, Functor.map,
    EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
    MonadState.get, MonadStateOf.get, getThe, absent, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw] at run

end BinaryFv.RiscV
