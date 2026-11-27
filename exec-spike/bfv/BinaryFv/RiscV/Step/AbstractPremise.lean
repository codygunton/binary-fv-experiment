import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Platform.FetchMmio
import BinaryFv.RiscV.Step.Context

/-!
# Abstract step premises, and what discharges them

exec-spike repair: the specialised model has no MMIO, interrupt dispatch or landing-pad checks, so
`AbstractPlatform` now carries only the base-fetch platform, and the Zicfilp abstraction
`AbstractElp` (with `AbstractElp.mono`, `abstractElp_of_base`, `witnessState_abstractElp`) was
deleted: the specialised `execute_JALR` performs no `update_elp_state`, so nothing consumes it.

The premise a machine-loop contract carries rather than re-establishes at every step: that the
configured machine's fetch path is enabled at every body pc. It is stated over all states agreeing
with a base state off the loop's write set, so that it survives each step.

It is parameterized by the register set `P` the loop preserves and by the address set `Pcs` of the
function's fetch addresses. Which registers and which addresses those are is a target fact.

**It is an assumption of the loop, not of the layer.** `abstractPlatform_of_base` builds it from
register-level facts about the base state alone, so a contract holding those facts owes nothing
further. `witnessState` below is a concrete state satisfying it, so "the contract may assume this"
is not standing in for "no state satisfies this".

The `Ext_Zca` premise of the same rules deliberately gets **no** abstraction of its own:
`Platform/Fetch.lean`'s `currentlyEnabledZca_run` turns a single `misa` read into the run, `misa` is
in `platformPreserved`, and so `currentlyEnabledZca_run_of_agree` covers every state the loop
reaches. A second `Abstract…` wrapper would carry no information the `misa` clause does not.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open extension

/-- exec-spike repair: the `FetchMemoryNoMMIO`, `InterruptDisabled` and `LandingPadNotExpected`
conjuncts were removed.
For any state agreeing with `base` off the write set and positioned at one of the function's
fetch addresses, the generated base-fetch path is enabled. -/
def AbstractPlatform (P : Register → Prop) (Pcs : BitVec 64 → Prop) (base : State) : Prop :=
  ∀ (t : State) (pc : BitVec 64), Agree P base t → t.regs.get? PC = some pc → Pcs pc →
    FetchBasePlatform t pc

/-- The abstract platform survives to an `Agree`-equal state. -/
theorem AbstractPlatform.mono {P : Register → Prop} {Pcs : BitVec 64 → Prop} {s s' : State}
    (h : Agree P s s') (hp : AbstractPlatform P Pcs s) : AbstractPlatform P Pcs s' :=
  fun t pc hst hPC hbody => hp t pc (Agree.trans h hst) hPC hbody

/-! ## The two transports `Platform/Fetch.lean` cannot state

`LandingPadNotExpected` and the `Ext_Zca` run live above `Platform/Fetch.lean` in the import graph,
so their `Agree` transports are here rather than beside the other four. -/

/-- `LandingPadNotExpected` is the eleventh of `NormalExecutionState`'s twelve pins. -/
theorem landingPadNotExpected_of_normal {state : State} (normal : NormalExecutionState state) :
    LandingPadNotExpected state :=
  normal.2.2.2.2.2.2.2.2.2.2.1

/-- `LandingPadNotExpected` is one register read, and `elp` is preserved. -/
theorem landingPadNotExpected_of_agree {before after : State}
    (agree : Agree platformPreserved before after) (h : LandingPadNotExpected before) :
    LandingPadNotExpected after :=
  (agree elp (by simp [platformPreserved])).trans h

/-- The `Ext_Zca` gate at any state agreeing with one where `misa` is known. -/
theorem currentlyEnabledZca_run_of_agree {before after : State} {misaBits : BitVec 64}
    (agree : Agree platformPreserved before after)
    (misaRead : before.regs.get? misa = some misaBits) :
    Runs (currentlyEnabled Ext_Zca) after after (_get_Misa_C misaBits == 1#1) :=
  currentlyEnabledZca_run after misaBits ((agree misa (by simp [platformPreserved])).trans misaRead)

/-! ## Constructors

exec-spike repair: only `AbstractPlatform` remains. It is built from facts about the base state
alone. The quantified `t` is handled by `fetchBasePlatform_of_agree` in `Platform/Fetch.lean`, and
the `PC` read `t` is required to satisfy is supplied by `AbstractPlatform`'s own hypothesis — which
is exactly the split `fetchBasePlatform_of_agree` was narrowed to express. -/

/--
**The abstract platform, from the base state's configuration.**

exec-spike repair: the `noMMIO`, `interrupts` and `notExpected` premises were removed.

`platform` is per-address because one of the eight off-`PC` conjuncts (the PMA lookup) depends on
the address; everything else is a register fact holding once.

Note what is *not* a hypothesis: nothing says the base state is at any of the `Pcs`. It cannot,
because the loop's states are at different pcs, and it need not, because `fetchBasePlatform_of_agree`
takes the landing pc from `t`.
-/
theorem abstractPlatform_of_base {Pcs : BitVec 64 → Prop} {base : State}
    (platform : ∀ pc, Pcs pc → FetchBasePlatformOffPC base pc) :
    AbstractPlatform platformPreserved Pcs base := by
  intro t pc agree landed hpc
  exact fetchBasePlatform_of_agree agree landed (platform pc hpc)

/-! ## The two premises at the state `tryStepRetRetires` actually asks about

`helpElp` and `hzca` are stated at `coreControlFlowNextState (tryStepControlFlowAfterIncrement
state) pc` — the pre-step state after the generated counter-increment and `nextPC := pc+4` writes.
Neither written register is in `platformPreserved`, so the reads a caller has at the *pre-step* state
are the reads those premises need. -/

/-- The state the execute stage runs in agrees with the pre-step state on every preserved register.
`minstret_increment` and `nextPC` are the only registers written, and neither is preserved. -/
theorem agree_stepPremiseState (state : State) (pc : BitVec 64) :
    Agree platformPreserved state
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl) <;>
    simp [coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert]

/-- `tryStepRetRetires`' `helpElp` premise, from the pre-step `cur_privilege` and `mseccfg` reads. -/
theorem updateElpState_run_atStepPremise (state : State) (pc : BitVec 64) (r : regidx)
    (mseccfgBits : BitVec 64)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (seccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (update_elp_state r)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) () :=
  updateElpState_run _ r mseccfgBits
    ((agree_stepPremiseState state pc cur_privilege (by simp [platformPreserved])).trans
      privilegeRead)
    ((platformPreserved_mseccfg (agree_stepPremiseState state pc)).trans seccfgRead)

/-- `tryStepRetRetires`' `hzca` premise, from the pre-step `misa` read. -/
theorem currentlyEnabledZca_run_atStepPremise (state : State) (pc : BitVec 64)
    (misaBits : BitVec 64) (misaRead : state.regs.get? misa = some misaBits) :
    Runs (currentlyEnabled Ext_Zca)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      (_get_Misa_C misaBits == 1#1) :=
  currentlyEnabledZca_run_of_agree (agree_stepPremiseState state pc) misaRead

/-! ## The transport is applied where the entry state is *not* at the exit pc

`fetchBasePlatform_of_agree` used to take the whole `FetchBasePlatform before pc` bundle, whose `PC`
read pins `before` to `pc`. It was therefore inapplicable at the one site it was written for, and
nothing in the build noticed, because a lemma is not obliged to be usable.

The two theorems below make that obligation mechanical. `fetchBasePlatform_of_agree_at_moved_pc`
applies the transport at a `before` whose `PC` is *provably* not the target — a statement the old
hypothesis could not even be given — and `witnessState_movedPc` instantiates it at a concrete state,
so the arrangement cannot be satisfied by contradictory hypotheses either. Widening the transport
back breaks the first; making the platform bundle unsatisfiable breaks the second. -/

theorem platformPreserved_ne_PC {r : Register} (h : platformPreserved r) : r ≠ PC := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> simp

/-- Moving `PC` alone disturbs no preserved register: `PC` is deliberately absent from
`platformPreserved`, and this is where that absence is used rather than described. -/
theorem agree_insert_PC (state : State) (pc : BitVec 64) :
    Agree platformPreserved state { state with regs := state.regs.insert PC pc } := by
  intro r hr
  change (state.regs.insert PC pc).get? r = state.regs.get? r
  rw [Std.ExtDHashMap.get?_insert]
  simp [Ne.symm (platformPreserved_ne_PC hr)]

/-- **The transport, applied across a genuine change of pc.** The first conjunct is the whole point:
the entry state does not satisfy `FetchBasePlatform before exitPc`, so the pre-narrowing form of
`fetchBasePlatform_of_agree` could not have been used here at all. -/
theorem fetchBasePlatform_of_agree_at_moved_pc {before : State} {entryPc exitPc : BitVec 64}
    (distinct : entryPc ≠ exitPc) (atEntry : before.regs.get? PC = some entryPc)
    (h : FetchBasePlatformOffPC before exitPc) :
    before.regs.get? PC ≠ some exitPc ∧
      FetchBasePlatform { before with regs := before.regs.insert PC exitPc } exitPc := by
  refine ⟨?_, fetchBasePlatform_of_agree (agree_insert_PC before exitPc) ?_ h⟩
  · rw [atEntry]
    simpa using distinct
  · change (before.regs.insert PC exitPc).get? PC = some exitPc
    rw [Std.ExtDHashMap.get?_insert]
    simp

/-! ## Nothing above is vacuous

Every predicate in this module and in `Platform/Fetch.lean` is an existential over register contents,
and an existential whose registers are mutually unsatisfiable proves everything. One concrete state
settles it: `witnessState` is `initialState` with nineteen registers set, and the theorems below
exhibit it satisfying `NormalExecutionState`, the whole off-`PC` fetch platform, the interrupt
exclusion, and the abstraction at once. (exec-spike repair: `witnessState_noMMIO` was deleted with
`FetchMemoryNoMMIO`, and `witnessState_abstractElp` with `AbstractElp`.)

It is a generic state, not the SSZ target's: the region table and the fetch address are chosen here.
That is deliberate — a satisfiability witness borrowed from the target would prove the target's
premises consistent, not this layer's. -/

/-- One executable region covering `[0, 0x2000)`, which is where `witnessPc` sits. -/
def witnessPmaRegion : PMA_Region :=
  { base := 0#64, size := 0x2000#64,
    attributes := { (default : PMA) with executable := true },
    include_in_device_tree := false }

/-- The fetch address the witness is exercised at: four-byte aligned, inside `witnessPmaRegion`, and
far below both `plat_clint_base` and `plat_sig_base`. -/
def witnessPc : BitVec 64 := 0x1000#64

/-- A concrete machine state carrying every register the retirement's premises read. `pc` is the
address it currently sits at, which the theorems below vary independently of `witnessPc`. -/
def witnessState (pc : BitVec 64) : State :=
  { initialState with
      regs :=
        ((((((((((((((((((initialState.regs.insert hart_state (HartState.HART_ACTIVE ())).insert
          cur_privilege Privilege.Machine).insert
          satp (0 : BitVec 64)).insert
          mideleg (0 : BitVec 64)).insert
          mie (0 : BitVec 64)).insert
          mip (0 : BitVec 64)).insert
          pmpcfg_n (default : Vector (BitVec 8) 64)).insert
          pmpaddr_n (default : Vector (BitVec 64) 64)).insert
          mcountinhibit (0 : BitVec 32)).insert
          minstretcfg (0 : BitVec 64)).insert
          elp (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED)).insert
          misa (0x1000 : BitVec 64)).insert
          mstatus (0 : BitVec 64)).insert
          sig_meip (0 : BitVec 1)).insert
          pma_regions [witnessPmaRegion]).insert
          mseccfg (0 : BitVec 64)).insert
          htif_tohost_base none).insert
          minstret (0 : BitVec 64)).insert
          PC pc }

theorem witnessState_normal (pc : BitVec 64) : NormalExecutionState (witnessState pc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [witnessState, Std.ExtDHashMap.get?_insert, Sail.BitVec.access]

theorem witnessState_retiredCounter (pc : BitVec 64) :
    RetiredCounterPresent (witnessState pc) :=
  ⟨0, by simp [witnessState, Std.ExtDHashMap.get?_insert]⟩

theorem witnessState_pma (pc : BitVec 64) : FetchPmaAllows (witnessState pc) witnessPc := by
  refine fetchPmaAllows_of_region (regions := [witnessPmaRegion]) (region := witnessPmaRegion)
    ?_ ?_ rfl
  · simp [witnessState, Std.ExtDHashMap.get?_insert]
  · rfl

theorem witnessState_offPC (pc : BitVec 64) :
    FetchBasePlatformOffPC (witnessState pc) witnessPc := by
  refine fetchBasePlatformOffPC_of_normal (mstatusBits := 0) (witnessState_normal pc) ?_ ?_
    (witnessState_pma pc)
  · simp [witnessState, Std.ExtDHashMap.get?_insert]
  · decide

theorem witnessState_interrupts (pc : BitVec 64) : InterruptDisabled (witnessState pc) := by
  refine interruptDisabled_of_normal (mstatusBits := 0) (witnessState_normal pc) ?_ ⟨0, ?_⟩ <;>
    simp [witnessState, Std.ExtDHashMap.get?_insert]

/-- **`AbstractPlatform` is inhabited**, at the single-address set `{witnessPc}`.
(exec-spike repair: the `noMMIO`, `interrupts` and `notExpected` arguments are gone.) -/
theorem witnessState_abstractPlatform (pc : BitVec 64) :
    AbstractPlatform platformPreserved (fun q => q = witnessPc) (witnessState pc) := by
  refine abstractPlatform_of_base ?_
  rintro q rfl
  exact witnessState_offPC pc

/-- **The transport, at a concrete entry state sitting at `0x2000` and a target of `0x1000`.**

This is the regression test the narrowing exists for. The first conjunct is checked, not asserted:
the entry state's `PC` really is not the exit, so the hypothesis
`FetchBasePlatform (witnessState 0x2000) 0x1000` is *false*, and a transport demanding it could not
be applied here. -/
theorem witnessState_movedPc :
    (witnessState 0x2000#64).regs.get? PC ≠ some witnessPc ∧
      FetchBasePlatform
        { witnessState 0x2000#64 with
            regs := (witnessState 0x2000#64).regs.insert PC witnessPc } witnessPc := by
  refine fetchBasePlatform_of_agree_at_moved_pc (entryPc := 0x2000#64) (by decide) ?_
    (witnessState_offPC _)
  simp [witnessState]

/-- **The pre-narrowing hypothesis is not merely unavailable at that instantiation — it is false.**

This is what makes the guard above a test rather than a preference. Restoring
`FetchBasePlatform before pc` as the transport's hypothesis does not just make
`witnessState_movedPc` awkward to prove; it makes it unprovable, because the premise it would then
need is refuted here. -/
theorem not_fetchBasePlatform_witnessState_movedPc :
    ¬ FetchBasePlatform (witnessState 0x2000#64) witnessPc := fun h =>
  witnessState_movedPc.1 (fetchBasePlatform_iff.mp h).1

end BinaryFv.RiscV
