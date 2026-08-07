import BinaryFv.RiscV.Elfling.SentinelBridge
import BinaryFv.RiscV.Step.Postlude
import BinaryFv.RiscV.Step.TryStep

/-!
# The bridge's hypotheses are satisfiable — a closed witness

`SentinelBridge` is a conditional theorem, and a conditional theorem whose hypotheses cannot all
hold at once proves nothing. This module discharges that worry the only way it can be discharged:
by **building** an instance. Everything below is closed — no free state, no admitted machine fact,
no `sorry` — so the objects it produces are inhabitants, not promises.

## What makes a closed machine step possible at all

Every `try_step` contract elsewhere in this layer is conditional on a program image: the active-hart
path fetches, which drags in translation, PMP, PMA and four bytes of memory. None of that can be
exhibited without a binary, which is exactly what a generic layer does not have.

The wait-wakeup path needs none of it. A hart parked in `HART_WAITING (WAIT_WRS_STO, _)` with no
pending-and-enabled interrupt takes the *invalid reservation* exit: `run_hart_waiting` returns the
hart to `HART_ACTIVE` and reports `Retire_Success` **without a fetch**, and the ordinary `try_step`
postlude then ticks `PC := nextPC` and retires. So it is a genuine, authoritative
`Runs (try_step k false) s s' false` over a state that mentions nine registers and no memory at all,
and its post-`PC` is whatever `nextPC` was — which is what lets the witness put the sentinel there.

## What this witness does and does not reach

It reaches, closed:

* `waitWakeRetires` — one real retirement of the generated `try_step`;
* `witnessEnteredRun` — an `EnteredFunctionTrace` of count **1**, so `FunctionTrace.step` and the
  entry conditions are satisfiable together with a real machine step;
* `witnessTraceToSentinel` — a `TraceToSentinel` of length **1** produced *by the bridge*, whose
  single step is that real retirement. It is a `TraceToSentinel.step`, not a `.done`: the trace type
  is inhabited non-degenerately, and every hypothesis of `traceToSentinel_of_functionTrace` holds
  simultaneously at a concrete, inhabited region and exit set with a sentinel outside both.

It does **not** reach a closed bridged trace of length ≥ 2, and the reason is structural rather than
a gap in effort. Every `try_step` that returns `false` ends with `hart_state = HART_ACTIVE` — the
postlude returns `true` on any state that is still waiting — so the wakeup path can only ever be the
**first** step of a chain. A bridged trace of length 2 therefore needs one retirement from an active
hart, which needs a fetch, which needs a program image. `witnessBridgeAtCountOne` states exactly
that residue: the count-1 instance of the bridge, closed except for one further
`Runs (try_step 1 false) … false`. Nothing else is missing.
-/

namespace BinaryFv.RiscV.Elfling

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/-! ## The wakeup retirement -/

/-- With no interrupt both pending and enabled, the waiting hart is not woken by one. -/
theorem shouldWakeForInterrupt_quiet (state : State)
    (pending : state.regs.get? mip = some (0 : BitVec 64))
    (enabled : state.regs.get? mie = some (0 : BitVec 64)) :
    Runs (shouldWakeForInterrupt ()) state state false := by
  unfold shouldWakeForInterrupt
  refine Runs.bind (readReg_run state mip 0 pending) ?_
  refine Runs.bind (readReg_run state mie 0 enabled) ?_
  unfold Runs
  simp [EStateM.run, EStateM.instMonad, EStateM.pure, zeros]

/-- Lift a generated waiting-hart step through the selector `try_step` uses. The mirror of
`activeHartStep_active`. -/
theorem activeHartStep_waiting (stepNo : Nat) (exitWait : Bool) (before after : State)
    (result : Step) (reason : WaitReason) (instbits : BitVec 32)
    (hHart : before.regs.get? hart_state = some (.HART_WAITING (reason, instbits)))
    (hWaiting : Runs (run_hart_waiting stepNo reason instbits exitWait) before after result) :
    Runs (activeHartStep stepNo exitWait) before after result := by
  unfold Runs at hWaiting ⊢
  simp only [activeHartStep, EStateM.run, EStateM.bind, EStateM.instMonad,
    PreSail.readReg, EStateM.get, EStateM.pure, MonadState.get, MonadStateOf.get, getThe, hHart]
  exact hWaiting

/-- The generated invalid-reservation wakeup: a `WAIT_WRS_STO` hart with no interrupt to wake it
returns to `HART_ACTIVE` and reports a successful retirement, touching nothing else.
`valid_reservation` is the constant `false` in this model, so the branch is the reachable one. -/
theorem runHartWaitingWakes (stepNo : Nat) (state : State) (instbits : BitVec 32)
    (pending : state.regs.get? mip = some (0 : BitVec 64))
    (enabled : state.regs.get? mie = some (0 : BitVec 64)) :
    Runs (run_hart_waiting stepNo .WAIT_WRS_STO instbits false) state
      { state with regs := state.regs.insert hart_state (HartState.HART_ACTIVE ()) }
      (.Step_Execute (.Retire_Success (), instbits)) := by
  have skipPrint : Runs (pure () : SailM Unit) state state () := rfl
  unfold run_hart_waiting
  refine Runs.bind (shouldWakeForInterrupt_quiet state pending enabled) ?_
  simp only [Bool.false_eq_true, if_false, valid_reservation, get_config_print_instr]
  refine Runs.bind skipPrint ?_
  refine Runs.bind (writeReg_run state hart_state (HartState.HART_ACTIVE ())) ?_
  rfl

/-- Everything the wakeup retirement reads. Nine registers; no memory, no instruction word, no
program image. -/
structure WaitWakeReady (state : State) (instbits : BitVec 32) (next retired : BitVec 64) :
    Prop where
  privilege : state.regs.get? cur_privilege = some Privilege.Machine
  inhibit : state.regs.get? mcountinhibit = some (0 : BitVec 32)
  filter : state.regs.get? minstretcfg = some (0 : BitVec 64)
  pending : state.regs.get? mip = some (0 : BitVec 64)
  enabled : state.regs.get? mie = some (0 : BitVec 64)
  counter : state.regs.get? minstret = some retired
  target : state.regs.get? nextPC = some next
  waiting : state.regs.get? hart_state = some (.HART_WAITING (.WAIT_WRS_STO, instbits))

/-! The three intermediate states the generated postlude passes through, named so the retirement
below can be stated without a page of record updates. -/

/-- After `try_step` records that this step will count towards `minstret`. -/
def afterCounterArmed (state : State) : State :=
  { state with regs := state.regs.insert minstret_increment true }

/-- After the wakeup returns the hart to running. -/
def afterHartWoken (state : State) : State :=
  { afterCounterArmed state with
    regs := (afterCounterArmed state).regs.insert hart_state (HartState.HART_ACTIVE ()) }

/-- After the postlude's `tick_pc` copies `nextPC` into `PC`. -/
def afterPcTicked (state : State) (next : BitVec 64) : State :=
  { afterHartWoken state with regs := (afterHartWoken state).regs.insert PC next }

/-- The state a wakeup retirement leaves behind: the hart is running again, the pc has advanced to
what `nextPC` held, and the retired-instruction counter has moved. -/
def wokenState (state : State) (next retired : BitVec 64) : State :=
  { afterPcTicked state next with
    regs := (afterPcTicked state next).regs.insert minstret (Sail.BitVec.addInt retired 1) }

@[simp] theorem wokenState_pc (state : State) (next retired : BitVec 64) :
    (wokenState state next retired).regs.get? PC = some next := by
  simp [wokenState, afterPcTicked, Std.ExtDHashMap.get?_insert]

/-- **A closed retirement of the generated `try_step`.** No program image, no fetch, no decode. -/
theorem waitWakeRetires (stepNo : Nat) (state : State) (instbits : BitVec 32)
    (next retired : BitVec 64) (ready : WaitWakeReady state instbits next retired) :
    Runs (try_step stepNo false) state (wokenState state next retired) false := by
  have armedWaiting : (afterCounterArmed state).regs.get? hart_state =
      some (.HART_WAITING (.WAIT_WRS_STO, instbits)) := by
    rw [afterCounterArmed,
      writeReg_read_unchanged state minstret_increment hart_state true (by decide)]
    exact ready.waiting
  have armedPending : (afterCounterArmed state).regs.get? mip = some (0 : BitVec 64) := by
    rw [afterCounterArmed, writeReg_read_unchanged state minstret_increment mip true (by decide)]
    exact ready.pending
  have armedEnabled : (afterCounterArmed state).regs.get? mie = some (0 : BitVec 64) := by
    rw [afterCounterArmed, writeReg_read_unchanged state minstret_increment mie true (by decide)]
    exact ready.enabled
  have selected : Runs (activeHartStep stepNo false) (afterCounterArmed state)
      (afterHartWoken state) (.Step_Execute (.Retire_Success (), instbits)) :=
    activeHartStep_waiting stepNo false (afterCounterArmed state) (afterHartWoken state) _
      .WAIT_WRS_STO instbits armedWaiting
      (runHartWaitingWakes stepNo (afterCounterArmed state) instbits armedPending armedEnabled)
  have wokenHart : (afterHartWoken state).regs.get? hart_state =
      some (HartState.HART_ACTIVE ()) := by
    simp [afterHartWoken]
  have wokenTarget : (afterHartWoken state).regs.get? nextPC = some next := by
    simp [afterHartWoken, afterCounterArmed, Std.ExtDHashMap.get?_insert, ready.target]
  have ticked : Runs (tick_pc ()) (afterHartWoken state) (afterPcTicked state next) () :=
    tickPc_run (afterHartWoken state) next wokenTarget
  have tickedIncrement : (afterPcTicked state next).regs.get? minstret_increment = some true := by
    simp [afterPcTicked, afterHartWoken, afterCounterArmed, Std.ExtDHashMap.get?_insert]
  have tickedCounter : (afterPcTicked state next).regs.get? minstret = some retired := by
    simp [afterPcTicked, afterHartWoken, afterCounterArmed, Std.ExtDHashMap.get?_insert,
      ready.counter]
  exact tryStepRetiresOfSelected stepNo state (afterCounterArmed state) (afterHartWoken state)
    (afterPcTicked state next) (wokenState state next retired) Privilege.Machine retired instbits
    ready.privilege
    (shouldIncMinstretMachine state 0 0 ready.inhibit ready.filter (by decide) (by decide))
    (writeReg_run state minstret_increment true) selected wokenHart ticked tickedIncrement
    tickedCounter
    (writeReg_run (afterPcTicked state next) minstret (Sail.BitVec.addInt retired 1))

/-! ## The witness proper

Three distinct addresses and a state built from `initialState` by hand. Nothing here is chosen to
make a proof go through: the only constraints are that the two in-function addresses differ from
each other and both differ from the sentinel, which is what the bridge's side conditions ask for and
what a real target's layout guarantees.
-/

/-- Where the witness run enters the function. -/
def witnessEntryPc : BitVec 64 := 0x1000#64

/-- The function's exit address — inside the binary, so not the sentinel. -/
def witnessExitPc : BitVec 64 := 0x1004#64

/-- The return sentinel: deliberately far from the two code addresses, as a real one is. -/
def witnessSentinel : BitVec 64 := 0xdead0000#64

/-- The witness function's execution extent. Inhabited, so `witnessRegionAvoidsSentinel` is a claim
about something rather than an empty quantification. -/
abbrev witnessRegion (pc : BitVec 64) : Prop := pc = witnessEntryPc ∨ pc = witnessExitPc

/-- The witness function's exit set. -/
abbrev witnessExit (pc : BitVec 64) : Prop := pc = witnessExitPc

theorem witnessRegionAvoidsSentinel : ∀ pc, witnessRegion pc → pc ≠ witnessSentinel := by
  rintro pc (rfl | rfl) <;> decide

theorem witnessExitAvoidsSentinel : ∀ pc, witnessExit pc → pc ≠ witnessSentinel := by
  rintro pc rfl
  decide

/-- The region really does contain both addresses, and the exit really is one of them: without this
the avoidance hypotheses above would be true for the empty reason. -/
theorem witnessRegion_inhabited :
    witnessRegion witnessEntryPc ∧ witnessRegion witnessExitPc ∧ witnessExit witnessExitPc :=
  ⟨Or.inl rfl, Or.inr rfl, rfl⟩

/-- A hart parked in a store-conditional wait, with `PC` and `nextPC` set by hand. Every register
the wakeup retirement reads is present; nothing else is, and memory is untouched. -/
def waitingState (pc next : BitVec 64) : State :=
  { initialState with
    regs := ((((((((initialState.regs.insert cur_privilege Privilege.Machine).insert
      mcountinhibit (0 : BitVec 32)).insert minstretcfg (0 : BitVec 64)).insert
      mip (0 : BitVec 64)).insert mie (0 : BitVec 64)).insert
      minstret (0 : BitVec 64)).insert PC pc).insert nextPC next).insert
      hart_state (HartState.HART_WAITING (WaitReason.WAIT_WRS_STO, (0 : BitVec 32))) }

@[simp] theorem waitingState_pc (pc next : BitVec 64) :
    (waitingState pc next).regs.get? PC = some pc := by
  simp [waitingState, Std.ExtDHashMap.get?_insert]

theorem waitingState_ready (pc next : BitVec 64) :
    WaitWakeReady (waitingState pc next) 0 next 0 where
  privilege := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  inhibit := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  filter := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  pending := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  enabled := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  counter := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  target := by simp [waitingState, Std.ExtDHashMap.get?_insert]
  waiting := by simp [waitingState]

/-- The state the witness run starts in: at the function's entry, with the exit address queued. -/
def witnessEntryState : State := waitingState witnessEntryPc witnessExitPc

/-- The state the witness run reaches: sitting on the function's exit address. -/
def witnessAtExitState : State := wokenState witnessEntryState witnessExitPc 0

/-- **A closed, entered, one-instruction run confined to the witness function.** The retirement is a
real `try_step` of the generated model, so `FunctionTrace.step` is inhabited by machine behaviour
rather than by an assumption. -/
theorem witnessEnteredRun :
    EnteredFunctionTrace witnessRegion witnessExit witnessEntryPc 0 1
      witnessEntryState witnessAtExitState where
  startsAtEntry := by simp [witnessEntryState]
  entryInRegion := Or.inl rfl
  entryNotExit := by decide
  trace :=
    FunctionTrace.step 0 0 witnessEntryPc witnessEntryState witnessAtExitState witnessAtExitState
      (by simp [witnessEntryState]) (Or.inl rfl) (by decide)
      (waitWakeRetires 0 witnessEntryState 0 witnessExitPc 0
        (waitingState_ready witnessEntryPc witnessExitPc))
      (FunctionTrace.exitAt 1 witnessAtExitState witnessExitPc
        (by simp [witnessAtExitState]) rfl)

/-! ### The bridge, instantiated

The run below starts already on the exit address with the sentinel queued in `nextPC` — the shape a
`ret` leaves — and the wakeup retirement plays the part of that `ret`. The result is a genuine
`TraceToSentinel`: a `.step` carrying a real `Runs (try_step 0 false) … false`, followed by `.done`
at the sentinel. -/

/-- The state the bridged run starts in. -/
def witnessRetState : State := waitingState witnessExitPc witnessSentinel

/-- The state it ends in, with the pc at the sentinel. -/
def witnessSentinelState : State := wokenState witnessRetState witnessSentinel 0

/-- The zero-step confined run this witness bridges: the machine is already on an exit. -/
theorem witnessAtExit :
    FunctionTrace witnessRegion witnessExit 0 0 witnessRetState witnessRetState :=
  FunctionTrace.exitAt 0 witnessRetState witnessExitPc (by simp [witnessRetState]) rfl

/--
**The conclusion is inhabited, and every hypothesis of the bridge holds at once.**

`witnessSentinelState`'s pc is the sentinel; the single retirement is the generated `try_step`; the
region and exit sets are inhabited and both miss the sentinel. So
`traceToSentinel_of_functionTrace` is not vacuous: it produces this.
-/
theorem witnessTraceToSentinel :
    TraceToSentinel witnessSentinel 0 1 witnessRetState witnessSentinelState :=
  traceToSentinel_of_functionTrace witnessRegionAvoidsSentinel witnessExitAvoidsSentinel
    witnessAtExit
    (waitWakeRetires 0 witnessRetState 0 witnessSentinel 0
      (waitingState_ready witnessExitPc witnessSentinel))
    (by simp [witnessSentinelState])

/-- The produced trace is a real step, not the degenerate `done`: it has positive length and its
final pc is the sentinel while its initial pc is not. -/
theorem witnessTraceToSentinel_nondegenerate :
    witnessRetState.regs.get? PC = some witnessExitPc ∧
      witnessExitPc ≠ witnessSentinel ∧
      witnessSentinelState.regs.get? PC = some witnessSentinel := by
  refine ⟨by simp [witnessRetState], by decide, by simp [witnessSentinelState]⟩

/--
**The residue, stated exactly.** The bridge at count 1 over the closed entered run of
`witnessEnteredRun`, with everything discharged except one further retirement from the state that
run ends in. That state has an *active* hart, so the missing step is an ordinary fetch-decode-execute
retirement — the one thing a layer with no program image cannot build. Nothing else about the
count-1 instance is open.
-/
theorem witnessBridgeAtCountOne {final : State}
    (ret : Runs (try_step 1 false) witnessAtExitState final false)
    (landed : final.regs.get? PC = some witnessSentinel) :
    TraceToSentinel witnessSentinel 0 2 witnessEntryState final :=
  traceToSentinel_of_functionTrace witnessRegionAvoidsSentinel witnessExitAvoidsSentinel
    witnessEnteredRun.trace ret landed

end BinaryFv.RiscV.Elfling
