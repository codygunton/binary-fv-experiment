import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.Zesu.Machine.DecodeTactic

/-!
# The post-state of a register-writing fall-through instruction, and its retirement

Ported from `d0f50581:BinaryFv/Zesu/MachineExecution/RegisterWriteStep.lean`, lines 56–151 and
184–223, which are target-agnostic: they mention no address, no generated program and no artifact.
What did not port is the part that did: `decodeRawExecutionPcs`, `decodeRawExit`, and the
`Artifacts.programImage` reads, all replaced by `BinaryFv/Zesu/Machine/Target.lean`.

`InstructionStepPlatform` went with the wipe, so `StepPremises` below replaces it. It is the same
bundle under a name this branch owns, and it is assembled from `abstractPlatform_of_base` /
`abstractElp_of_base` in `RiscV/Step/AbstractPremise.lean` rather than proved from scratch.

## What one instruction costs

This module is the reason the class-lemma layer existed. `tryStepFallThroughWriteRegRetires` takes
twenty premises and `execute_LOAD_lbu_run` twelve more; `fallThroughRegisterWriteStepWithoutReturn`
reduces the first twenty to one `StepPremises` plus the four that are genuinely per-instruction.
That is the collapse `PLAN_PROOF_PATTERNS.md` measured at 2.33x for instruction-step families, and
it is what a motif lemma has to beat — not the raw obligation count.
-/

namespace BinaryFv.Zesu.Machine

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

/-! ## The post-state -/

/-- Exact post-state of a register-writing fall-through instruction. -/
def afterRegisterWrite (state : State) (pc retired : BitVec 64) (destination : Register)
    (value : RegisterType destination) : State :=
  tryStepControlFlowAfterRetired
    { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
      regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
        destination value }
    (Sail.BitVec.addInt pc 4) retired

theorem afterRegisterWrite_agree_of {P : Register → Prop} {state : State}
    {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination}
    (notDestination : ¬ P destination) (notPc : ¬ P PC) (notNextPc : ¬ P nextPC)
    (notIncrement : ¬ P minstret_increment) (notRetired : ¬ P minstret) :
    Agree P state (afterRegisterWrite state pc retired destination value) := by
  intro register preserved
  have different : destination ≠ register := by
    intro equal
    exact notDestination (equal ▸ preserved)
  have differentPc : PC ≠ register := by
    intro equal
    subst register
    exact notPc preserved
  have differentNextPc : nextPC ≠ register := by
    intro equal
    subst register
    exact notNextPc preserved
  have differentIncrement : minstret_increment ≠ register := by
    intro equal
    subst register
    exact notIncrement preserved
  have differentRetired : minstret ≠ register := by
    intro equal
    subst register
    exact notRetired preserved
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    different, differentPc, differentNextPc, differentIncrement, differentRetired]

theorem afterRegisterWrite_agree {state : State} {pc retired : BitVec 64}
    {destination : Register} {value : RegisterType destination}
    (notPreserved : ¬ platformPreserved destination) :
    Agree platformPreserved state (afterRegisterWrite state pc retired destination value) :=
  afterRegisterWrite_agree_of notPreserved (by simp [platformPreserved])
    (by simp [platformPreserved]) (by simp [platformPreserved]) (by simp [platformPreserved])

theorem afterRegisterWrite_register (state : State) (pc retired : BitVec 64)
    (destination register : Register) (value : RegisterType destination)
    (notDestination : destination ≠ register) (notPc : PC ≠ register)
    (notNextPc : nextPC ≠ register) (notIncrement : minstret_increment ≠ register)
    (notRetired : minstret ≠ register) :
    (afterRegisterWrite state pc retired destination value).regs.get? register =
      state.regs.get? register := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notDestination, notPc, notNextPc, notIncrement, notRetired]

/-- The write set of a full register-writing retirement: the `try_step` bookkeeping, plus the
instruction's destination.

`destination` stays a separate `RegSet.only` rather than being folded into a closed set. That is
what lets `RegSet.Disjoint.union` split a later obligation into a fact about the bookkeeping, proved
once per preserved predicate, and one disequality about the destination. Widening the destination
into a closed over-approximation looks tempting and is wrong: it strengthens the obligation into
something false for `platformPreserved`, which holds `x1`. -/
theorem afterRegisterWrite_writes (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only destination)) state
      (afterRegisterWrite state pc retired destination value) :=
  fun r hr =>
    afterRegisterWrite_register state pc retired destination r value
      (fun h => hr (Or.inr h.symm))
      (fun h => hr (Or.inl (Or.inl h.symm)))
      (fun h => hr (Or.inl (Or.inr (Or.inl h.symm))))
      (fun h => hr (Or.inl (Or.inr (Or.inr (Or.inr h.symm)))))
      (fun h => hr (Or.inl (Or.inr (Or.inr (Or.inl h.symm)))))

theorem afterRegisterWrite_mem (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).mem = state.mem := rfl

theorem afterRegisterWrite_retired_present (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    RetiredCounterPresent (afterRegisterWrite state pc retired destination value) := by
  refine ⟨Sail.BitVec.addInt retired 1, ?_⟩
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]

theorem afterRegisterWrite_pc (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination) :
    (afterRegisterWrite state pc retired destination value).regs.get? PC =
      some (Sail.BitVec.addInt pc 4) := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

/-! ## The step premises, bundled

`InstructionStepPlatform` went with the wipe. This is the same bundle: everything
`tryStepFallThroughWriteRegRetires` needs that is a fact about the *state* rather than about the
instruction. Bundling matters — a call site carries one of these across a whole segment, and only
the per-instruction facts change from step to step.

Not `Prop`: it carries three counter values (`inhibit`, `config`, `retired`) alongside its proofs,
and a `Prop`-valued structure with several data fields gets no projections, because it is not
subsingleton-eliminable. -/

structure StepPremises (state : State) (pc : BitVec 64) where
  fetch : FetchBasePlatform (tryStepControlFlowAfterIncrement state) pc
  fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) pc
  interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state)
  notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state)
  hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())
  inhibit : BitVec 32
  inhibitRead : state.regs.get? mcountinhibit = some inhibit
  notInhibited : _get_Counterin_IR inhibit = 0#1
  config : BitVec 64
  configRead : state.regs.get? minstretcfg = some config
  machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1
  retired : BitVec 64
  retiredRead : state.regs.get? minstret = some retired

/-- One register-writing fall-through instruction, retired.

The `Runs (execute …)` premise is the only genuinely per-instruction work left: everything about the
machine is in `premises`, and the four disequalities are `decide`. -/
theorem fallThroughRegisterWriteStep (stepNo : Nat) (state : State) (pc : BitVec 64)
    (byte0 byte1 byte2 byte3 : BitVec 8) (inst : instruction)
    (destination : Register) (value : RegisterType destination)
    (premises : StepPremises state pc)
    (bytes : FetchBytesAt (tryStepControlFlowAfterIncrement state) pc byte0 byte1 byte2 byte3)
    (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (execute : Runs (execute inst)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc with
        regs := (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc).regs.insert
          destination value }
      (.Retire_Success ()))
    (destinationNotNextPc : destination ≠ nextPC := by decide)
    (destinationNotHart : destination ≠ hart_state := by decide)
    (destinationNotIncrement : destination ≠ minstret_increment := by decide)
    (destinationNotRetired : destination ≠ minstret := by decide) :
    Runs (try_step stepNo false) state
      (afterRegisterWrite state pc premises.retired destination value) false :=
  tryStepFallThroughWriteRegRetires stepNo state pc premises.retired premises.inhibit
    premises.config byte0 byte1 byte2 byte3 inst destination value premises.fetch
    premises.fetchNoMMIO bytes premises.interrupts base decode premises.notExpected execute
    destinationNotNextPc destinationNotHart destinationNotIncrement destinationNotRetired
    premises.hartRead premises.inhibitRead premises.configRead premises.notInhibited
    premises.machineEnabled premises.retiredRead

end BinaryFv.Zesu.Machine
