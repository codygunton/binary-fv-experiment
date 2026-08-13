import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.RegisterWrite
import BinaryFv.RiscV.Elfling.Seg
import BinaryFv.Zesu.Machine.DecodeTactic

/-!
# The post-state of a register-writing fall-through instruction, and its retirement

Only `StepPremises` and `fallThroughRegisterWriteStep` live here. The post-state family
(`afterRegisterWrite` and its five lemmas) is in `BinaryFv/RiscV/Step/RegisterWrite.lean`, which
survived the wipe — and it must be *that* constant, because `Seg.step` is stated against it.

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

/-! ## The post-state

`afterRegisterWrite` and its five lemmas are **not** redefined here. They survived the wipe in
`BinaryFv/RiscV/Step/RegisterWrite.lean`, and `Seg.step` is stated against those, so a local copy
would be a different constant that `Seg.step` refuses. An earlier revision of this file duplicated
them; that was wasted work and it would have made the composition below impossible. -/

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
