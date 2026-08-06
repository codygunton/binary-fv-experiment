import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# Shared `zesu_decode_raw` epilogue

The wrapper paths meet at `0x1035c`.  This module proves that common instruction sequence; callers
supply the value already selected for `a0`, the normalized status in `a1`, and the ordinary
machine frame carried from their own path.  No source-function ABI is assigned to an inline child.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exact state after the final `addi sp, sp, 2032` at `0x10374`. -/
def wrapperAfterFinalStackRestore (state : State) (retired stack : BitVec 64) : State :=
  tryStepStackAddiAfterRetired state (BitVec.ofNat 64 0x10374) 0x7f0#12 stack retired

/-- The final stack restoration writes `x2`, so memory is the memory it was handed. -/
@[grind =] theorem wrapperAfterFinalStackRestore_mem (state : State) (retired stack : BitVec 64) :
    (wrapperAfterFinalStackRestore state retired stack).mem = state.mem := rfl

/-- Exact state after the wrapper's final `ret` at `0x10378`. -/
def wrapperAfterReturn (state : State) (retired link : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x10378) link)
    link retired

/-- The wrapper's final `ret` touches no memory. -/
@[grind =] theorem wrapperAfterReturn_mem (state : State) (retired link : BitVec 64) :
    (wrapperAfterReturn state retired link).mem = state.mem := rfl

/-- Compact public composition rule for the eight concrete instructions from the status store
through the restored-link return.  The caller supplies the typed intermediate frame facts to the
individual step theorems; this rule merely records their real machine sequencing. -/
theorem wrapper_epilogue_trace (fromStep : Nat) (before afterStore afterFirst afterRa afterS0 afterS1
    afterS2 afterStack after : State)
    (statusStore : Runs (try_step fromStep false) before afterStore false)
    (firstRestore : Runs (try_step (fromStep + 1) false) afterStore afterFirst false)
    (restoreRa : Runs (try_step (fromStep + 2) false) afterFirst afterRa false)
    (restoreS0 : Runs (try_step (fromStep + 3) false) afterRa afterS0 false)
    (restoreS1 : Runs (try_step (fromStep + 4) false) afterS0 afterS1 false)
    (restoreS2 : Runs (try_step (fromStep + 5) false) afterS1 afterS2 false)
    (finalRestore : Runs (try_step (fromStep + 6) false) afterS2 afterStack false)
    (returnRun : Runs (try_step (fromStep + 7) false) afterStack after false) :
    Trace fromStep 8 before after := by
  trace_steps [statusStore, firstRestore, restoreRa, restoreS0, restoreS1, restoreS2, finalRestore,
    returnRun]

/-- The public post-status tail boundary.  The capstone establishes this frame after the status
store; this module consumes it only from `0x10360` onward. -/
structure WrapperEpilogueTailInput (state : State) : Prop where
  frame : WrapperSavedRegisterFrame stackBase link savedS0 savedS1 savedS2 state
  stack : state.regs.get? x2 = some stackValue
  result : state.regs.get? x10 = some resultValue
  status : state.regs.get? x11 = some statusValue

/-- A compact tail result exposes the actual return target and restored callee-visible registers. -/
structure WrapperEpilogueTailResult (fromStep : Nat) (before after : State) (link savedS0 savedS1
    savedS2 stack result status : BitVec 64) : Prop where
  trace : Trace fromStep 7 before after
  pc : after.regs.get? PC = some link
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some stack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after

/-- The final two instructions of the wrapper epilogue return through the restored link without
changing its saved-register result. -/
structure WrapperEpilogueReturnResult (fromStep : Nat) (base before after : State)
    (link savedS0 savedS1 savedS2 stack restoredStack result status : BitVec 64) : Prop where
  trace : Trace fromStep 2 before after
  pc : after.regs.get? PC = some link
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some restoredStack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

/-- The complete post-status epilogue result, from the first stack adjustment through `ret`. -/
structure WrapperEpilogueCompleteResult (fromStep : Nat) (base before after : State)
    (link savedS0 savedS1 savedS2 restoredStack result status : BitVec 64) : Prop where
  trace : Trace fromStep 7 before after
  pc : after.regs.get? PC = some link
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some restoredStack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

end BinaryFv.Zesu.MachineExecution
