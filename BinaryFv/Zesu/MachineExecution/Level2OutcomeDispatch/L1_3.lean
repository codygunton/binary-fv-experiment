import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.Level2TerminalRouteFrame
import BinaryFv.Zesu.MachineExecution.Level2RetryExitSteps

/-!
# Level 2 result-tag dispatch

The wrapper owns the instructions after either inlined `decode` segment reaches `0x103fc`.
These Sail proofs distinguish the internal result tags before entering the shared wrapper tail.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exact post-state of the tag-one branch at `0x10408`. -/
def wrapperDispatchTag1BranchAfter (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x10408) (BitVec.ofNat 64 0x10428))
    (BitVec.ofNat 64 0x10428) retired

/-- The short prefix of the tag-one route, kept separate from its result-tail frame. -/
theorem wrapper_dispatch_tag1_trace_prefix {state s1 s2 s3 s4 : State} (stepNo : Nat)
    (run1 : Runs (try_step stepNo false) state s1 false)
    (run2 : Runs (try_step (stepNo + 1) false) s1 s2 false)
    (run3 : Runs (try_step (stepNo + 2) false) s2 s3 false)
    (run4 : Runs (try_step (stepNo + 3) false) s3 s4 false) :
    Trace stepNo 4 state s4 := by
  exact Trace.step _ _ _ _ _ run1 <| Trace.step _ _ _ _ _ run2 <|
    Trace.step _ _ _ _ _ run3 <| Trace.one (stepNo + 3) _ _ run4

/-- The short result-tail of the tag-one route. -/
theorem wrapper_dispatch_tag1_trace_suffix {s4 s5 s6 s7 : State} (stepNo : Nat)
    (run5 : Runs (try_step (stepNo + 4) false) s4 s5 false)
    (run6 : Runs (try_step (stepNo + 5) false) s5 s6 false)
    (run7 : Runs (try_step (stepNo + 6) false) s6 s7 false) :
    Trace (stepNo + 4) 3 s4 s7 := by
  exact Trace.step _ _ _ _ _ run5 <| Trace.step _ _ _ _ _ run6 <|
    Trace.one (stepNo + 6) _ _ run7

/-- The short prefix of the tag-two route, before it writes the rejection result. -/
theorem wrapper_dispatch_tag2_trace_prefix {state s1 s2 s3 s4 s5 : State} (stepNo : Nat)
    (run1 : Runs (try_step stepNo false) state s1 false)
    (run2 : Runs (try_step (stepNo + 1) false) s1 s2 false)
    (run3 : Runs (try_step (stepNo + 2) false) s2 s3 false)
    (run4 : Runs (try_step (stepNo + 3) false) s3 s4 false)
    (run5 : Runs (try_step (stepNo + 4) false) s4 s5 false) :
    Trace stepNo 5 state s5 := by
  exact Trace.step _ _ _ _ _ run1 <| Trace.step _ _ _ _ _ run2 <|
    Trace.step _ _ _ _ _ run3 <| Trace.step _ _ _ _ _ run4 <|
    Trace.one (stepNo + 4) _ _ run5

/-- The short rejection tail of the tag-two route. -/
theorem wrapper_dispatch_tag2_trace_suffix {s5 s6 s7 s8 s9 : State} (stepNo : Nat)
    (run6 : Runs (try_step (stepNo + 5) false) s5 s6 false)
    (run7 : Runs (try_step (stepNo + 6) false) s6 s7 false)
    (run8 : Runs (try_step (stepNo + 7) false) s7 s8 false)
    (run9 : Runs (try_step (stepNo + 8) false) s8 s9 false) :
    Trace (stepNo + 5) 4 s5 s9 := by
  exact Trace.step _ _ _ _ _ run6 <| Trace.step _ _ _ _ _ run7 <|
    Trace.step _ _ _ _ _ run8 <| Trace.one (stepNo + 8) _ _ run9

end BinaryFv.Zesu.MachineExecution
