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

end BinaryFv.Zesu.MachineExecution
