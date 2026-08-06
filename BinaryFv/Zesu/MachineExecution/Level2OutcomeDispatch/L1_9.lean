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
