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

/-- Compact concrete evidence for a wrapper result-tag route.  The existential lives inside this
`Prop`-valued record, so route composition exposes its trace and final frame without a tower of
retired-counter/state binders in every theorem statement. -/
structure DispatchPath (base : State) (fromStep steps : Nat) (entry : State)
    (exit a0 a1 : BitVec 64) : Prop where
  evidence : ∃ final,
    Trace fromStep steps entry final ∧
    final.regs.get? PC = some exit ∧
    final.regs.get? x10 = some a0 ∧
    final.regs.get? x11 = some a1 ∧
    RetiredCounterPresent final ∧
    final.mem = entry.mem ∧
    Agree platformPreserved base final ∧
    canonicalContractParams.env.CodeIntact final ∧
    final.regs.get? x18 = entry.regs.get? x18 ∧
    final.regs.get? x2 = entry.regs.get? x2

/-- The concrete comparison phase of the tag-one route, through the taken branch at `0x10408`. -/
structure Tag1PrefixPath (base : State) (fromStep : Nat) (entry : State) : Prop where
  evidence : ∃ after,
    Trace fromStep 4 entry after ∧
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 4 entry after ∧
    after.regs.get? PC = some (BitVec.ofNat 64 0x10428) ∧
    after.regs.get? x10 = some (BitVec.ofNat 64 1) ∧
    after.regs.get? x11 = some (BitVec.ofNat 64 1) ∧
    RetiredCounterPresent after ∧
    after.mem = entry.mem ∧
    Agree platformPreserved base after ∧
    canonicalContractParams.env.CodeIntact after ∧
    after.regs.get? x18 = entry.regs.get? x18 ∧
    after.regs.get? x2 = entry.regs.get? x2

end BinaryFv.Zesu.MachineExecution
