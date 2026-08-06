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

/-- The concrete rejection-result phase of the tag-one route, from `0x10428` to `0x1035c`. -/
structure Tag1SuffixPath (base : State) (fromStep : Nat) (entry : State) : Prop where
  evidence : ∃ final,
    Trace fromStep 3 entry final ∧
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 3 entry final ∧
    final.regs.get? PC = some (BitVec.ofNat 64 0x1035c) ∧
    final.regs.get? x10 = some (BitVec.ofNat 64 0) ∧
    final.regs.get? x11 = some (BitVec.ofNat 64 4) ∧
    RetiredCounterPresent final ∧
    final.mem = entry.mem ∧
    Agree platformPreserved base final ∧
    canonicalContractParams.env.CodeIntact final ∧
    final.regs.get? x18 = entry.regs.get? x18 ∧
    final.regs.get? x2 = entry.regs.get? x2

/-- The public, composable boundary of one result-tag route.  Unlike the local Sail step
proofs, this keeps the exact execution trace together with the state frame needed by the next
wrapper segment. -/
structure WrapperDispatchRouteFrame (base before after : State) (fromStep steps : Nat)
    (terminalPc result status : BitVec 64) : Prop where
  trace : Trace fromStep steps before after
  atTerminal : after.regs.get? PC = some terminalPc
  resultValue : after.regs.get? x10 = some result
  statusValue : after.regs.get? x11 = some status
  memory : after.mem = before.mem
  platform : Agree platformPreserved base after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after
  savedS2 : after.regs.get? x18 = before.regs.get? x18
  savedStack : after.regs.get? x2 = before.regs.get? x2

end BinaryFv.Zesu.MachineExecution
