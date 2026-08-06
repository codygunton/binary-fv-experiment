import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryPrefix
import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.Zesu.MachineExecution.MemcpyDecoderBridge
import BinaryFv.Zesu.Elflings.GeneratedProgramGeometry
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.Zesu.MachineExecution.OwnedPc

/-!
# Sail proof for the inlined `decode` scope

This file executes the 31 instructions owned directly by the compiler's inlined `decode` instance
and composes them with the three Level 3 child summaries. The inventory below is the reviewable
starting point: every owned word is checked against the pinned program image before any path proof
uses it.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep
open BinaryFv.RiscV.Sep

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The inlined `decode` instance's own execution scope, named once for the whole module.

Spelled out, this occupied a line to itself at 73 sites here, and it is the `own` half of the
`(own, exit, childSummary)` triple every `ConfinedPrefix`, `ScopedTrace` and `CallTransfer` in this
file carries; the other two halves are `DecodeInlineExit args` and `Level3ChildSummary`, which are
already short. As an `abbrev` it is reducible, so it *is* the spelled-out application: a proof or a
downstream module written against the long form elaborates unchanged, and `owned_pc` still sees the
`functionInstanceExecutionPcs` it decides. -/
abbrev decodeInlineOwnPcs : BitVec 64 → Prop :=
  functionInstanceExecutionPcs generatedProgram
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31

def decodeInlineImageWord? (address : Nat) : Option Nat := do
  let byte0 ← Artifacts.programImage.readByte? address
  let byte1 ← Artifacts.programImage.readByte? (address + 1)
  let byte2 ← Artifacts.programImage.readByte? (address + 2)
  let byte3 ← Artifacts.programImage.readByte? (address + 3)
  pure (byte0.toNat + byte1.toNat * 2 ^ 8 + byte2.toNat * 2 ^ 16 + byte3.toNat * 2 ^ 24)

end BinaryFv.Zesu.MachineExecution
