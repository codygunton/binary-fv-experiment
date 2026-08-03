import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.Catalog.Dispatch
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.MachineExecution.Level2AllocatorProof
import BinaryFv.Zesu.MachineExecution.MemcpyInstance

/-!
# The one Level 2 child-summary relation

The wrapper proof selects exactly three compiled children: the inlined allocator, the inlined
`decode`, and the emitted `memcpy`. `Level2ChildSummary` is the single relation consumed by its
`ScopedTrace`; constructors make it impossible to discharge a splice with an unselected function.

The allocator and `memcpy` arms are proved by Sail execution. The `decode` arm is the fixed
two-phase non-ABI contract for its real entries at `0x10308` and `0x10380`.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions

/-- The common type of an exact machine-code child summary. -/
abbrev MachineChildSummary :=
  FunctionInstanceId → Nat → Nat → State → State → Prop

/-- The complete two-segment machine contract for the selected inlined allocator. -/
abbrev AllocatorInlineContract : Prop := MachineExecution.AllocatorInlineContract

/-- Both allocator segments are discharged by concrete Sail execution. -/
theorem allocatorInlineContract_proved : AllocatorInlineContract :=
  MachineExecution.allocatorInlineContract_proved

/-- The emitted `memcpy` body's typed compiled contract, at its generated entry and exits. -/
def memcpyChildSummary (child : FunctionInstanceId) (fromStep used : Nat)
    (before after : State) : Prop :=
  MachineExecution.compiledMemcpySummary child fromStep used before after

/-- The one closed correctness condition for the selected emitted `memcpy` body. -/
abbrev MemcpyInstanceContract : Prop :=
  MachineExecution.CompiledMemcpyInstanceContract

/-- Applying the emitted-body contract produces exactly the summary consumed at any of the three
wrapper call sites. The caller still has to establish the typed copy entry binding. -/
theorem memcpyChildSummary_of_contract (contract : MemcpyInstanceContract)
    (args : CopyArgs)
    (fromStep : Nat) (before : State)
    (pre : (MachineExecution.compiledMemcpyContract
      canonicalContractParams.env).binding.entry args before) :
    ∃ used after,
      used ≤ (MachineExecution.compiledMemcpyContract
        canonicalContractParams.env).binding.stepBound args ∧
      memcpyChildSummary functionInstance_memcpyId fromStep used before after := by
  exact MachineExecution.compiledMemcpySummary_of_contract contract args fromStep before pre

/-- Sail execution of the emitted body produces the selected child summary without assuming a
`memcpy` contract. The caller supplies only the concrete entry binding for its copy arguments. -/
theorem memcpyChildSummary_proved (args : CopyArgs) (fromStep : Nat) (before : State)
    (pre : (MachineExecution.compiledMemcpyContract
      canonicalContractParams.env).binding.entry args before) :
    ∃ used after,
      used ≤ (MachineExecution.compiledMemcpyContract
        canonicalContractParams.env).binding.stepBound args ∧
      memcpyChildSummary functionInstance_memcpyId fromStep used before after := by
  exact memcpyChildSummary_of_contract MachineExecution.compiledMemcpyInstanceContract_proved
    args fromStep before pre

/-- One summary relation for exactly the three children selected at Level 2. -/
inductive Level2ChildSummary : MachineChildSummary where
  | allocator {fromStep used before after}
      (run : MachineExecution.allocatorChildSummary
        functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41Id
        fromStep used before after) :
      Level2ChildSummary
        functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41Id
        fromStep used before after
  | decode {fromStep used before after}
      (run : level3DecodeChildSummary
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
        fromStep used before after) :
      Level2ChildSummary
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
        fromStep used before after
  | memcpy {fromStep used before after}
      (run : memcpyChildSummary functionInstance_memcpyId fromStep used before after) :
      Level2ChildSummary functionInstance_memcpyId fromStep used before after

/-- Every proved allocator segment embeds in the one Level 2 child relation. -/
theorem allocatorChildSummary_to_level2
    {child : FunctionInstanceId} {fromStep used : Nat} {before after : State}
    (run : MachineExecution.allocatorChildSummary child fromStep used before after) :
    Level2ChildSummary child fromStep used before after := by
  rcases run with ⟨rfl, execution⟩
  exact .allocator ⟨rfl, execution⟩

/-- The proved six-instruction allocator setup remains a prefix under the complete Level 2 child
relation. The widening changes no state and no retired-step count. -/
theorem allocator_setup_prefix_level2 (fromStep : Nat)
    (entry afterFirst afterTag afterDecode : State)
    (first : InlineTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      MachineExecution.allocatorChildSummary allocatorInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      fromStep 0 entry afterFirst)
    (atTag : afterFirst.regs.get? Register.PC = some (BitVec.ofNat 64 0x102f4))
    (tagStep : Runs (try_step (fromStep + 1) false) afterFirst afterTag false)
    (second : InlineTransfer
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      MachineExecution.allocatorChildSummary allocatorInlineBoundary generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw
      functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41
      (fromStep + 2) 3 afterTag afterDecode) :
    ConfinedPrefix
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary fromStep 6 entry afterDecode := by
  exact MachineExecution.allocator_setup_prefix fromStep entry afterFirst afterTag afterDecode
    (first.mapSummary fun child stepNo used before after run =>
      allocatorChildSummary_to_level2 run)
    atTag tagStep
    (second.mapSummary fun child stepNo used before after run =>
      allocatorChildSummary_to_level2 run)

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
