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

/-! ## Compiled wrapper entry

`preZesuDecodeRaw` is the public C interface: input bytes, code, `a0`, `a1`, and decoder globals.
Those facts intentionally say nothing about privilege, counters, physical-memory access, or the
runner's stack. A theorem that executes the wrapper through Sail needs those concrete machine facts
as an additional compiled binding; they cannot be derived from the public interface.
-/

/-- The input-readable region used by the wrapper and every selected descendant. -/
def zesuDecodeRawMachineArgs (args : ZesuDecodeRawArgs) : DecoderMachineArgs where
  inputBase := args.inputBase
  bytes := args.bytes

/-- Machine facts at the actual `zesu_decode_raw` entry. `stackBase` is the stack pointer after the
two emitted frame decrements; the entered stack pointer is exactly `stackBase + 0xa20`.

The `< 2 MiB` clause is the existing public theorem scope. The stack interval is stated explicitly
because the wrapper constructs the allocator object and both inlined `decode` result objects there.
The borrowed input must not overlap that writable frame or the wrapper's `attempted` byte: without
these clauses the wrapper can overwrite its own input before reaching the selected `decode` child.
-/
structure ZesuDecodeRawMachinePre (args : ZesuDecodeRawArgs) (stackBase : Nat)
    (state : State) : Prop where
  atEntry : state.regs.get? Register.PC = some (BitVec.ofNat 64 0x102b0)
  linkAtEntry : ∃ link, state.regs.get? Register.x1 = some link
  savedS0AtEntry : ∃ value, state.regs.get? Register.x8 = some value
  savedS1AtEntry : ∃ value, state.regs.get? Register.x9 = some value
  savedS2AtEntry : ∃ value, state.regs.get? Register.x18 = some value
  savedS3AtEntry : ∃ value, state.regs.get? Register.x19 = some value
  savedS4AtEntry : ∃ value, state.regs.get? Register.x20 = some value
  savedS5AtEntry : ∃ value, state.regs.get? Register.x21 = some value
  savedS6AtEntry : ∃ value, state.regs.get? Register.x22 = some value
  savedS7AtEntry : ∃ value, state.regs.get? Register.x23 = some value
  savedS8AtEntry : ∃ value, state.regs.get? Register.x24 = some value
  savedS9AtEntry : ∃ value, state.regs.get? Register.x25 = some value
  savedS10AtEntry : ∃ value, state.regs.get? Register.x26 = some value
  savedS11AtEntry : ∃ value, state.regs.get? Register.x27 = some value
  stackAtEntry : state.regs.get? Register.x2 = some (BitVec.ofNat 64 (stackBase + 0xa20))
  inputFits : args.inputBase + args.bytes.size ≤ 2 ^ 64
  inputBound : args.bytes.size < 2 * 1024 * 1024
  inputAvoidsStack : args.inputBase + args.bytes.size ≤ stackBase ∨
    stackBase + 0xa20 ≤ args.inputBase
  inputAvoidsAttempted : args.inputBase + args.bytes.size ≤ 0x4215020 ∨
    0x4215020 < args.inputBase
  /-- The exported postcondition preserves every borrowed input byte.  The wrapper writes the
  generated decoder `.bss` block (including `attempted`, `last_status`, and `stored_result`), so
  the input interval must be disjoint from that checked whole block, not merely from `attempted`. -/
  inputAvoidsDecoderGlobals :
    args.inputBase + args.bytes.size ≤ Elflings.GeneratedDecoderGlobals.bssBase ∨
      Elflings.GeneratedDecoderGlobals.bssBase + Elflings.GeneratedDecoderGlobals.bssSize ≤
        args.inputBase
  /-- The borrowed input is outside the allocator interval that `decodeRaw` may own and mutate.
  This is an entry-layout condition: the allocation bound proves every actual cursor interval stays
  inside this authoritative canonical arena. -/
  inputAvoidsCanonicalArena :
    args.inputBase + args.bytes.size ≤ canonicalContractParams.env.arenaBase ∨
      Elflings.canonicalHeapLimit ≤ args.inputBase
  /-- The borrowed input also excludes the two generated mutable allocator words, which sit just
  below the arena and are separately admitted by `ownedRegion`. -/
  inputAvoidsAllocatorState : ∀ address, canonicalContractParams.env.allocatorState address →
    args.inputBase + args.bytes.size ≤ address ∨ address < args.inputBase
  /-- `ownedRegion` also admits the complete canonical stack, not merely this wrapper's local
  frame, so borrowed input must be disjoint from that authoritative interval as well. -/
  inputAvoidsCanonicalStack : ∀ address, canonicalContractParams.env.stack address →
    args.inputBase + args.bytes.size ≤ address ∨ address < args.inputBase
  stackAligned : stackBase % 16 = 0
  stackFrameFits : stackBase + 0xa20 ≤ 2 ^ 64
  /-- The concrete local frame cannot overlap the wrapper's attempted/status globals. -/
  stackAvoidsStatusGlobals : stackBase + 0xa20 ≤ 0x4215020 ∨ 0x4215028 ≤ stackBase
  stackFrameWritable : ∀ index, index < 0xa20 →
    canonicalContractParams.env.stack (stackBase + index)
  /-- The raw decoder's own frame lies below the inline caller's stack pointer after its
  `0xe80` decrement.  This exact interval covers the later `sp + 0x2a0` parent slot. -/
  rawFrameWritable : ∀ index, index < 0x7f0 →
    canonicalContractParams.env.stack (stackBase - 0xe80 + index)
  stackObjectsFit : stackBase + 0x6b0 + canonicalContractParams.env.record.entryResult ≤
    2 ^ 64
  stackObjectsReadable : ∀ index,
    index < 0x6b0 + canonicalContractParams.env.record.entryResult →
      canonicalContractParams.env.stack (stackBase + index)
  machine : DecoderMachinePre
    (functionInstanceExecutionPcs generatedProgram
      functionInstance_raw_decoder_root_zesu_decode_raw)
    (zesuDecodeRawMachineArgs args) state

/-- The real wrapper frame begins above the complete 832-byte `stored_result` payload.  This is
derived from the entry's writable-stack membership in the canonical runner stack, not assumed by a
later continuation. -/
theorem wrapper_stack_after_stored_result {args : ZesuDecodeRawArgs} {stackBase : Nat} {state : State}
    (pre : ZesuDecodeRawMachinePre args stackBase state) :
    0x4215030 + 832 ≤ stackBase := by
  have stackBaseInCanonicalStack : canonicalStack stackBase := by
    simpa only [canonicalContractParams, canonicalEnvironment] using
      pre.stackFrameWritable 0 (by decide)
  simp only [canonicalStack, range] at stackBaseInCanonicalStack
  rw [canonicalStack_pinned.1] at stackBaseInCanonicalStack
  omega

/-- The old one-byte `attempted` exclusion admits an input at `last_status`; the generated `.bss`
interval exclusion rejects that concrete overlap. This checks that the strengthened premise guards
the bytes the first-success route later writes. -/
theorem inputAtStatusViolatesDecoderGlobalsSeparation :
    ¬ ((Elflings.GeneratedDecoderGlobals.bssBase + 4) + 1 ≤
          Elflings.GeneratedDecoderGlobals.bssBase ∨
        Elflings.GeneratedDecoderGlobals.bssBase + Elflings.GeneratedDecoderGlobals.bssSize ≤
          Elflings.GeneratedDecoderGlobals.bssBase + 4) := by
  native_decide

/-- An input beginning at the canonical allocator arena cannot satisfy the entry placement rule. -/
theorem inputAtCanonicalArenaViolatesArenaSeparation :
    ¬ (canonicalContractParams.env.arenaBase + 1 ≤ canonicalContractParams.env.arenaBase ∨
      Elflings.canonicalHeapLimit ≤ canonicalContractParams.env.arenaBase) := by
  native_decide

/-- A byte at `ZKVM_HEAP_POS` is rejected by the allocator-state part of the input placement rule. -/
theorem inputAtAllocatorCursorViolatesAllocatorSeparation :
    ¬ (Elflings.canonicalHeapPosAddr + 1 ≤ Elflings.canonicalHeapPosAddr ∨
      Elflings.canonicalHeapPosAddr < Elflings.canonicalHeapPosAddr) := by
  native_decide

/-- Hide the proof-only stack-base witness from the public C argument type. -/
def CompiledZesuDecodeRawPre (args : ZesuDecodeRawArgs) (state : State) : Prop :=
  ∃ stackBase, ZesuDecodeRawMachinePre args stackBase state

/-- The public wrapper contract with only the machine premises required to execute its emitted
instructions added at entry. Its meaning, public entry clauses, exit clauses, and step bound are
unchanged. -/
def compiledZesuDecodeRawContract : FunctionInstanceContract
    ZesuDecodeRawArgs (Except Contracts.DecodeError BinaryFv.Specs.SSZ.StatelessInput) :=
  let source := functionInstanceZesuDecodeRaw canonicalContractParams.env
    canonicalContractParams.globals canonicalContractParams.resultBuffer
    canonicalContractParams.repStatelessInput DecoderGlobalsModel.fresh
  { spec := source.spec
    binding :=
      { entry := fun args state => source.binding.entry args state ∧
          CompiledZesuDecodeRawPre args state
        exit := source.binding.exit
        stepBound := source.binding.stepBound } }

/-- The Level 2 theorem target for the emitted wrapper. -/
abbrev CompiledZesuDecodeRawInstanceContract : Prop :=
  compiledZesuDecodeRawContract.ImplementsFunctionInstance
    functionInstance_raw_decoder_root_zesu_decode_raw
    (functionInstanceReachedPcs generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceEntryWord functionInstance_raw_decoder_root_zesu_decode_raw)
    (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)

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
