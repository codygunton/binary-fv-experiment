import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4BoundaryInventory
import BinaryFv.Zesu.Contracts.Canonicality
import BinaryFv.Zesu.Contracts.Collections
import BinaryFv.Zesu.Contracts.Containers
import BinaryFv.Zesu.Contracts.PrimitiveReadsAndSlices
import BinaryFv.Zesu.Contracts.Runtime

/-!
# Level 4 `decodeRaw` boundary contracts

The Level 4 selection is the 18 displayed boundaries in `Level4BoundaryInventory`: fourteen
generated `FunctionInstance` values and four excluded inline regions.  Every interface below keeps
the source meaning and a finite conservative bound.  Inlined Zig functions do not receive a
source-level RISC-V ABI: their adapters bind the source values to the live registers and stack
carriers at the optimized entry instead.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.DecodedValue BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.Elflings.GeneratedLevel4Attribution
open LeanRV64DExecutable.Functions Register

/-- A generated-function boundary with its source meaning, optimized entry/exit binding, and
conservative step bound. -/
structure Level4FunctionInstanceInterface (Args Outcome : Type) where
  functionInstance : FunctionInstance
  spec : SourceFunctionSpec Args Outcome
  entry : Args → State → Prop
  exit : Args → Outcome → State → State → Prop
  /-- Exact machine region owned by this boundary kind. -/
  executionPcs : BitVec 64 → Prop
  /-- Terminal may depend on the incoming link for a `ret` leaf. -/
  terminal : State → BitVec 64 → Prop
  stepBound : Args → Nat

/-- A non-cataloged inline-region boundary.  Excluded regions have no `FunctionInstanceContract`:
they are distinct optimized regions and must not be represented as source functions. -/
structure Level4InlineRegionInterface (Args : Type) where
  region : Program.ExcludedFunctionInstance
  entry : Args → State → Prop
  exit : Args → State → State → Prop
  stepBound : Args → Nat

/-- A full optimized boundary whose source occurrence has several generated fragments. -/
structure Level4DynamicFunctionInterface (Args Outcome : Type) where
  functionInstance : FunctionInstance
  boundary : AttributionFragmentBoundary
  carrierRoutes : Array AttributionOutcomeCarrierRoute
  spec : SourceFunctionSpec Args Outcome
  entry : Args → State → Prop
  reached : BitVec 64 → Prop
  terminal : BitVec 64 → Prop
  exit : Args → Outcome → State → State → Prop
  stepBound : Args → Nat

/-- Values read by the `decodeRaw` prologue before it writes its 13-word save area.  This is a
boundary binding for the actual optimized entry at `0x10444`, not a RISC-V ABI premise: both real
calls from inlined `decode` must construct it from their concrete caller state. -/
structure Level4DecodeRawEntryFrame (state : State) where
  stackPointer : BitVec 64
  link : BitVec 64
  savedS0 : BitVec 64
  savedS1 : BitVec 64
  savedS2 : BitVec 64
  savedS3 : BitVec 64
  savedS4 : BitVec 64
  savedS5 : BitVec 64
  savedS6 : BitVec 64
  savedS7 : BitVec 64
  savedS8 : BitVec 64
  savedS9 : BitVec 64
  savedS10 : BitVec 64
  savedS11 : BitVec 64
  stackPointerAtEntry : state.regs.get? x2 = some stackPointer
  linkAtEntry : state.regs.get? x1 = some link
  savedS0AtEntry : state.regs.get? x8 = some savedS0
  savedS1AtEntry : state.regs.get? x9 = some savedS1
  savedS2AtEntry : state.regs.get? x18 = some savedS2
  savedS3AtEntry : state.regs.get? x19 = some savedS3
  savedS4AtEntry : state.regs.get? x20 = some savedS4
  savedS5AtEntry : state.regs.get? x21 = some savedS5
  savedS6AtEntry : state.regs.get? x22 = some savedS6
  savedS7AtEntry : state.regs.get? x23 = some savedS7
  savedS8AtEntry : state.regs.get? x24 = some savedS8
  savedS9AtEntry : state.regs.get? x25 = some savedS9
  savedS10AtEntry : state.regs.get? x26 = some savedS10
  savedS11AtEntry : state.regs.get? x27 = some savedS11

def HasDecodeRawEntryFrame (state : State) : Prop := Nonempty (Level4DecodeRawEntryFrame state)

/-- The strengthened emitted-`decodeRaw` entry is available for Level 4 proof work but is not yet
wired into the Level 3/root gauge.  Replacing the old entry requires proofs that both actual calls
at `0x1031c` and `0x103d8` supply this frame. -/
def compiledDecodeRawContractWithEntryFrame : FunctionInstanceContract
    EntryArgs (Except Contracts.DecodeError BinaryFv.Specs.SSZ.StatelessInput) :=
  let prior := compiledDecodeRawContract
  { spec := prior.spec
    binding :=
      { entry := fun args state => prior.binding.entry args state ∧ HasDecodeRawEntryFrame state
        exit := prior.binding.exit
        stepBound := prior.binding.stepBound } }

abbrev CompiledDecodeRawEntryFrameContract : Prop :=
  compiledDecodeRawContractWithEntryFrame.ImplementsFunctionInstance
    functionInstance_ssz_raw_decodeRaw
    (functionInstanceReachedPcs generatedProgram functionInstance_ssz_raw_decodeRaw)
    (functionInstanceEntryWord functionInstance_ssz_raw_decodeRaw)
    (functionInstanceExitPred functionInstance_ssz_raw_decodeRaw)

/-- The exact generated entry word is a static boundary fact, not an ABI claim. -/
def Level4FunctionInstanceInterface.atEntry {Args Outcome : Type}
    (interface : Level4FunctionInstanceInterface Args Outcome) (state : State) : Prop :=
  state.regs.get? PC = some (functionInstanceEntryWord interface.functionInstance)

/-- A Level 4 function-instance assumption has the same bounded entered-trace shape that its
parent composition consumes.  The bound is an assumed universal contract clause; finite evidence
only checks observed executions and is not substituted for this quantifier. -/
def Level4FunctionInstanceInterface.BoundedImplements {Args Outcome : Type}
    (interface : Level4FunctionInstanceInterface Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (before : State), interface.entry args before →
    ∃ used after,
      used ≤ interface.stepBound args ∧
      EnteredFunctionTrace
        interface.executionPcs (interface.terminal before)
        (functionInstanceEntryWord interface.functionInstance) fromStep used before after ∧
        interface.exit args (interface.spec.meaning args) before after

/-- The dynamic assumptions range over the accepted recursive subtree geometry.  Carrier routes
classified as source-reviewed outcomes are obligations for the later fi6 proof; intermediate and
unclassified routes remain progress transitions, never semantic terminals. -/
def Level4DynamicFunctionInterface.ResumableSubtree {Args Outcome : Type}
    (interface : Level4DynamicFunctionInterface Args Outcome) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (before : State), interface.entry args before →
    ∀ route ∈ interface.carrierRoutes,
      route.child = interface.functionInstance.id →
      route.handoff ∈ interface.boundary.handoffs →
      ∃ used after, used ≤ interface.stepBound args ∧
        EnteredFunctionTrace
          (fun pc => pc.toNat ∈ interface.boundary.fullExecutionPcs)
          (fun pc => pc = BitVec.ofNat 64 route.handoff.target)
          (functionInstanceEntryWord interface.functionInstance) fromStep used before after ∧
        (route.classification = .sourceReviewedOutcomePath →
          interface.exit args (interface.spec.meaning args) before after)

/-- Excluded regions have no generated `FunctionInstance` exit predicate.  They return to the
caller-held link register, except for the allocator-free tail-call path which enters the selected
allocator-free instance. -/
def inlineRegionExit (region : Program.ExcludedFunctionInstance) (before after : State) : Prop :=
  after.regs.get? PC = before.regs.get? x1 ∨
    (region.id = excludedFunctionInstance_mem_Allocator_free_anon_1214Id ∧
      after.regs.get? PC = some
        (functionInstanceEntryWord functionInstance_raw_decoder_root_allocatorFree))

def Level4InlineRegionInterface.BoundedImplements {Args : Type}
    (interface : Level4InlineRegionInterface Args) : Prop :=
  ∀ (args : Args) (fromStep : Nat) (before : State), interface.entry args before →
    ∃ used after,
      used ≤ interface.stepBound args ∧
      EnteredFunctionTrace (RegionPcs interface.region.regions)
        (fun pc => pc = before.regs.getD x1 0 ∨
          (interface.region.id = excludedFunctionInstance_mem_Allocator_free_anon_1214Id ∧
            pc = functionInstanceEntryWord functionInstance_raw_decoder_root_allocatorFree))
        (BitVec.ofNat 64 interface.region.regions[0]!.start) fromStep used before after ∧
        inlineRegionExit interface.region before after ∧ interface.exit args before after

/-- Keep a source contract's meaning and source-level semantic postcondition at a genuine emitted
call boundary, adding only the generated entry word. -/
def sourceFunctionInstanceInterface {Error Args Result : Type} (functionInstance : FunctionInstance)
    (contract : FunctionContract Error Args Result) :
    Level4FunctionInstanceInterface Args (Except Error Result) where
  functionInstance := functionInstance
  spec := contract.toSourceFunctionSpec
  entry := fun args state =>
    contract.pre args state ∧ state.regs.get? PC = some (functionInstanceEntryWord functionInstance)
  exit := contract.post
  executionPcs := functionInstanceExecutionPcs generatedProgram functionInstance
  terminal := fun _ => functionInstanceExitPred functionInstance
  stepBound := contract.stepBound

/-- The four direct `readOffset` occurrences consume bytes through `s4`, not the source ABI's
`a0`/`a1`/`a2` convention.  Each adapter records its actual input base and byte window. -/
structure ReadOffsetInlineArgs where
  inputBase : Nat
  bytes : ByteArray
  offset : Nat

def readOffsetOccurrenceOffset (id : FunctionInstanceId) : Nat :=
  if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23Id then 2
  else if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23Id then 6
  else if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23Id then 10
  else 14

def readOffsetOccurrenceResult (id : FunctionInstanceId) (value : Nat) (state : State) : Prop :=
  if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23Id then
    state.regs.get? x23 = some (BitVec.ofNat 64 value)
  else if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23Id then
    state.regs.get? x25 = some (BitVec.ofNat 64 value)
  else if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23Id then
    state.regs.get? x24 = some (BitVec.ofNat 64 value)
  else state.regs.get? x19 = some (BitVec.ofNat 64 value)

def readOffsetOccurrenceResultPc (id : FunctionInstanceId) : BitVec 64 :=
  if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23Id then
    BitVec.ofNat 64 0x105c8
  else if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23Id then
    BitVec.ofNat 64 0x105cc
  else if id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23Id then
    BitVec.ofNat 64 0x105d0
  else BitVec.ofNat 64 0x105d4

/-- The source meaning shared by all four adapters.  The adapter-specific offset and result register
remain separate because the optimized regions are interleaved. -/
def readOffsetSourceMeaning (args : ReadOffsetInlineArgs) : Except Contracts.DecodeError Nat :=
  meaningReadOffset args.bytes args.offset

def readOffsetInlineEntry (functionInstance : FunctionInstance) (args : ReadOffsetInlineArgs)
    (state : State) : Prop :=
  state.regs.get? PC = some (functionInstanceEntryWord functionInstance) ∧
    canonicalContractParams.env.CodeIntact state ∧
    MemoryBytes state args.inputBase args.bytes ∧
    state.regs.get? x20 = some (BitVec.ofNat 64 args.inputBase) ∧
    args.offset = readOffsetOccurrenceOffset functionInstance.id ∧ args.offset + 4 ≤ args.bytes.size
    ∧ args.inputBase < 2 ^ 64 ∧ args.inputBase + args.bytes.size ≤ 2 ^ 64

def inputWindowFits64 (base size : Nat) : Prop := base < 2 ^ 64 ∧ base + size ≤ 2 ^ 64

/-- The four byte lanes used by an occurrence.  `get!` is safe under its entry's four-byte
window premise; keeping the lanes in the contract makes the optimized register arithmetic
auditable without pretending that the source reader has an ABI at these inline PCs. -/
def readOffsetLane (args : ReadOffsetInlineArgs) (lane : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (args.bytes.get! (args.offset + lane)).toNat

def readOffsetShift (args : ReadOffsetInlineArgs) (lane shift : Nat) : BitVec 64 :=
  readOffsetLane args lane <<< BitVec.ofNat 64 shift

/-- Exact register values after each owned non-final reader fragment, transcribed from the
production `lbu`/`slli`/`or` words at `0x10534` through `0x105c0`. -/
def readOffsetFragmentOutput (start : Nat) (args : ReadOffsetInlineArgs) (state : State) : Prop :=
  if start = 0x10534 then
    state.regs.get? x10 = some (readOffsetLane args 0) ∧
    state.regs.get? x11 = some (readOffsetLane args 1) ∧
    state.regs.get? x12 = some (readOffsetLane args 2) ∧
    state.regs.get? x13 = some (readOffsetLane args 3)
  else if start = 0x10554 then
    state.regs.get? x10 = some (readOffsetShift args 1 8 ||| readOffsetLane args 0) ∧
    state.regs.get? x12 = some (readOffsetShift args 3 24 ||| readOffsetShift args 2 16)
  else if start = 0x10544 then
    state.regs.get? x14 = some (readOffsetLane args 0) ∧
    state.regs.get? x15 = some (readOffsetLane args 1) ∧
    state.regs.get? x16 = some (readOffsetLane args 2) ∧
    state.regs.get? x17 = some (readOffsetLane args 3)
  else if start = 0x10578 then
    state.regs.get? x14 = some (readOffsetLane args 0) ∧
    state.regs.get? x15 = some (readOffsetShift args 1 8) ∧
    state.regs.get? x16 = some (readOffsetShift args 2 16) ∧
    state.regs.get? x17 = some (readOffsetShift args 3 24)
  else if start = 0x10590 then
    state.regs.get? x14 = some (readOffsetShift args 1 8 ||| readOffsetLane args 0) ∧
    state.regs.get? x15 = some (readOffsetShift args 3 24 ||| readOffsetShift args 2 16)
  else if start = 0x10568 then
    state.regs.get? x11 = some (readOffsetLane args 0) ∧
    state.regs.get? x13 = some (readOffsetLane args 1) ∧
    state.regs.get? x5 = some (readOffsetLane args 2) ∧
    state.regs.get? x6 = some (readOffsetLane args 3)
  else if start = 0x10584 then
    state.regs.get? x11 = some (readOffsetLane args 0) ∧ state.regs.get? x13 = some (readOffsetShift args 1 8) ∧
    state.regs.get? x5 = some (readOffsetShift args 2 16) ∧
    state.regs.get? x6 = some (readOffsetShift args 3 24)
  else if start = 0x10598 then
    state.regs.get? x11 = some (readOffsetShift args 1 8 ||| readOffsetLane args 0) ∧
    state.regs.get? x13 = some (readOffsetShift args 3 24 ||| readOffsetShift args 2 16)
  else
    state.regs.get? x16 = some (readOffsetShift args 1 8 ||| readOffsetLane args 0) ∧
    state.regs.get? x17 = some (readOffsetShift args 3 24 ||| readOffsetShift args 2 16)

/-- Live inputs consumed by each non-first fragment.  These are exactly the outputs published by
the preceding fragment of the same occurrence; the parent may interleave sibling instructions but
cannot start a reader fragment from arbitrary argument registers. -/
def readOffsetFragmentInput (start : Nat) (args : ReadOffsetInlineArgs) (state : State) : Prop :=
  if start = 0x10534 ∨ start = 0x10544 ∨ start = 0x10568 ∨ start = 0x105a0 then True
  else if start = 0x10554 then
    state.regs.get? x10 = some (readOffsetLane args 0) ∧ state.regs.get? x11 = some (readOffsetLane args 1) ∧
    state.regs.get? x12 = some (readOffsetLane args 2) ∧ state.regs.get? x13 = some (readOffsetLane args 3)
  else if start = 0x10578 then
    state.regs.get? x14 = some (readOffsetLane args 0) ∧ state.regs.get? x15 = some (readOffsetLane args 1) ∧
    state.regs.get? x16 = some (readOffsetLane args 2) ∧ state.regs.get? x17 = some (readOffsetLane args 3)
  else if start = 0x10590 then
    state.regs.get? x14 = some (readOffsetLane args 0) ∧ state.regs.get? x15 = some (readOffsetShift args 1 8) ∧
    state.regs.get? x16 = some (readOffsetShift args 2 16) ∧ state.regs.get? x17 = some (readOffsetShift args 3 24)
  else if start = 0x10584 then
    state.regs.get? x11 = some (readOffsetLane args 0) ∧ state.regs.get? x13 = some (readOffsetLane args 1) ∧
    state.regs.get? x5 = some (readOffsetLane args 2) ∧ state.regs.get? x6 = some (readOffsetLane args 3)
  else if start = 0x10598 then
    state.regs.get? x11 = some (readOffsetLane args 0) ∧ state.regs.get? x13 = some (readOffsetShift args 1 8) ∧ state.regs.get? x5 = some (readOffsetShift args 2 16) ∧
    state.regs.get? x6 = some (readOffsetShift args 3 24)
  else True

/-- A direct reader publishes its accumulator only after its final interleaved fragment. -/
def readOffsetContinuationExit (functionInstance : FunctionInstance) (args : ReadOffsetInlineArgs)
    (result : Except Contracts.DecodeError Nat) (_before after : State) : Prop :=
  result = readOffsetSourceMeaning args ∧
    after.regs.get? PC = some (readOffsetOccurrenceResultPc functionInstance.id) ∧
    ∃ value, result = .ok value ∧ readOffsetOccurrenceResult functionInstance.id value after

/-- The final `or` operands are live partial accumulators, not newly reconstructed source inputs. -/
def readOffsetFinalPieces (functionInstance : FunctionInstance) (args : ReadOffsetInlineArgs)
    (state : State) : Prop :=
  ∃ value left right, readOffsetSourceMeaning args = .ok value ∧
    state.regs.get? x20 = some (BitVec.ofNat 64 args.inputBase) ∧
    args.offset = readOffsetOccurrenceOffset functionInstance.id ∧
    left ||| right = BitVec.ofNat 64 value ∧
    if functionInstance.id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23Id then
      state.regs.get? x10 = some left ∧ state.regs.get? x12 = some right
    else if functionInstance.id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23Id then
      state.regs.get? x14 = some left ∧ state.regs.get? x15 = some right
    else if functionInstance.id = functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23Id then
      state.regs.get? x11 = some left ∧ state.regs.get? x13 = some right
    else state.regs.get? x16 = some left ∧ state.regs.get? x17 = some right

def readOffsetInlineInterface (functionInstance : FunctionInstance) :
    Level4FunctionInstanceInterface ReadOffsetInlineArgs (Except Contracts.DecodeError Nat) where
  functionInstance := functionInstance
  spec := { meaning := readOffsetSourceMeaning }
  entry := readOffsetInlineEntry functionInstance
  exit := readOffsetContinuationExit functionInstance
  executionPcs := functionInstanceExecutionPcs generatedProgram functionInstance
  terminal := fun _ pc => pc = readOffsetOccurrenceResultPc functionInstance.id
  stepBound := fun _ => 65

/-- One generated reader fragment. Its end PC is the immediate successor after the edge source;
the caller owns the intervening sibling fragments. -/
def ReadOffsetFragmentContract (functionInstance : FunctionInstance) (start source successor : Nat) : Prop :=
  ∀ (args : ReadOffsetInlineArgs) (fromStep : Nat) (before : State),
    before.regs.get? PC = some (BitVec.ofNat 64 start) ∧
      canonicalContractParams.env.CodeIntact before ∧ MemoryBytes before args.inputBase args.bytes ∧
      before.regs.get? x20 = some (BitVec.ofNat 64 args.inputBase) ∧
      args.offset = readOffsetOccurrenceOffset functionInstance.id ∧
      readOffsetFragmentInput start args before →
    ∃ used after, used ≤ 65 ∧
      EnteredFunctionTrace
        (fun pc => start ≤ pc.toNat ∧ pc.toNat ≤ source ∧ pc.toNat % 4 = 0)
        (fun pc => pc = BitVec.ofNat 64 successor) (BitVec.ofNat 64 start) fromStep used before after ∧
      canonicalContractParams.env.CodeIntact after ∧ MemoryBytes after args.inputBase args.bytes ∧
      after.regs.get? x20 = some (BitVec.ofNat 64 args.inputBase) ∧
      args.offset = readOffsetOccurrenceOffset functionInstance.id ∧
      readOffsetFragmentOutput start args after

/-- The four selected reader fields each bundle exactly their own generated fragments.  The final
fragment carries the observable accumulator register; no field owns its siblings' instructions. -/
structure ReadOffsetOccurrenceContract (interface :
    Level4FunctionInstanceInterface ReadOffsetInlineArgs (Except Contracts.DecodeError Nat))
    (fragments : List (Nat × Nat × Nat)) : Prop where
  covers : ∀ edge ∈ fragments, let (start, source, successor) := edge
    ReadOffsetFragmentContract interface.functionInstance start source successor
  finalEdge : ∀ args fromStep before,
    before.regs.get? PC = some (readOffsetOccurrenceResultPc interface.functionInstance.id - 4) ∧
      canonicalContractParams.env.CodeIntact before ∧ MemoryBytes before args.inputBase args.bytes ∧
      readOffsetFinalPieces interface.functionInstance args before →
    ∃ used after, used ≤ 65 ∧
      EnteredFunctionTrace
        (fun pc => pc = readOffsetOccurrenceResultPc interface.functionInstance.id - 4)
        (fun pc => pc = readOffsetOccurrenceResultPc interface.functionInstance.id)
        (readOffsetOccurrenceResultPc interface.functionInstance.id - 4) fromStep used before after ∧
      interface.exit args (interface.spec.meaning args) before after

/-- `requireU32Length` starts at `0x10484`; its only data input is the already-live `a3` length.
The parent establishes the source input snapshot and the `< 2^32` gate. -/
structure RequireU32LengthInlineArgs where
  inputBase : Nat
  bytes : ByteArray

def requireU32LengthSourceMeaning (args : RequireU32LengthInlineArgs) :
    Except Contracts.DecodeError Unit :=
  meaningRequireU32Length args.bytes

/-- The generated fragment ends at `0x1048c`; this Level 4 continuation includes the two tests and
stops before the parent-owned success-path setup at `0x1049c`. -/
def requireU32LengthContinuationPc : BitVec 64 := BitVec.ofNat 64 0x10490

def requireU32LengthInlineInterface :
    Level4FunctionInstanceInterface RequireU32LengthInlineArgs
      (Except Contracts.DecodeError Unit) where
  functionInstance := functionInstance_ssz_raw_requireU32Length_in_ssz_raw_decodeRaw_at_191_25
  spec := { meaning := requireU32LengthSourceMeaning }
  entry := fun args state =>
    state.regs.get? PC = some (functionInstanceEntryWord
      functionInstance_ssz_raw_requireU32Length_in_ssz_raw_decodeRaw_at_191_25) ∧
      MemoryBytes state args.inputBase args.bytes ∧
      canonicalContractParams.env.CodeIntact state ∧
      state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size) ∧
      args.bytes.size < 2 ^ 32 ∧ inputWindowFits64 args.inputBase args.bytes.size
  exit := fun args result _ after =>
    result = requireU32LengthSourceMeaning args ∧
      after.regs.get? PC = some requireU32LengthContinuationPc
  executionPcs := fun pc => BitVec.ofNat 64 0x10484 ≤ pc ∧ pc ≤ BitVec.ofNat 64 0x1048c
  terminal := fun _ pc => pc = requireU32LengthContinuationPc
  stepBound := fun _ => 32

/-- The source container arguments plus the two stack words that form a sliced `body` value in
the optimized `decodeRaw` frame.  These are machine carriers, not a source ABI assertion. -/
structure StackSliceContainerArgs where
  container : ContainerArgs
  stackPointer : Nat
  parentBase : Nat
  sliceOffset : Nat

structure StackSliceCollectionArgs where
  container : CollectionArgs
  stackPointer : Nat
  parentBase : Nat
  sliceOffset : Nat

def stackWord (state : State) (base offset value : Nat) : Prop :=
  BitVectorLERep state (base + offset) (BitVec.ofNat 64 value)

def stackSliceContainerEntry (functionInstance : FunctionInstance)
    (baseOffset offsetOffset resultOffset resultSize : Nat)
    (args : StackSliceContainerArgs) (state : State) : Prop :=
  state.regs.get? PC = some (functionInstanceEntryWord functionInstance) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    stackWord state args.stackPointer baseOffset args.parentBase ∧
    stackWord state args.stackPointer offsetOffset args.sliceOffset ∧
    args.container.base = args.parentBase + args.sliceOffset ∧
    args.container.resultBase = args.stackPointer + resultOffset ∧
    MemoryBytes state args.container.base args.container.bytes ∧
    args.stackPointer < 2 ^ 64 ∧ args.parentBase < 2 ^ 64 ∧ args.sliceOffset < 2 ^ 64 ∧
    args.container.base < 2 ^ 64 ∧
    args.container.base + args.container.bytes.size ≤ 2 ^ 64 ∧
    args.stackPointer + resultOffset + resultSize ≤ 2 ^ 64

def stackSliceCollectionEntry (functionInstance : FunctionInstance)
    (baseOffset offsetOffset resultOffset resultSize : Nat)
    (args : StackSliceCollectionArgs) (state : State) : Prop :=
  state.regs.get? PC = some (functionInstanceEntryWord functionInstance) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    stackWord state args.stackPointer baseOffset args.parentBase ∧
    stackWord state args.stackPointer offsetOffset args.sliceOffset ∧
    args.container.base = args.parentBase + args.sliceOffset ∧
    args.container.resultBase = args.stackPointer + resultOffset ∧
    MemoryBytes state args.container.base args.container.bytes ∧
    args.stackPointer < 2 ^ 64 ∧ args.parentBase < 2 ^ 64 ∧ args.sliceOffset < 2 ^ 64 ∧
    args.container.base < 2 ^ 64 ∧
    args.container.base + args.container.bytes.size ≤ 2 ^ 64 ∧
    args.stackPointer + resultOffset + resultSize ≤ 2 ^ 64

def specializedDecoderTerminal (successPc : Nat) (pc : BitVec 64) : Prop :=
  pc = BitVec.ofNat 64 successPc ∨ pc = BitVec.ofNat 64 0x11ba4

def specializedDecoderExit {Result Args : Type} (successPc : Nat)
    (post : Args → Except Contracts.DecodeError Result → State → State → Prop)
    (args : Args) (result : Except Contracts.DecodeError Result) (before after : State) : Prop :=
  post args result before after ∧
    match result with
    | .ok _ => after.regs.get? PC = some (BitVec.ofNat 64 successPc)
    | .error _ => after.regs.get? PC = some (BitVec.ofNat 64 0x11ba4)

/-- `decodePublicKeys` stops before `decodeRaw` stores its slice descriptor at `sp+0x600`.
The child publishes only its live `(base,count)` carrier in `s6`/`s1`; the parent-owned stores
are what later establish `postCollection`. -/
def publicKeysChildExit (args : StackSliceCollectionArgs)
    (result : Except Contracts.DecodeError
      (Array (BinaryFv.Specs.SSZ.RawByteVector BinaryFv.Specs.SSZ.publicKeyBytes)))
    (_before after : State) : Prop :=
  canonicalContractParams.env.CodeIntact after ∧
  MemoryBytes after args.container.base args.container.bytes ∧
  canonicalContractParams.env.WritesOnlyWithinOwnAllocation args.container.resultBase
    canonicalContractParams.env.record.sliceDescriptor _before after ∧
  match result with
  | .ok values => ∃ base, after.regs.get? x22 = some (BitVec.ofNat 64 base) ∧
      after.regs.get? x9 = some (BitVec.ofNat 64 values.size) ∧
      HeapArrayRep after base values.size BinaryFv.Specs.SSZ.publicKeyBytes ∧ base < 2 ^ 64
  | .error _ => True

/-- `decodeNewPayloadRequest` starts with the body base in `s4`, its two offset-table values in
`s7`/`s9`, and DWARF's only paramless-entry local: `result = x2 + 2320`. -/
def decodeNewPayloadRequestEntry (args : ContainerArgs) (state : State) : Prop :=
  ∃ stackPointer inputBase startOffset endOffset,
    state.regs.get? PC = some (functionInstanceEntryWord
      functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer) ∧
    state.regs.get? x20 = some (BitVec.ofNat 64 inputBase) ∧
    state.regs.get? x23 = some (BitVec.ofNat 64 startOffset) ∧
    state.regs.get? x25 = some (BitVec.ofNat 64 endOffset) ∧
    args.base = inputBase + 2 + startOffset ∧
    args.bytes.size + startOffset = endOffset ∧
    args.resultBase = stackPointer + 2320 ∧
    MemoryBytes state args.base args.bytes ∧
    stackPointer < 2 ^ 64 ∧ inputBase < 2 ^ 64 ∧ startOffset < 2 ^ 64 ∧ endOffset < 2 ^ 64 ∧
    args.base < 2 ^ 64 ∧
    args.base + args.bytes.size ≤ 2 ^ 64 ∧
    stackPointer + 2320 + canonicalContractParams.env.record.newPayloadRequest ≤ 2 ^ 64

noncomputable def decodeNewPayloadRequestInterface :
    Level4DynamicFunctionInterface ContainerArgs
      (Except Contracts.DecodeError BinaryFv.Specs.SSZ.RawNewPayloadRequest) where
  functionInstance := functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61
  boundary := functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61_attributionBoundary
  carrierRoutes := functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61_attributionBoundary_carrierRoutes
  spec := (contractNewPayloadRequest canonicalContractParams.env
    canonicalContractParams.repNewPayloadRequest).toSourceFunctionSpec
  entry := decodeNewPayloadRequestEntry
  reached := functionInstanceExecutionPcs generatedProgram
    functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61
  terminal := specializedDecoderTerminal 0x1201c
  exit := specializedDecoderExit 0x1201c (fun args result before after =>
    postAllocatingContainer canonicalContractParams.env args
      canonicalContractParams.repNewPayloadRequest canonicalContractParams.env.record.newPayloadRequest
      result before after)
  stepBound := fun args => 8192 + 256 * args.bytes.size

/-- At `decodeExecutionWitness` entry `a1` names the materialized slice descriptor; the first two
instructions load its base/length and immediately store them at `s0 + 0x1dc`, the result carrier. -/
def decodeExecutionWitnessEntry (args : ContainerArgs) (state : State) : Prop :=
  ∃ stackPointer descriptorBase resultCarrier,
    state.regs.get? PC = some (functionInstanceEntryWord
      functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 stackPointer) ∧
    state.regs.get? x11 = some (BitVec.ofNat 64 descriptorBase) ∧
    state.regs.get? x8 = some (BitVec.ofNat 64 resultCarrier) ∧
    stackWord state descriptorBase 0 args.base ∧
    stackWord state descriptorBase 8 args.bytes.size ∧
    args.resultBase = resultCarrier + 0x1dc ∧
    MemoryBytes state args.base args.bytes ∧
    stackPointer < 2 ^ 64 ∧ descriptorBase < 2 ^ 64 ∧ resultCarrier < 2 ^ 64 ∧
    args.base < 2 ^ 64 ∧ descriptorBase + 16 ≤ 2 ^ 64 ∧ args.base + args.bytes.size ≤ 2 ^ 64 ∧
    resultCarrier + 0x1dc + canonicalContractParams.env.record.executionWitness ≤ 2 ^ 64

noncomputable def decodeExecutionWitnessInterface :
    Level4DynamicFunctionInterface ContainerArgs
      (Except Contracts.DecodeError BinaryFv.Specs.SSZ.RawExecutionWitness) where
  functionInstance := functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48
  boundary := functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary
  carrierRoutes := functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48_attributionBoundary_carrierRoutes
  spec := (contractExecutionWitness canonicalContractParams.env
    canonicalContractParams.repExecutionWitness).toSourceFunctionSpec
  entry := decodeExecutionWitnessEntry
  reached := functionInstanceExecutionPcs generatedProgram
    functionInstance_ssz_raw_decodeExecutionWitness_in_ssz_raw_decodeRaw_at_209_48
  terminal := specializedDecoderTerminal 0x12738
  exit := specializedDecoderExit 0x12738 (fun args result before after =>
    postAllocatingContainer canonicalContractParams.env args
      canonicalContractParams.repExecutionWitness canonicalContractParams.env.record.executionWitness
      result before after)
  stepBound := fun args => 1024 + 256 * args.bytes.size

/-- The chain-config slice is still represented by the parent frame at `x2+0x238`/`x2+0x250`;
`s5` already holds its length.  Its completed fixed record starts at `x2+0x5b0`. -/
noncomputable def decodeChainConfigInterface :
    Level4DynamicFunctionInterface StackSliceContainerArgs
      (Except Contracts.DecodeError BinaryFv.Specs.SSZ.RawChainConfig) where
  functionInstance := functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
  boundary := functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48_attributionBoundary
  carrierRoutes := functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48_attributionBoundary_carrierRoutes
  spec := { meaning := fun args =>
    (contractChainConfig canonicalContractParams.env
      canonicalContractParams.repChainConfig).meaning args.container }
  entry := fun args state =>
    stackSliceContainerEntry
      functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
      0x238 0x250 0x5b0 canonicalContractParams.env.record.chainConfig args state ∧
      state.regs.get? x21 = some (BitVec.ofNat 64 args.container.bytes.size)
  reached := functionInstanceExecutionPcs generatedProgram
    functionInstance_ssz_raw_decodeChainConfig_in_ssz_raw_decodeRaw_at_211_48
  terminal := specializedDecoderTerminal 0x12e64
  exit := specializedDecoderExit 0x12e64 (fun args result before after =>
    postFixedContainer canonicalContractParams.env args.container
      canonicalContractParams.repChainConfig canonicalContractParams.env.record.chainConfig
      result before after)
  stepBound := fun _ => 2048

/-- `decodePublicKeys` takes the final body slice from `x2+0x238`/`x2+0x240`; `s2` is its byte
length and the slice descriptor result is written at `x2+0x600`. -/
noncomputable def decodePublicKeysInterface :
    Level4DynamicFunctionInterface StackSliceCollectionArgs
      (Except Contracts.DecodeError
        (Array (BinaryFv.Specs.SSZ.RawByteVector BinaryFv.Specs.SSZ.publicKeyBytes))) where
  functionInstance := functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46
  boundary := functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46_attributionBoundary
  carrierRoutes := functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46_attributionBoundary_carrierRoutes
  spec := { meaning := fun args =>
    (contractPublicKeys canonicalContractParams.env).meaning args.container }
  entry := fun args state =>
    stackSliceCollectionEntry
      functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46
      0x238 0x240 0x600 canonicalContractParams.env.record.sliceDescriptor args state ∧
      state.regs.get? x18 = some (BitVec.ofNat 64 args.container.bytes.size)
  reached := functionInstanceExecutionPcs generatedProgram
    functionInstance_ssz_raw_decodePublicKeys_in_ssz_raw_decodeRaw_at_212_46
  /- The child owns the branch at `0x12f8c`; `0x12f90` and the following result stores belong
     to `decodeRaw` and are intentionally not executed by this interface. -/
  terminal := specializedDecoderTerminal 0x12f90
  exit := specializedDecoderExit 0x12f90 publicKeysChildExit
  stepBound := fun args => 128 + 128 *
    (args.container.bytes.size / BinaryFv.Specs.SSZ.publicKeyBytes + 1)

/-- Concrete caller-visible carriers for cleanup regions.  The parent retains the records only on
success paths; cleanup consumes their slice descriptors through the actual `a0`/`a1` entries. -/
structure DeinitInlineArgs where
  recordBase : Nat
  allocatorBase : Nat
  stackPointer : Nat
  frameSize : Nat

structure AllocatorFreeInlineArgs where
  allocatorBase : Nat
  bufferBase : Nat
  elementCount : Nat

structure AllocBytesWithAlignmentInlineArgs where
  resultBase : Nat
  allocatorBase : Nat
  byteCount : Nat
  /-- The production adapter materializes `li a2, 0` before its vtable call: byte alignment. -/
  alignmentLog2 : Nat
  stackPointer : Nat

/-- The two deinit regions invoke only allocator-free paths. They preserve code and allocator
state and may write their concrete stack frame, but no caller record or input byte. -/
def deinitExit (_args : DeinitInlineArgs) (before after : State) : Prop :=
  canonicalContractParams.env.CodeIntact after ∧
    canonicalContractParams.env.NoAllocation before after ∧
    canonicalContractParams.env.WritesOnlyWithinOwnRecord 0 0 before after

def rawExecutionWitnessDeinitInterface : Level4InlineRegionInterface DeinitInlineArgs where
  region := excludedFunctionInstance_ssz_raw_RawExecutionWitness_deinit
  entry := fun args state => state.regs.get? PC = some (BitVec.ofNat 64 0x13038) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x10 = some (BitVec.ofNat 64 args.recordBase) ∧
    state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    args.recordBase < 2 ^ 64 ∧ args.allocatorBase < 2 ^ 64 ∧ args.stackPointer < 2 ^ 64 ∧
    args.stackPointer + args.frameSize ≤ 2 ^ 64
  exit := deinitExit
  stepBound := fun _ => 1024

/-- `Allocator.free__anon_1214` either returns on a zero length or tail-enters the selected
`raw_decoder_root.allocatorFree` instance.  Both paths preserve allocator state and the caller's
non-stack memory. -/
def allocatorFreeAnonInterface : Level4InlineRegionInterface AllocatorFreeInlineArgs where
  region := excludedFunctionInstance_mem_Allocator_free_anon_1214
  entry := fun args state => state.regs.get? PC = some (BitVec.ofNat 64 0x130ac) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x10 = some (BitVec.ofNat 64 args.allocatorBase) ∧
    state.regs.get? x11 = some (BitVec.ofNat 64 args.bufferBase) ∧
    state.regs.get? x12 = some (BitVec.ofNat 64 args.elementCount) ∧
    args.allocatorBase < 2 ^ 64 ∧ args.bufferBase < 2 ^ 64 ∧
    args.bufferBase + 16 * args.elementCount ≤ 2 ^ 64
  exit := fun _ before after =>
    canonicalContractParams.env.CodeIntact after ∧
      canonicalContractParams.env.NoAllocation before after ∧
      canonicalContractParams.env.WritesOnlyWithinOwnRecord 0 0 before after
  stepBound := fun _ => 64

/-- The allocation adapter writes its 16-byte error-union record at `a0` and may advance the bump
cursor; its ownership frame therefore includes the published record, allocated arena interval,
allocator state, and stack. -/
def zeroU16At (state : State) (base : Nat) : Prop :=
  state.mem.get? base = some (BitVec.ofNat 8 0) ∧
    state.mem.get? (base + 1) = some (BitVec.ofNat 8 0)

def allocBytesWithAlignmentExit (args : AllocBytesWithAlignmentInlineArgs)
    (before after : State) : Prop :=
  before.regs.get? x10 = some (BitVec.ofNat 64 args.resultBase) ∧
    before.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
    before.regs.get? x12 = some (BitVec.ofNat 64 args.byteCount) ∧
    canonicalContractParams.env.CodeIntact after ∧
    canonicalContractParams.env.WritesOnlyWithinOwnAllocation args.resultBase
      canonicalContractParams.env.record.sliceDescriptor before after ∧
    ((args.byteCount = 0 ∧ BitVectorLERep after args.resultBase (BitVec.ofNat 64 (2 ^ 64 - 1)) ∧
        zeroU16At after (args.resultBase + 8)) ∨
      (zeroU16At after (args.resultBase + 8) ∧
        ∃ address, BitVectorLERep after args.resultBase (BitVec.ofNat 64 address) ∧
          address ≠ 0) ∨
      (BitVectorLERep after args.resultBase (BitVec.ofNat 64 0) ∧
        after.mem.get? (args.resultBase + 8) = some (BitVec.ofNat 8 1))) ∧
    ∃ cursorBefore cursorAfter,
      canonicalContractParams.env.cursor? before = some cursorBefore ∧
      canonicalContractParams.env.cursor? after = some cursorAfter ∧
      ((args.byteCount = 0 ∧ cursorAfter = cursorBefore) ∨
       (zeroU16At after (args.resultBase + 8) ∧
          ∃ address, BitVectorLERep after args.resultBase (BitVec.ofNat 64 address) ∧
            cursorBefore ≤ address ∧ address + args.byteCount ≤ cursorAfter) ∨
        (BitVectorLERep after args.resultBase (BitVec.ofNat 64 0) ∧ cursorAfter = cursorBefore))

def allocBytesWithAlignmentAnonInterface :
    Level4InlineRegionInterface AllocBytesWithAlignmentInlineArgs where
  region := excludedFunctionInstance_mem_Allocator_allocBytesWithAlignment_anon_1331
  entry := fun args state => state.regs.get? PC = some (BitVec.ofNat 64 0x130d0) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x10 = some (BitVec.ofNat 64 args.resultBase) ∧
    state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
    state.regs.get? x12 = some (BitVec.ofNat 64 args.byteCount) ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    args.alignmentLog2 = 0 ∧ args.resultBase < 2 ^ 64 ∧ args.allocatorBase < 2 ^ 64 ∧
    args.byteCount < 2 ^ 64 ∧ args.stackPointer < 2 ^ 64 ∧ args.resultBase + 16 ≤ 2 ^ 64 ∧
    args.stackPointer + 16 ≤ 2 ^ 64
  exit := allocBytesWithAlignmentExit
  stepBound := fun _ => 1024

def rawNewPayloadRequestDeinitInterface : Level4InlineRegionInterface DeinitInlineArgs where
  region := excludedFunctionInstance_ssz_raw_RawNewPayloadRequest_deinit
  entry := fun args state => state.regs.get? PC = some (BitVec.ofNat 64 0x131ec) ∧
    canonicalContractParams.env.CodeIntact state ∧
    state.regs.get? x10 = some (BitVec.ofNat 64 args.recordBase) ∧
    state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
    state.regs.get? x2 = some (BitVec.ofNat 64 args.stackPointer) ∧
    args.recordBase < 2 ^ 64 ∧ args.allocatorBase < 2 ^ 64 ∧ args.stackPointer < 2 ^ 64 ∧
    args.stackPointer + args.frameSize ≤ 2 ^ 64
  exit := deinitExit
  stepBound := fun _ => 1024

/-! ## Eighteen selected contracts -/

def allocatorFreeInterface : Level4FunctionInstanceInterface Unit
    (Except Contracts.DecodeError Unit) where
  functionInstance := functionInstance_raw_decoder_root_allocatorFree
  spec := (contractAllocatorFree canonicalContractParams.env).toSourceFunctionSpec
  entry := fun args state => (contractAllocatorFree canonicalContractParams.env).pre args state ∧
    state.regs.get? PC = some (BitVec.ofNat 64 0x10440) ∧
    state.regs.getD x1 0 ≠ BitVec.ofNat 64 0x10440
  exit := (contractAllocatorFree canonicalContractParams.env).post
  /- `allocatorFree` is the one-instruction `ret` leaf: its terminal is the incoming link, not
     its generated entry/exit marker (both are 0x10440). -/
  executionPcs := fun pc => pc = BitVec.ofNat 64 0x10440
  terminal := fun before pc => pc = before.regs.getD x1 0
  stepBound := (contractAllocatorFree canonicalContractParams.env).stepBound

def readOffset199Interface :=
  readOffsetInlineInterface functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_199_23
def readOffset200Interface :=
  readOffsetInlineInterface functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_200_23
def readOffset201Interface :=
  readOffsetInlineInterface functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_201_23
def readOffset202Interface :=
  readOffsetInlineInterface functionInstance_ssz_raw_readOffset_in_ssz_raw_decodeRaw_at_202_23

def readOffset199Fragments : List (Nat × Nat × Nat) :=
  [(0x10534, 0x10540, 0x10544), (0x10554, 0x10564, 0x10568)]
def readOffset200Fragments : List (Nat × Nat × Nat) :=
  [(0x10544, 0x10550, 0x10554), (0x10578, 0x10580, 0x10584),
   (0x10590, 0x10594, 0x10598)]
def readOffset201Fragments : List (Nat × Nat × Nat) :=
  [(0x10568, 0x10574, 0x10578), (0x10584, 0x1058c, 0x10590),
   (0x10598, 0x1059c, 0x105a0)]
def readOffset202Fragments : List (Nat × Nat × Nat) :=
  [(0x105a0, 0x105c0, 0x105c4)]

def decodeByteListListInterface : Level4FunctionInstanceInterface ByteListListArgs
    (Except Contracts.DecodeError (Array BinaryFv.Specs.SSZ.RawBytes)) where
  functionInstance := functionInstance_ssz_raw_decodeByteListList
  spec := (contractByteListList canonicalContractParams.env).toSourceFunctionSpec
  entry := fun args state => (contractByteListList canonicalContractParams.env).pre args state ∧
    state.regs.get? PC = some (functionInstanceEntryWord functionInstance_ssz_raw_decodeByteListList) ∧
    inputWindowFits64 args.base args.bytes.size ∧ args.resultBase + 16 ≤ 2 ^ 64
  exit := (contractByteListList canonicalContractParams.env).post
  executionPcs := functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_decodeByteListList
  terminal := fun _ => functionInstanceExitPred functionInstance_ssz_raw_decodeByteListList
  stepBound := (contractByteListList canonicalContractParams.env).stepBound

def requireCanonicalOffsetsInterface : Level4FunctionInstanceInterface CanonicalOffsetsArgs
    (Except Contracts.DecodeError Unit) where
  functionInstance := functionInstance_ssz_raw_requireCanonicalOffsets
  spec := (contractRequireCanonicalOffsets canonicalContractParams.env).toSourceFunctionSpec
  entry := fun args state => (contractRequireCanonicalOffsets canonicalContractParams.env).pre args state ∧
    state.regs.get? PC = some (functionInstanceEntryWord functionInstance_ssz_raw_requireCanonicalOffsets) ∧
    inputWindowFits64 args.base args.bytes.size
  exit := (contractRequireCanonicalOffsets canonicalContractParams.env).post
  executionPcs := functionInstanceExecutionPcs generatedProgram functionInstance_ssz_raw_requireCanonicalOffsets
  terminal := fun _ => functionInstanceExitPred functionInstance_ssz_raw_requireCanonicalOffsets
  stepBound := (contractRequireCanonicalOffsets canonicalContractParams.env).stepBound

def allocatorAllocInterface : Level4FunctionInstanceInterface AllocArgs (Except Contracts.DecodeError Nat) where
  functionInstance := functionInstance_raw_decoder_root_allocatorAlloc
  spec := (contractAllocatorAlloc canonicalContractParams.env canonicalContractParams.heap).toSourceFunctionSpec
  entry := fun args state => (contractAllocatorAlloc canonicalContractParams.env canonicalContractParams.heap).pre args state ∧
    state.regs.get? PC = some (functionInstanceEntryWord functionInstance_raw_decoder_root_allocatorAlloc) ∧
    args.allocatorBase < 2 ^ 64 ∧ args.bytes < 2 ^ 64 ∧ args.alignment < 2 ^ 64
  /- `functionInstanceExecutionPcs` includes the reached tail callee extent, so this selected
     boundary executes the `jr` at `0x1377c` and returns with the allocator's source result. -/
  exit := (contractAllocatorAlloc canonicalContractParams.env canonicalContractParams.heap).post
  executionPcs := RegionPcs allocatorAllocTailExecutionRegions
  terminal := fun _ pc => pc = BitVec.ofNat 64 66208
  stepBound := (contractAllocatorAlloc canonicalContractParams.env canonicalContractParams.heap).stepBound

def memmoveInterface : Level4FunctionInstanceInterface CopyArgs (Except Contracts.DecodeError ByteArray) where
  functionInstance := functionInstance_memmove
  spec := (contractMemmove canonicalContractParams.env).toSourceFunctionSpec
  entry := fun args state => (contractMemmove canonicalContractParams.env).pre args state ∧
    state.regs.get? PC = some (functionInstanceEntryWord functionInstance_memmove) ∧
    inputWindowFits64 args.source args.length ∧ inputWindowFits64 args.destination args.length
  exit := (contractMemmove canonicalContractParams.env).post
  executionPcs := functionInstanceExecutionPcs generatedProgram functionInstance_memmove
  terminal := fun _ => functionInstanceExitPred functionInstance_memmove
  stepBound := (contractMemmove canonicalContractParams.env).stepBound

/-- The fourteen generated contracts in the selected bundle, kept as identities so a future proof
cannot replace an inline occurrence with a source-family look-up. -/
noncomputable def level4FunctionInstanceContractIds : List FunctionInstanceId :=
  [ allocatorFreeInterface.functionInstance.id
  , requireU32LengthInlineInterface.functionInstance.id
  , decodeNewPayloadRequestInterface.functionInstance.id
  , decodeExecutionWitnessInterface.functionInstance.id
  , decodeChainConfigInterface.functionInstance.id, decodePublicKeysInterface.functionInstance.id
  , decodeByteListListInterface.functionInstance.id
  , requireCanonicalOffsetsInterface.functionInstance.id
  , allocatorAllocInterface.functionInstance.id
  , memmoveInterface.functionInstance.id
  , readOffset199Interface.functionInstance.id, readOffset200Interface.functionInstance.id
  , readOffset201Interface.functionInstance.id, readOffset202Interface.functionInstance.id
  ]

/-- The four separate non-`FunctionInstance` contracts in the selected bundle. -/
noncomputable def level4InlineRegionContractIds : List FunctionInstanceId :=
  [ rawExecutionWitnessDeinitInterface.region.id, allocatorFreeAnonInterface.region.id
  , allocBytesWithAlignmentAnonInterface.region.id, rawNewPayloadRequestDeinitInterface.region.id
  ]

theorem level4FunctionInstanceContractIds_match_inventory :
    level4FunctionInstanceContractIds = level4DisplayedFunctionInstances.map (·.id) := rfl

theorem level4InlineRegionContractIds_match_inventory :
    level4InlineRegionContractIds = level4DisplayedExcludedInstances.map (·.id) := rfl

abbrev AllocatorFreeContract : Prop := allocatorFreeInterface.BoundedImplements
abbrev RequireU32LengthContract : Prop := requireU32LengthInlineInterface.BoundedImplements
abbrev ReadOffset199Contract : Prop := ReadOffsetOccurrenceContract readOffset199Interface readOffset199Fragments
abbrev ReadOffset200Contract : Prop := ReadOffsetOccurrenceContract readOffset200Interface readOffset200Fragments
abbrev ReadOffset201Contract : Prop := ReadOffsetOccurrenceContract readOffset201Interface readOffset201Fragments
abbrev ReadOffset202Contract : Prop := ReadOffsetOccurrenceContract readOffset202Interface readOffset202Fragments
abbrev DecodeNewPayloadRequestContract : Prop :=
  decodeNewPayloadRequestInterface.ResumableSubtree
abbrev DecodeExecutionWitnessContract : Prop :=
  decodeExecutionWitnessInterface.ResumableSubtree
abbrev DecodeChainConfigContract : Prop :=
  decodeChainConfigInterface.ResumableSubtree
abbrev DecodePublicKeysContract : Prop :=
  decodePublicKeysInterface.ResumableSubtree
abbrev DecodeByteListListContract : Prop := decodeByteListListInterface.BoundedImplements
abbrev RequireCanonicalOffsetsContract : Prop :=
  requireCanonicalOffsetsInterface.BoundedImplements
abbrev AllocatorAllocContract : Prop := allocatorAllocInterface.BoundedImplements
abbrev MemmoveContract : Prop := memmoveInterface.BoundedImplements
abbrev RawExecutionWitnessDeinitContract : Prop :=
  rawExecutionWitnessDeinitInterface.BoundedImplements
abbrev AllocatorFreeAnonContract : Prop := allocatorFreeAnonInterface.BoundedImplements
abbrev AllocBytesWithAlignmentAnonContract : Prop :=
  allocBytesWithAlignmentAnonInterface.BoundedImplements
abbrev RawNewPayloadRequestDeinitContract : Prop :=
  rawNewPayloadRequestDeinitInterface.BoundedImplements

/-- The only outstanding propositions selected at reviewed UI Level 4.  It includes all fourteen
generated function-instance contracts and all four excluded inline-region contracts; every field
contains its own semantic entered-trace bound, but this bundle adds no parent theorem, semantic
oracle, coverage fact, or ad hoc machine-state premise. -/
structure Level4ContractAssumptions : Prop where
  allocatorFree : AllocatorFreeContract
  requireU32Length : RequireU32LengthContract
  readOffset199 : ReadOffset199Contract
  readOffset200 : ReadOffset200Contract
  readOffset201 : ReadOffset201Contract
  readOffset202 : ReadOffset202Contract
  decodeNewPayloadRequest : DecodeNewPayloadRequestContract
  decodeExecutionWitness : DecodeExecutionWitnessContract
  decodeChainConfig : DecodeChainConfigContract
  decodePublicKeys : DecodePublicKeysContract
  rawExecutionWitnessDeinit : RawExecutionWitnessDeinitContract
  allocatorFreeAnon : AllocatorFreeAnonContract
  allocBytesWithAlignmentAnon : AllocBytesWithAlignmentAnonContract
  rawNewPayloadRequestDeinit : RawNewPayloadRequestDeinitContract
  decodeByteListList : DecodeByteListListContract
  requireCanonicalOffsets : RequireCanonicalOffsetsContract
  allocatorAlloc : AllocatorAllocContract
  memmove : MemmoveContract

/-- The complete selected-child bundle for the eventual Level 4-to-3 edge.  `memcpy` is already
proved at Level 3 and is filled here rather than becoming a Level 4 assumption. -/
structure Level4SelectedContracts : Prop where
  allocatorFree : AllocatorFreeContract
  requireU32Length : RequireU32LengthContract
  readOffset199 : ReadOffset199Contract
  readOffset200 : ReadOffset200Contract
  readOffset201 : ReadOffset201Contract
  readOffset202 : ReadOffset202Contract
  decodeNewPayloadRequest : DecodeNewPayloadRequestContract
  decodeExecutionWitness : DecodeExecutionWitnessContract
  decodeChainConfig : DecodeChainConfigContract
  decodePublicKeys : DecodePublicKeysContract
  rawExecutionWitnessDeinit : RawExecutionWitnessDeinitContract
  allocatorFreeAnon : AllocatorFreeAnonContract
  allocBytesWithAlignmentAnon : AllocBytesWithAlignmentAnonContract
  rawNewPayloadRequestDeinit : RawNewPayloadRequestDeinitContract
  decodeByteListList : DecodeByteListListContract
  requireCanonicalOffsets : RequireCanonicalOffsetsContract
  allocatorAlloc : AllocatorAllocContract
  memmove : MemmoveContract
  memcpy : MachineExecution.CompiledMemcpyInstanceContract

def selectedContracts_of_level4 (hLevel4 : Level4ContractAssumptions) :
    Level4SelectedContracts where
  allocatorFree := hLevel4.allocatorFree
  requireU32Length := hLevel4.requireU32Length
  readOffset199 := hLevel4.readOffset199
  readOffset200 := hLevel4.readOffset200
  readOffset201 := hLevel4.readOffset201
  readOffset202 := hLevel4.readOffset202
  decodeNewPayloadRequest := hLevel4.decodeNewPayloadRequest
  decodeExecutionWitness := hLevel4.decodeExecutionWitness
  decodeChainConfig := hLevel4.decodeChainConfig
  decodePublicKeys := hLevel4.decodePublicKeys
  rawExecutionWitnessDeinit := hLevel4.rawExecutionWitnessDeinit
  allocatorFreeAnon := hLevel4.allocatorFreeAnon
  allocBytesWithAlignmentAnon := hLevel4.allocBytesWithAlignmentAnon
  rawNewPayloadRequestDeinit := hLevel4.rawNewPayloadRequestDeinit
  decodeByteListList := hLevel4.decodeByteListList
  requireCanonicalOffsets := hLevel4.requireCanonicalOffsets
  allocatorAlloc := hLevel4.allocatorAlloc
  memmove := hLevel4.memmove
  memcpy := MachineExecution.compiledMemcpyInstanceContract_proved

theorem selectedContracts_of_level4_memcpy (hLevel4 : Level4ContractAssumptions) :
    (selectedContracts_of_level4 hLevel4).memcpy =
      MachineExecution.compiledMemcpyInstanceContract_proved := rfl

/-- Typed child summary produced by an ordinary selected function-instance contract. -/
structure Level4FunctionSummary {Args Outcome : Type}
    (interface : Level4FunctionInstanceInterface Args Outcome) : Prop where
  run : interface.BoundedImplements

def Level4FunctionSummary.of_contract {Args Outcome : Type}
    (interface : Level4FunctionInstanceInterface Args Outcome)
    (contract : interface.BoundedImplements) : Level4FunctionSummary interface :=
  ⟨contract⟩

structure Level4DynamicFunctionSummary {Args Outcome : Type}
    (interface : Level4DynamicFunctionInterface Args Outcome) : Prop where
  run : interface.ResumableSubtree

def Level4DynamicFunctionSummary.of_contract {Args Outcome : Type}
    (interface : Level4DynamicFunctionInterface Args Outcome)
    (contract : interface.ResumableSubtree) : Level4DynamicFunctionSummary interface := ⟨contract⟩

/-- The four direct readers have an owned final instruction, so their child summary stops at the
observable successor rather than a generated pre-result exit. -/
structure ReadOffsetContinuationSummary
    (interface : Level4FunctionInstanceInterface ReadOffsetInlineArgs
      (Except Contracts.DecodeError Nat)) (fragments : List (Nat × Nat × Nat)) : Prop where
  run : ReadOffsetOccurrenceContract interface fragments

def ReadOffsetContinuationSummary.of_contract
    (interface : Level4FunctionInstanceInterface ReadOffsetInlineArgs
      (Except Contracts.DecodeError Nat)) (fragments : List (Nat × Nat × Nat))
    (contract : ReadOffsetOccurrenceContract interface fragments) : ReadOffsetContinuationSummary interface fragments :=
  ⟨contract⟩

structure Level4InlineRegionSummary {Args : Type} (interface : Level4InlineRegionInterface Args) : Prop where
  run : interface.BoundedImplements

def Level4InlineRegionSummary.of_contract {Args : Type}
    (interface : Level4InlineRegionInterface Args)
    (contract : interface.BoundedImplements) : Level4InlineRegionSummary interface :=
  ⟨contract⟩

/-- The typed inputs available to the future `decodeRaw` parent composition. This contains no
parent route theorem: the 172-PC proof must consume these summaries explicitly before it can prove
`CompiledDecodeRawInstanceContract`. -/
structure Level4SelectedSummaries : Prop where
  allocatorFree : Level4FunctionSummary allocatorFreeInterface
  requireU32Length : Level4FunctionSummary requireU32LengthInlineInterface
  readOffset199 : ReadOffsetContinuationSummary readOffset199Interface readOffset199Fragments
  readOffset200 : ReadOffsetContinuationSummary readOffset200Interface readOffset200Fragments
  readOffset201 : ReadOffsetContinuationSummary readOffset201Interface readOffset201Fragments
  readOffset202 : ReadOffsetContinuationSummary readOffset202Interface readOffset202Fragments
  decodeNewPayloadRequest : Level4DynamicFunctionSummary decodeNewPayloadRequestInterface
  decodeExecutionWitness : Level4DynamicFunctionSummary decodeExecutionWitnessInterface
  decodeChainConfig : Level4DynamicFunctionSummary decodeChainConfigInterface
  decodePublicKeys : Level4DynamicFunctionSummary decodePublicKeysInterface
  rawExecutionWitnessDeinit : Level4InlineRegionSummary rawExecutionWitnessDeinitInterface
  allocatorFreeAnon : Level4InlineRegionSummary allocatorFreeAnonInterface
  allocBytesWithAlignmentAnon : Level4InlineRegionSummary allocBytesWithAlignmentAnonInterface
  rawNewPayloadRequestDeinit : Level4InlineRegionSummary rawNewPayloadRequestDeinitInterface
  decodeByteListList : Level4FunctionSummary decodeByteListListInterface
  requireCanonicalOffsets : Level4FunctionSummary requireCanonicalOffsetsInterface
  allocatorAlloc : Level4FunctionSummary allocatorAllocInterface
  memmove : Level4FunctionSummary memmoveInterface
  memcpy : MachineExecution.CompiledMemcpyInstanceContract

/-- Turns every selected assumption into its typed child summary. This is deliberately not the
future theorem `compiledDecodeRawContract_of_level4`, whose result must be the actual parent
`CompiledDecodeRawInstanceContract`. -/
def selectedSummaries_of_level4 (hLevel4 : Level4ContractAssumptions) :
    Level4SelectedSummaries where
  allocatorFree := .of_contract allocatorFreeInterface hLevel4.allocatorFree
  requireU32Length := .of_contract requireU32LengthInlineInterface hLevel4.requireU32Length
  readOffset199 := .of_contract readOffset199Interface readOffset199Fragments hLevel4.readOffset199
  readOffset200 := .of_contract readOffset200Interface readOffset200Fragments hLevel4.readOffset200
  readOffset201 := .of_contract readOffset201Interface readOffset201Fragments hLevel4.readOffset201
  readOffset202 := .of_contract readOffset202Interface readOffset202Fragments hLevel4.readOffset202
  decodeNewPayloadRequest := .of_contract decodeNewPayloadRequestInterface hLevel4.decodeNewPayloadRequest
  decodeExecutionWitness := .of_contract decodeExecutionWitnessInterface hLevel4.decodeExecutionWitness
  decodeChainConfig := .of_contract decodeChainConfigInterface hLevel4.decodeChainConfig
  decodePublicKeys := .of_contract decodePublicKeysInterface hLevel4.decodePublicKeys
  rawExecutionWitnessDeinit := .of_contract rawExecutionWitnessDeinitInterface hLevel4.rawExecutionWitnessDeinit
  allocatorFreeAnon := .of_contract allocatorFreeAnonInterface hLevel4.allocatorFreeAnon
  allocBytesWithAlignmentAnon := .of_contract allocBytesWithAlignmentAnonInterface hLevel4.allocBytesWithAlignmentAnon
  rawNewPayloadRequestDeinit := .of_contract rawNewPayloadRequestDeinitInterface hLevel4.rawNewPayloadRequestDeinit
  decodeByteListList := .of_contract decodeByteListListInterface hLevel4.decodeByteListList
  requireCanonicalOffsets := .of_contract requireCanonicalOffsetsInterface hLevel4.requireCanonicalOffsets
  allocatorAlloc := .of_contract allocatorAllocInterface hLevel4.allocatorAlloc
  memmove := .of_contract memmoveInterface hLevel4.memmove
  memcpy := MachineExecution.compiledMemcpyInstanceContract_proved

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
