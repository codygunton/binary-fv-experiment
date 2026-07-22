import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals
import BinaryFv.SSZ.Zesu.Runtime.BumpAllocator

/-!
# The canonical contract parameters

`ContractParams` was previously only ever quantified existentially (`∃ p, sszProgramCorrectness …`).
This module replaces that existential with one concrete value, `canonicalContractParams`, whose
address- and layout-bearing fields are taken from validated pinned artifacts — never handwritten:

- `env.image` is the pinned canonical image `Artifact.programImage`;
- `env.allocatorState` is `canonicalAllocatorState` (the `ZKVM_HEAP_POS`/`ZKVM_HEAP_TOP` byte ranges,
  extracted and checked in `Elfling.GeneratedDecoderGlobals`);
- `heap` is the validated 64 MiB `heap` region;
- `globals`/`resultBuffer` are the validated decoder globals.

The Zig `?T` option layouts are the ABI's payload-then-discriminant layout at the pinned sizes
(`AbiManifest`), chosen so `ValidEnvironment` holds.

The container representations are **concrete but partial**: `repRawV4` is the materialized fixed-field
representation `RawV4FixedFieldsRep`; the seven nested-container representations are deliberately
trivial placeholders, to be strengthened to full field/collection layouts in the containers row (H).
Per `ProgramCorrectness`, a weak representation only weakens a contract's success arm — it cannot make
the per-occurrence obligation vacuous, because `ImplementsInstance` still demands an actual entered
trace reaching a generated exit with frame preservation.
-/

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Elfling
  (canonicalDecoderGlobalsLayout canonicalResultBuffer canonicalHeapBase canonicalHeapLimit
   canonicalAllocatorState)

/-! ## The Zig option/aggregate layouts

Payload at offset 0, discriminant after the payload, at the pinned `AbiManifest` sizes. -/

/-- `?u64`: 16 bytes, `u64` payload at 0, discriminant at 8. -/
def canonicalOptionalU64 : OptionLayout :=
  { size := 16, discriminantOffset := 8, payloadOffset := 0 }

/-- `?RawBlobSchedule`: 32 bytes, 24-byte payload at 0, discriminant at 24. -/
def canonicalOptionalBlobSchedule : OptionLayout :=
  { size := 32, discriminantOffset := 24, payloadOffset := 0 }

/-- `RawBlobSchedule`: three consecutive `u64` fields. -/
def canonicalBlobScheduleLayout : BlobScheduleLayout :=
  { targetOffset := 0, maxOffset := 8, baseFeeUpdateFractionOffset := 16 }

/-- The canonical decoder environment: the pinned image, the checked allocator state, and the ABI
option/aggregate layouts. -/
def canonicalEnvironment : DecoderEnvironment :=
  { image := Artifact.programImage
    allocatorState := canonicalAllocatorState
    optionalBlobSchedule := canonicalOptionalBlobSchedule
    blobSchedule := canonicalBlobScheduleLayout
    optionalU64 := canonicalOptionalU64 }

/-- The canonical bump heap: the validated 64 MiB `heap` region, cursor at its base. -/
def canonicalHeap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap :=
  { position := canonicalHeapBase, limit := canonicalHeapLimit }

/-! ## Container representations

`repRawV4` is materialized and input-free; the seven nested reps are concrete placeholders pinned in
the containers row. -/

/-- The materialized fixed-field representation of a decoded `RawV4` at `base`. -/
def canonicalRepRawV4 : ContainerRepresentation SszBridge.RawV4 :=
  fun value state base => RawV4FixedFieldsRep state base value

/-- A concrete placeholder representation, strengthened to the container's full field/collection
layout in the containers row (H). -/
def placeholderRep (α : Type) : ContainerRepresentation α := fun _ _ _ => True

/-! ## The canonical parameters -/

/-- The one concrete `ContractParams` the root obligation is stated against. Every address- and
layout-bearing field comes from a validated pinned artifact; the container representations are
concrete (partial for the nested containers, full for `RawV4`'s fixed fields). -/
def canonicalContractParams : ContractParams :=
  { env := canonicalEnvironment
    heap := canonicalHeap
    globals := canonicalDecoderGlobalsLayout
    resultBuffer := canonicalResultBuffer
    repForkActivation := placeholderRep _
    repForkConfig := placeholderRep _
    repChainConfig := placeholderRep _
    repExecutionWitness := placeholderRep _
    repExecutionRequests := placeholderRep _
    repExecutionPayload := placeholderRep _
    repNewPayloadRequest := placeholderRep _
    repRawV4 := canonicalRepRawV4 }

end BinaryFv.SSZ.Zesu.Contracts
