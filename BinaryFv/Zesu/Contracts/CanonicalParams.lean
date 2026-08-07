import BinaryFv.Zesu.Contracts.Catalog
import BinaryFv.Zesu.Elflings.GeneratedDecoderGlobals
import BinaryFv.Zesu.MemoryRepresentation.Containers
import BinaryFv.Zesu.Runtime.BumpAllocator

/-!
# The canonical contract parameters

`ContractParams` was previously only ever quantified existentially (`∃ p, sszProgramCorrectness …`).
This module replaces that existential with one concrete value, `canonicalContractParams`, whose
address- and layout-bearing fields are taken from validated pinned artifacts — never handwritten:

- `env.image` is the pinned canonical image `Artifacts.programImage`;
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

namespace BinaryFv.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.Zesu.MemoryRepresentation
open BinaryFv.Zesu.Elflings
  (canonicalDecoderGlobalsLayout canonicalResultBuffer canonicalHeapBase canonicalHeapLimit
   canonicalAllocatorState)

/-! ## The Zig option/aggregate layouts

Every field of these layouts is read straight from the compiler-reflected ABI manifest (`?u64` and
`?RawBlobSchedule` now emit `|size`, `|payload`, and `|tag` — the reflected discriminant offset — not
just the size). The `getD` fallbacks are never taken: `canonicalOptionalU64_pinned` /
`canonicalOptionalBlobSchedule_pinned` prove each field equals the exact manifest value, so a mutated
offset in the manifest (or a wrong key here) fails those `native_decide` checks. -/

open BinaryFv.Zesu.Artifacts in
/-- `?u64`, defined entirely from the manifest: total size, payload offset, and reflected tag offset. -/
def canonicalOptionalU64 : OptionLayout :=
  { size := optionalU64Size.getD 0,
    discriminantOffset := optionalU64TagOffset.getD 0,
    payloadOffset := optionalU64PayloadOffset.getD 0 }

open BinaryFv.Zesu.Artifacts in
/-- `?RawBlobSchedule`, defined entirely from the manifest. -/
def canonicalOptionalBlobSchedule : OptionLayout :=
  { size := optionalBlobScheduleSize.getD 0,
    discriminantOffset := optionalBlobScheduleTagOffset.getD 0,
    payloadOffset := optionalBlobSchedulePayloadOffset.getD 0 }

/-- Per-offset mutation guard: the `?u64` layout is exactly the reflected 16/8/0. -/
theorem canonicalOptionalU64_pinned :
    canonicalOptionalU64 = { size := 16, discriminantOffset := 8, payloadOffset := 0 } := by
  native_decide

/-- Per-offset mutation guard: the `?RawBlobSchedule` layout is exactly the reflected 32/24/0. -/
theorem canonicalOptionalBlobSchedule_pinned :
    canonicalOptionalBlobSchedule = { size := 32, discriminantOffset := 24, payloadOffset := 0 } := by
  native_decide

/-- `RawBlobSchedule`: three consecutive `u64` fields. -/
def canonicalBlobScheduleLayout : BlobScheduleLayout :=
  { targetOffset := 0, maxOffset := 8, baseFeeUpdateFractionOffset := 16 }

/-- The canonical decoder environment: the pinned image, the checked allocator state, and the ABI
option/aggregate layouts. -/
def canonicalEnvironment : DecoderEnvironment :=
  { image := Artifacts.programImage
    allocatorState := canonicalAllocatorState
    optionalBlobSchedule := canonicalOptionalBlobSchedule
    blobSchedule := canonicalBlobScheduleLayout
    optionalU64 := canonicalOptionalU64 }

/-- The canonical bump heap: the validated 64 MiB `heap` region, cursor at its base. -/
def canonicalHeap : BinaryFv.Zesu.Runtime.BumpHeap :=
  { position := canonicalHeapBase, limit := canonicalHeapLimit }

/-! ## Container representations

Every container's representation is the exact native RV64 layout from `MemoryRepresentation.Containers`
(offsets pinned against the ABI manifest by `container_field_offsets_valid` and the `RawV4` audits).
`repRawV4` is the complete `RawV4Rep` — root allocation, all ten heap arrays, the descriptor table,
every borrowed input slice, and all inline fixed fields — not merely the fixed-field fragment. The
input base and bytes carried by `ContainerRepresentation` let the allocating containers and `RawV4`
describe their input-relative borrowed slices. -/

/-- The complete native representation of a decoded `RawV4` rooted at `base`, decoded from the caller's
input at `inputBase`/`input`. -/
def canonicalRepRawV4 : ContainerRepresentation BinaryFv.Specs.SSZ.RawV4 :=
  fun inputBase input value state base => RawV4Rep state inputBase input base value

def canonicalRepForkActivation : ContainerRepresentation BinaryFv.Specs.SSZ.RawForkActivation :=
  fun _ _ value state base => ForkActivationRep state base value

def canonicalRepForkConfig : ContainerRepresentation BinaryFv.Specs.SSZ.RawForkConfig :=
  fun _ _ value state base => ForkConfigRep state base value

def canonicalRepChainConfig : ContainerRepresentation BinaryFv.Specs.SSZ.RawChainConfig :=
  fun _ _ value state base => ChainConfigRep state base value

def canonicalRepExecutionWitness : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionWitness :=
  fun inputBase input value state base => ExecutionWitnessRep state inputBase input base value

def canonicalRepExecutionRequests : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionRequests :=
  fun _ _ value state base => ExecutionRequestsRep state base value

def canonicalRepExecutionPayload : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionPayload :=
  fun inputBase input value state base => ExecutionPayloadRep state inputBase input base value

def canonicalRepNewPayloadRequest : ContainerRepresentation BinaryFv.Specs.SSZ.RawNewPayloadRequest :=
  fun inputBase input value state base => NewPayloadRequestRep state inputBase input base value

/-! ## The canonical parameters -/

/-- The one concrete `ContractParams` the root obligation is stated against. Every address-, layout-,
and representation-bearing field comes from a validated pinned artifact or the exact native layout;
there are no placeholder representations. -/
def canonicalContractParams : ContractParams :=
  { env := canonicalEnvironment
    heap := canonicalHeap
    globals := canonicalDecoderGlobalsLayout
    resultBuffer := canonicalResultBuffer
    repForkActivation := canonicalRepForkActivation
    repForkConfig := canonicalRepForkConfig
    repChainConfig := canonicalRepChainConfig
    repExecutionWitness := canonicalRepExecutionWitness
    repExecutionRequests := canonicalRepExecutionRequests
    repExecutionPayload := canonicalRepExecutionPayload
    repNewPayloadRequest := canonicalRepNewPayloadRequest
    repRawV4 := canonicalRepRawV4 }

end BinaryFv.Zesu.Contracts
