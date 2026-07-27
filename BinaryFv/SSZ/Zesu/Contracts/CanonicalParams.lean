import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals
import BinaryFv.SSZ.Zesu.MemoryRepresentation.Containers
import BinaryFv.SSZ.Zesu.Runtime.BumpAllocator

/-!
# The concrete binary and ABI used by every contract

`ContractParams` collects the external facts needed to interpret a decoder contract: the loaded
program, allocator addresses, heap range, private globals, Zig layouts, and predicates describing
decoded values in memory. The final proof uses the single value `canonicalContractParams`; it cannot
choose a more convenient environment.

Its fields come from checked artifacts:

- `env.image` is the pinned canonical image `Artifact.programImage`;
- `env.allocatorState` is `canonicalAllocatorState` (the `ZKVM_HEAP_POS`/`ZKVM_HEAP_TOP` byte ranges,
  extracted and checked in `Elfling.GeneratedDecoderGlobals`);
- `heap` is the validated 64 MiB `heap` region;
- `globals`/`resultBuffer` are the validated decoder globals.

The Zig optional layouts come from the ABI manifest produced by the pinned compiler.

The container representations are **concrete and complete**: `repRawV4` is the full input-aware
`RawV4Rep` (allocation, slice descriptors, and borrowed input slices, not just the fixed fields), and
all seven nested-container representations use the concrete layouts in
`MemoryRepresentation.Containers`. Later execution proofs must establish these predicates; they may
not replace them with placeholders. Lean checks every literal field offset against the manifest.
-/

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Elfling
  (canonicalDecoderGlobalsLayout canonicalResultBuffer canonicalHeapBase canonicalHeapLimit
   canonicalAllocatorState)

/-! ## The Zig option/aggregate layouts

Every field of these layouts is read straight from the compiler-reflected ABI manifest (`?u64` and
`?RawBlobSchedule` now emit `|size`, `|payload`, and `|tag`, not just the size). Size and alignment
are genuinely reflected (`@sizeOf`/`@alignOf`); the payload/discriminant offsets are derived from the
pinned compiler's non-niche optional ABI and guarded in `abi_manifest.zig`'s `optionalTagOffset` (see
its comment). The `getD` fallbacks are never taken: `canonicalOptionalU64_pinned` /
`canonicalOptionalBlobSchedule_pinned` prove each field equals the exact manifest value, so a mutated
offset in the manifest (or a wrong key here) fails those `native_decide` checks. -/

open BinaryFv.SSZ.Zesu.Artifact in
/-- `?u64`, defined entirely from the manifest: total size, payload offset, and reflected tag offset. -/
def canonicalOptionalU64 : OptionLayout :=
  { size := optionalU64Size.getD 0,
    discriminantOffset := optionalU64TagOffset.getD 0,
    payloadOffset := optionalU64PayloadOffset.getD 0 }

open BinaryFv.SSZ.Zesu.Artifact in
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

open BinaryFv.SSZ.Zesu.Artifact in
/-- The result-record sizes the ownership clause states its permission over, every one of them read
from the compiler-reflected manifest.

`entryResult` is the internal `decodeRaw`/`decode` result/error union — the `?RawStatelessInput`
object, whose 832-byte payload sits at offset 0 with the discriminant above it — which is why it is
`storedResultSize` and not `rawStatelessInputSize`. Writing the payload size here would understate
the record by the discriminant and hand a sibling permission to overwrite the tag.

`sliceDescriptor` is the only entry not reflected: a Zig `[]T` is a pointer/length pair, 16 bytes on
this target, and the manifest has no key for it. It is the same 16 that `contractByteListList`
already passes as its element size, for the same reason — a descriptor array's stride *is* the
descriptor size.

The `getD 0` fallbacks are never taken, and taking one would fail closed rather than open:
`canonicalRecordSizes_pinned` proves every field equals its exact reflected value, and a zero size
would make the clause demand the routine write nothing at all. -/
def canonicalRecordSizes : ResultRecordSizes :=
  { forkActivation := forkActivationSize.getD 0,
    forkConfig := forkConfigSize.getD 0,
    chainConfig := chainConfigSize.getD 0,
    executionRequests := executionRequestsSize.getD 0,
    executionWitness := executionWitnessSize.getD 0,
    executionPayload := executionPayloadSize.getD 0,
    newPayloadRequest := newPayloadRequestSize.getD 0,
    entryResult := storedResultSize.getD 0,
    sliceDescriptor := 16 }

/-- Per-size mutation guard: the record sizes are exactly the reflected 32/72/80/48/48/592/688/848.

The same role `canonicalOptionalU64_pinned` plays for the option layouts. It matters more here than
it looks: the clause is a *permission*, so an over-large record proves exactly as easily while giving
a sibling room to clobber — a wrong size is invisible at the use site in the weakening direction. -/
theorem canonicalRecordSizes_pinned :
    canonicalRecordSizes =
      { forkActivation := 32, forkConfig := 72, chainConfig := 80,
        executionRequests := 48, executionWitness := 48, executionPayload := 592,
        newPayloadRequest := 688, entryResult := 848, sliceDescriptor := 16 } := by
  native_decide

/-- The canonical decoder environment: the pinned image, the checked allocator state, and the ABI
option/aggregate layouts. -/
def canonicalEnvironment : DecoderEnvironment :=
  { image := Artifact.programImage
    allocatorState := canonicalAllocatorState
    heapPosAddr := Elfling.canonicalHeapPosAddr
    arenaBase := canonicalHeapBase
    optionalBlobSchedule := canonicalOptionalBlobSchedule
    blobSchedule := canonicalBlobScheduleLayout
    optionalU64 := canonicalOptionalU64
    record := canonicalRecordSizes }

/-- **The cursor address really is allocator state.** Without this the environment could name a
`heapPosAddr` outside the range `NoAllocation` pins, and a non-allocating routine could move the
cursor while still satisfying its contract. It is what makes `cursor_eq_of_noAllocation` applicable
at the canonical parameters. -/
theorem canonical_heapPos_is_allocator_state (i : Nat) (h : i < 8) :
    canonicalEnvironment.allocatorState (canonicalEnvironment.heapPosAddr + i) := by
  refine Or.inl ⟨by simp [canonicalEnvironment], ?_⟩
  simp only [canonicalEnvironment]
  omega

/-- The canonical bump heap: the validated 64 MiB `heap` region, cursor at its base. -/
def canonicalHeap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap :=
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
def canonicalRepRawV4 : ContainerRepresentation SszBridge.RawV4 :=
  fun inputBase input value state base => RawV4Rep state inputBase input base value

def canonicalRepForkActivation : ContainerRepresentation SszBridge.RawForkActivation :=
  fun _ _ value state base => ForkActivationRep state base value

def canonicalRepForkConfig : ContainerRepresentation SszBridge.RawForkConfig :=
  fun _ _ value state base => ForkConfigRep state base value

def canonicalRepChainConfig : ContainerRepresentation SszBridge.RawChainConfig :=
  fun _ _ value state base => ChainConfigRep state base value

def canonicalRepExecutionWitness : ContainerRepresentation SszBridge.RawExecutionWitness :=
  fun inputBase input value state base => ExecutionWitnessRep state inputBase input base value

def canonicalRepExecutionRequests : ContainerRepresentation SszBridge.RawExecutionRequests :=
  fun _ _ value state base => ExecutionRequestsRep state base value

def canonicalRepExecutionPayload : ContainerRepresentation SszBridge.RawExecutionPayload :=
  fun inputBase input value state base => ExecutionPayloadRep state inputBase input base value

def canonicalRepNewPayloadRequest : ContainerRepresentation SszBridge.RawNewPayloadRequest :=
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

/-! ## Non-local premises about the environment (Row D, D4)

Two of the premises the root obligation rests on are facts about the canonical parameters
themselves, independent of any execution. Both are settled here rather than assumed. -/

/-- **The canonical environment is valid.** Every satisfiability obligation in the catalog is
conditioned on `ValidEnvironment env`; discharging it here is what stops those obligations from
being vacuous claims about a nonsensical layout. It is a statement about the reflected `?u64` and
`?RawBlobSchedule` offsets — each discriminant inside its option, each payload fitting — so the
pinned manifest values settle it. -/
theorem canonical_environment_valid : ValidEnvironment canonicalEnvironment := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [canonicalEnvironment, canonicalOptionalBlobSchedule_pinned,
      canonicalOptionalU64_pinned] <;>
    decide

/-- **A fresh globals model cannot produce `alreadyDecoded`.**

The exported wrapper refuses a *second* call, and the refusal is observationally a `0` return — the
same code a rejection returns. The root theorem runs the decoder exactly once from a freshly built
state, so this rules the refusal out at the source rather than relying on the runner to notice it
downstream. `DecoderGlobalsModel.fresh` has `attempted = false`, and `callOutcome` only produces
`alreadyDecoded` when `attempted` is set. -/
theorem fresh_call_is_never_alreadyDecoded
    (result : Except SszDecodeError SszBridge.RawV4) :
    callOutcome DecoderGlobalsModel.fresh result ≠ .alreadyDecoded := by
  cases result <;> simp [callOutcome, DecoderGlobalsModel.fresh]

/-- The same fact in the form the status dispatch consumes: a fresh call never records the
`alreadyDecoded` status, so a run that *did* record it is a misbehaving wrapper rather than a
second call the root failed to account for. -/
theorem fresh_call_status_is_never_alreadyDecoded
    (result : Except SszDecodeError SszBridge.RawV4) :
    (callOutcome DecoderGlobalsModel.fresh result).status ≠ .alreadyDecoded := by
  cases result with
  | ok _ => simp [callOutcome, DecodeCallOutcome.status, DecoderGlobalsModel.fresh]
  | error error =>
    cases error <;>
      simp [callOutcome, DecodeCallOutcome.status, DecoderGlobalsModel.fresh, statusOfResult]

end BinaryFv.SSZ.Zesu.Contracts
