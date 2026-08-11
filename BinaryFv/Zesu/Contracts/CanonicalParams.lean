import BinaryFv.Zesu.Contracts.Catalog.Dispatch
import BinaryFv.Zesu.Elflings.GeneratedDecoderGlobals
import BinaryFv.Zesu.DecodedValue.Containers
import BinaryFv.Zesu.Runtime.BumpAllocator
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Layout

/-!
# The concrete binary and ABI used by every contract

`ContractParams` collects the external facts needed to interpret a decoder contract: the loaded
program, allocator addresses, heap range, private globals, Zig layouts, and predicates describing
decoded values in memory. The final proof uses the single value `canonicalContractParams`; it cannot
choose a more convenient environment.

Its fields come from checked artifacts:

- `env.image` is the pinned canonical image `Artifacts.programImage`;
- `env.allocatorState` is `canonicalAllocatorState` (the `ZKVM_HEAP_POS`/`ZKVM_HEAP_TOP` byte ranges,
  extracted and checked in `Elflings.GeneratedDecoderGlobals`);
- `heap` is the validated 64 MiB `heap` region;
- `globals`/`resultBuffer` are the validated decoder globals.

The Zig optional layouts come from the ABI manifest produced by the pinned compiler.

The container representations are **concrete and complete**: `repStatelessInput` is the full input-aware
`StatelessInputRep` (allocation, slice descriptors, and borrowed input slices, not just the fixed fields), and
all seven nested-container representations use the concrete layouts in
`DecodedValue.Containers`. Later execution proofs must establish these predicates; they may
not replace them with placeholders. Lean checks every literal field offset against the manifest.
-/

namespace BinaryFv.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.Zesu.DecodedValue
open BinaryFv.Zesu.Elflings
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

open BinaryFv.Zesu.Artifacts in
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
would make the clause demand the function instance write nothing at all. -/
def canonicalRecordSizes : ResultRecordSizes :=
  { forkActivation := forkActivationSize.getD 0,
    forkConfig := forkConfigSize.getD 0,
    chainConfig := chainConfigSize.getD 0,
    executionRequests := executionRequestsSize.getD 0,
    executionWitness := executionWitnessSize.getD 0,
    executionPayload := executionPayloadSize.getD 0,
    newPayloadRequest := newPayloadRequestSize.getD 0,
    entryResult := storedResultSize.getD 0,
    entryResultTagOffset := storedResultTagOffset.getD 0,
    sliceDescriptor := 16,
    allocatorObject := 16 }

/-- Per-size mutation guard: the record sizes are exactly the reflected 32/72/80/48/48/592/688/848.

The same role `canonicalOptionalU64_pinned` plays for the option layouts. It matters more here than
it looks: the clause is a *permission*, so an over-large record proves exactly as easily while giving
a sibling room to clobber — a wrong size is invisible at the use site in the weakening direction. -/
theorem canonicalRecordSizes_pinned :
    canonicalRecordSizes =
      { forkActivation := 32, forkConfig := 72, chainConfig := 80,
        executionRequests := 48, executionWitness := 48, executionPayload := 592,
        newPayloadRequest := 688, entryResult := 848, entryResultTagOffset := 832,
        sliceDescriptor := 16,
        allocatorObject := 16 } := by
  native_decide

/-! ## The machine stack

`DecoderEnvironment.stack` is the last region the ownership clause needs and the only one that is not
a fact about the ELF: the linked image contains no stack, the runner supplies one. So it is read from
the *same* `canonicalRunnerLayout` the runner builds its state from, rather than restated here — a
second copy of `0x3000_0000_0000` would be exactly the silent drift `Entrypoints/…/Layout.lean`'s
opening docstring calls a silent unsoundness, and would let a relocated stack leave the contracts
protecting an address range nothing runs in.

That import is the reason this module names an `Entrypoints` module at all. It is a genuine
dependency and not a layering slip: which memory a contract may permit a function instance to scribble is a
fact about the machine the contracts are interpreted in, and the runner is what fixes it — the same
status `image` and `allocatorState` already have. -/

/-- The canonical machine stack: the runner's 1 MiB stack, as a region. -/
def canonicalStack : Region :=
  range Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackBase
    Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackSize

/-- Per-address mutation guard on the region the ownership clause permits: the canonical stack is
exactly `[0x3000_0000_0000, 0x3000_0010_0000)`.

The same role `canonicalRecordSizes_pinned` plays for the record sizes, and it matters in the same
direction. The stack is the one component of the owned region that is pure *permission* with no
countervailing conjunct: a stack accidentally relocated downward into the arena would weaken every
ownership clause in the catalog and break no proof, because a wider permission is easier to satisfy.
Proved by `decide` rather than `native_decide`: this opens no trust door. -/
theorem canonicalStack_pinned :
    Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackBase = 0x3000_0000_0000 ∧
      Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackSize = 1024 * 1024 := by
  constructor <;> rfl

/-! ### The stack is disjoint from everything the discipline protects

Item four of what the clause must still do. A wider permission is only safe if nothing the ownership
composition transports lives inside it, and that has to be *proved* — `arena_disjoint_from_globals`
is the existing shape and this is the same argument against a third region.

All of it reduces to one comparison, because the runner deliberately places every range it owns above
`loadedCeiling`, one address above everything the ELF loads. So the arena and the decoder's private
globals are excluded together rather than one at a time. -/

/-- **Nothing the image loads is in the stack.** The single fact the three below are corollaries
of. -/
theorem canonicalStack_above_loaded (address : Nat)
    (below : address < Entrypoints.ZesuDecodeRaw.loadedCeiling) : ¬ canonicalStack address := by
  rintro ⟨hlo, _⟩
  have : Entrypoints.ZesuDecodeRaw.loadedCeiling
      ≤ Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackBase := by decide
  omega

/-- **The arena is not in the stack.** So an allocated sibling's record and the heap arrays it points
at are outside every function instance's stack permission, which is what keeps `chain_agrees_on_region` usable
after the widening. -/
theorem canonicalStack_disjoint_from_arena (address : Nat)
    (inArena : address < Entrypoints.ZesuDecodeRaw.heapCeiling) : ¬ canonicalStack address :=
  canonicalStack_above_loaded address
    (Nat.lt_of_lt_of_le inArena Entrypoints.ZesuDecodeRaw.runtime_below_ceiling.1)

/-- **The decoder's private globals are not in the stack.** This is the one that covers
`stored_result`, the record the exported accessors publish and the root theorem reads: it sits in the
decoder `.bss` block, which `GeneratedDecoderGlobals.withinBss` checks and `globalsCeiling` bounds. -/
theorem canonicalStack_disjoint_from_globals (address : Nat)
    (inGlobals : address < Entrypoints.ZesuDecodeRaw.globalsCeiling) : ¬ canonicalStack address :=
  canonicalStack_above_loaded address
    (Nat.lt_of_lt_of_le inGlobals Entrypoints.ZesuDecodeRaw.runtime_below_ceiling.2)

/-- **The allocator's own mutable state is not in the stack.** `ZKVM_HEAP_POS` and `ZKVM_HEAP_TOP`
live just below the arena, so the two halves of an allocating function instance's permission stay distinct
rather than one swallowing the other. -/
theorem canonicalStack_disjoint_from_allocatorState (address : Nat)
    (inAllocator : canonicalAllocatorState address) : ¬ canonicalStack address := by
  refine canonicalStack_above_loaded address ?_
  have hpos : Elflings.canonicalHeapPosAddr + 8 ≤ Entrypoints.ZesuDecodeRaw.loadedCeiling := by decide
  have htop : Elflings.canonicalHeapTopAddr + 8 ≤ Entrypoints.ZesuDecodeRaw.loadedCeiling := by decide
  rcases inAllocator with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- **The exported result buffer is not in the stack**, byte for byte across the whole 848-byte
`stored_result` object.

The corollary that matters, because `stored_result` is the one record the root theorem actually
reads: without it "the globals are not in the stack" is a statement about a ceiling and not yet about
the object. -/
theorem canonicalResultBuffer_not_in_stack (index : Nat) (h : index < 848) :
    ¬ canonicalStack (Elflings.canonicalResultBuffer + index) := by
  refine canonicalStack_disjoint_from_globals _ ?_
  have : Elflings.canonicalResultBuffer + 848 ≤ Entrypoints.ZesuDecodeRaw.globalsCeiling := by decide
  omega

/-- **No address of the 64 MiB arena is in the stack**, stated at `canonicalHeapLimit` — the bound the
allocator contracts are written against — rather than at the fold `heapCeiling` computes. -/
theorem canonicalArena_not_in_stack (address : Nat) (h : address < Elflings.canonicalHeapLimit) :
    ¬ canonicalStack address := by
  refine canonicalStack_disjoint_from_arena address ?_
  have : Elflings.canonicalHeapLimit ≤ Entrypoints.ZesuDecodeRaw.heapCeiling := by decide
  omega

/-- **The borrowed input buffer is not in the stack either.** Not needed by the composition — the
input is pinned absolutely by `MemoryBytes`, not transported — but recorded because "the callee may
write its whole stack" is only harmless if the caller's input is somewhere else, and that is a runner
placement fact rather than something a contract could establish. -/
theorem canonicalStack_disjoint_from_input (address : Nat)
    (inInput : address < Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.inputStop) :
    ¬ canonicalStack address := by
  rintro ⟨hlo, _⟩
  have := Entrypoints.ZesuDecodeRaw.layout_pairwise_disjoint.1
  omega

/-- The canonical decoder environment: the pinned image, the checked allocator state, and the ABI
option/aggregate layouts. -/
def canonicalEnvironment : DecoderEnvironment :=
  { image := Artifacts.programImage
    allocatorState := canonicalAllocatorState
    heapPosAddr := Elflings.canonicalHeapPosAddr
    arenaBase := canonicalHeapBase
    optionalBlobSchedule := canonicalOptionalBlobSchedule
    blobSchedule := canonicalBlobScheduleLayout
    optionalU64 := canonicalOptionalU64
    record := canonicalRecordSizes
    stack := canonicalStack }

/-- **The cursor address really is allocator state.** Without this the environment could name a
`heapPosAddr` outside the range `NoAllocation` pins, and a non-allocating function instance could move the
cursor while still satisfying its contract. It is what makes `cursor_eq_of_noAllocation` applicable
at the canonical parameters. -/
theorem canonical_heapPos_is_allocator_state (i : Nat) (h : i < 8) :
    canonicalEnvironment.allocatorState (canonicalEnvironment.heapPosAddr + i) := by
  refine Or.inl ⟨by simp [canonicalEnvironment], ?_⟩
  simp only [canonicalEnvironment]
  omega

/-- The canonical bump heap: the validated 64 MiB `heap` region, cursor at its base. -/
def canonicalHeap : BinaryFv.Zesu.Runtime.BumpHeap :=
  { position := canonicalHeapBase, limit := canonicalHeapLimit }

/-! ## Container representations

Every container's representation is the exact native RV64 layout from `DecodedValue.Containers`
(offsets pinned against the ABI manifest by `container_field_offsets_valid` and the `StatelessInput` audits).
`repStatelessInput` is the complete `StatelessInputRep` — root allocation, all ten heap arrays, the descriptor table,
every borrowed input slice, and all inline fixed fields — not merely the fixed-field fragment. The
input base and bytes carried by `ContainerRepresentation` let the allocating containers and `StatelessInput`
describe their input-relative borrowed slices. -/

/-- The complete native representation of a decoded `StatelessInput` rooted at `base`, decoded from the caller's
input at `inputBase`/`input`. -/
def canonicalStatelessInputRep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput :=
  fun inputBase input value state base => StatelessInputRep state inputBase input base value

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
    repStatelessInput := canonicalStatelessInputRep }

/-! ## Facts about the canonical environment

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
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) :
    callOutcome DecoderGlobalsModel.fresh result ≠ .alreadyDecoded := by
  cases result <;> simp [callOutcome, DecoderGlobalsModel.fresh]

/-- The same fact in the form the status dispatch consumes: a fresh call never records the
`alreadyDecoded` status, so a run that *did* record it is a misbehaving wrapper rather than a
second call the root failed to account for. -/
theorem fresh_call_status_is_never_alreadyDecoded
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) :
    (callOutcome DecoderGlobalsModel.fresh result).status ≠ .alreadyDecoded := by
  cases result with
  | ok _ => simp [callOutcome, DecodeCallOutcome.status, DecoderGlobalsModel.fresh]
  | error error =>
    cases error <;>
      simp [callOutcome, DecodeCallOutcome.status, DecoderGlobalsModel.fresh, statusOfResult]


/-- The pinned image behind `canonicalContractParams`, as a projection equation.

Stated at the *projection* rather than through `CodeIntact`: deciding
`canonicalContractParams.env.CodeIntact state` against
`Artifacts.programImage.fileBytesLoadedFaithfully state.mem` directly forces evaluation of the whole
program image (~29 s, and it exhausts the default recursion depth). This equation is two projections
and closes by `rfl`. -/
theorem canonicalEnvironment_image :
    canonicalEnvironment.image = BinaryFv.Zesu.Artifacts.programImage := by
  simp only [canonicalEnvironment]

/-- Transport a canonical `CodeIntact` to the raw pinned image, without the expensive defeq.

Every site that hands a `CodeIntact` where the raw image is expected otherwise pays that defeq in
full; there are hundreds of such sites. Note the `simpa [canonicalContractParams,
canonicalEnvironment] using code` idiom found at them is not what costs the time -- a bare
`exact code` measures the same -- so the fix is routing through this transport, not dropping the
simp set. -/
theorem canonicalCodeIntact_image {state : BinaryFv.RiscV.State}
    (code : canonicalContractParams.env.CodeIntact state) :
    BinaryFv.Zesu.Artifacts.programImage.fileBytesLoadedFaithfully state.mem :=
  canonicalEnvironment_image ▸ code

/-- The reverse of `canonicalCodeIntact_image`, for goals stated at the raw image. -/
theorem canonicalCodeIntact_of_image {state : BinaryFv.RiscV.State}
    (h : BinaryFv.Zesu.Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    canonicalContractParams.env.CodeIntact state := by
  show canonicalEnvironment.image.fileBytesLoadedFaithfully state.mem
  rw [canonicalEnvironment_image]; exact h

end BinaryFv.Zesu.Contracts
