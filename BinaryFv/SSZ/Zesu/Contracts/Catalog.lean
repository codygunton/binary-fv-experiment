import BinaryFv.SSZ.Zesu.Contracts.Runtime
import BinaryFv.SSZ.Zesu.Contracts.ExportedDecoder

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-!
# The semantic-routine catalog

The complete enumeration of routines the proof must cover, each carrying a stable, address-free
`FunctionId` (pinned source file, qualified name, and concrete specialization — **no** declaration
line or content hash: those are validated provenance, not identity), the `RoutineTag` that selects
its handwritten contract, and a `Presence` classification.

Membership is pinned to source: every catalog `FunctionId` names a routine in
`src/stateless/stateless/ssz_raw.zig`, `src/zkvm/raw_decoder_root.zig`, `src/zkvm/raw_allocator.zig`,
or the freestanding RV64 runtime, and every excluded routine carries a machine-checkable reason.
Nothing here carries an address, an instruction word, or a symbol — an entry is identity plus its
contract selector, and the generated Elfling program is what binds each identity to canonical-ELF
ranges.

The qualified-name convention is the Zig module-qualified form, which the extraction row reconciles
against DWARF. The declaration line and the source content hash are **not** part of the identity;
they are provenance carried by generated function instances and checked — the hash for equality against
`pinnedSourceManifest`, the line for `> 0` — by `sourceProvenanceRecorded`.
-/

/-! ## Source files

Each routine's declaring source file, by path only. Content hashes and declaration lines are
validated *provenance* (`DeclarationProvenance`), carried by generated function instances and checked
against the pinned source in the extraction row — they are not part of these identities. -/

/-- The SSZ decoder body: `src/stateless/stateless/ssz_raw.zig`. -/
def decoderSourceFile : SourceFile :=
  { path := "src/stateless/stateless/ssz_raw.zig" }

/-- The freestanding decoder root: the exported wrapper and the allocator vtable thunks. -/
def rootSourceFile : SourceFile :=
  { path := "src/zkvm/raw_decoder_root.zig" }

/-- The bump-allocator object that defines the exported `zesu_raw_alloc`. -/
def allocatorSourceFile : SourceFile :=
  { path := "src/zkvm/raw_allocator.zig" }

/-- The freestanding RV64 C runtime that supplies `memcpy`/`memmove`. Not a Zig decoder source. -/
def runtimeSourceFile : SourceFile :=
  { path := "targets/common/riscv64_runtime.c" }

/-- The authoritative pinned-source manifest: each catalog source file mapped to the SHA-256 of its
pinned content — the Zesu source at `github:codygunton/zesu@96f1621` and the repo's freestanding RV64
runtime.

`sourceProvenanceRecorded` checks every function instance's recorded `declProvenance.sourceFileHash` for
*equality* with the manifest entry for its file, so provenance is validated against the pin rather
than merely being non-empty. If the pinned revision (or the runtime source) changes, this manifest
must change with it — that coupling is exactly what provenance is for. -/
def pinnedSourceManifest : List (SourceFile × String) :=
  [ (decoderSourceFile, "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131"),
    (rootSourceFile, "53afe7a5c7c70122a3e2a9f9673a3415a50579a2ed11a21d9dd1c839e0c18a5e"),
    (allocatorSourceFile, "c9e9457e45a3827729adb1921e07ba31997a536dc8f719e04d2d0d6f4c742591"),
    (runtimeSourceFile, "5f80e272e96ccb30ca109bb77c9a78c9769bfd6b54ac2d7f712d3c2deb9b8235") ]

/-- The pinned content hash for a source file, if it is one of the manifest files; `none` otherwise
(which makes `sourceProvenanceRecorded` reject a function instance attributed to an off-manifest file). -/
def pinnedSourceHash (file : SourceFile) : Option String :=
  (pinnedSourceManifest.find? (fun entry => decide (entry.1 = file))).map (·.2)

/-! ## Identity and dispatch -/

/-- The handwritten routine groups. -/
inductive RoutineGroup where
  | entry | container | collection | option | leaf | runtime
deriving DecidableEq, Repr, Inhabited

/-- The dispatch key: one constructor per handwritten contract. This is what turns "this function instance's
identity" into "this function instance's `correctnessClaim`", so the per-function-instance obligation is a total
function of the catalog rather than a hand-maintained list of unrelated propositions. -/
inductive RoutineTag where
  | zesuDecodeRaw | decode | decodeRaw
  | newPayloadRequest | executionPayload | executionRequests | executionWitness
  | chainConfig | forkConfig | forkActivation
  | optionalU64 | optionalBlobSchedule
  | versionedHashes | withdrawals | depositRequests | withdrawalRequests
  | consolidationRequests | publicKeys | byteListList
  | requireCanonicalOffsets | requireU32Length | readOffset | readU32 | readU64 | readU256
  | readArray | bytesAt | hasExactErePrefix
  | rawAlloc | memcpy | memmove | rawResult | rawError
  | allocatorAlloc | allocatorResize | allocatorRemap | allocatorFree | allocatorCtor
deriving DecidableEq, Repr, Inhabited

/-- Why a source routine is excluded from the cataloged semantic proof — either it has no live
function instance in the canonical binary, or it is reachable emitted glue whose net effect is captured
elsewhere. The last two are the row-2 reachable-but-excluded categories, shared with the generated
Elfling reachable-partition taxonomy (stack-integration point). -/
inductive ExclusionReason where
  /-- Not compiled into the `ReleaseSmall` object (a test-only helper). -/
  | testOnly
  /-- Present in source but not reachable from `zesu_decode_raw`. -/
  | unreachable
  /-- Reachable `std`/`mem`/`math` implementation emitted as its own routine (allocator vtable), whose
  net behavior is captured by the cataloged allocator contracts. -/
  | reachableStdlib
  /-- Reachable `*.deinit` error-path cleanup; the freestanding zkVM's allocator free is a no-op, so it
  never changes the accept/reject outcome. -/
  | reachableCleanupNoOp
deriving DecidableEq, Repr, Inhabited

/-- Whether a cataloged routine is expected to occur in the canonical program. -/
inductive Presence where
  /-- Appears as one or more generated function instances (emitted or inlined). -/
  | live
  /-- Has no function instance, for the given reason. -/
  | absent (reason : ExclusionReason)
deriving DecidableEq, Repr, Inhabited

/-- A cataloged routine: full address-free identity, its contract selector, and its expected
presence. -/
structure CatalogEntry where
  functionId : FunctionId
  group : RoutineGroup
  tag : RoutineTag
  allocates : Bool
  hasSymbol : Bool
  presence : Presence
deriving Repr, Inhabited

namespace CatalogEntry

/-- The catalog entry is expected to have live function instances. -/
def isLive (entry : CatalogEntry) : Bool :=
  match entry.presence with | .live => true | .absent _ => false

end CatalogEntry

/-! ## Builders -/

private def fid (file : SourceFile) (name : String) (spec : Array String := #[]) : FunctionId :=
  { declaration := { file := file, qualifiedName := name }, specialization := spec }

/-- A live decoder-source routine with no specialization. -/
private def dec (name : String) (group : RoutineGroup) (tag : RoutineTag)
    (allocates : Bool) : CatalogEntry :=
  { functionId := fid decoderSourceFile ("ssz_raw." ++ name)
    group := group, tag := tag, allocates := allocates, hasSymbol := false, presence := .live }

/-- A live `readArray` specialization: same routine, distinct concrete width. -/
private def readArrayEntry (width : Nat) : CatalogEntry :=
  { functionId := fid decoderSourceFile "ssz_raw.readArray" #[toString width]
    group := .leaf, tag := .readArray, allocates := false, hasSymbol := false, presence := .live }

/-- The canonical entry routine's identity: the exported `zesu_decode_raw` wrapper. -/
def zesuDecodeRawFunctionId : FunctionId :=
  fid rootSourceFile "raw_decoder_root.zesu_decode_raw"

/-! ## The catalog -/

/--
The complete catalog of live routines.

Every entry has handwritten `meaning`, `pre`, `post`, `contract`, `correctnessClaim`, and
`satisfiable` definitions, and its `tag` selects them in `functionInstanceObligation`. `readArray` appears
once per concrete width the decoder instantiates (20, 32, 48, 65, 96, 256), so a generated
function instance is matched by full identity, not by the bare name.
-/
def catalog : Array CatalogEntry :=
  #[ -- Entry / top level
     { functionId := zesuDecodeRawFunctionId
       group := .entry, tag := .zesuDecodeRaw, allocates := true, hasSymbol := true
       presence := .live }
   , dec "decode" .entry .decode true
   , dec "decodeRaw" .entry .decodeRaw true
     -- Containers
   , dec "decodeNewPayloadRequest" .container .newPayloadRequest true
   , dec "decodeExecutionPayload" .container .executionPayload true
   , dec "decodeExecutionRequests" .container .executionRequests true
   , dec "decodeExecutionWitness" .container .executionWitness true
   , dec "decodeChainConfig" .container .chainConfig false
   , dec "decodeForkConfig" .container .forkConfig false
   , dec "decodeForkActivation" .container .forkActivation false
     -- Options
   , dec "decodeOptionalU64" .option .optionalU64 false
   , dec "decodeOptionalBlobSchedule" .option .optionalBlobSchedule false
     -- Collections
   , dec "decodeVersionedHashes" .collection .versionedHashes true
   , dec "decodeWithdrawals" .collection .withdrawals true
   , dec "decodeDepositRequests" .collection .depositRequests true
   , dec "decodeWithdrawalRequests" .collection .withdrawalRequests true
   , dec "decodeConsolidationRequests" .collection .consolidationRequests true
   , dec "decodePublicKeys" .collection .publicKeys true
   , dec "decodeByteListList" .collection .byteListList true
     -- Leaves (non-readArray)
   , dec "requireCanonicalOffsets" .leaf .requireCanonicalOffsets false
   , dec "requireU32Length" .leaf .requireU32Length false
   , dec "readOffset" .leaf .readOffset false
   , dec "readU32" .leaf .readU32 false
   , dec "readU64" .leaf .readU64 false
   , dec "readU256" .leaf .readU256 false
   , dec "bytesAt" .leaf .bytesAt false
   , dec "hasExactErePrefix" .leaf .hasExactErePrefix false
     -- readArray specializations
   , readArrayEntry 20, readArrayEntry 32, readArrayEntry 48
   , readArrayEntry 65, readArrayEntry 96, readArrayEntry 256
     -- Runtime and accessors
   , { functionId := fid allocatorSourceFile "raw_allocator.zesu_raw_alloc"
       group := .runtime, tag := .rawAlloc, allocates := true, hasSymbol := true, presence := .live }
   , { functionId := fid rootSourceFile "raw_decoder_root.zesu_raw_result"
       group := .runtime, tag := .rawResult, allocates := false, hasSymbol := true, presence := .live }
   , { functionId := fid rootSourceFile "raw_decoder_root.zesu_raw_error"
       group := .runtime, tag := .rawError, allocates := false, hasSymbol := true, presence := .live }
   , { functionId := fid runtimeSourceFile "memcpy"
       group := .runtime, tag := .memcpy, allocates := false, hasSymbol := true, presence := .live }
   , { functionId := fid runtimeSourceFile "memmove"
       group := .runtime, tag := .memmove, allocates := false, hasSymbol := true, presence := .live }
     -- Allocator wrapper / vtable thunks
   , { functionId := fid rootSourceFile "raw_decoder_root.allocatorAlloc"
       group := .runtime, tag := .allocatorAlloc, allocates := true, hasSymbol := false
       presence := .live }
   , { functionId := fid rootSourceFile "raw_decoder_root.allocatorResize"
       group := .runtime, tag := .allocatorResize, allocates := false, hasSymbol := false
       presence := .live }
   , { functionId := fid rootSourceFile "raw_decoder_root.allocatorRemap"
       group := .runtime, tag := .allocatorRemap, allocates := false, hasSymbol := false
       presence := .live }
   , { functionId := fid rootSourceFile "raw_decoder_root.allocatorFree"
       group := .runtime, tag := .allocatorFree, allocates := false, hasSymbol := false
       presence := .live }
   , { functionId := fid rootSourceFile "raw_decoder_root.allocator"
       group := .runtime, tag := .allocatorCtor, allocates := false, hasSymbol := false
       presence := .live } ]

/-- Routines present in source but with no live function instance in the canonical program, each with a
machine-checkable reason. Coverage requires that none of these is matched by a generated function instance. -/
def excludedRoutines : Array CatalogEntry :=
  #[ { functionId := fid decoderSourceFile "ssz_raw.putU32"
       group := .leaf, tag := .requireU32Length, allocates := false, hasSymbol := false
       presence := .absent .testOnly }
   , { functionId := fid decoderSourceFile "ssz_raw.putU64"
       group := .leaf, tag := .requireU32Length, allocates := false, hasSymbol := false
       presence := .absent .testOnly }
   , { functionId := fid decoderSourceFile "ssz_raw.makeMinimalV4"
       group := .leaf, tag := .requireU32Length, allocates := false, hasSymbol := false
       presence := .absent .testOnly } ]

/-- The concrete `readArray` widths the pinned decoder instantiates, as source-derived facts. -/
def requiredReadArrayWidths : List Nat := [20, 32, 48, 65, 96, 256]

/-- The width a generated `readArray` function instance carries, parsed from its specialization. -/
def readArrayWidthOf (function : FunctionId) : Nat :=
  ((function.specialization[0]?).bind String.toNat?).getD 0

/-! ## Typed per-function-instance dispatch -/

/--
Everything a per-function-instance obligation needs beyond the function instance itself: the pinned environment, the
allocator heap, the status slot, and the container/RawV4 result representations.

Bundling these keeps `functionInstanceObligation` a total function while letting each container assert its own
result layout. -/
structure ContractParams where
  env : DecoderEnvironment
  heap : BinaryFv.SSZ.Zesu.Runtime.BumpHeap
  /-- The pinned addresses of the three private decoder globals (`attempted`, 32-bit `last_status`,
  and the inline optional `stored_result` object), read back through the exported accessors. This replaces the
  previous free public 64-bit `statusBase` slot, which the wrapper never writes. -/
  globals : DecoderGlobalsLayout
  /-- The payload address returned by `zesu_raw_result` when `stored_result` is present. -/
  resultBuffer : Nat
  repForkActivation : ContainerRepresentation SszBridge.RawForkActivation
  repForkConfig : ContainerRepresentation SszBridge.RawForkConfig
  repChainConfig : ContainerRepresentation SszBridge.RawChainConfig
  repExecutionWitness : ContainerRepresentation SszBridge.RawExecutionWitness
  repExecutionRequests : ContainerRepresentation SszBridge.RawExecutionRequests
  repExecutionPayload : ContainerRepresentation SszBridge.RawExecutionPayload
  repNewPayloadRequest : ContainerRepresentation SszBridge.RawNewPayloadRequest
  repRawV4 : ContainerRepresentation SszBridge.RawV4

/--
The correctness obligation a single generated function instance owes, selected by its routine `tag`.

The entry PC and exit predicate come from the function instance's generated data, never from an existential,
so a proof cannot pick a convenient entry or exit. Every branch returns the `correctnessClaim` for
exactly the routine the identity names; heterogeneous `Args`/`Result` types are erased to `Prop`
here, which is why one typed dispatch can cover the whole catalog. -/
def routineObligation (p : ContractParams) (functionInstance : FunctionInstance) (tag : RoutineTag) : Prop :=
  let entry : BitVec 64 := BitVec.ofNat 64 functionInstance.entryPc
  let exit : BitVec 64 → Prop := fun pc => functionInstance.isExit pc.toNat
  match tag with
  | .zesuDecodeRaw =>
      correctnessClaimZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4 functionInstance entry exit
  | .decode => correctnessClaimDecode p.env p.repRawV4 functionInstance entry exit
  | .decodeRaw => correctnessClaimDecodeRaw p.env p.repRawV4 functionInstance entry exit
  | .newPayloadRequest =>
      correctnessClaimNewPayloadRequest p.env p.repNewPayloadRequest functionInstance entry exit
  | .executionPayload =>
      correctnessClaimExecutionPayload p.env p.repExecutionPayload functionInstance entry exit
  | .executionRequests =>
      correctnessClaimExecutionRequests p.env p.repExecutionRequests functionInstance entry exit
  | .executionWitness =>
      correctnessClaimExecutionWitness p.env p.repExecutionWitness functionInstance entry exit
  | .chainConfig => correctnessClaimChainConfig p.env p.repChainConfig functionInstance entry exit
  | .forkConfig => correctnessClaimForkConfig p.env p.repForkConfig functionInstance entry exit
  | .forkActivation => correctnessClaimForkActivation p.env p.repForkActivation functionInstance entry exit
  | .optionalU64 => correctnessClaimOptionalU64 p.env functionInstance entry exit
  | .optionalBlobSchedule => correctnessClaimOptionalBlobSchedule p.env functionInstance entry exit
  | .versionedHashes => correctnessClaimVersionedHashes p.env functionInstance entry exit
  | .withdrawals => correctnessClaimWithdrawals p.env functionInstance entry exit
  | .depositRequests => correctnessClaimDepositRequests p.env functionInstance entry exit
  | .withdrawalRequests => correctnessClaimWithdrawalRequests p.env functionInstance entry exit
  | .consolidationRequests => correctnessClaimConsolidationRequests p.env functionInstance entry exit
  | .publicKeys => correctnessClaimPublicKeys p.env functionInstance entry exit
  | .byteListList => correctnessClaimByteListList p.env functionInstance entry exit
  | .requireCanonicalOffsets => correctnessClaimRequireCanonicalOffsets p.env functionInstance entry exit
  | .requireU32Length => correctnessClaimRequireU32Length p.env functionInstance entry exit
  | .readOffset => correctnessClaimReadOffset p.env functionInstance entry exit
  | .readU32 => correctnessClaimReadU32 p.env functionInstance entry exit
  | .readU64 => correctnessClaimReadU64 p.env functionInstance entry exit
  | .readU256 => correctnessClaimReadU256 p.env functionInstance entry exit
  | .readArray =>
      correctnessClaimReadArray p.env (readArrayWidthOf functionInstance.id.function) functionInstance entry exit
  | .bytesAt => correctnessClaimBytesAt p.env functionInstance entry exit
  | .hasExactErePrefix => correctnessClaimHasExactErePrefix p.env functionInstance entry exit
  | .rawAlloc => correctnessClaimAlloc p.env p.heap functionInstance entry exit
  | .memcpy => correctnessClaimMemcpy p.env functionInstance entry exit
  | .memmove => correctnessClaimMemmove p.env functionInstance entry exit
  | .rawResult =>
      correctnessClaimRawResult p.env p.globals p.resultBuffer functionInstance entry exit
  | .rawError => correctnessClaimRawError p.env p.globals functionInstance entry exit
  | .allocatorAlloc => correctnessClaimAllocatorAlloc p.env p.heap functionInstance entry exit
  | .allocatorResize => correctnessClaimAllocatorResize p.env functionInstance entry exit
  | .allocatorRemap => correctnessClaimAllocatorRemap p.env functionInstance entry exit
  | .allocatorFree => correctnessClaimAllocatorFree p.env functionInstance entry exit
  | .allocatorCtor => correctnessClaimAllocatorCtor p.env functionInstance entry exit

/-- The satisfiability obligation for a routine's contract, selected by the same `tag`.

Aggregating these through the dispatch is what makes anti-vacuity uniform: every live function instance's
contract must have a satisfiable precondition under a valid environment, stated at the routine's own
parameter level. -/
def routineSatisfiable (p : ContractParams) (function : FunctionId) (tag : RoutineTag) : Prop :=
  match tag with
  | .zesuDecodeRaw => satisfiableZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4
  | .decode => satisfiableDecode p.env p.repRawV4
  | .decodeRaw => satisfiableDecodeRaw p.env p.repRawV4
  | .newPayloadRequest => satisfiableNewPayloadRequest p.env p.repNewPayloadRequest
  | .executionPayload => satisfiableExecutionPayload p.env p.repExecutionPayload
  | .executionRequests => satisfiableExecutionRequests p.env p.repExecutionRequests
  | .executionWitness => satisfiableExecutionWitness p.env p.repExecutionWitness
  | .chainConfig => satisfiableChainConfig p.env p.repChainConfig
  | .forkConfig => satisfiableForkConfig p.env p.repForkConfig
  | .forkActivation => satisfiableForkActivation p.env p.repForkActivation
  | .optionalU64 => satisfiableOptionalU64 p.env
  | .optionalBlobSchedule => satisfiableOptionalBlobSchedule p.env
  | .versionedHashes => satisfiableVersionedHashes p.env
  | .withdrawals => satisfiableWithdrawals p.env
  | .depositRequests => satisfiableDepositRequests p.env
  | .withdrawalRequests => satisfiableWithdrawalRequests p.env
  | .consolidationRequests => satisfiableConsolidationRequests p.env
  | .publicKeys => satisfiablePublicKeys p.env
  | .byteListList => satisfiableByteListList p.env
  | .requireCanonicalOffsets => satisfiableRequireCanonicalOffsets p.env
  | .requireU32Length => satisfiableRequireU32Length p.env
  | .readOffset => satisfiableReadOffset p.env
  | .readU32 => satisfiableReadU32 p.env
  | .readU64 => satisfiableReadU64 p.env
  | .readU256 => satisfiableReadU256 p.env
  | .readArray => satisfiableReadArray p.env (readArrayWidthOf function)
  | .bytesAt => satisfiableBytesAt p.env
  | .hasExactErePrefix => satisfiableHasExactErePrefix p.env
  | .rawAlloc => satisfiableAlloc p.env p.heap
  | .memcpy => satisfiableMemcpy p.env
  | .memmove => satisfiableMemmove p.env
  | .rawResult => satisfiableRawResult p.env p.globals p.resultBuffer
  | .rawError => satisfiableRawError p.env p.globals
  | .allocatorAlloc => satisfiableAllocatorAlloc p.env p.heap
  | .allocatorResize => satisfiableAllocatorResize p.env
  | .allocatorRemap => satisfiableAllocatorRemap p.env
  | .allocatorFree => satisfiableAllocatorFree p.env
  | .allocatorCtor => satisfiableAllocatorCtor p.env

/-! ## Full-identity matching -/

/-- The catalog entry whose full `FunctionId` equals `function`, if any. Matching is by the whole
identity — file, qualified name, and specialization — so a `readArray[32]` function instance cannot be
satisfied by the `readArray[20]` contract. -/
def catalogEntryFor (function : FunctionId) : Option CatalogEntry :=
  catalog.find? fun entry => decide (entry.functionId = function)

/-- An excluded routine matching `function`, if any. -/
def excludedEntryFor (function : FunctionId) : Option CatalogEntry :=
  excludedRoutines.find? fun entry => decide (entry.functionId = function)

/-! ## Coverage and uniqueness obligations -/

/-- Every live catalog entry has at least one generated function instance carrying its exact identity. -/
def everyRoutineHasFunctionInstance (program : Program) : Prop :=
  ∀ entry ∈ catalog, entry.isLive = true →
    ∃ functionInstance ∈ program.functionInstances, functionInstance.id.function = entry.functionId

/-- Every generated function instance carries the identity of exactly one live catalog entry. This is the
direction that forbids an unproved region — including an un-accounted compiler/runtime routine —
hiding inside a "complete" proof. -/
def everyFunctionInstanceIsCataloged (program : Program) : Prop :=
  ∀ functionInstance ∈ program.functionInstances,
    ∃ entry ∈ catalog, entry.isLive = true ∧ functionInstance.id.function = entry.functionId

/-- No excluded routine has any generated function instance: the exclusions are honest. -/
def excludedRoutinesAbsent (program : Program) : Prop :=
  ∀ functionInstance ∈ program.functionInstances, ∀ excluded ∈ excludedRoutines,
    functionInstance.id.function ≠ excluded.functionId

/-- Each catalog identity is unique, so one function instance cannot be counted against two entries. -/
def catalogIdentitiesDistinct : Prop :=
  ∀ i j, (hi : i < catalog.size) → (hj : j < catalog.size) →
    (catalog[i]).functionId = (catalog[j]).functionId → i = j

/-- Every generated function instance is matched by exactly one live catalog entry, and every function instance
identity is distinct: one convenient function instance cannot satisfy several entries, and a duplicated
function instance cannot slip through.

Uniqueness of the matched entry is `catalogEntryFor` returning `some` (a single entry from
`Array.find?`) together with `catalogIdentitiesDistinct`, which rules out a second entry with the
same identity. -/
def instancesDispatchUniquely (program : Program) : Prop :=
  program.functionInstanceIdsDistinct ∧
  catalogIdentitiesDistinct ∧
  ∀ functionInstance ∈ program.functionInstances,
    ∃ entry, catalogEntryFor functionInstance.id.function = some entry

/-- Every required `readArray` width is present as a live catalog entry. -/
def readArrayWidthsPresent : Prop :=
  ∀ width ∈ requiredReadArrayWidths,
    ∃ entry ∈ catalog, entry.tag = .readArray ∧ readArrayWidthOf entry.functionId = width

/-- The full coverage obligation: both matching directions, honest exclusions, unique dispatch, the
required specializations, and a defect-free extraction. -/
def coverage (program : Program) : Prop :=
  everyRoutineHasFunctionInstance program ∧
  everyFunctionInstanceIsCataloged program ∧
  excludedRoutinesAbsent program ∧
  instancesDispatchUniquely program ∧
  catalogIdentitiesDistinct ∧
  readArrayWidthsPresent ∧
  extractionDefectFree program
where
  /-- The extraction reported no unresolved attribution. -/
  extractionDefectFree (program : Program) : Prop := program.defects = #[]

/-! ## The catalog's semantic obligations -/

/-- Every claim the catalog makes about the decoder's meaning, as one conjunction.

`sourceShapedDecodeAgreesWithOracle` and `catalogGroundsInSpec` carry the root theorem; the rest
bound which errors each group can produce and record the known asymmetries. -/
def catalogSemanticObligations : Prop :=
  sourceShapedDecodeAgreesWithOracle ∧
  catalogGroundsInSpec ∧
  retryTailNeverSchemaValid ∧
  v3ShapeExcludesCanonicalV4 ∧
  sourceShapedContainersAgreeWithOracle ∧
  canonicalOffsetsCharacterization ∧
  zeroFirstOffsetAliasRejected ∧
  bytesAtSucceedsIffFits ∧
  readOffsetIsWidenedReadU32 ∧
  leafReadsOnlyFailInvalid ∧
  collectionsNeverUnknownFork ∧
  emptyByteListListStillAllocates ∧
  onlyForkConfigRaisesUnknownFork ∧
  fixedContainersNeverAllocate ∧
  allocatorVtableEntriesAreConstant ∧
  outOfMemoryUnreachableBelowBound ∧
  meaningEmptyIsNone ∧
  meaningTwentyFourIsSome ∧
  meaningOtherLengthIsInvalid ∧
  meaningNeverForkOrMemory

/-- The two known asymmetries between the binary and the oracle, conjoined so the navigation surfaces
them rather than letting them read as oversights. -/
def knownDivergences : Prop :=
  forkErrorOrderingDiffers ∧ ereGateDivergesAboveU32

end BinaryFv.SSZ.Zesu.Contracts
