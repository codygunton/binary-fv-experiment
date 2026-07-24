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
they are provenance carried by generated occurrences and checked — the hash for equality against
`pinnedSourceManifest`, the line for `> 0` — by `sourceProvenanceRecorded`.
-/

/-! ## Source files

Each routine's declaring source file, by path only. Content hashes and declaration lines are
validated *provenance* (`DeclarationProvenance`), carried by generated occurrences and checked
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

`sourceProvenanceRecorded` checks every occurrence's recorded `declProvenance.sourceFileHash` for
*equality* with the manifest entry for its file, so provenance is validated against the pin rather
than merely being non-empty. If the pinned revision (or the runtime source) changes, this manifest
must change with it — that coupling is exactly what provenance is for. -/
def pinnedSourceManifest : List (SourceFile × String) :=
  [ (decoderSourceFile, "ea5a1b36f72c888a0bcb73f2ea1f2bf7ebf00c63c6460c84015d0f6783a1d131"),
    (rootSourceFile, "53afe7a5c7c70122a3e2a9f9673a3415a50579a2ed11a21d9dd1c839e0c18a5e"),
    (allocatorSourceFile, "c9e9457e45a3827729adb1921e07ba31997a536dc8f719e04d2d0d6f4c742591"),
    (runtimeSourceFile, "5f80e272e96ccb30ca109bb77c9a78c9769bfd6b54ac2d7f712d3c2deb9b8235") ]

/-- The pinned content hash for a source file, if it is one of the manifest files; `none` otherwise
(which makes `sourceProvenanceRecorded` reject an occurrence attributed to an off-manifest file). -/
def pinnedSourceHash (file : SourceFile) : Option String :=
  (pinnedSourceManifest.find? (fun entry => decide (entry.1 = file))).map (·.2)

/-! ## Identity and dispatch -/

/-- The handwritten routine groups. -/
inductive RoutineGroup where
  | entry | container | collection | option | leaf | runtime
deriving DecidableEq, Repr, Inhabited

/-- The dispatch key: one constructor per handwritten contract. This is what turns "this instance's
identity" into "this instance's `correctnessClaim`", so the per-instance obligation is a total
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

/-- The tag's constructor name, so a generated artifact can carry the dispatch key as a string
without importing the handwritten catalog and the proof layer can still check the two agree. -/
def RoutineTag.name : RoutineTag → String
  | .zesuDecodeRaw => "zesuDecodeRaw" | .decode => "decode" | .decodeRaw => "decodeRaw"
  | .newPayloadRequest => "newPayloadRequest" | .executionPayload => "executionPayload"
  | .executionRequests => "executionRequests" | .executionWitness => "executionWitness"
  | .chainConfig => "chainConfig" | .forkConfig => "forkConfig"
  | .forkActivation => "forkActivation"
  | .optionalU64 => "optionalU64" | .optionalBlobSchedule => "optionalBlobSchedule"
  | .versionedHashes => "versionedHashes" | .withdrawals => "withdrawals"
  | .depositRequests => "depositRequests" | .withdrawalRequests => "withdrawalRequests"
  | .consolidationRequests => "consolidationRequests" | .publicKeys => "publicKeys"
  | .byteListList => "byteListList"
  | .requireCanonicalOffsets => "requireCanonicalOffsets" | .requireU32Length => "requireU32Length"
  | .readOffset => "readOffset" | .readU32 => "readU32" | .readU64 => "readU64"
  | .readU256 => "readU256" | .readArray => "readArray" | .bytesAt => "bytesAt"
  | .hasExactErePrefix => "hasExactErePrefix"
  | .rawAlloc => "rawAlloc" | .memcpy => "memcpy" | .memmove => "memmove"
  | .rawResult => "rawResult" | .rawError => "rawError"
  | .allocatorAlloc => "allocatorAlloc" | .allocatorResize => "allocatorResize"
  | .allocatorRemap => "allocatorRemap" | .allocatorFree => "allocatorFree"
  | .allocatorCtor => "allocatorCtor"

/-- Distinct tags have distinct names, so matching a generated row's tag string against
`RoutineTag.name` identifies exactly one tag. -/
theorem RoutineTag.name_injective : ∀ a b : RoutineTag, a.name = b.name → a = b := by
  intro a b h; revert h; cases a <;> cases b <;> simp [RoutineTag.name]

/-- Why a source routine is excluded from the cataloged semantic proof — either it has no live
occurrence in the canonical binary, or it is reachable emitted glue whose net effect is captured
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
  /-- Appears as one or more generated occurrences (emitted or inlined). -/
  | live
  /-- Has no occurrence, for the given reason. -/
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

/-- The catalog entry is expected to have live occurrences. -/
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
`satisfiable` definitions, and its `tag` selects them in `instanceObligation`. `readArray` appears
once per concrete width the decoder instantiates (20, 32, 48, 65, 96, 256), so a generated
occurrence is matched by full identity, not by the bare name.
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

/-- Routines present in source but with no live occurrence in the canonical program, each with a
machine-checkable reason. Coverage requires that none of these is matched by a generated instance. -/
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

/-- The width a generated `readArray` occurrence carries, parsed from its specialization. -/
def readArrayWidthOf (function : FunctionId) : Nat :=
  ((function.specialization[0]?).bind String.toNat?).getD 0

/-! ## Typed per-instance dispatch -/

/--
Everything a per-instance obligation needs beyond the instance itself: the pinned environment, the
allocator heap, the status slot, and the container/RawV4 result representations.

Bundling these keeps `instanceObligation` a total function while letting each container assert its own
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

/-- One routine's handwritten contract with its argument and outcome types packaged alongside it.

Heterogeneity is the whole reason this exists. The decoder's leaves produce
`Except SszDecodeError _` over half a dozen argument records, while the exported wrapper produces
`DecodeCallOutcome`; there is no single `OccurrenceContract Args Outcome` the catalog could return.
Packaging the types lets **one** total dispatch select the real typed contract, after which the
closed and the local obligation are both formed from that same selection — so they cannot drift, and
neither can be stated for a contract the other does not use. Erasure to `Prop` happens only after a
branch has chosen its contract, never before. -/
structure TaggedContract where
  Args : Type
  Outcome : Type
  contract : OccurrenceContract Args Outcome

/--
The typed contract a generated occurrence's routine `tag` selects.

This is the single point at which an occurrence's identity becomes a handwritten contract. A routine
whose contract is source-shaped is projected through `FunctionContract.toOccurrence`; the exported
wrapper, whose outcome is richer than `Except`, supplies its `OccurrenceContract` directly. -/
def routineContract (p : ContractParams) (function : FunctionId) (tag : RoutineTag) :
    TaggedContract :=
  match tag with
  | .zesuDecodeRaw =>
      ⟨_, _, occurrenceZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4
                DecoderGlobalsModel.fresh⟩
  | .decode => ⟨_, _, (contractDecode p.env p.repRawV4).toOccurrence⟩
  | .decodeRaw => ⟨_, _, (contractDecodeRaw p.env p.repRawV4).toOccurrence⟩
  | .newPayloadRequest => ⟨_, _, (contractNewPayloadRequest p.env p.repNewPayloadRequest).toOccurrence⟩
  | .executionPayload => ⟨_, _, (contractExecutionPayload p.env p.repExecutionPayload).toOccurrence⟩
  | .executionRequests => ⟨_, _, (contractExecutionRequests p.env p.repExecutionRequests).toOccurrence⟩
  | .executionWitness => ⟨_, _, (contractExecutionWitness p.env p.repExecutionWitness).toOccurrence⟩
  | .chainConfig => ⟨_, _, (contractChainConfig p.env p.repChainConfig).toOccurrence⟩
  | .forkConfig => ⟨_, _, (contractForkConfig p.env p.repForkConfig).toOccurrence⟩
  | .forkActivation => ⟨_, _, (contractForkActivation p.env p.repForkActivation).toOccurrence⟩
  | .optionalU64 => ⟨_, _, (contractOptionalU64 p.env).toOccurrence⟩
  | .optionalBlobSchedule => ⟨_, _, (contractOptionalBlobSchedule p.env).toOccurrence⟩
  | .versionedHashes => ⟨_, _, (contractVersionedHashes p.env).toOccurrence⟩
  | .withdrawals => ⟨_, _, (contractWithdrawals p.env).toOccurrence⟩
  | .depositRequests => ⟨_, _, (contractDepositRequests p.env).toOccurrence⟩
  | .withdrawalRequests => ⟨_, _, (contractWithdrawalRequests p.env).toOccurrence⟩
  | .consolidationRequests => ⟨_, _, (contractConsolidationRequests p.env).toOccurrence⟩
  | .publicKeys => ⟨_, _, (contractPublicKeys p.env).toOccurrence⟩
  | .byteListList => ⟨_, _, (contractByteListList p.env).toOccurrence⟩
  | .requireCanonicalOffsets => ⟨_, _, (contractRequireCanonicalOffsets p.env).toOccurrence⟩
  | .requireU32Length => ⟨_, _, (contractRequireU32Length p.env).toOccurrence⟩
  | .readOffset => ⟨_, _, (contractReadOffset p.env).toOccurrence⟩
  | .readU32 => ⟨_, _, (contractReadU32 p.env).toOccurrence⟩
  | .readU64 => ⟨_, _, (contractReadU64 p.env).toOccurrence⟩
  | .readU256 => ⟨_, _, (contractReadU256 p.env).toOccurrence⟩
  | .readArray => ⟨_, _, (contractReadArray p.env (readArrayWidthOf function)).toOccurrence⟩
  | .bytesAt => ⟨_, _, (contractBytesAt p.env).toOccurrence⟩
  | .hasExactErePrefix => ⟨_, _, (contractHasExactErePrefix p.env).toOccurrence⟩
  | .rawAlloc => ⟨_, _, (contractAlloc p.env p.heap).toOccurrence⟩
  | .memcpy => ⟨_, _, (contractMemcpy p.env).toOccurrence⟩
  | .memmove => ⟨_, _, (contractMemmove p.env).toOccurrence⟩
  | .rawResult => ⟨_, _, (contractRawResult p.env p.globals p.resultBuffer).toOccurrence⟩
  | .rawError => ⟨_, _, (contractRawError p.env p.globals).toOccurrence⟩
  | .allocatorAlloc => ⟨_, _, (contractAllocatorAlloc p.env p.heap).toOccurrence⟩
  | .allocatorResize => ⟨_, _, (contractAllocatorResize p.env).toOccurrence⟩
  | .allocatorRemap => ⟨_, _, (contractAllocatorRemap p.env).toOccurrence⟩
  | .allocatorFree => ⟨_, _, (contractAllocatorFree p.env).toOccurrence⟩
  | .allocatorCtor => ⟨_, _, (contractAllocatorCtor p.env).toOccurrence⟩

/-- The run one occurrence supplies to whoever splices it, at this contract's own types.

Every component the splice needs is present and typed: the arguments it was called with, its step
bound, a confined entered run of *exactly* `used` machine steps from its generated entry to one of
its generated exits, and its exit binding at the outcome its `meaning` prescribes. Nothing here is a
bare state relation — the binding handoff survives into the summary rather than being erased before
it is proved. -/
def TaggedContract.summary (tc : TaggedContract) (region exit : BitVec 64 → Prop)
    (entry : BitVec 64) (fromStep used : Nat) (s s' : BinaryFv.RiscV.State) : Prop :=
  ∃ args : tc.Args,
    tc.contract.binding.entry args s ∧
    used ≤ tc.contract.binding.stepBound args ∧
    EnteredFunctionTrace region exit entry fromStep used s s' ∧
    tc.contract.binding.exit args (tc.contract.spec.meaning args) s s'

/-! ## Where an occurrence executes

Two address sets, both computed from the generated program, decide what any per-occurrence obligation
can possibly say. See `BinaryFv.Binary.Elfling.Program.ownedRanges`/`extentRanges` for the data and
`InstanceExecutionPcs` for why the distinction is forced rather than chosen. -/

/-- What an occurrence's *local* proof may retire step by step: its own code plus the uncataloged
routines it absorbs. -/
def instanceOwnPcs (program : Program) (instance_ : FunctionInstance) : BitVec 64 → Prop :=
  RegionPcs (Program.ownedRanges program instance_)

/-- The addresses an occurrence reaches: the transfer-graph extent of everything it may call or
inline. Supplied to the closed obligation as its `reached` set. -/
def instanceReachedPcs (program : Program) (instance_ : FunctionInstance) : BitVec 64 → Prop :=
  RegionPcs (Program.extentRanges program instance_)

/-- Where an occurrence's execution may sit: its own regions together with everything it reaches. -/
def instanceExecutionPcs (program : Program) (instance_ : FunctionInstance) : BitVec 64 → Prop :=
  InstanceExecutionPcs instance_ (instanceReachedPcs program instance_)

/-- The entry PC of a generated occurrence, as a machine word. Read off the occurrence, never
existentially chosen. -/
def instanceEntryWord (instance_ : FunctionInstance) : BitVec 64 :=
  BitVec.ofNat 64 instance_.entryPc

/-- The exit predicate of a generated occurrence: exactly its generated exit PCs. -/
def instanceExitPred (instance_ : FunctionInstance) (pc : BitVec 64) : Prop :=
  instance_.isExit pc.toNat

/--
The **closed** correctness obligation a single generated occurrence owes, selected by its routine
`tag`: it implements its contract, confined to where it executes, entering at its generated entry and
stopping at a generated exit.

The entry PC, exit predicate and reachable address set all come from generated data, never from an
existential, so a proof cannot pick a convenient entry, exit, or confinement. `reached` is the
occurrence's transfer-graph extent — see `InstanceExecutionPcs` for why an obligation confined to the
occurrence's own regions alone would be false for every occurrence that calls out. -/
def routineObligation (p : ContractParams) (instance_ : FunctionInstance)
    (reached : BitVec 64 → Prop) (tag : RoutineTag) : Prop :=
  (routineContract p instance_.id.function tag).contract.ImplementsInstance instance_ reached
    (instanceEntryWord instance_) (instanceExitPred instance_)

/--
The **local** obligation a single generated occurrence owes: it implements *the same* contract
against summaries of the occurrences below it, retiring its own steps only inside what it owns.

This is the proposition the local-proof campaign discharges once per occurrence, and the one
`LocalContractAssumptions` quantifies. It is not an implication between closed obligations: its
premise content is the admitted `childSummary` relation, its conclusion is an `EnteredScopedTrace`,
and the closed obligation appears nowhere in it. -/
def routineLocalObligation (p : ContractParams) (instance_ : FunctionInstance)
    (own : BitVec 64 → Prop)
    (childSummary : InstanceId → Nat → Nat → BinaryFv.RiscV.State → BinaryFv.RiscV.State → Prop) (tag : RoutineTag) : Prop :=
  (routineContract p instance_.id.function tag).contract.LocallyImplementsInstance own
    (instanceEntryWord instance_) (instanceExitPred instance_) childSummary

/-- The local and closed obligations of an occurrence are formed from **one** contract selection, so
composing the first into the second is a statement about the same contract. This is the step
`global_of_local` performs per occurrence; `hsub` and `hcompose` are the generated geometry and the
discharged child summaries. -/
theorem routineObligation_of_local {p : ContractParams} {instance_ : FunctionInstance}
    {own reached : BitVec 64 → Prop}
    {childSummary : InstanceId → Nat → Nat → BinaryFv.RiscV.State → BinaryFv.RiscV.State → Prop} {tag : RoutineTag}
    (hsub : ∀ pc, own pc → InstanceExecutionPcs instance_ reached pc)
    (hcompose : SummariesCompose (InstanceExecutionPcs instance_ reached)
      (instanceExitPred instance_) childSummary)
    (hlocal : routineLocalObligation p instance_ own childSummary tag) :
    routineObligation p instance_ reached tag :=
  OccurrenceContract.LocallyImplementsInstance.toImplementsInstance hsub hcompose hlocal

/-- The satisfiability obligation for a routine's contract, selected by the same `tag`.

Aggregating these through the dispatch is what makes anti-vacuity uniform: every live instance's
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
identity — file, qualified name, and specialization — so a `readArray[32]` occurrence cannot be
satisfied by the `readArray[20]` contract. -/
def catalogEntryFor (function : FunctionId) : Option CatalogEntry :=
  catalog.find? fun entry => decide (entry.functionId = function)

/-- An excluded routine matching `function`, if any. -/
def excludedEntryFor (function : FunctionId) : Option CatalogEntry :=
  excludedRoutines.find? fun entry => decide (entry.functionId = function)

/-! ## Coverage and uniqueness obligations -/

/-- Every live catalog entry has at least one generated occurrence carrying its exact identity. -/
def everyRoutineHasInstance (program : Program) : Prop :=
  ∀ entry ∈ catalog, entry.isLive = true →
    ∃ instance_ ∈ program.instances, instance_.id.function = entry.functionId

/-- Every generated occurrence carries the identity of exactly one live catalog entry. This is the
direction that forbids an unproved region — including an un-accounted compiler/runtime routine —
hiding inside a "complete" proof. -/
def everyInstanceIsCataloged (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances,
    ∃ entry ∈ catalog, entry.isLive = true ∧ instance_.id.function = entry.functionId

/-- No excluded routine has any generated occurrence: the exclusions are honest. -/
def excludedRoutinesAbsent (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances, ∀ excluded ∈ excludedRoutines,
    instance_.id.function ≠ excluded.functionId

/-- Each catalog identity is unique, so one occurrence cannot be counted against two entries. -/
def catalogIdentitiesDistinct : Prop :=
  ∀ i j, (hi : i < catalog.size) → (hj : j < catalog.size) →
    (catalog[i]).functionId = (catalog[j]).functionId → i = j

/-- Every generated occurrence is matched by exactly one live catalog entry, and every occurrence
identity is distinct: one convenient occurrence cannot satisfy several entries, and a duplicated
occurrence cannot slip through.

Uniqueness of the matched entry is `catalogEntryFor` returning `some` (a single entry from
`Array.find?`) together with `catalogIdentitiesDistinct`, which rules out a second entry with the
same identity. -/
def instancesDispatchUniquely (program : Program) : Prop :=
  program.instanceIdsDistinct ∧
  catalogIdentitiesDistinct ∧
  ∀ instance_ ∈ program.instances,
    ∃ entry, catalogEntryFor instance_.id.function = some entry

/-- Every required `readArray` width is present as a live catalog entry. -/
def readArrayWidthsPresent : Prop :=
  ∀ width ∈ requiredReadArrayWidths,
    ∃ entry ∈ catalog, entry.tag = .readArray ∧ readArrayWidthOf entry.functionId = width

/-- The full coverage obligation: both matching directions, honest exclusions, unique dispatch, the
required specializations, and a defect-free extraction. -/
def coverage (program : Program) : Prop :=
  everyRoutineHasInstance program ∧
  everyInstanceIsCataloged program ∧
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
