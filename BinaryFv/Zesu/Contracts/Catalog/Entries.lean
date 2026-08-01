import BinaryFv.Zesu.Contracts.Runtime
import BinaryFv.Zesu.Contracts.ExportedDecoder

namespace BinaryFv.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-!
# Source-function contract entries

The complete enumeration of source functions the proof must cover, each carrying a stable, address-free
`FunctionId` (pinned source file, qualified name, and concrete specialization — **no** declaration
line or content hash: those are validated provenance, not identity), the `ContractTag` that selects
its handwritten contract, and a `Presence` classification.

Membership is pinned to source: every catalog `FunctionId` names a source function in
`src/stateless/stateless/ssz_raw.zig`, `src/zkvm/raw_decoder_root.zig`, `src/zkvm/raw_allocator.zig`,
or the freestanding RV64 runtime, and every excluded source function carries a machine-checkable reason.
Nothing here carries an address, an instruction word, or a symbol — an entry is identity plus its
contract selector, and the generated Elfling program is what binds each identity to canonical-ELF
ranges.

The qualified-name convention is the Zig module-qualified form, which the extraction row reconciles
against DWARF. The declaration line and the source content hash are **not** part of the identity;
they are provenance carried by generated occurrences and checked — the hash for equality against
`pinnedSourceManifest`, the line for `> 0` — by `sourceProvenanceRecorded`.
-/

/-! ## Source files

Each source function's declaring source file, by path only. Content hashes and declaration lines are
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

/-- The handwritten source function groups. -/
inductive SourceFunctionGroup where
  | entry | container | collection | option | leaf | runtime
deriving DecidableEq, Repr, Inhabited

/-- The dispatch key: one constructor per handwritten contract. This is what turns "this instance's
identity" into "this instance's `correctnessClaim`", so the per-instance obligation is a total
function of the catalog rather than a hand-maintained list of unrelated propositions. -/
inductive ContractTag where
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

/-- Why a source function is excluded from the cataloged semantic proof — either it has no live
occurrence in the canonical binary, or it is reachable emitted glue whose net effect is captured
elsewhere. The last two are the row-2 reachable-but-excluded categories, shared with the generated
Elfling reachable-partition taxonomy (stack-integration point). -/
inductive ExclusionReason where
  /-- Not compiled into the `ReleaseSmall` object (a test-only helper). -/
  | testOnly
  /-- Present in source but not reachable from `zesu_decode_raw`. -/
  | unreachable
  /-- Reachable `std`/`mem`/`math` implementation emitted as its own source function (allocator vtable), whose
  net behavior is captured by the cataloged allocator contracts. -/
  | reachableStdlib
  /-- Reachable `*.deinit` error-path cleanup; the freestanding zkVM's allocator free is a no-op, so it
  never changes the accept/reject outcome. -/
  | reachableCleanupNoOp
deriving DecidableEq, Repr, Inhabited

/-- Whether a cataloged source function is expected to occur in the canonical program. -/
inductive Presence where
  /-- Appears as one or more generated occurrences (emitted or inlined). -/
  | live
  /-- Has no occurrence, for the given reason. -/
  | absent (reason : ExclusionReason)
deriving DecidableEq, Repr, Inhabited

/-- A cataloged source function: full address-free identity, its contract selector, and its expected
presence. -/
structure CatalogEntry where
  functionId : FunctionId
  group : SourceFunctionGroup
  tag : ContractTag
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

/-- A live decoder-source function with no specialization. -/
private def dec (name : String) (group : SourceFunctionGroup) (tag : ContractTag)
    (allocates : Bool) : CatalogEntry :=
  { functionId := fid decoderSourceFile ("ssz_raw." ++ name)
    group := group, tag := tag, allocates := allocates, hasSymbol := false, presence := .live }

/-- A live `readArray` specialization: same source function, distinct concrete width. -/
private def readArrayEntry (width : Nat) : CatalogEntry :=
  { functionId := fid decoderSourceFile "ssz_raw.readArray" #[toString width]
    group := .leaf, tag := .readArray, allocates := false, hasSymbol := false, presence := .live }

/-- The canonical entry source function's identity: the exported `zesu_decode_raw` wrapper. -/
def zesuDecodeRawFunctionId : FunctionId :=
  fid rootSourceFile "raw_decoder_root.zesu_decode_raw"

/-! ## The catalog -/

/--
The complete catalog of live source functions.

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

/-- Source functions present in source but with no live occurrence in the canonical program, each with a
machine-checkable reason. Coverage requires that none of these is matched by a generated instance. -/
def excludedSourceFunctions : Array CatalogEntry :=
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



end BinaryFv.Zesu.Contracts
