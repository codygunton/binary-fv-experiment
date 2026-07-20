import BinaryFv.SSZ.Zesu.Contracts.Runtime

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-!
# The semantic-routine catalog

The complete enumeration of routines the proof must cover, and the coverage obligations that make
"complete" checkable rather than asserted.

Membership is pinned to the pinned source: every entry below names a routine in
`src/stateless/stateless/ssz_raw.zig` or `src/zkvm/raw_decoder_root.zig`, at the revision recorded
in `sourceFile`. The five test-only helpers (`putU32`, `putU64`, `makeMinimalV4`, and the two
`test` blocks' bodies) are excluded because they are not present in the `ReleaseSmall` object.

The catalog is *identity* only. It carries no address, no instruction word, and no symbol — an entry
is an `InstanceId`, and the generated Elfling program is what binds each one to canonical-ELF ranges.
That separation is what `coverage` below checks.
-/

/-- The pinned decoder source file.

`contentHash` is left as the empty string here and supplied by the generator: this module is
handwritten and must not embed a build-dependent digest, or editing a proof would require editing a
hash. The extraction row fills it in and Lean checks it. -/
def decoderSourceFile : SourceFile :=
  { path := "src/stateless/stateless/ssz_raw.zig", contentHash := "" }

def rootSourceFile : SourceFile :=
  { path := "src/zkvm/raw_decoder_root.zig", contentHash := "" }

/-- A cataloged routine: its source identity and which semantic group it belongs to. -/
inductive RoutineGroup where
  | entry
  | container
  | collection
  | option
  | leaf
  | runtime
deriving DecidableEq, Repr, Inhabited

structure CatalogEntry where
  name : String
  file : SourceFile
  group : RoutineGroup
  /-- Compile-time specialization, for routines emitted once per `comptime` instantiation. -/
  specialization : Array String := #[]
  /-- Whether the routine allocates. Recorded here so a contract that denies allocation can be
  cross-checked against the catalog rather than only against its own prose. -/
  allocates : Bool
  /-- Whether the routine carries a symbol in the canonical ELF. Annotation only: 97% of the decoder
  object is symbol-less, so this must never be used to define a proof region. -/
  hasSymbol : Bool
deriving Repr, Inhabited

private def d (name : String) (group : RoutineGroup) (allocates : Bool)
    (specialization : Array String := #[]) : CatalogEntry :=
  { name := name, file := decoderSourceFile, group := group
    specialization := specialization, allocates := allocates, hasSymbol := false }

/--
The complete catalog: 33 entries.

Every entry has handwritten `meaning`, `pre`, `post`, `contract`, and `correctnessClaim` definitions
in the corresponding `Contracts/` module.
-/
def catalog : Array CatalogEntry := #[
  -- Entry / top level
  { name := "zesu_decode_raw", file := rootSourceFile, group := .entry
    allocates := true, hasSymbol := true },
  d "decode" .entry true,
  d "decodeRaw" .entry true,
  -- Containers
  d "decodeNewPayloadRequest" .container true,
  d "decodeExecutionPayload" .container true,
  d "decodeExecutionRequests" .container true,
  d "decodeExecutionWitness" .container true,
  d "decodeChainConfig" .container false,
  d "decodeForkConfig" .container false,
  d "decodeForkActivation" .container false,
  -- Options
  d "decodeOptionalU64" .option false,
  d "decodeOptionalBlobSchedule" .option false,
  -- Collections
  d "decodeVersionedHashes" .collection true,
  d "decodeWithdrawals" .collection true,
  d "decodeDepositRequests" .collection true,
  d "decodeWithdrawalRequests" .collection true,
  d "decodeConsolidationRequests" .collection true,
  d "decodePublicKeys" .collection true,
  d "decodeByteListList" .collection true,
  -- Leaves
  d "requireCanonicalOffsets" .leaf false,
  d "requireU32Length" .leaf false,
  d "readOffset" .leaf false,
  d "readU32" .leaf false,
  d "readU64" .leaf false,
  d "readU256" .leaf false,
  d "readArray" .leaf false #["N"],
  d "bytesAt" .leaf false,
  d "hasExactErePrefix" .leaf false,
  -- Runtime
  { name := "zesu_raw_alloc", file := rootSourceFile, group := .runtime
    allocates := true, hasSymbol := true },
  { name := "memcpy", file := rootSourceFile, group := .runtime
    allocates := false, hasSymbol := true },
  { name := "memmove", file := rootSourceFile, group := .runtime
    allocates := false, hasSymbol := true },
  { name := "zesu_raw_result", file := rootSourceFile, group := .runtime
    allocates := false, hasSymbol := true },
  { name := "zesu_raw_error", file := rootSourceFile, group := .runtime
    allocates := false, hasSymbol := true }
]

/-- Routines deliberately excluded, with the reason, so an omission cannot pass for an oversight. -/
def excludedTestOnly : Array String :=
  #["putU32", "putU64", "makeMinimalV4"]

/-!
## Coverage obligations
-/

/-- Every cataloged routine is matched by at least one generated occurrence in the Elfling program.

This is the direction that catches a routine the generator failed to find. -/
def everyRoutineHasInstance (program : Program) : Prop :=
  ∀ entry ∈ catalog,
    ∃ instance_ ∈ program.instances,
      instance_.id.function.declaration.qualifiedName = entry.name

/-- Every generated occurrence corresponds to a cataloged routine.

This is the direction that catches a region of the binary nobody wrote a contract for — the failure
mode that would otherwise let an unproved code path hide inside a "complete" proof. -/
def everyInstanceIsCataloged (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances,
    ∃ entry ∈ catalog,
      instance_.id.function.declaration.qualifiedName = entry.name

/-- The extraction reported no unresolved attribution.

`AttributionDefect` values are uncovered addresses, overlapping ownership, ambiguous DWARF
attribution, and unmapped regions. Requiring the array to be empty is what stops any of them being
silently discarded. -/
def extractionDefectFree (program : Program) : Prop :=
  program.defects = #[]

/-- Full coverage: both directions plus a defect-free extraction. -/
def coverage (program : Program) : Prop :=
  everyRoutineHasInstance program ∧
  everyInstanceIsCataloged program ∧
  extractionDefectFree program

/-!
## The catalog's semantic obligations

Gathered in one place so the root navigation can point at a single name.
-/

/-- Every claim the catalog makes about the decoder's meaning, as one conjunction.

`sourceShapedDecodeAgreesWithOracle` and `catalogGroundsInSpec` are the two that carry the root
theorem; the rest bound which errors each group can produce and record the two known asymmetries. -/
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

/-- The two known asymmetries between the binary and the oracle.

Both are *true* statements of divergence, not obligations to discharge. They are conjoined here so
that the navigation scaffold surfaces them rather than letting them read as oversights: the first is
masked by `retryTailNeverSchemaValid`, and the second is excluded by `rootComplianceScope`. -/
def knownDivergences : Prop :=
  forkErrorOrderingDiffers ∧ ereGateDivergesAboveU32

end BinaryFv.SSZ.Zesu.Contracts
