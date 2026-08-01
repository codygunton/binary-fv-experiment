import BinaryFv.Zesu.Contracts.Catalog.Dispatch

namespace BinaryFv.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-! ## Full-identity matching -/

/-- The catalog entry whose full `FunctionId` equals `function`, if any. Matching is by the whole
identity — file, qualified name, and specialization — so a `readArray[32]` occurrence cannot be
satisfied by the `readArray[20]` contract. -/
def catalogEntryFor (function : FunctionId) : Option CatalogEntry :=
  catalog.find? fun entry => decide (entry.functionId = function)

/-- An excluded source function matching `function`, if any. -/
def excludedEntryFor (function : FunctionId) : Option CatalogEntry :=
  excludedSourceFunctions.find? fun entry => decide (entry.functionId = function)

/-! ## Coverage and uniqueness obligations -/

/-- Every live catalog entry has at least one generated occurrence carrying its exact identity. -/
def everySourceFunctionHasInstance (program : Program) : Prop :=
  ∀ entry ∈ catalog, entry.isLive = true →
    ∃ instance_ ∈ program.instances, instance_.id.function = entry.functionId

/-- Every generated occurrence carries the identity of exactly one live catalog entry. This is the
direction that forbids an unproved region — including an un-accounted compiler/runtime source function —
hiding inside a "complete" proof. -/
def everyInstanceIsCataloged (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances,
    ∃ entry ∈ catalog, entry.isLive = true ∧ instance_.id.function = entry.functionId

/-- No excluded source function has any generated occurrence: the exclusions are honest. -/
def excludedSourceFunctionsAbsent (program : Program) : Prop :=
  ∀ instance_ ∈ program.instances, ∀ excluded ∈ excludedSourceFunctions,
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
  everySourceFunctionHasInstance program ∧
  everyInstanceIsCataloged program ∧
  excludedSourceFunctionsAbsent program ∧
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

/-! Compatibility vocabulary for the function-instance data-model migration. -/

abbrev everySourceFunctionHasFunctionInstance := everySourceFunctionHasInstance
abbrev everyFunctionInstanceIsCataloged := everyInstanceIsCataloged
abbrev functionInstancesDispatchUniquely := instancesDispatchUniquely

end BinaryFv.Zesu.Contracts

