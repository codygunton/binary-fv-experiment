/-!
# Row C: types for the SCALED per-occurrence production-ELF validation

Compact, deterministic per-occurrence evidence (`OccScaleEvidence`) and the eight generic check results
(`ScaleChecks`) for the scaled Row C validator. One `OccScaleEvidence` per occurrence in `program.json`
carries only the reduced facts the checker needs — never the raw multi-MB trace — captured from the
UNCHANGED production `zesu-ssz` ELF under pinned QEMU. Each check is an `Option Bool`: `some true` pass,
`some false` fail, `none` an EXPLICIT gap (coverage or check not evaluable), never silently a pass.

This is a validation-namespace module: diagnostic/regression evidence, NEVER imported by the theorem
graph (enforced by the validation-import guard).
-/

namespace BinaryFv.Zesu.Validation

/-- The compact per-occurrence facts reduced from the production trace (observed facts only). -/
structure OccScaleEvidence where
  /-- occurrence index in `program.json`. -/
  index : Nat
  /-- fully-qualified inlined name (for readability / reports). -/
  qualified : String
  /-- the source-function short name (last dotted component). -/
  sourceFunction : String
  /-- the arm whose trace covers this occurrence (`""` if uncovered). -/
  arm : String
  /-- declared Row A entry PC. -/
  entryPc : Nat
  /-- whether the occurrence's region executed under the chosen arm. -/
  covered : Bool
  /-- first in-region PC executed (0 if uncovered). -/
  firstInRegion : Nat
  /-- max instructions in one invocation (span between successive `entryPc` executions). -/
  maxInsnPerInvocation : Nat
  /-- the occurrence's declared CFG edges (generator: attributed from DEEPEST-owned PCs). -/
  declaredEdges : List (Nat × Nat)
  /-- distinct executed transfers whose SOURCE is a PC this occurrence owns (dynamic returns and
  unresolved indirect calls excluded — those are validated against `exits`). -/
  executedOwnedEdges : List (Nat × Nat)
  /-- the declared exit PCs. -/
  exits : List Nat
  /-- owned PCs from which execution actually left the occurrence's regions. -/
  leavingSources : List Nat
  /-- owned PCs whose transfer is dynamic (ret / unresolved indirect call). -/
  dynamicTransferSources : List Nat
  /-- the resolved contract step bound, or `none` if input-dependent/unknown (an explicit gap). -/
  stepBound : Option Nat
  /-- whether the source sourceFunction allocates (bumps the allocator cursor). -/
  allocates : Bool
  /-- meaning-tie family: "scalarLE" | "offset" | "slice" | other (structural → gap). -/
  meaningTieKind : String
  /-- true when the store set is summarized (raw mem primitives: memcpy/memmove). -/
  storesSummarized : Bool
  /-- deterministic NON-STACK in-region store addresses (fixed vaddrs); the checker RE-CLASSIFIES each.
  Stack addresses are environment-dependent and are summarized via `hadStackStore` instead. -/
  inRegionStores : List Nat
  /-- whether any in-region store landed on the stack (benign; not carried as an address). -/
  hadStackStore : Bool
  /-- pre-classified distinct write classes — used only when `storesSummarized` (raw primitives). -/
  storeClasses : List String
  /-- a value both loaded from the input and stored (scalar carried input→result). -/
  scalarCarried : Bool
  /-- a stored value that is an input-region pointer (slice view). -/
  storeHasInputPtr : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The eight generic per-occurrence checks; `none` is an EXPLICIT gap (never counted as a pass). -/
structure ScaleChecks where
  entryReached : Option Bool
  controlFlowIntegrity : Option Bool
  exitsRespected : Option Bool
  withinStepBound : Option Bool
  allocationConsistent : Option Bool
  inputPreserved : Option Bool
  codePreserved : Option Bool
  writesClassified : Option Bool
  meaningTie : Option Bool
  deriving Repr, DecidableEq, BEq, Inhabited

end BinaryFv.Zesu.Validation
