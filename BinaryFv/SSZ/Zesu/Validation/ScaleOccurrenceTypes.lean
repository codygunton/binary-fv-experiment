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

namespace BinaryFv.SSZ.Zesu.Validation

/-- The compact per-occurrence facts reduced from the production trace (observed facts only). -/
structure OccScaleEvidence where
  /-- occurrence index in `program.json`. -/
  index : Nat
  /-- fully-qualified inlined name (for readability / reports). -/
  qualified : String
  /-- the source-routine short name (last dotted component). -/
  routine : String
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
  /-- whether the source routine allocates (bumps the allocator cursor). -/
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
  -- Row A entry/exit BINDINGS (the declared machine placement), evaluated against the real run.
  /-- how each declared effective binding row resolved: "exact" (a deterministic value), "stack" (a
  real but environment-dependent stack address, carried as its class only), or "unresolved" (the
  declared location could not be read — a FAILURE, never a gap). -/
  bindingHows : List String
  /-- the routine's binding-consequence family ("entryAbi" / "rawCopy" / "alloc" / "offsetRead" /
  "comptime"), or `""` when no consequence is defined for it. -/
  bindingFamily : String
  /-- the decisive scalar observations of the FIRST captured invocation, as (name, value) pairs. -/
  bindingObs : List (String × Int)
  /-- per-invocation consequence verdicts, reduced to counts. -/
  realizedPass : Nat
  realizedFail : Nat
  realizedGap : Nat
  /-- the exit convention declared for this routine ("" if none). -/
  exitConvention : String
  /-- declared exits that are genuine `ret` instructions (a tail-call exit carries the callee's
  arguments, not this occurrence's result, so a result convention does not apply there). -/
  returnExits : List Nat
  /-- how `a0` classifies at each captured return exit. -/
  exitA0Classes : List String
  -- Allocation ledger, reconstructed from the bump cursor's own write history.
  /-- allocation events (cursor bumps) inside this occurrence's invocation windows. -/
  ledgerEventCount : Nat
  /-- every sized event strictly advanced the cursor. -/
  ledgerAllPositive : Bool
  /-- every event left the cursor inside the heap. -/
  ledgerAfterInHeap : Bool
  -- Meaning.
  /-- the declared little-endian width of a fixed-width leaf reader (`none` otherwise). -/
  meaningWidth : Option Nat
  /-- the little-endian value of the EXACT window the occurrence read (`none` if the window read was
  not exactly `meaningWidth` bytes). -/
  meaningValue : Option Nat
  /-- the decoded value left the occurrence: stored, or held in a register at a declared exit. -/
  meaningProduced : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The generic per-occurrence checks; `none` is an EXPLICIT gap (never counted as a pass). -/
structure ScaleChecks where
  entryReached : Option Bool
  controlFlowIntegrity : Option Bool
  exitsRespected : Option Bool
  withinStepBound : Option Bool
  allocationConsistent : Option Bool
  inputPreserved : Option Bool
  codePreserved : Option Bool
  writesClassified : Option Bool
  /-- every declared Row A binding row resolved against the real machine state at the entry PC. -/
  bindingsEvaluable : Option Bool
  /-- the resolved bindings had their declared consequence in the trace. -/
  bindingsRealized : Option Bool
  /-- the result register at a declared RETURN exit matches the routine's exit convention. -/
  exitBindingRealized : Option Bool
  /-- an allocating occurrence's cursor bumps are well-formed ledger events. -/
  allocationLedger : Option Bool
  meaningTie : Option Bool
  deriving Repr, DecidableEq, BEq, Inhabited

end BinaryFv.SSZ.Zesu.Validation
