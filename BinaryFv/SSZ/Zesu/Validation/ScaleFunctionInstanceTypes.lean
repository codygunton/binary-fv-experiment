/-!
# Compact evidence for all compiled functionInstances

The raw QEMU traces are several megabytes and contain host-dependent details. The reducer stores one
`FunctionInstanceScaleEvidence` record per generated functionInstance with only the facts needed by the Lean checker.
`ScaleChecks` uses `some true` for a pass, `some false` for a contradiction, and `none` for an
explicit coverage or observability gap. A gap is never treated as success.

These records are validation-only and cannot be imported by the compliance theorem.
-/

namespace BinaryFv.SSZ.Zesu.Validation

/-- A loop-`derived` Row A binding row, evaluated at every captured entry of its functionInstance.

The row declares `value = index * stride + constant` with the scaled index living in `register`
(`BindingInventory.DerivedIndexRep`). The evidence carries what that register actually held and what
the row resolved to, at each invocation, so the relation is CHECKED rather than assumed: a row whose
register does not carry a multiple of the stride, or whose argument is not that value plus the
constant, fails. -/
structure DerivedRowEvidence where
  /-- the Zig parameter name the row binds. -/
  name : String
  /-- the loop-carried register holding `index * stride`. -/
  register : Nat
  /-- the pinned source stride (`WITHDRAWAL_SIZE`). -/
  stride : Nat
  /-- the row's constant addend (the field's offset within the element). -/
  constant : Nat
  /-- what `register` held at each captured entry, in invocation order. -/
  registerValues : List Nat
  /-- what the row resolved to at each of those entries. -/
  values : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- One allocation as the UNCHANGED production ELF performed it: a write of the bump cursor, plus the
pointer the allocator handed back at its return. Reconstructed from `ZKVM_HEAP_POS`'s own write
history — the allocation ACT — not from anything the allocator reports about itself. -/
structure ObservedAlloc where
  /-- position in the run's allocation sequence (the startup cursor write is not an allocation). -/
  ordinal : Nat
  cursorBefore : Nat
  cursorAfter : Nat
  /-- `a0` at the allocator's return inside this event's window, when it was captured. -/
  returnedPointer : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- One allocation the fixture REQUIRES, derived without reference to the binary: the pinned Zig decode
order applied to the exact bytes fed to the process, sized by the Row B probe's element ABI. -/
structure ExpectedAlloc where
  ordinal : Nat
  /-- the Zig routine whose `alloc(T, n)` this is. -/
  routine : String
  /-- the element type (`--dump-abi` key). -/
  element : String
  count : Nat
  /-- `count * @sizeOf(element)`. -/
  size : Nat
  /-- `@alignOf(element)`. -/
  alignment : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One arm's WHOLE-RUN allocation ledger: everything the ELF did beside everything it had to do. -/
structure ArmLedger where
  arm : String
  /-- the process exit code (0 decoded, 1 rejected). -/
  decision : Nat
  inputBytes : Nat
  /-- where the independent shape walk says the pinned decoder rejects this fixture (`""` if it
  decodes) — the reason a rejected arm allocates a prefix of the full sequence. -/
  rejectedAt : String
  observed : List ObservedAlloc
  expected : List ExpectedAlloc
  deriving Repr, DecidableEq, Inhabited

/-- The compact per-functionInstance facts reduced from the production trace (observed facts only). -/
structure FunctionInstanceScaleEvidence where
  /-- functionInstance index in `program.json`. -/
  index : Nat
  /-- fully-qualified inlined name (for readability / reports). -/
  qualified : String
  /-- the source-routine short name (last dotted component). -/
  routine : String
  /-- the arm whose trace covers this functionInstance (`""` if uncovered). -/
  arm : String
  /-- declared Row A entry PC. -/
  entryPc : Nat
  /-- whether the functionInstance's region executed under the chosen arm. -/
  covered : Bool
  /-- first in-region PC executed (0 if uncovered). -/
  firstInRegion : Nat
  /-- max instructions in one invocation (span between successive `entryPc` executions). -/
  maxInsnPerInvocation : Nat
  /-- the functionInstance's declared CFG edges (generator: attributed from DEEPEST-owned PCs). -/
  declaredEdges : List (Nat × Nat)
  /-- distinct executed transfers whose SOURCE is a PC this functionInstance owns (dynamic returns and
  unresolved indirect calls excluded — those are validated against `exits`). -/
  executedOwnedEdges : List (Nat × Nat)
  /-- the declared exit PCs. -/
  exits : List Nat
  /-- owned STATIC-transfer PCs at which execution DEPARTED the functionInstance's regions — it left and
  did not come back to that pc's own in-region fall-through. Leaving and departing are not the same:
  a call leaves and returns, so a call site departs only in tail position. A departing `ret` is
  carried by `dynamicTransferSources`, not here; the two lists partition the departure sources by
  whether the transfer's target is statically known, and BOTH must be declared exits. -/
  leavingSources : List Nat
  /-- owned PCs whose transfer is dynamic (`ret` / unresolved indirect jump or call), every one that
  executed — not only those seen to leave. That is deliberately STRICTER than the static exit rule,
  which declares a `ret` an exit but declares neither kind of unresolved indirect transfer one: such a
  transfer has neither a declared edge nor a declared exit, so the generated CFG models it not at all,
  and requiring it to be declared is the conservative alarm. (One such site exists in the binary, an
  allocator vtable `jalr`; it does not execute on any arm, so the strictness costs nothing today.) -/
  dynamicTransferSources : List Nat
  /-- owned CALL sites that left the regions and were OBSERVED, in the trace, to resume at their own
  in-region fall-through. These are the sites `leavingSources` excludes, carried so the exclusion is
  auditable: none of them may appear in `exits`, or `exitPcs` is over-declared again. -/
  returningCallSites : List Nat
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
  /-- the functionInstance's loop-`derived` rows with the machine values they were evaluated against. -/
  derivedRows : List DerivedRowEvidence
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
  /-- invocations whose returned `a0` equalled the `dst` argument captured at that same invocation's
  entry, and the number of invocations for which both were captured. -/
  exitPairsMatched : Nat
  exitPairsTotal : Nat
  /-- distinct values returned at a declared return exit (bounded sample). -/
  exitReturnedValues : List Nat
  /-- the process exit code of the arm this functionInstance was evaluated on. -/
  armDecision : Nat
  /-- declared exits that are genuine `ret` instructions (a tail-call exit carries the callee's
  arguments, not this functionInstance's result, so a result convention does not apply there). -/
  returnExits : List Nat
  /-- how `a0` classifies at each captured return exit. -/
  exitA0Classes : List String
  -- Allocation ledger: the cursor's own write history beside the independently expected sequence.
  /-- allocation events inside this functionInstance's dynamic extents. -/
  ledgerEventCount : Nat
  /-- those events as the ELF performed them, in order. -/
  ledgerObserved : List ObservedAlloc
  /-- the events this functionInstance MUST perform on this arm's fixture, derived without the binary. -/
  ledgerExpected : List ExpectedAlloc
  /-- observed events whose returned pointer was not captured (a narrow, explicit per-field gap). -/
  ledgerReturnedUnknown : Nat
  -- Meaning.
  /-- the declared little-endian width of a fixed-width leaf reader (`none` otherwise). -/
  meaningWidth : Option Nat
  /-- the little-endian value of the EXACT window the functionInstance read (`none` if the window read was
  not exactly `meaningWidth` bytes). -/
  meaningValue : Option Nat
  /-- the decoded value left the functionInstance: stored, or held in a register at a declared exit. -/
  meaningProduced : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The generic per-functionInstance checks; `none` is an EXPLICIT gap (never counted as a pass). -/
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
  /-- every loop-`derived` row's `index * stride + constant` relation held at every captured entry. -/
  derivedBindingsHold : Option Bool
  /-- the result register at a declared RETURN exit matches the routine's exit convention. -/
  exitBindingRealized : Option Bool
  /-- the functionInstance's cursor events ARE the independently expected allocation sequence. -/
  allocationLedger : Option Bool
  meaningTie : Option Bool
  deriving Repr, DecidableEq, BEq, Inhabited

end BinaryFv.SSZ.Zesu.Validation
