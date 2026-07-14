import BinaryFv.Keccak.CallClosure
namespace BinaryFv.Keccak
open BinaryFv.RISCV LeanRV64DExecutable.Functions
/-- Generated instruction constructors retained by the closed static inventory. -/
inductive ExecutionConstructor where
  | illegal | compressedIllegal | landingPad | utype | jal | jalr | btype | itype | shiftIop
  | rtype | load | store | addiw | rtypew | shiftiwop | fenceTso | fence | ecall | mret | sret
  | ebreak | wfi | sfenceVma | mul | div | rem | mulw | divw | remw
  deriving BEq, DecidableEq, Repr
def executionConstructor : instruction → ExecutionConstructor
  | .ILLEGAL _ => .illegal | .C_ILLEGAL _ => .compressedIllegal | .LPAD _ => .landingPad
  | .UTYPE _ => .utype | .JAL _ => .jal | .JALR _ => .jalr | .BTYPE _ => .btype
  | .ITYPE _ => .itype | .SHIFTIOP _ => .shiftIop | .RTYPE _ => .rtype | .LOAD _ => .load
  | .STORE _ => .store | .ADDIW _ => .addiw | .RTYPEW _ => .rtypew | .SHIFTIWOP _ => .shiftiwop
  | .FENCE_TSO _ => .fenceTso | .FENCE _ => .fence | .ECALL _ => .ecall | .MRET _ => .mret
  | .SRET _ => .sret | .EBREAK _ => .ebreak | .WFI _ => .wfi | .SFENCE_VMA _ => .sfenceVma
  | .MUL _ => .mul | .DIV _ => .div | .REM _ => .rem | .MULW _ => .mulw | .DIVW _ => .divw
  | .REMW _ => .remw
/-- `framed` has an exported all-outcome `x2` frame; stack adjustment changes `x2` by design. -/
inductive X2FrameStatus where
  | framed (constructor : ExecutionConstructor) | stackAdjustment | pendingLoad | pendingStore
  | uncovered (constructor : ExecutionConstructor)
  deriving BEq, DecidableEq, Repr
def nonStackDestination (destination : regidx) : Bool := destination != stackPointer
def frameForDestination (constructor : ExecutionConstructor) (destination : regidx) :
    X2FrameStatus :=
  if nonStackDestination destination then .framed constructor else .uncovered constructor
/--
Map generated constructors to the already exported frame families: UTYPE, RTYPE, ITYPE, SHIFTIOP,
MUL/DIV/REM, BTYPE, non-`x2` JAL/JALR, and FENCE/FENCE_TSO. LOAD and STORE are kept as explicit
remaining obligations. All other constructors and unexpected `x2` writes remain uncovered; this is
not semantic reachability, arbitrary-state execution coverage, or a stack-bound claim.
-/
def x2FrameStatus (decoded : instruction) : X2FrameStatus :=
  if (instructionStackDelta? decoded).isSome then .stackAdjustment else
  match decoded with
  | .UTYPE (_, destination, _) => frameForDestination .utype destination
  | .JAL (_, destination) => frameForDestination .jal destination
  | .JALR (_, _, destination) => frameForDestination .jalr destination
  | .BTYPE _ => .framed .btype
  | .ITYPE (_, _, destination, _) => frameForDestination .itype destination
  | .SHIFTIOP (_, _, destination, _) => frameForDestination .shiftIop destination
  | .RTYPE (_, _, destination, _) => frameForDestination .rtype destination
  | .LOAD (_, _, destination, _, _) =>
    if nonStackDestination destination then .pendingLoad else .uncovered .load
  | .STORE _ => .pendingStore
  | .FENCE_TSO _ => .framed .fenceTso
  | .FENCE _ => .framed .fence
  | .MUL (_, _, destination, _) => frameForDestination .mul destination
  | .DIV (_, _, destination, _) => frameForDestination .div destination
  | .REM (_, _, destination, _) => frameForDestination .rem destination
  | _ => .uncovered (executionConstructor decoded)
def X2FrameStatus.isClassified : X2FrameStatus → Bool
  | .framed _ | .stackAdjustment | .pendingLoad | .pendingStore => true
  | .uncovered _ => false
def closureWordSets? (sets : Array FunctionWordSet) (closure : Array Nat) :
    Option (Array FunctionWordSet) :=
  closure.foldl (fun selected start => do
    let selected ← selected
    let set ← functionWordSetAtStart? sets start
    pure (selected.push set)) (some #[])
/-- Parser-owned closure words; absent selected symbols remain `none`. -/
def entrySyntacticClosureWords? : Option (Array DecodedWord) := do
  let sets ← artifactFunctionWordSets?
  let closure ← entrySyntacticFunctionClosure?
  let selected ← closureWordSets? sets closure
  pure (selected.flatMap FunctionWordSet.words)
structure FrameCoverageEntry where
  word : DecodedWord
  constructor : ExecutionConstructor
  status : X2FrameStatus
def entrySyntacticClosureFrameInventory? : Option (Array FrameCoverageEntry) :=
  entrySyntacticClosureWords?.map fun words => words.map fun word =>
    { word
      constructor := executionConstructor word.instruction
      status := x2FrameStatus word.instruction }
def entrySyntacticClosureFrameStatuses? : Option (Array X2FrameStatus) :=
  entrySyntacticClosureFrameInventory?.map fun inventory => inventory.map FrameCoverageEntry.status
/-- No unclassified constructor or unexpected non-adjustment `x2` write occurs in this closure. -/
def entrySyntacticClosureHasOnlyKnownOrMemoryBuckets : Bool :=
  match entrySyntacticClosureFrameStatuses? with
  | some statuses => statuses.all X2FrameStatus.isClassified
  | none => false
def entrySyntacticClosureHasPendingLoadBucket : Bool :=
  entrySyntacticClosureFrameStatuses?.any fun statuses => statuses.any (· == .pendingLoad)
def entrySyntacticClosureHasPendingStoreBucket : Bool :=
  entrySyntacticClosureFrameStatuses?.any fun statuses => statuses.any (· == .pendingStore)
/-- Closed parser classification, not a dynamic-reachability claim. -/
theorem entry_syntactic_closure_has_only_known_or_memory_buckets :
    entrySyntacticClosureHasOnlyKnownOrMemoryBuckets = true := by
  native_decide
theorem entry_syntactic_closure_has_pending_load_bucket :
    entrySyntacticClosureHasPendingLoadBucket = true := by
  native_decide

theorem entry_syntactic_closure_has_pending_store_bucket :
    entrySyntacticClosureHasPendingStoreBucket = true := by
  native_decide
end BinaryFv.Keccak
