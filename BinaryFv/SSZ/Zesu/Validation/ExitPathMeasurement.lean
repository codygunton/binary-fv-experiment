import BinaryFv.SSZ.Zesu.Validation.RepairBlastRadius
import BinaryFv.SSZ.Zesu.Elfling.GeneratedReturnExits

/-!
# Row D½ actual-successor measurement

The old inline-boundary inventory asks whether a pair has *some* suitable edge. That is not a
semantics for a pending exit: a conditional exit can stay inside the child on one arm and leave it
on the other, and a tail call's completion is not its immediate callee edge. This module records
the decoded completion alternative for every generated exit source and joins each target to the
exact execution extents consumed by the trace machinery.

This is intentionally pre-repair and validation-only. It changes no generated data, contract, or
trace API. Its pins are allowed to be red. Every dataset is checked back against the canonical Sail
decode and `functionInstanceExecutionRanges`, rather than merely against another projection of the
generated edge table.
-/

namespace BinaryFv.SSZ.Zesu.Validation.ExitPathMeasurement

set_option maxRecDepth 8000

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.ControlFlow (controlFlow?)
open BinaryFv.SSZ.Zesu.Elfling.Generated
  (generatedExcludedFunctionInstances generatedProgram)
open BinaryFv.SSZ.Zesu.Elfling.Validation
  (EdgeCategory classifyEdge deepestOwner? exclEntryPc regionPcList returnExitPcs)
open BinaryFv.SSZ.Zesu.Validation.RepairBlastRadius
  (allGeneratedEdges sameEntryInlinePair sharedExitInlineFinish)

inductive ExitControlKind
  | fallthrough
  | conditional
  | jump
  | call
  | return_
  | indirect
  | indirectCall
  | terminal
deriving DecidableEq, Repr

/-- Tags are load-bearing. In particular, the two conditional arms may not be exchanged merely
because they have the same unlabelled target set. -/
inductive ExitArm
  | fallthrough
  | conditionalTaken
  | conditionalNotTaken
  | jump
  | callReturn
deriving DecidableEq, Repr

structure ExitSourceRow where
  functionIndex : Nat
  dieOffset : Nat
  source : Nat
  kind : ExitControlKind
  immediateCallee? : Option Nat
  returnAddress? : Option Nat
deriving DecidableEq, Repr

structure StaticExitPath where
  functionIndex : Nat
  dieOffset : Nat
  source : Nat
  arm : ExitArm
  target : Nat
  insideExecution : Bool
deriving DecidableEq, Repr

/-- A decode failure produces empty measurements and therefore breaks every nonzero pin below. -/
def nodes : Array ControlFlowNode := controlFlow?.getD #[]

def controlKind : ControlTransfer → ExitControlKind
  | .fallthrough _ => .fallthrough
  | .conditional _ _ => .conditional
  | .jump _ => .jump
  | .call _ _ _ => .call
  | .return_ _ => .return_
  | .indirect => .indirect
  | .indirectCall _ _ => .indirectCall
  | .terminal => .terminal

def exitSourceRows : Array ExitSourceRow :=
  generatedProgram.functionInstances.zipIdx.foldl (fun rows pair =>
    let functionInstance := pair.1
    let index := pair.2
    functionInstance.exitPcs.foldl (fun rows source =>
      match ControlFlowNodeAt? nodes source with
      | some node =>
          rows.push {
            functionIndex := index
            dieOffset := functionInstance.provenance.entryOffset
            source
            kind := controlKind node.transfer
            immediateCallee? := match node.transfer with
              | .call target _ _ => target
              | _ => none
            returnAddress? := match node.transfer with
              | .call _ returnAddress _ => some returnAddress
              | _ => none }
      | none => rows) rows) #[]

def inExecution (functionInstance : FunctionInstance) (target : Nat) : Bool :=
  Program.inRanges
    (functionInstanceExecutionRanges generatedProgram functionInstance) target

def staticPath (functionInstance : FunctionInstance) (functionIndex source : Nat)
    (arm : ExitArm) (target : Nat) : StaticExitPath :=
  { functionIndex
    dieOffset := functionInstance.provenance.entryOffset
    source
    arm
    target
    insideExecution := inExecution functionInstance target }

def staticPathsAt (functionInstance : FunctionInstance) (functionIndex source : Nat) :
    Array StaticExitPath :=
  match ControlFlowNodeAt? nodes source with
  | some { transfer := .fallthrough target, .. } =>
      #[staticPath functionInstance functionIndex source .fallthrough target]
  | some { transfer := .conditional (some taken) notTaken, .. } =>
      #[staticPath functionInstance functionIndex source .conditionalTaken taken,
        staticPath functionInstance functionIndex source .conditionalNotTaken notTaken]
  | some { transfer := .conditional none notTaken, .. } =>
      #[staticPath functionInstance functionIndex source .conditionalNotTaken notTaken]
  | some { transfer := .jump (some target), .. } =>
      #[staticPath functionInstance functionIndex source .jump target]
  | some { transfer := .call _ returnAddress _, .. } =>
      #[staticPath functionInstance functionIndex source .callReturn returnAddress]
  | _ => #[]

def staticExitPaths : Array StaticExitPath :=
  generatedProgram.functionInstances.zipIdx.foldl (fun paths pair =>
    pair.1.exitPcs.foldl (fun paths source =>
      paths ++ staticPathsAt pair.1 pair.2 source) paths) #[]

def sourceKey (row : ExitSourceRow) : Nat × Nat :=
  (row.dieOffset, row.source)

def staticPathKey (row : StaticExitPath) : Nat × Nat × ExitArm :=
  (row.dieOffset, row.source, row.arm)

def staticPathsForSource (row : ExitSourceRow) : Array StaticExitPath :=
  staticExitPaths.filter fun path =>
    path.dieOffset == row.dieOffset && path.source == row.source

def allExitSourcesDecoded : Bool :=
  generatedProgram.functionInstances.all fun functionInstance =>
    functionInstance.exitPcs.all fun source =>
      (ControlFlowNodeAt? nodes source).isSome

/-- Consumer-side validation for one proposed completion. It re-reads the canonical decoded
transfer, checks the arm tag and target, and recomputes exact-extent membership. -/
def staticPathValid (row : StaticExitPath) : Bool :=
  match generatedProgram.functionInstances[row.functionIndex]? with
  | none => false
  | some functionInstance =>
      row.dieOffset == functionInstance.provenance.entryOffset &&
        functionInstance.exitPcs.contains row.source &&
        row.insideExecution == inExecution functionInstance row.target &&
        match ControlFlowNodeAt? nodes row.source, row.arm with
        | some { transfer := .fallthrough target, .. }, .fallthrough =>
            row.target == target
        | some { transfer := .conditional (some taken) _, .. }, .conditionalTaken =>
            row.target == taken
        | some { transfer := .conditional _ notTaken, .. }, .conditionalNotTaken =>
            row.target == notTaken
        | some { transfer := .jump (some target), .. }, .jump =>
            row.target == target
        | some { transfer := .call _ returnAddress _, .. }, .callReturn =>
            row.target == returnAddress
        | _, _ => false

/-- Equality supplies completeness and multiplicity; `staticPathValid` supplies the independent
consumer join to decoded control and exact extents. -/
def staticPathDatasetValid (rows : Array StaticExitPath) : Bool :=
  rows == staticExitPaths && rows.all staticPathValid

theorem exact_exit_source_inventory :
    allExitSourcesDecoded = true ∧
      exitSourceRows.size = 469 ∧
      (exitSourceRows.toList.map sourceKey).eraseDups.length = 469 ∧
      (exitSourceRows.toList.map (·.source)).eraseDups.length = 331 ∧
      (exitSourceRows.filter fun row => row.kind == .fallthrough).size = 287 ∧
      (exitSourceRows.filter fun row => row.kind == .conditional).size = 136 ∧
      (exitSourceRows.filter fun row => row.kind == .jump).size = 23 ∧
      (exitSourceRows.filter fun row => row.kind == .call).size = 7 ∧
      (exitSourceRows.filter fun row => row.kind == .return_).size = 16 ∧
      (exitSourceRows.filter fun row =>
        row.kind == .indirect || row.kind == .indirectCall ||
          row.kind == .terminal).size = 0 := by
  native_decide

def sourceHasInsidePath (row : ExitSourceRow) : Bool :=
  (staticPathsForSource row).any (·.insideExecution)

def sourceHasOutsidePath (row : ExitSourceRow) : Bool :=
  (staticPathsForSource row).any fun path => !path.insideExecution

theorem exact_static_completion_inventory :
    staticPathDatasetValid staticExitPaths = true ∧
      staticExitPaths.size = 589 ∧
      (staticExitPaths.toList.map staticPathKey).eraseDups.length = 589 ∧
      (staticExitPaths.filter (·.insideExecution)).size = 97 ∧
      (staticExitPaths.filter fun row => !row.insideExecution).size = 492 ∧
      (exitSourceRows.filter fun row =>
        sourceHasInsidePath row && sourceHasOutsidePath row).size = 97 ∧
      (exitSourceRows.filter fun row =>
        !sourceHasInsidePath row && sourceHasOutsidePath row).size = 356 ∧
      (exitSourceRows.filter fun row =>
        !sourceHasInsidePath row && !sourceHasOutsidePath row).size = 16 := by
  native_decide

/-- Dynamic returns have no static target, but all sixteen are independently tied to the
file-backed `ret` encoding through `ra`. Thus the full completion population is 589 static
alternatives plus sixteen dynamic returns. -/
theorem exact_dynamic_return_inventory :
    (exitSourceRows.filter fun row => row.kind == .return_).size = 16 ∧
      staticExitPaths.size +
        (exitSourceRows.filter fun row => row.kind == .return_).size = 605 ∧
      BinaryFv.SSZ.Zesu.Elfling.Validation.returnExitsAreRetB
        nodes BinaryFv.SSZ.Zesu.Artifact.programImage generatedProgram = true := by
  native_decide

/-! ## Resolved-call joins -/

structure ResolvedCallRow where
  callerIndex : Nat
  callerDieOffset : Nat
  source : Nat
  target : Nat
  returnAddress : Nat
  callerExit : Bool
  targetInsideCaller : Bool
  returnInsideCaller : Bool
  generatedCalleeIndex? : Option Nat
  excludedTarget : Bool
  returnInsideGeneratedCallee : Bool
deriving DecidableEq, Repr

def generatedAtEntry? (target : Nat) : Option (FunctionInstance × Nat) :=
  generatedProgram.functionInstances.zipIdx.find? fun pair =>
    pair.1.entryPc == target

def excludedAtEntry (target : Nat) : Bool :=
  generatedExcludedFunctionInstances.any fun functionInstance =>
    exclEntryPc functionInstance == target

def resolvedCallRows : Array ResolvedCallRow :=
  generatedProgram.functionInstances.zipIdx.foldl (fun rows pair =>
    let caller := pair.1
    let callerIndex := pair.2
    (regionPcList caller).foldl (fun rows source =>
      match ControlFlowNodeAt? nodes source with
      | some { transfer := .call (some target) returnAddress _, .. } =>
          let generatedCallee := generatedAtEntry? target
          rows.push {
            callerIndex
            callerDieOffset := caller.provenance.entryOffset
            source
            target
            returnAddress
            callerExit := caller.exitPcs.contains source
            targetInsideCaller := inExecution caller target
            returnInsideCaller := inExecution caller returnAddress
            generatedCalleeIndex? := generatedCallee.map (·.2)
            excludedTarget := excludedAtEntry target
            returnInsideGeneratedCallee :=
              generatedCallee.any fun callee => inExecution callee.1 returnAddress }
      | _ => rows) rows) #[]

theorem exact_resolved_call_join :
    resolvedCallRows.size = 180 ∧
      (resolvedCallRows.toList.map (·.source)).eraseDups.length = 68 ∧
      (resolvedCallRows.filter fun row => !row.callerExit).size = 173 ∧
      (resolvedCallRows.filter (·.callerExit)).size = 7 ∧
      (resolvedCallRows.filter fun row => row.generatedCalleeIndex?.isSome).size = 114 ∧
      (resolvedCallRows.filter fun row =>
        row.generatedCalleeIndex?.isSome && !row.callerExit).size = 107 ∧
      (resolvedCallRows.filter (·.excludedTarget)).size = 66 ∧
      (resolvedCallRows.filter fun row =>
        row.generatedCalleeIndex?.isNone && !row.excludedTarget).size = 0 ∧
      resolvedCallRows.all (·.targetInsideCaller) = true ∧
      (resolvedCallRows.filter (·.returnInsideCaller)).size = 173 ∧
      (resolvedCallRows.filter fun row => !row.returnInsideCaller).size = 7 ∧
      (resolvedCallRows.filter fun row =>
        row.generatedCalleeIndex?.isSome &&
          row.returnInsideGeneratedCallee).size = 0 ∧
      ((resolvedCallRows.filter fun row =>
        row.generatedCalleeIndex?.isSome).toList.map (·.source)).eraseDups.length = 41 ∧
      ((resolvedCallRows.filter (·.excludedTarget)).toList.map
        (·.source)).eraseDups.length = 27 := by
  native_decide

def functionIndexForId? (id : FunctionInstanceId) : Option Nat :=
  (generatedProgram.functionInstances.zipIdx.find? fun pair =>
    decide (pair.1.id = id)).map (·.2)

structure TailCallRow where
  callerIndex : Nat
  callerDieOffset : Nat
  callerRoutine : String
  source : Nat
  calleeIndex : Nat
  calleeDieOffset : Nat
  calleeEntry : Nat
  calleeReturnExit : Nat
  returnAddress : Nat
  parentIndex : Nat
  receiverIndex : Nat
  returnInsideParent : Bool
deriving DecidableEq, Repr

def tailCallRows : Array TailCallRow :=
  (resolvedCallRows.filter (·.callerExit)).filterMap fun call =>
    match generatedProgram.functionInstances[call.callerIndex]?,
        call.generatedCalleeIndex? with
    | some caller, some calleeIndex =>
        match generatedProgram.functionInstances[calleeIndex]?,
            caller.parent?.bind functionIndexForId?,
            (deepestOwner? call.returnAddress).bind
              (fun receiver => functionIndexForId? receiver.id) with
        | some callee, some parentIndex, some receiverIndex =>
            match (returnExitPcs nodes callee)[0]? with
            | some calleeReturnExit =>
                some {
                  callerIndex := call.callerIndex
                  callerDieOffset := caller.provenance.entryOffset
                  callerRoutine := caller.id.function.declaration.qualifiedName
                  source := call.source
                  calleeIndex
                  calleeDieOffset := callee.provenance.entryOffset
                  calleeEntry := callee.entryPc
                  calleeReturnExit
                  returnAddress := call.returnAddress
                  parentIndex
                  receiverIndex
                  returnInsideParent :=
                    (generatedProgram.functionInstances[parentIndex]?).any fun parent =>
                      inExecution parent call.returnAddress }
            | none => none
        | _, _, _ => none
    | _, _ => none

/-- The seven source-is-exit calls all invoke the same generated `memcpy`. Completion is composite:
the child must run to its `ret`, after which its dynamic link lands outside the tail caller and
inside the recorded parent/receiver occurrence. -/
theorem exact_tail_call_rows :
    tailCallRows = #[
      { callerIndex := 3, callerDieOffset := 8487
        callerRoutine := "ssz_raw.decode", source := 66360
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 66364
        parentIndex := 1, receiverIndex := 1, returnInsideParent := true },
      { callerIndex := 16, callerDieOffset := 11305
        callerRoutine := "ssz_raw.decodeNewPayloadRequest", source := 75508
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 75512
        parentIndex := 6, receiverIndex := 6, returnInsideParent := true },
      { callerIndex := 23, callerDieOffset := 11623
        callerRoutine := "ssz_raw.decodeExecutionPayload", source := 73048
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 73052
        parentIndex := 16, receiverIndex := 16, returnInsideParent := true },
      { callerIndex := 23, callerDieOffset := 11623
        callerRoutine := "ssz_raw.decodeExecutionPayload", source := 73076
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 73080
        parentIndex := 16, receiverIndex := 16, returnInsideParent := true },
      { callerIndex := 23, callerDieOffset := 11623
        callerRoutine := "ssz_raw.decodeExecutionPayload", source := 73104
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 73108
        parentIndex := 16, receiverIndex := 16, returnInsideParent := true },
      { callerIndex := 23, callerDieOffset := 11623
        callerRoutine := "ssz_raw.decodeExecutionPayload", source := 73132
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 73136
        parentIndex := 16, receiverIndex := 16, returnInsideParent := true },
      { callerIndex := 37, callerDieOffset := 12157
        callerRoutine := "ssz_raw.readArray", source := 69584
        calleeIndex := 139, calleeDieOffset := 523, calleeEntry := 81592
        calleeReturnExit := 81600, returnAddress := 69588
        parentIndex := 23, receiverIndex := 38, returnInsideParent := true }
    ] := by
  native_decide

/-! ## The no-link jump tail -/

inductive JumpCompletionRole
  | directCompletion
  | tailDelegate (calleeIndex : Nat)
deriving DecidableEq, Repr

structure JumpExitRow where
  functionIndex : Nat
  dieOffset : Nat
  source : Nat
  target : Nat
  role : JumpCompletionRole
  targetInsideExecution : Bool
  declaredExternalCall : Bool
  currentCategory : Option EdgeCategory
deriving DecidableEq, Repr

def jumpExitRows : Array JumpExitRow :=
  exitSourceRows.filterMap fun sourceRow =>
    if sourceRow.kind != .jump then none else
      match generatedProgram.functionInstances[sourceRow.functionIndex]?,
          ControlFlowNodeAt? nodes sourceRow.source with
      | some functionInstance, some { transfer := .jump (some target), .. } =>
          let targetInstance := generatedAtEntry? target
          some {
            functionIndex := sourceRow.functionIndex
            dieOffset := sourceRow.dieOffset
            source := sourceRow.source
            target
            role := match targetInstance with
              | some pair => .tailDelegate pair.2
              | none => .directCompletion
            targetInsideExecution := inExecution functionInstance target
            declaredExternalCall := targetInstance.any fun pair =>
              functionInstance.externalCalls.any fun id => decide (id = pair.1.id)
            currentCategory :=
              classifyEdge functionInstance { source := sourceRow.source, target } }
      | _, _ => none

def jumpExitKey (row : JumpExitRow) : Nat × Nat :=
  (row.dieOffset, row.source)

/-- Of 23 resolved jump exits, exactly one targets another generated function entry. It is the
emitted `allocatorAlloc` wrapper jumping without a link to `raw_alloc`; the current edge classifier
calls it an ordinary function exit because `externalCalls` carries no tail-delegate relation. -/
theorem allocator_tail_delegate_counterexample :
    jumpExitRows.size = 23 ∧
      (jumpExitRows.toList.map jumpExitKey).eraseDups.length = 23 ∧
      (jumpExitRows.filter fun row =>
        row.role == .directCompletion).size = 22 ∧
      (jumpExitRows.filter fun row =>
        match row.role with | .tailDelegate _ => true | _ => false).size = 1 ∧
      (jumpExitRows.filter fun row =>
        match row.role with | .tailDelegate _ => true | _ => false) = #[
          { functionIndex := 136
            dieOffset := 19818
            source := 79740
            target := 66124
            role := .tailDelegate 0
            targetInsideExecution := false
            declaredExternalCall := false
            currentCategory := some .functionExit }
        ] := by
  native_decide

/-! ## Inline child-exit joins -/

inductive InlinePathClass
  | stayChild
  | resumeParent
  | propagate
  | childOnly
deriving DecidableEq, Repr

structure InlineExitPath where
  parentIndex : Nat
  childIndex : Nat
  parentDieOffset : Nat
  childDieOffset : Nat
  source : Nat
  arm : ExitArm
  target : Nat
  sourceParentExit : Bool
  sameEntryPair : Bool
  coarseSharedPair : Bool
  pathClass : InlinePathClass
deriving DecidableEq, Repr

def classifyInlineTarget (parent child : FunctionInstance) (target : Nat) :
    InlinePathClass :=
  match inExecution child target, inExecution parent target with
  | true, true => .stayChild
  | false, true => .resumeParent
  | false, false => .propagate
  | true, false => .childOnly

def inlineExitPaths : Array InlineExitPath :=
  (Boundary.inlinePairs generatedProgram).foldl (fun rows pair =>
    match functionIndexForId? pair.1.id, functionIndexForId? pair.2.id with
    | some parentIndex, some childIndex =>
        pair.2.exitPcs.foldl (fun rows source =>
          rows ++ (staticPathsAt pair.2 childIndex source).map fun path => {
            parentIndex
            childIndex
            parentDieOffset := pair.1.provenance.entryOffset
            childDieOffset := pair.2.provenance.entryOffset
            source := path.source
            arm := path.arm
            target := path.target
            sourceParentExit := pair.1.exitPcs.contains path.source
            sameEntryPair := sameEntryInlinePair pair
            coarseSharedPair := sharedExitInlineFinish pair
            pathClass := classifyInlineTarget pair.1 pair.2 path.target }) rows
    | _, _ => rows) #[]

def inlinePathKey (row : InlineExitPath) : Nat × Nat × Nat × ExitArm :=
  (row.parentDieOffset, row.childDieOffset, row.source, row.arm)

def inlineSourceKey (row : InlineExitPath) : Nat × Nat × Nat :=
  (row.parentDieOffset, row.childDieOffset, row.source)

def inlineSourceKeys : List (Nat × Nat × Nat) :=
  (inlineExitPaths.toList.map inlineSourceKey).eraseDups

def inlinePathsForSourceKey (key : Nat × Nat × Nat) : Array InlineExitPath :=
  inlineExitPaths.filter fun row => inlineSourceKey row == key

def inlineSourceMixed (key : Nat × Nat × Nat) : Bool :=
  ((inlinePathsForSourceKey key).toList.map (·.pathClass)).eraseDups.length > 1

def inlineSourceParentExit (key : Nat × Nat × Nat) : Bool :=
  (inlinePathsForSourceKey key).any (·.sourceParentExit)

def inlineSourceSameEntry (key : Nat × Nat × Nat) : Bool :=
  (inlinePathsForSourceKey key).any (·.sameEntryPair)

def inlineSourceCoarseShared (key : Nat × Nat × Nat) : Bool :=
  (inlinePathsForSourceKey key).any (·.coarseSharedPair)

/-- The pair-level 82/45 inventory is not a finish-mode partition. Exact decoded completion paths
split 97/341/150, with 108 source rows having different classes on different arms. Seven of the
apparent parent-resume paths are tagged call returns and therefore require the composite child
execution measured above; the other 334 are direct non-call successors. -/
theorem exact_inline_path_join :
    (Boundary.inlinePairs generatedProgram).size = 127 ∧
      inlineSourceKeys.length = 452 ∧
      inlineExitPaths.size = 588 ∧
      (inlineExitPaths.toList.map inlinePathKey).eraseDups.length = 588 ∧
      (inlineExitPaths.filter fun row => row.pathClass == .stayChild).size = 97 ∧
      (inlineExitPaths.filter fun row => row.pathClass == .resumeParent).size = 341 ∧
      (inlineExitPaths.filter fun row => row.pathClass == .propagate).size = 150 ∧
      (inlineExitPaths.filter fun row => row.pathClass == .childOnly).size = 0 ∧
      (inlineSourceKeys.filter inlineSourceMixed).length = 108 ∧
      inlineExitPaths.all (fun row =>
        allGeneratedEdges.contains { source := row.source, target := row.target }) = true ∧
      (inlineExitPaths.filter fun row =>
        row.pathClass == .resumeParent && row.arm == .callReturn).size = 7 ∧
      (inlineExitPaths.filter fun row =>
        row.pathClass == .resumeParent && row.arm != .callReturn).size = 334 := by
  native_decide

/-- Source-level accounting exposes why a mode attached to a source is still too coarse. Of 314
parent-nonexit sources, 66 are mixed; of 138 parent-exit sources, 42 are mixed. The path counts on
the right show the actual alternatives those source groups contribute. -/
theorem inline_source_and_path_partitions :
    (inlineSourceKeys.filter fun key => !inlineSourceParentExit key).length = 314 ∧
      (inlineSourceKeys.filter inlineSourceParentExit).length = 138 ∧
      (inlineSourceKeys.filter fun key =>
        !inlineSourceParentExit key && inlineSourceMixed key).length = 66 ∧
      (inlineSourceKeys.filter fun key =>
        inlineSourceParentExit key && inlineSourceMixed key).length = 42 ∧
      (inlineExitPaths.filter fun row =>
        !row.sourceParentExit && row.pathClass == .stayChild).size = 66 ∧
      (inlineExitPaths.filter fun row =>
        !row.sourceParentExit && row.pathClass == .resumeParent).size = 330 ∧
      (inlineExitPaths.filter fun row =>
        !row.sourceParentExit && row.pathClass == .propagate).size = 0 ∧
      (inlineExitPaths.filter fun row =>
        row.sourceParentExit && row.pathClass == .stayChild).size = 31 ∧
      (inlineExitPaths.filter fun row =>
        row.sourceParentExit && row.pathClass == .resumeParent).size = 11 ∧
      (inlineExitPaths.filter fun row =>
        row.sourceParentExit && row.pathClass == .propagate).size = 150 ∧
      (inlineExitPaths.filter fun row =>
        !row.sourceParentExit && row.pathClass == .resumeParent &&
          row.arm != .callReturn).size = 323 := by
  native_decide

/-- The old coarse classes are retained as measurements, but their joined successor populations
make the mismatch explicit. Same-entry and coarse-shared pairs each contain mixed sources. -/
theorem same_entry_and_coarse_shared_successors :
    ((Boundary.inlinePairs generatedProgram).filter sameEntryInlinePair).size = 46 ∧
      (inlineSourceKeys.filter inlineSourceSameEntry).length = 107 ∧
      (inlineExitPaths.filter (·.sameEntryPair)).size = 138 ∧
      (inlineExitPaths.filter fun row =>
        row.sameEntryPair && row.pathClass == .stayChild).size = 11 ∧
      (inlineExitPaths.filter fun row =>
        row.sameEntryPair && row.pathClass == .resumeParent).size = 10 ∧
      (inlineExitPaths.filter fun row =>
        row.sameEntryPair && row.pathClass == .propagate).size = 117 ∧
      (inlineSourceKeys.filter fun key =>
        inlineSourceSameEntry key && inlineSourceMixed key).length = 20 ∧
      ((Boundary.inlinePairs generatedProgram).filter sharedExitInlineFinish).size = 45 ∧
      (inlineSourceKeys.filter inlineSourceCoarseShared).length = 106 ∧
      (inlineExitPaths.filter (·.coarseSharedPair)).size = 137 ∧
      (inlineExitPaths.filter fun row =>
        row.coarseSharedPair && row.pathClass == .stayChild).size = 11 ∧
      (inlineExitPaths.filter fun row =>
        row.coarseSharedPair && row.pathClass == .resumeParent).size = 9 ∧
      (inlineExitPaths.filter fun row =>
        row.coarseSharedPair && row.pathClass == .propagate).size = 117 ∧
      (inlineSourceKeys.filter fun key =>
        inlineSourceCoarseShared key && inlineSourceMixed key).length = 20 := by
  native_decide

def inlineWitnessRows (parentDieOffset childDieOffset source : Nat) :
    Array (ExitArm × Nat × InlinePathClass) :=
  (inlineExitPaths.filter fun row =>
    row.parentDieOffset == parentDieOffset &&
      row.childDieOffset == childDieOffset &&
      row.source == source).map fun row =>
        (row.arm, row.target, row.pathClass)

/-- Concrete mixed-arm witnesses. The first stays in both extents on one arm and propagates past
both on the other; the second resumes its parent on one arm and propagates on the other. -/
theorem representative_mixed_inline_sources :
    inlineWitnessRows 8487 8508 66452 = #[
      (.conditionalTaken, 66592, .propagate),
      (.conditionalNotTaken, 66456, .stayChild)
    ] ∧
      inlineWitnessRows 12827 12857 72140 = #[
        (.conditionalTaken, 72492, .propagate),
        (.conditionalNotTaken, 72144, .resumeParent)
      ] := by
  native_decide

/-! ## Mutation power -/

/-- This preserves the two targets, the row count, and each target's extent bit while exchanging
only which conditional arm reaches which target. An unlabelled successor-set check cannot see it. -/
def branchArmSwap : Array StaticExitPath :=
  staticExitPaths.map fun row =>
    if row.dieOffset == 8508 && row.source == 66452 then
      match row.arm with
      | .conditionalTaken => { row with target := 66456, insideExecution := true }
      | .conditionalNotTaken => { row with target := 66592, insideExecution := false }
      | _ => row
    else row

def branchArmDrop : Array StaticExitPath :=
  staticExitPaths.filter fun row =>
    !(row.dieOffset == 8508 && row.source == 66452 &&
      row.arm == .conditionalNotTaken)

/-- A tail call's immediate callee is not its completion. This mutant puts the `memcpy` entry in
the `callReturn` row where the decoded consumer requires the fall-through return address. -/
def callCalleeForReturn : Array StaticExitPath :=
  staticExitPaths.map fun row =>
    if row.dieOffset == 8487 && row.source == 66360 &&
        row.arm == .callReturn then
      { row with target := 81592, insideExecution := true }
    else row

def jumpExitRowValid (row : JumpExitRow) : Bool :=
  match generatedProgram.functionInstances[row.functionIndex]?,
      ControlFlowNodeAt? nodes row.source with
  | some functionInstance, some { transfer := .jump (some target), .. } =>
      let targetInstance := generatedAtEntry? target
      row.dieOffset == functionInstance.provenance.entryOffset &&
        functionInstance.exitPcs.contains row.source &&
        row.target == target &&
        row.role == (match targetInstance with
          | some pair => .tailDelegate pair.2
          | none => .directCompletion) &&
        row.targetInsideExecution == inExecution functionInstance target &&
        row.declaredExternalCall == (targetInstance.any fun pair =>
          functionInstance.externalCalls.any fun id => decide (id = pair.1.id)) &&
        row.currentCategory ==
          classifyEdge functionInstance { source := row.source, target }
  | _, _ => false

def jumpExitDatasetValid (rows : Array JumpExitRow) : Bool :=
  rows == jumpExitRows && rows.all jumpExitRowValid

def allocatorTailTagLost : Array JumpExitRow :=
  jumpExitRows.map fun row =>
    if row.dieOffset == 19818 && row.source == 79740 then
      { row with role := .directCompletion }
    else row

def allocatorTailTargetChanged : Array JumpExitRow :=
  jumpExitRows.map fun row =>
    if row.dieOffset == 19818 && row.source == 79740 then
      { row with target := 79744 }
    else row

/-- Each mutation is checked through the same consumer-shaped validators as the canonical rows.
The arm swap is the important non-cardinality probe; the call mutation distinguishes immediate
callee from completion; and the two allocator mutations independently protect target and role. -/
theorem measurement_mutation_power :
    staticPathDatasetValid branchArmSwap = false ∧
      branchArmSwap.size = staticExitPaths.size ∧
      staticPathDatasetValid branchArmDrop = false ∧
      branchArmDrop.size + 1 = staticExitPaths.size ∧
      staticPathDatasetValid callCalleeForReturn = false ∧
      callCalleeForReturn.size = staticExitPaths.size ∧
      jumpExitDatasetValid jumpExitRows = true ∧
      jumpExitDatasetValid allocatorTailTagLost = false ∧
      jumpExitDatasetValid allocatorTailTargetChanged = false := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.ExitPathMeasurement
