import BinaryFv.Keccak.CallClosure

namespace BinaryFv.Keccak

open BinaryFv.RISCV

def syntacticClosureStackWritesClassified (sets : Array FunctionWordSet) (closure : Array Nat) :
    Bool :=
  closure.all fun start =>
    match functionWordSetAtStart? sets start with
    | some set => set.stackWritesClassified
    | none => false

def entrySyntacticClosureStackWritesClassified : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureStackWritesClassified sets closure
  | _, _ => false

/-- Closed static inspection: all selected closure writes to `sp` are classified adjustments. -/
theorem entry_syntactic_closure_stack_writes_classified :
    entrySyntacticClosureStackWritesClassified = true := by
  native_decide

structure StackDeltaState where
  address : Nat
  delta : Int
deriving Repr

/-- A static control-flow boundary deliberately not traversed by function-local delta flow. -/
inductive StackFlowFrontierKind where
  | call (target : Option Nat) (returnAddress : Nat) (link : regidx)
  | return_ (link : regidx)
  | indirectCall (returnAddress : Nat) (link : regidx)
  | indirectTransfer
  | terminal
  | leavingFunction (target : Nat)
  | unknownConditionalTarget
  | unknownJumpTarget
deriving Repr

structure StackFlowFrontier where
  address : Nat
  kind : StackFlowFrontierKind
deriving Repr

structure IntraproceduralStackFlow where
  states : Array StackDeltaState
  frontiers : Array StackFlowFrontier
deriving Repr

inductive StackFlowError where
  | missingNode (address : Nat)
  | unclassifiedStackWrite (address : Nat)
  | conflictingDelta (address : Nat) (first second : Int)
  | fuelExhausted
deriving Repr

def stackDeltaAt? (states : Array StackDeltaState) (address : Nat) : Option Int :=
  (states.toList.find? fun state => state.address == address).map StackDeltaState.delta

def decodedStackAdjustment? (word : DecodedWord) : Option Int :=
  if word.writesStackPointer then word.stackDelta? else some 0

def directIntraFlowTargets (node : ControlFlowNode) : Array Nat :=
  match node.transfer with
  | .fallthrough next => #[next]
  | .conditional (some taken) notTaken => #[taken, notTaken]
  | .conditional none notTaken => #[notTaken]
  | .jump (some target) => #[target]
  | .jump none | .call _ _ _ | .indirect | .indirectCall _ _ | .return_ _ | .terminal => #[]

def intraFlowSuccessors (nodes : Array ControlFlowNode) (node : ControlFlowNode) : Array Nat :=
  (directIntraFlowTargets node).filter (hasControlFlowAddress nodes)

def leavingFunctionFrontiers (nodes : Array ControlFlowNode) (node : ControlFlowNode) :
    Array StackFlowFrontier :=
  (directIntraFlowTargets node).foldl (fun frontiers target =>
    if hasControlFlowAddress nodes target then frontiers
    else
      frontiers.push {
        address := node.word.encoded.address
        kind := .leavingFunction target
      }) #[]

def stackFlowFrontiers (nodes : Array ControlFlowNode) (node : ControlFlowNode) :
    Array StackFlowFrontier :=
  let address := node.word.encoded.address
  match node.transfer with
  | .call target returnAddress link => #[{ address, kind := .call target returnAddress link }]
  | .return_ link => #[{ address, kind := .return_ link }]
  | .indirectCall returnAddress link => #[{ address, kind := .indirectCall returnAddress link }]
  | .indirect => #[{ address, kind := .indirectTransfer }]
  | .terminal => #[{ address, kind := .terminal }]
  | .conditional none _ =>
    #[{ address, kind := .unknownConditionalTarget }] ++ leavingFunctionFrontiers nodes node
  | .jump none => #[{ address, kind := .unknownJumpTarget }]
  | _ => leavingFunctionFrontiers nodes node

def addStackDeltaState (states : Array StackDeltaState) (pending : List Nat) (address : Nat)
    (delta : Int) : Except StackFlowError (Array StackDeltaState × List Nat) :=
  match stackDeltaAt? states address with
  | none => pure (states.push { address, delta }, pending ++ [address])
  | some known =>
    if known == delta then pure (states, pending)
    else throw (.conflictingDelta address known delta)

/--
Static, non-linear delta exploration over direct edges contained in one function symbol. It does not
assume that calls return, that return links are valid, or that a decoded CFG edge is semantically
executed. Those cases are emitted as frontiers for later proof obligations.
-/
def intraproceduralStackDeltaFlow (set : FunctionWordSet) :
    Except StackFlowError IntraproceduralStackFlow :=
  let nodes := controlFlowNodes set.words
  let rec enqueue : Array StackDeltaState → List Nat → Int → List Nat →
      Except StackFlowError (Array StackDeltaState × List Nat)
    | states, pending, _, [] => pure (states, pending)
    | states, pending, delta, successor :: successors => do
      let (states, pending) ← addStackDeltaState states pending successor delta
      enqueue states pending delta successors
  let rec loop : Nat → Array StackDeltaState → List Nat → Array StackFlowFrontier →
      Except StackFlowError IntraproceduralStackFlow
    | 0, states, [], frontiers => pure { states, frontiers }
    | 0, _, _ :: _, _ => throw .fuelExhausted
    | _ + 1, states, [], frontiers => pure { states, frontiers }
    | fuel + 1, states, address :: pending, frontiers => do
      let some node := ControlFlowNodeAt? nodes address | throw (.missingNode address)
      let some adjustment := decodedStackAdjustment? node.word |
        throw (.unclassifiedStackWrite address)
      let current := (stackDeltaAt? states address).getD 0
      let next := current + adjustment
      let frontiers := frontiers ++ stackFlowFrontiers nodes node
      let (states, pending) ← enqueue states pending next (intraFlowSuccessors nodes node).toList
      loop fuel states pending frontiers
  if hasControlFlowAddress nodes set.function.value then
    loop (nodes.size + 1) #[{ address := set.function.value, delta := 0 }] [set.function.value] #[]
  else
    throw (.missingNode set.function.value)

def entryClosureIntraproceduralStackFlows? :
    Option (Array (Nat × Except StackFlowError IntraproceduralStackFlow)) :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure =>
    some <| closure.map fun start =>
      match functionWordSetAtStart? sets start with
      | some set => (start, intraproceduralStackDeltaFlow set)
      | none => (start, .error (.missingNode start))
  | _, _ => none

def entryClosureIntraproceduralStackFlowsSucceed : Bool :=
  match entryClosureIntraproceduralStackFlows? with
  | some flows => flows.all fun flow => flow.2.isOk
  | none => false

def exploredDownwardDelta (delta : Int) : Nat :=
  if delta < 0 then (-delta).toNat else 0

def maximumExploredDownwardDelta (flow : IntraproceduralStackFlow) : Nat :=
  flow.states.foldl (fun demand state => max demand (exploredDownwardDelta state.delta)) 0

/--
Summary of the finite states explored before the current function-local frontier model stops.
`maximumExploredDownwardDelta` is not a local, runtime, or global stack bound: calls and other
frontiers deliberately truncate the explored state set.
-/
structure FrontierTruncatedStackStateSummary where
  functionStart : Nat
  maximumExploredDownwardDelta : Nat
  frontierCount : Nat
deriving Repr

def entryClosureFrontierTruncatedStackStateSummaries? :
    Option (Array FrontierTruncatedStackStateSummary) :=
  match entryClosureIntraproceduralStackFlows? with
  | some flows =>
    flows.foldl (fun summaries flow =>
      match summaries, flow.2 with
      | some summaries, .ok result =>
        some <| summaries.push {
          functionStart := flow.1
          maximumExploredDownwardDelta := maximumExploredDownwardDelta result
          frontierCount := result.frontiers.size
        }
      | _, _ => none) (some #[])
  | none => none

def entryClosureFrontierTruncatedStackStateSummariesAvailable : Bool :=
  entryClosureFrontierTruncatedStackStateSummaries?.isSome

/--
Closed availability fact for static frontier-truncated state summaries. It is not a stack-bound
theorem; a later proof must discharge the recorded frontiers before drawing that conclusion.
-/
theorem entry_closure_frontier_truncated_stack_state_summaries_available :
    entryClosureFrontierTruncatedStackStateSummariesAvailable = true := by
  native_decide

/--
Closed static exploration fact. It does not provide a stack bound or establish that generated Sail
execution follows the explored edges.
-/
theorem entry_closure_intraprocedural_stack_flows_succeed :
    entryClosureIntraproceduralStackFlowsSucceed = true := by
  native_decide

end BinaryFv.Keccak
