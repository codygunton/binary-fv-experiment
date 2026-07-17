import BinaryFv.RiscV.Analysis.FunctionWords

/-!
# Syntactic call graph and function closure

Resolution of direct-call obligations against a set of decoded functions, and the syntactic closure
of the functions reachable from an entry. Parameterized by the function word sets and the entry;
which functions a binary has, and whether its closure is well-behaved, are target facts.
-/

namespace BinaryFv.RiscV

def parserFunctionAtAddress? (functions : Array StaticSymbol) (address : Nat) :
    Option StaticSymbol :=
  match (functions.filter fun function => functionContainsAddress function address).toList with
  | [function] => some function
  | _ => none

def functionWordSetAtStart? (sets : Array FunctionWordSet) (start : Nat) : Option FunctionWordSet :=
  match (sets.filter fun set => set.function.value == start).toList with
  | [set] => some set
  | _ => none

/--
A static transfer which prevents a direct call target from being fully resolved.
Dynamic return candidates remain in `FunctionWordSet.returnCandidates` for separate link checking.
-/
inductive SyntacticCallObligation where
  | unresolvedDirect (source returnAddress : Nat) (link : regidx)
  | indirectCall (source returnAddress : Nat) (link : regidx)
  | indirectTransfer (source : Nat)

/-- A decoder-derived direct-call candidate or an explicit unresolved-transfer obligation. -/
inductive SyntacticCallResolution where
  | resolved (call : DirectCallEdge) (callee : StaticSymbol)
  | unresolved (obligation : SyntacticCallObligation)

def SyntacticCallResolution.isResolved : SyntacticCallResolution → Bool
  | .resolved _ _ => true
  | .unresolved _ => false

def SyntacticCallResolution.obligation? : SyntacticCallResolution → Option SyntacticCallObligation
  | .resolved _ _ => none
  | .unresolved obligation => some obligation

def syntacticCallResolutions (set : FunctionWordSet) (functions : Array StaticSymbol) :
    Array SyntacticCallResolution :=
  (controlFlowNodes set.words).foldl (fun resolutions node =>
    match node.transfer with
    | .call (some target) returnAddress link =>
      let call : DirectCallEdge := {
        source := node.word.encoded.address
        target
        returnAddress
        link
      }
      match parserFunctionAtAddress? functions target with
      | some callee => resolutions.push (.resolved call callee)
      | none =>
        resolutions.push (.unresolved (.unresolvedDirect call.source call.returnAddress call.link))
    | .call none returnAddress link =>
      resolutions.push <|
        .unresolved (.unresolvedDirect node.word.encoded.address returnAddress link)
    | .indirectCall returnAddress link =>
      resolutions.push (.unresolved (.indirectCall node.word.encoded.address returnAddress link))
    | .indirect => resolutions.push (.unresolved (.indirectTransfer node.word.encoded.address))
    | _ => resolutions) #[]

def containsFunctionStart (starts : Array Nat) (start : Nat) : Bool :=
  starts.any fun known => known == start

def appendResolvedCallees (known : Array Nat) (resolutions : Array SyntacticCallResolution) :
    Array Nat :=
  resolutions.foldl (fun known resolution =>
    match resolution with
    | .resolved _ callee =>
      if containsFunctionStart known callee.value then known else known.push callee.value
    | .unresolved _ => known) known

def expandSyntacticFunctionClosure (sets : Array FunctionWordSet) (known : Array Nat) : Array Nat :=
  let functions := sets.map FunctionWordSet.function
  known.foldl (fun known start =>
    match functionWordSetAtStart? sets start with
    | some set => appendResolvedCallees known (syntacticCallResolutions set functions)
    | none => known) known

/--
Finite function-level closure over every decoded call candidate in each selected symbol.
This is deliberately not a semantic or basic-block reachability relation.
-/
def syntacticFunctionClosureFrom (sets : Array FunctionWordSet) (entry : Nat) : Array Nat :=
  let rec loop : Nat → Array Nat → Array Nat
    | 0, known => known
    | fuel + 1, known =>
      let expanded := expandSyntacticFunctionClosure sets known
      if expanded.size == known.size then known else loop fuel expanded
  if (functionWordSetAtStart? sets entry).isSome then loop (sets.size + 1) #[entry] else #[]

def syntacticClosureResolvesOnlyParserFunctions (sets : Array FunctionWordSet)
    (closure : Array Nat) : Bool :=
  let functions := sets.map FunctionWordSet.function
  closure.all fun start =>
    match functionWordSetAtStart? sets start with
    | some set => (syntacticCallResolutions set functions).all SyntacticCallResolution.isResolved
    | none => false

def SyntacticCallResolution.targetIsCalleeStart : SyntacticCallResolution → Bool
  | .resolved call callee => call.target == callee.value
  | .unresolved _ => false

/--
Checks decoded direct-call targets against the selected static symbol starts. This remains a
syntactic check: it does not show that any dynamic control path reaches a call or its target.
-/
def syntacticClosureTargetsAreFunctionStarts (sets : Array FunctionWordSet) (closure : Array Nat) :
    Bool :=
  let functions := sets.map FunctionWordSet.function
  closure.all fun start =>
    match functionWordSetAtStart? sets start with
    | some set =>
      (syntacticCallResolutions set functions).all SyntacticCallResolution.targetIsCalleeStart
    | none => false

def syntacticClosureDirectCallLinks (sets : Array FunctionWordSet) (closure : Array Nat) :
    Array regidx :=
  let functions := sets.map FunctionWordSet.function
  closure.foldl (fun links start =>
    match functionWordSetAtStart? sets start with
    | some set =>
      (syntacticCallResolutions set functions).foldl (fun links resolution =>
        match resolution with
        | .resolved call _ => links.push call.link
        | .unresolved _ => links) links
    | none => links) #[]

def syntacticClosureReturnLinks (sets : Array FunctionWordSet) (closure : Array Nat) :
    Array regidx :=
  closure.foldl (fun links start =>
    match functionWordSetAtStart? sets start with
    | some set => set.returnCandidates.foldl (fun links candidate => links.push candidate.2) links
    | none => links) #[]

def SyntacticCallResolution.callsFunctionWithLink (resolution : SyntacticCallResolution)
    (function : StaticSymbol) (link : regidx) : Bool :=
  match resolution with
  | .resolved call callee => callee.value == function.value && call.link == link
  | .unresolved _ => false

def syntacticClosureHasIncomingResolvedCallWithLink (sets : Array FunctionWordSet)
    (closure : Array Nat) (function : StaticSymbol) (link : regidx) : Bool :=
  let functions := sets.map FunctionWordSet.function
  closure.any fun callerStart =>
    match functionWordSetAtStart? sets callerStart with
    | some caller =>
      (syntacticCallResolutions caller functions).any fun resolution =>
        resolution.callsFunctionWithLink function link
    | none => false

/--
Checks a necessary syntactic association only: every return candidate in a selected non-entry
function has an incoming resolved direct call in this closure to that function using its link.
The parser-derived entry is exempt because it returns to the frozen ABI sentinel, not an in-ELF
direct caller. This does not establish dynamic call/return pairing, reachability, or return values.
-/
def syntacticClosureNonEntryReturnCandidatesHaveIncomingResolvedCalls
    (sets : Array FunctionWordSet) (closure : Array Nat) (entryStart : Nat) : Bool :=
  closure.all fun start =>
    match functionWordSetAtStart? sets start with
    | some set =>
      if set.function.value == entryStart then
        true
      else
        set.returnCandidates.all fun candidate =>
          syntacticClosureHasIncomingResolvedCallWithLink sets closure set.function candidate.2
    | none => false

/--
Checks only register availability: each static return link occurs in some static direct call in the
same closure. It deliberately does not pair a return with a caller or establish call/return
semantics.
-/
def syntacticClosureReturnLinksHaveAvailableCallLinks (sets : Array FunctionWordSet)
    (closure : Array Nat) : Bool :=
  let callLinks := syntacticClosureDirectCallLinks sets closure
  (syntacticClosureReturnLinks sets closure).all fun returnLink =>
    callLinks.any fun callLink => callLink == returnLink

def closureWordSets? (sets : Array FunctionWordSet) (closure : Array Nat) :
    Option (Array FunctionWordSet) :=
  closure.foldl (fun selected start => do
    let selected ← selected
    let set ← functionWordSetAtStart? sets start
    pure (selected.push set)) (some #[])

end BinaryFv.RiscV
