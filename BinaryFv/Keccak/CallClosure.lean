import BinaryFv.Keccak.Stack

namespace BinaryFv.Keccak

open BinaryFv.RISCV

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

def entrySyntacticFunctionClosure? : Option (Array Nat) :=
  match artifactEntryWordSet?, artifactFunctionWordSets? with
  | some entry, some sets => some (syntacticFunctionClosureFrom sets entry.function.value)
  | _, _ => none

def syntacticClosureResolvesOnlyParserFunctions (sets : Array FunctionWordSet)
    (closure : Array Nat) : Bool :=
  let functions := sets.map FunctionWordSet.function
  closure.all fun start =>
    match functionWordSetAtStart? sets start with
    | some set => (syntacticCallResolutions set functions).all SyntacticCallResolution.isResolved
    | none => false

def entrySyntacticClosureResolvesOnlyParserFunctions : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureResolvesOnlyParserFunctions sets closure
  | _, _ => false

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

def entrySyntacticClosureTargetsAreFunctionStarts : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureTargetsAreFunctionStarts sets closure
  | _, _ => false

def entrySyntacticClosureReturnLinksHaveAvailableCallLinks : Bool :=
  match artifactFunctionWordSets?, entrySyntacticFunctionClosure? with
  | some sets, some closure => syntacticClosureReturnLinksHaveAvailableCallLinks sets closure
  | _, _ => false

/-- Closed artifact fact for static function-level target resolution, not semantic reachability. -/
theorem entry_syntactic_closure_resolves_only_parser_functions :
    entrySyntacticClosureResolvesOnlyParserFunctions = true := by
  native_decide

/-- Closed syntactic target-start fact; it is not a dynamic control-flow theorem. -/
theorem entry_syntactic_closure_targets_are_function_starts :
    entrySyntacticClosureTargetsAreFunctionStarts = true := by
  native_decide

/-- Closed link-availability fact; it is not a caller/return-pairing or execution theorem. -/
theorem entry_syntactic_closure_return_links_have_available_call_links :
    entrySyntacticClosureReturnLinksHaveAvailableCallLinks = true := by
  native_decide

end BinaryFv.Keccak
