import BinaryFv.Keccak.Decode
import BinaryFv.RiscV.Stack

namespace BinaryFv.Keccak

open BinaryFv.RiscV

/-- Parser-owned executable function symbols, without target names or addresses. -/
def artifactFunctions : Except ArtifactDecodeError (Array StaticSymbol) := do
  let elf ← Artifact.parsed.mapError .elf
  pure elf.executableFunctions

def functionContainsDecodedWord (function : StaticSymbol) (word : DecodedWord) : Bool :=
  function.value ≤ word.encoded.address && word.encoded.address + 4 ≤ function.value + function.size

/-- A parser-selected function together with its decoded fixed-width executable words. -/
structure FunctionWordSet where
  function : StaticSymbol
  words : Array DecodedWord

def functionWordSet (function : StaticSymbol) (words : Array DecodedWord) : FunctionWordSet where
  function
  words := words.filter (functionContainsDecodedWord function)

def artifactFunctionWordSets? : Option (Array FunctionWordSet) :=
  match artifactFunctions, artifactDecodedWords? with
  | .ok functions, some words => some (functions.map fun function => functionWordSet function words)
  | _, _ => none

def functionContainsAddress (function : StaticSymbol) (address : Nat) : Bool :=
  function.value ≤ address && address < function.value + function.size

def artifactEntryFunction? : Option StaticSymbol :=
  match Artifact.entryAddress, artifactFunctions with
  | .ok entry, .ok functions =>
    match (functions.filter fun function => functionContainsAddress function entry).toList with
    | [function] => some function
    | _ => none
  | _, _ => none

def artifactEntryWordSet? : Option FunctionWordSet :=
  match artifactEntryFunction?, artifactDecodedWords? with
  | some function, some words => some (functionWordSet function words)
  | _, _ => none

def portableCoreWordSet? : Option FunctionWordSet :=
  match portableCore, artifactDecodedWords? with
  | .ok function, some words => some (functionWordSet function words)
  | _, _ => none

def FunctionWordSet.stackWritesClassified (set : FunctionWordSet) : Bool :=
  set.words.all DecodedWord.stackWriteClassified

def allArtifactFunctionStackWritesClassified : Bool :=
  match artifactFunctionWordSets? with
  | some sets => sets.all FunctionWordSet.stackWritesClassified
  | none => false

def entryAndPortableCoreWordSets? : Option (Array FunctionWordSet) :=
  match artifactEntryWordSet?, portableCoreWordSet? with
  | some entry, some core =>
    if entry.function.value == core.function.value then some #[entry] else some #[entry, core]
  | _, _ => none

def entryAndPortableCoreStackWritesClassified : Bool :=
  match entryAndPortableCoreWordSets? with
  | some sets => sets.all FunctionWordSet.stackWritesClassified
  | none => false

def portableCoreStackWritesClassified : Bool :=
  match portableCoreWordSet? with
  | some set => set.stackWritesClassified
  | none => false

/-- Closed fixed-artifact inspection for the parser-selected entry and portable core. -/
theorem entry_and_portable_core_stack_writes_classified :
    entryAndPortableCoreStackWritesClassified = true := by
  native_decide

/-- Closed fixed-artifact inspection for the structurally selected portable Keccak core. -/
theorem portable_core_stack_writes_classified : portableCoreStackWritesClassified = true := by
  native_decide

/-- Direct call candidates retain the generated decoder's resolved target and link register. -/
def FunctionWordSet.directCallCandidates (set : FunctionWordSet) : Array DirectCallEdge :=
  directCallEdges (controlFlowNodes set.words)

/-- Return candidates retain their link register, including non-`ra` outlined-helper returns. -/
def FunctionWordSet.returnCandidates (set : FunctionWordSet) : Array (Nat × regidx) :=
  (controlFlowNodes set.words).foldl (fun candidates node =>
    match node.returnLink? with
    | some link => candidates.push (node.word.encoded.address, link)
    | none => candidates) #[]

def artifactFunctionDirectCallCandidates? : Option (Array (StaticSymbol × DirectCallEdge)) :=
  artifactFunctionWordSets?.map fun sets =>
    sets.flatMap fun set => set.directCallCandidates.map fun call => (set.function, call)

def artifactFunctionReturnCandidates? : Option (Array (StaticSymbol × Nat × regidx)) :=
  artifactFunctionWordSets?.map fun sets =>
    sets.flatMap fun set => set.returnCandidates.map fun candidate =>
      (set.function, candidate.1, candidate.2)

end BinaryFv.Keccak
