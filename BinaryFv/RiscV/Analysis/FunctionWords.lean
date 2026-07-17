import BinaryFv.RiscV.ELF.CFG
import BinaryFv.RiscV.ELF.Decode
import BinaryFv.RiscV.Analysis.StackFlow

/-!
# Function word sets

A decoded function's word set, and the syntactic classification of its stack writes, direct-call
candidates, and return candidates. Everything is parameterized by a `StaticSymbol` and an array of
`DecodedWord`s, so this is the pivot type the reachability, call-graph, and stack-flow analyses are
built on. Which functions a particular binary has is a target fact.
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open LeanRV64DExecutable.Functions

def functionContainsDecodedWord (function : StaticSymbol) (word : DecodedWord) : Bool :=
  function.value ≤ word.encoded.address && word.encoded.address + 4 ≤ function.value + function.size
/-- A parser-selected function together with its decoded fixed-width executable words. -/
structure FunctionWordSet where
  function : StaticSymbol
  words : Array DecodedWord
def functionWordSet (function : StaticSymbol) (words : Array DecodedWord) : FunctionWordSet where
  function
  words := words.filter (functionContainsDecodedWord function)
def functionContainsAddress (function : StaticSymbol) (address : Nat) : Bool :=
  function.value ≤ address && address < function.value + function.size
def FunctionWordSet.stackWritesClassified (set : FunctionWordSet) : Bool :=
  set.words.all DecodedWord.stackWriteClassified
/-- Direct call candidates retain the generated decoder's resolved target and link register. -/
def FunctionWordSet.directCallCandidates (set : FunctionWordSet) : Array DirectCallEdge :=
  directCallEdges (controlFlowNodes set.words)
/-- Return candidates retain their link register, including non-`ra` outlined-helper returns. -/
def FunctionWordSet.returnCandidates (set : FunctionWordSet) : Array (Nat × regidx) :=
  (controlFlowNodes set.words).foldl (fun candidates node =>
    match node.returnLink? with
    | some link => candidates.push (node.word.encoded.address, link)
    | none => candidates) #[]

end BinaryFv.RiscV
