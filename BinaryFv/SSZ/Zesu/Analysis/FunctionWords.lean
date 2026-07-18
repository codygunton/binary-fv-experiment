import BinaryFv.SSZ.Zesu.Analysis.Decode
import BinaryFv.RiscV.Analysis.FunctionWords

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV

/-- All executable function symbols selected by the parser from the immutable ELF. -/
def executableFunctions : Array StaticSymbol :=
  match Artifact.parsed with
  | .ok parsedElf => parsedElf.executableFunctions
  | .error _ => #[]

def functionWordSets? : Option (Array FunctionWordSet) :=
  decodedWords?.map fun words => executableFunctions.map fun function => functionWordSet function words

def entryFunction? : Option StaticSymbol :=
  match Artifact.zesuDecodeRaw with
  | .ok entry => some entry
  | .error _ => none

def entryWordSet? : Option FunctionWordSet := do
  let entry ← entryFunction?
  let words ← decodedWords?
  pure (functionWordSet entry words)

def entryStackWritesClassified : Bool :=
  match entryWordSet? with
  | some words => words.stackWritesClassified
  | none => false

theorem entry_stack_writes_classified : entryStackWritesClassified = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Analysis
