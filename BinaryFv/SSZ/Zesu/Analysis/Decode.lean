import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.RiscV.ELF.CFG
import BinaryFv.RiscV.Model.State

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

private def decodeState : State := {
  initialState with
  regs := (((initialState.regs.insert cur_privilege Privilege.Machine).insert mseccfg 0#64).insert
    misa (1#64 <<< 12))
}

def decodedWords? : Option (Array DecodedWord) :=
  match Artifact.parsed with
  | .ok parsedElf =>
    match parsedElf.executableWords with
    | .ok words =>
      match (decodeWords words).run decodeState with
      | .ok decoded _ => some decoded
      | .error _ _ => none
    | .error _ => none
  | .error _ => none

def controlFlow? : Option (Array ControlFlowNode) := decodedWords?.map controlFlowNodes

def wordsLegal : Bool :=
  match decodedWords? with
  | some words => words.all DecodedWord.legal
  | none => false

theorem words_legal : wordsLegal = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Analysis
