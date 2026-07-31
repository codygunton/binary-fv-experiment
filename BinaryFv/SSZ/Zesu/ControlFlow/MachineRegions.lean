import BinaryFv.SSZ.Zesu.ControlFlow.Decode
import GeneratedMachineRegions

/-!
# Independent checks for the generated machine-region database

LLVM proposes the address/word table, CFG, ownership partition, and SCC certificate. These checks tie
the proposal back to the production ELF decoded through Sail. The SCC certificate consists of strongly
connected members plus a strictly increasing rank on every cross-component edge; consequently its
condensation is acyclic and no two proposed components can belong to one larger SCC.
-/

namespace BinaryFv.SSZ.Zesu.MachineRegions

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.ControlFlow (controlFlow?)
open Generated

set_option maxRecDepth 8000

def wordsMatch (nodes : Array ControlFlowNode) : Bool :=
  words.all fun row =>
    match ControlFlowNodeAt? nodes row.1 with
    | some node => node.word.encoded.bits.toNat == row.2
    | none => false

def generatedSuccessors (address : Nat) : List Nat :=
  (edges.toList.filter fun edge => edge.1 == address).map Prod.snd

def edgesMatch (nodes : Array ControlFlowNode) : Bool :=
  let addresses := words.map Prod.fst
  words.all fun row =>
    let decoded := (directSuccessorsAt nodes row.1).filter fun target => addresses.contains target
    let proposed := (generatedSuccessors row.1).toArray
    decoded.all proposed.contains && proposed.all decoded.contains

def ownershipTiles : Bool :=
  ownership.map Prod.fst == words.map Prod.fst

def sccMembershipTiles : Bool :=
  sccMembership.map Prod.fst == words.map Prod.fst

def component? (address : Nat) : Option Nat :=
  (sccMembership.toList.find? fun row => row.1 == address).map Prod.snd

def rank? (component : Nat) : Option Nat :=
  (sccRanks.toList.find? fun row => row.1 == component).map Prod.snd

def root? (component : Nat) : Option Nat :=
  (sccRoots.toList.find? fun row => row.1 == component).map Prod.snd

def treeDepth? (tree : Array SccTreeRow) (address : Nat) : Option Nat :=
  (tree.find? fun row => row.address == address).map SccTreeRow.depth

def treeValid (tree : Array SccTreeRow) (reverse : Bool) : Bool :=
  tree.size == words.size &&
    words.all (fun word => tree.any fun row => row.address == word.1) &&
    tree.all fun row =>
      match component? row.address, component? row.parent with
      | some component, some parentComponent =>
          component == parentComponent &&
            if row.depth == 0 then
              root? component == some row.address && row.parent == row.address
            else
              treeDepth? tree row.parent == some (row.depth - 1) &&
                if reverse then
                  edges.contains (row.address, row.parent)
                else
                  edges.contains (row.parent, row.address)
      | _, _ => false

def componentsStronglyConnected : Bool :=
  treeValid sccForwardTree false && treeValid sccReverseTree true

def condensationRanksIncrease : Bool :=
  edges.all fun edge =>
    match component? edge.1, component? edge.2 with
    | some source, some target =>
        source == target ||
          match rank? source, rank? target with
          | some sourceRank, some targetRank => sourceRank < targetRank
          | _, _ => false
    | _, _ => false

def validatesAgainstProduction : Bool :=
  match controlFlow? with
  | some nodes =>
      wordsMatch nodes && edgesMatch nodes && ownershipTiles && sccMembershipTiles &&
        componentsStronglyConnected && condensationRanksIncrease
  | none => false

theorem validates_against_production : validatesAgainstProduction = true := by
  native_decide

/-! Power probes: each independent field check rejects a representative corruption. -/

theorem word_mutation_rejected :
    (match controlFlow? with
    | some nodes =>
        let badWords := words.set! 0 (words[0]!.1, words[0]!.2 + 1)
        badWords.all fun row =>
          match ControlFlowNodeAt? nodes row.1 with
          | some node => node.word.encoded.bits.toNat == row.2
          | none => false
    | none => false) = false := by
  native_decide

theorem edge_deletion_rejected :
    (match controlFlow? with
    | some nodes =>
        let badEdges := edges.pop
        let addresses := words.map Prod.fst
        words.all fun row =>
          let decoded := (directSuccessorsAt nodes row.1).filter fun target => addresses.contains target
          let proposed :=
            ((badEdges.toList.filter fun edge => edge.1 == row.1).map Prod.snd).toArray
          decoded.all proposed.contains && proposed.all decoded.contains
    | none => false) = false := by
  native_decide

theorem ownership_deletion_rejected :
    (ownership.pop.map Prod.fst == words.map Prod.fst) = false := by
  native_decide

end BinaryFv.SSZ.Zesu.MachineRegions
