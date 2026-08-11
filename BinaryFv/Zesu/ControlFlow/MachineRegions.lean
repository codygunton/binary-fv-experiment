import BinaryFv.Zesu.ControlFlow.Decode
import GeneratedMachineRegions

/-!
# Checking the generated machine-region database

The generator uses LLVM to propose an instruction table, a direct control-flow graph, an owner for
every instruction, and a partition into strongly connected components (SCCs). An SCC is a maximal
group of instructions in which every instruction can reach every other instruction; a nontrivial SCC
therefore identifies a possible machine-code loop.

The generated data is not trusted. This module compares every proposed instruction word and direct
edge with the production ELF decoded through Sail, and checks that the ownership and SCC tables cover
exactly the same instructions. For each proposed SCC, generated forward and reverse spanning trees
prove mutual reachability. Ranks that strictly increase on edges between SCCs prove that two adjacent
components cannot really be one larger SCC and that collapsing each SCC leaves an acyclic graph.
`validates_against_production` combines all of these checks; the mutation theorems below show that
representative corruptions are rejected.
-/

namespace BinaryFv.Zesu.MachineRegions

open BinaryFv.RiscV
open BinaryFv.Zesu.ControlFlow (controlFlow?)
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

/-! ## The word table as file-backed image words

`wordsMatch` above ties every row to the Sail decode of the pinned ELF's executable words. The check
below ties the same rows to the *file-backed* bytes of `Artifacts.programImage`. That is a second,
independent reading of the same binary, and it is the reading a running machine can use: file-backed
bytes are the currency `CodeIntact` (`fileBytesLoadedFaithfully`) preserves, so a machine proof can take
its instruction word from this table instead of restating four byte literals at every address it
steps through. -/

/-- The generated instruction word recorded at `address`, if the table has a row for it. -/
def wordAt? (address : Nat) : Option Nat :=
  (words.find? fun row => row.1 == address).map Prod.snd

/-- Every generated row is a machine-word address whose four file-backed image bytes are exactly the
recorded little-endian word. Stated for an arbitrary image, so the pinned artifact enters only at the
instantiation below. -/
def wordsAreFileImageWords (image : BinaryFv.Binary.ProgramImage) : Bool :=
  words.all fun row =>
    decide (row.1 < 2 ^ 64) && (image.readFileU32LE? row.1 == some row.2)

theorem words_are_file_image_words :
    wordsAreFileImageWords Artifacts.programImage = true := by
  native_decide

/-- The per-address fact extracted from the aggregate check: a table lookup is a pinned-ELF file
read. This is the only bridge a proof needs; it never names bytes. -/
theorem readFileU32LE_of_wordAt {address word : Nat} (row : wordAt? address = some word) :
    address < 2 ^ 64 ∧ Artifacts.programImage.readFileU32LE? address = some word := by
  unfold wordAt? at row
  match hfind : words.find? (fun candidate => candidate.1 == address) with
  | none => rw [hfind] at row; exact absurd row (by simp)
  | some found =>
    rw [hfind] at row
    have foundWord : found.2 = word := by simpa using row
    have foundAddress : found.1 = address := by simpa using Array.find?_some hfind
    have checked := Array.all_eq_true.mp words_are_file_image_words
    obtain ⟨index, bound, get⟩ := Array.getElem_of_mem (Array.mem_of_find?_eq_some hfind)
    have rowChecked := checked index bound
    rw [get, Bool.and_eq_true, beq_iff_eq] at rowChecked
    rw [foundAddress, foundWord] at rowChecked
    exact ⟨of_decide_eq_true rowChecked.1, rowChecked.2⟩

/-! Power probes: the file-backed check rejects a corrupted word and a shifted address. -/

theorem file_image_word_mutation_rejected :
    (let badWords := words.set! 0 (words[0]!.1, words[0]!.2 + 1)
     badWords.all fun row =>
       decide (row.1 < 2 ^ 64) &&
         (Artifacts.programImage.readFileU32LE? row.1 == some row.2)) = false := by
  native_decide

theorem file_image_address_shift_rejected :
    (let badWords := words.set! 0 (words[0]!.1 + 1, words[0]!.2)
     badWords.all fun row =>
       decide (row.1 < 2 ^ 64) &&
         (Artifacts.programImage.readFileU32LE? row.1 == some row.2)) = false := by
  native_decide

end BinaryFv.Zesu.MachineRegions
