import BinaryFv.SSZ.Zesu.Elfling.GeneratedValidationBridges
import BinaryFv.SSZ.Zesu.ControlFlow.Decode
import GeneratedElfling

/-!
# Byte-level instruction check: every generated PC decodes to a legal instruction

The M3 slice only checked that trace PCs fell inside DWARF-proposed ranges. This module makes the
trust-boundary step-up the plan requires: DWARF *proposes* the ranges, and Lean confirms them against
the **canonical ELF bytes** by re-decoding. For every 4-byte program counter of every generated
region, the statically decoded control-flow graph of the canonical `Artifact` ELF has a node at that
exact address whose decoded instruction is legal (not `ILLEGAL`/`C_ILLEGAL`). Because the check
dispatches through `controlFlow?` — the full ELF parse + per-word Sail decode — a `true` result also
certifies that the canonical ELF decoded.

Region sizes are all multiples of four (`generated_regions_word_aligned`), so the `r.size / 4`
word-PCs of each region exactly tile `[start, stop)`: no byte between word boundaries is skipped, so
the check is not vacuous on a partial word.

This is an SSZ/artifact-layer fact, so the `Bool` uses the documented `native_decide` trust; the
bridge that turns it into the per-PC statement is an ordinary kernel proof.
-/

namespace BinaryFv.SSZ.Zesu.Elfling.Validation

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.ControlFlow
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedElfling)

/-! ## Region word-alignment (so the word-PCs tile each region) -/

/-- Every generated region has a size divisible by 4. -/
def regionsWordAlignedB : Bool :=
  generatedElfling.functionInstances.all fun functionInstance => functionInstance.regions.all fun r => r.size % 4 == 0

theorem regionsWordAlignedB_true : regionsWordAlignedB = true := by native_decide

theorem generated_regions_word_aligned :
    ∀ functionInstance ∈ generatedElfling.functionInstances, ∀ r ∈ functionInstance.regions, r.size % 4 = 0 := by
  intro functionInstance hFunctionInstance r hr
  have h := forall_mem_of_all (forall_mem_of_all regionsWordAlignedB_true functionInstance hFunctionInstance) r hr
  exact eq_of_beq h

/-! ## The per-PC decode + legality check -/

/-- At every word-PC of every region, the decoded CFG has a node whose instruction is legal. -/
def regionPCsLegalIn (nodes : Array ControlFlowNode) (program : Elfling) : Bool :=
  program.functionInstances.all fun functionInstance =>
    functionInstance.regions.all fun r =>
      (List.range (r.size / 4)).all fun i =>
        match ControlFlowNodeAt? nodes (r.start + 4 * i) with
        | some node => node.word.legal
        | none => false

/-- The check dispatched through the canonical decoded control flow. `Option.map`/`getD` (not a
`match`) so the bridge below never forces the kernel to reduce `controlFlow?` (the full ELF decode). -/
def regionPCsLegal : Bool :=
  (controlFlow?.map (fun nodes => regionPCsLegalIn nodes generatedElfling)).getD false

theorem regionPCsLegal_true : regionPCsLegal = true := by native_decide

/-- The canonical ELF decodes to some node array. -/
theorem controlFlow_exists : ∃ nodes, controlFlow? = some nodes :=
  Option.isSome_iff_exists.mp (by native_decide : controlFlow?.isSome = true)

/-- Specialise the dispatched check to explicit decoded `nodes` without reducing the decode. -/
theorem regionPCsLegal_some {nodes : Array ControlFlowNode}
    (hn : controlFlow? = some nodes) (h : regionPCsLegal = true) :
    regionPCsLegalIn nodes generatedElfling = true := by
  unfold regionPCsLegal at h
  rw [hn] at h
  simpa only [Option.map_some, Option.getD_some] using h

/-- Extract the per-PC decode fact from the aggregate `Bool`. -/
theorem regionPCsLegalIn_elim {nodes : Array ControlFlowNode} {program : Elfling}
    (h : regionPCsLegalIn nodes program = true)
    {functionInstance : FunctionInstance} (hFunctionInstance : functionInstance ∈ program.functionInstances)
    {r : AddressRange} (hr : r ∈ functionInstance.regions)
    {i : Nat} (hi : i < r.size / 4) :
    ∃ node, ControlFlowNodeAt? nodes (r.start + 4 * i) = some node ∧ node.word.legal = true := by
  have hf := forall_mem_of_all h functionInstance hFunctionInstance
  have hg := forall_mem_of_all hf r hr
  have hb := forall_mem_of_all_list hg i (List.mem_range.mpr hi)
  revert hb
  cases hc : ControlFlowNodeAt? nodes (r.start + 4 * i) with
  | none => intro hb; exact absurd hb (by decide)
  | some node => intro hb; exact ⟨node, rfl, hb⟩

/-! ## The certified statement -/

/-- **Every generated region PC corresponds to a real decoded legal instruction in the canonical
ELF.** The canonical ELF decodes; for every word-PC of every generated region there is a decoded
control-flow node *at that exact address* whose instruction is legal. DWARF proposed the ranges; this
confirms them against the ELF bytes. -/
theorem generated_region_pcs_are_legal_instructions :
    ∃ nodes, controlFlow? = some nodes ∧
      ∀ functionInstance ∈ generatedElfling.functionInstances, ∀ r ∈ functionInstance.regions, ∀ i, i < r.size / 4 →
        ∃ node, ControlFlowNodeAt? nodes (r.start + 4 * i) = some node ∧
          node.word.encoded.address = r.start + 4 * i ∧ node.word.legal = true := by
  obtain ⟨nodes, hn⟩ := controlFlow_exists
  refine ⟨nodes, hn, ?_⟩
  intro functionInstance hFunctionInstance r hr i hi
  obtain ⟨node, hnode, hlegal⟩ :=
    regionPCsLegalIn_elim (regionPCsLegal_some hn regionPCsLegal_true) hFunctionInstance hr hi
  refine ⟨node, hnode, ?_, hlegal⟩
  have hnode' : nodes.toList.find? (fun n => n.word.encoded.address == r.start + 4 * i) = some node :=
    hnode
  have hp := List.find?_some hnode'
  exact eq_of_beq hp

end BinaryFv.SSZ.Zesu.Elfling.Validation
