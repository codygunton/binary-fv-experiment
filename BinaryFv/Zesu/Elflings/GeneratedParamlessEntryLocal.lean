import BinaryFv.Zesu.ControlFlow.MachineRegions
import BinaryFv.Zesu.Elflings.GeneratedValidationBridges
import GeneratedBindings

/-!
# Validating the `decodeNewPayloadRequest` DWARF-paramless entry local

`decodeNewPayloadRequest@decodeRaw:207:61` has no formal-parameter DIEs, so this module does not
invent Zig's source ABI.  The generated binding artifact instead records the concrete inlined DIE's
named `result` local at the function instance's entry.  Nix accepts its DWARF sidecar only after its
`.text` is byte-identical to the canonical link input; the checks here bind that named sidecar record
to the generated production instance, its canonical entry PC, the decoded instruction state there,
and the file-backed instruction word.

This is a location witness only.  It says neither what `result` contains nor how source parameters
are represented at this optimized inlined boundary.
-/

namespace BinaryFv.Zesu.Elflings.Validation

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.Zesu.ControlFlow
open BinaryFv.Zesu.MachineRegions
open BinaryFv.Zesu.Elflings.Generated
open BinaryFv.Zesu.Elflings.GeneratedBindings

private def decodeNewPayloadRequestId : FunctionInstanceId :=
  functionInstance_ssz_raw_decodeNewPayloadRequest_in_ssz_raw_decodeRaw_at_207_61Id

/-- The sole currently admitted local-location witness.  Its identity is source-derived; no generated
catalog position occurs in this statement. -/
def decodeNewPayloadRequestResultEntryLocation :
    FunctionInstanceId × String × String × Int × Int × Nat :=
  (decodeNewPayloadRequestId, "result", "fbreg", 2, 2320, 67084)

/-- The generated sidecar output must contain precisely the admitted `result = sp + 2320` entry
location, with no silent additional interpretation. -/
theorem decodeNewPayloadRequest_result_entry_location_generated :
    paramlessEntryLocalWitnesses = [decodeNewPayloadRequestResultEntryLocation] := by native_decide

/-- The matching generated function instance carries the decoder sidecar hash that Nix checked
byte-identical against the production link input, and has the same entry PC as the local witness. -/
def decodeNewPayloadRequestProductionInstanceB : Bool :=
  generatedProgram.functionInstances.any fun functionInstance =>
    decide (functionInstance.id = decodeNewPayloadRequestId) &&
      functionInstance.entryPc == 67084 &&
      decide (functionInstance.provenance.sidecarHash =
        "f3a296a2510a8c7db132cacfb72cbd53266e609199ba844d31a777ca7072530d")

theorem decodeNewPayloadRequestProductionInstanceB_true :
    decodeNewPayloadRequestProductionInstanceB = true := by native_decide

theorem decodeNewPayloadRequest_result_entry_location_production_instance :
    ∃ functionInstance ∈ generatedProgram.functionInstances,
      functionInstance.id = decodeNewPayloadRequestId ∧ functionInstance.entryPc = 67084 ∧
        functionInstance.provenance.sidecarHash =
          "f3a296a2510a8c7db132cacfb72cbd53266e609199ba844d31a777ca7072530d" := by
  obtain ⟨functionInstance, hinstance, hcheck⟩ :=
    exists_mem_of_any decodeNewPayloadRequestProductionInstanceB_true
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    decide_eq_true_eq] at hcheck
  exact ⟨functionInstance, hinstance, hcheck.1.1, hcheck.1.2, hcheck.2⟩

/-- The Sail-decoded canonical instruction state at the witness entry. -/
def decodeNewPayloadRequestEntryInstructionStateAt (nodes : Array ControlFlowNode) : Bool :=
  match ControlFlowNodeAt? nodes 67084 with
  | some node => decide (node.word.encoded.address = 67084) && node.word.legal
  | none => false

/-- Dispatch through `controlFlow?` only in compiled evaluation: the theorem below transports the
result through a variable `nodes`, so Lean does not reduce the pinned ELF while checking it. -/
def decodeNewPayloadRequestEntryInstructionStateB : Bool :=
  (controlFlow?.map decodeNewPayloadRequestEntryInstructionStateAt).getD false

theorem decodeNewPayloadRequestEntryInstructionStateB_true :
    decodeNewPayloadRequestEntryInstructionStateB = true := by native_decide

theorem decodeNewPayloadRequest_result_entry_instruction_state :
    ∃ nodes, controlFlow? = some nodes ∧
      ∃ node, ControlFlowNodeAt? nodes 67084 = some node ∧
        node.word.encoded.address = 67084 ∧ node.word.legal = true := by
  obtain ⟨nodes, hnodes⟩ :=
    Option.isSome_iff_exists.mp (by native_decide : controlFlow?.isSome = true)
  have h := decodeNewPayloadRequestEntryInstructionStateB_true
  unfold decodeNewPayloadRequestEntryInstructionStateB at h
  rw [hnodes] at h
  simp only [Option.map_some, Option.getD_some] at h
  unfold decodeNewPayloadRequestEntryInstructionStateAt at h
  split at h
  · rename_i node hnode
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨nodes, hnodes, node, hnode, h.1, h.2⟩
  · simp at h

/-- The generated machine-region word table reads the production file image at the same entry PC. -/
theorem decodeNewPayloadRequest_result_entry_instruction_word :
    wordAt? 67084 = some 276099 := by native_decide

theorem decodeNewPayloadRequest_result_entry_instruction_file_word :
    Artifacts.programImage.readFileU32LE? 67084 = some 276099 :=
  (readFileU32LE_of_wordAt decodeNewPayloadRequest_result_entry_instruction_word).2

/-! ## Mutation checks -/

/-- A changed stack offset does not pass the generated witness check. -/
theorem decodeNewPayloadRequest_result_entry_location_mutation_rejected :
    paramlessEntryLocalWitnesses !=
      [(decodeNewPayloadRequestId, "result", "fbreg", 2, 2312, 67084)] := by native_decide

/-- A changed entry PC does not pass the generated witness check. -/
theorem decodeNewPayloadRequest_result_entry_pc_mutation_rejected :
    paramlessEntryLocalWitnesses !=
      [(decodeNewPayloadRequestId, "result", "fbreg", 2, 2320, 67088)] := by native_decide

/-- A changed canonical entry instruction word is rejected by the production word table. -/
theorem decodeNewPayloadRequest_result_entry_word_mutation_rejected :
    wordAt? 67084 != some 0 := by native_decide

end BinaryFv.Zesu.Elflings.Validation
