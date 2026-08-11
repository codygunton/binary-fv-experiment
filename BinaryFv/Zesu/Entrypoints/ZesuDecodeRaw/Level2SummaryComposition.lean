import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts

/-!
# Flattening the selected Level 2 and Level 3 child summaries

The wrapper and its inlined `decode` child use `ScopedTrace` while their selected children are
proved separately.  This module supplies the generated-geometry composition facts which turn those
child summaries back into ordinary `FunctionTrace`s.  The facts retain the generated parent and
child instances at every boundary; they do not turn a source-level call graph into an ABI claim.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated
open LeanRV64DExecutable.Functions Register

private theorem generated_child_composes
    {parent child : FunctionInstance} {fromStep used count : Nat} {before after final : State}
    (parentMember : parent ∈ generatedProgram.functionInstances)
    (childCallee : child ∈ calleeFunctionInstances generatedProgram parent)
    (body : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram child)
      (functionInstanceExitPred child) fromStep used before after)
    (cont : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram parent)
      (functionInstanceExitPred parent) (fromStep + used) count after final) :
    FunctionTrace
      (functionInstanceExecutionPcs generatedProgram parent)
      (functionInstanceExitPred parent) fromStep (used + count) before final := by
  let geometry := programGeometry_of_check (program := generatedProgram) (by native_decide)
  exact summaryComposes_of_subtrace
    (fun pc inside => geometry.calleeWithinExecution parent parentMember child childCallee pc inside)
    (fun pc inside outerExit =>
      geometry.calleeExitContainment parent parentMember child childCallee pc inside outerExit)
    body cont

private theorem generated_member_of_find {functionInstance : FunctionInstance}
    (found : generatedProgram.find? functionInstance.id = some functionInstance) :
    functionInstance ∈ generatedProgram.functionInstances :=
  Array.mem_of_find?_eq_some found

private theorem decodeRaw_is_generated :
    functionInstance_ssz_raw_decodeRaw ∈ generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem decodeRaw_is_decode_callee :
    functionInstance_ssz_raw_decodeRaw ∈ calleeFunctionInstances generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  apply Array.mem_filter.mpr
  refine ⟨decodeRaw_is_generated, ?_⟩
  native_decide

private theorem hasExactErePrefix_is_generated :
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35 ∈
      generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem hasExactErePrefix_is_decode_callee :
    functionInstance_ssz_raw_hasExactErePrefix_in_raw_decoder_root_zesu_decode_raw_at_112_31_in_ssz_raw_decode_at_223_35 ∈
      calleeFunctionInstances generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  apply Array.mem_filter.mpr
  refine ⟨hasExactErePrefix_is_generated, ?_⟩
  native_decide

private theorem memcpy_is_generated :
    functionInstance_memcpy ∈ generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem memcpy_is_decode_callee :
    functionInstance_memcpy ∈ calleeFunctionInstances generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 := by
  apply Array.mem_filter.mpr
  refine ⟨memcpy_is_generated, ?_⟩
  native_decide

private theorem decode_is_generated :
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
      generatedProgram.functionInstances := by
  apply generated_member_of_find
  set_option maxRecDepth 100000 in
  rfl

/-- Every selected Level 3 child summary expands inside the inlined `decode` execution extent.
This is the concrete `SummariesCompose` instance consumed when a Level 2 wrapper route flattens its
inlined `decode` body. -/
theorem level3ChildSummary_composes_decodeRaw :
    SummariesCompose
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      (functionInstanceExitPred
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31)
      Level3ChildSummary := by
  intro child fromStep used count before after final run cont
  cases run with
  | decodeRaw run =>
      rcases run with ⟨_, args, pre, bound, trace, post⟩
      exact generated_child_composes decode_is_generated decodeRaw_is_decode_callee trace.trace cont
  | hasExactErePrefix run =>
      rcases run with ⟨_, args, pre, bound, trace, post⟩
      exact generated_child_composes decode_is_generated hasExactErePrefix_is_decode_callee trace cont
  | memcpy run =>
      rcases run with ⟨_, args, pre, bound, trace, post⟩
      exact generated_child_composes decode_is_generated memcpy_is_decode_callee trace.trace cont

private theorem wrapper_is_generated :
    functionInstance_raw_decoder_root_zesu_decode_raw ∈ generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem allocator_is_generated :
    functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41 ∈
      generatedProgram.functionInstances :=
  generated_member_of_find (by
    set_option maxRecDepth 100000 in
    rfl)

private theorem allocator_is_wrapper_callee :
    functionInstance_raw_decoder_root_allocator_in_raw_decoder_root_zesu_decode_raw_at_112_41 ∈
      calleeFunctionInstances generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw := by
  apply Array.mem_filter.mpr
  refine ⟨allocator_is_generated, ?_⟩
  native_decide

private theorem decode_is_wrapper_callee :
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 ∈
      calleeFunctionInstances generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw := by
  apply Array.mem_filter.mpr
  refine ⟨decode_is_generated, ?_⟩
  native_decide

private theorem memcpy_is_wrapper_callee :
    functionInstance_memcpy ∈
      calleeFunctionInstances generatedProgram functionInstance_raw_decoder_root_zesu_decode_raw := by
  apply Array.mem_filter.mpr
  refine ⟨memcpy_is_generated, ?_⟩
  native_decide

private theorem generated_child_composes_with_child_exit
    {parent child : FunctionInstance} {childExit : BitVec 64 → Prop}
    {fromStep used count : Nat} {before after final : State}
    (parentMember : parent ∈ generatedProgram.functionInstances)
    (childCallee : child ∈ calleeFunctionInstances generatedProgram parent)
    (outerExitsStopChild : ∀ pc,
      functionInstanceExecutionPcs generatedProgram child pc →
      functionInstanceExitPred parent pc → childExit pc)
    (body : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram child)
      childExit fromStep used before after)
    (cont : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram parent)
      (functionInstanceExitPred parent) (fromStep + used) count after final) :
    FunctionTrace
      (functionInstanceExecutionPcs generatedProgram parent)
      (functionInstanceExitPred parent) fromStep (used + count) before final := by
  let geometry := programGeometry_of_check (program := generatedProgram) (by native_decide)
  exact summaryComposes_of_subtrace
    (fun pc inside => geometry.calleeWithinExecution parent parentMember child childCallee pc inside)
    outerExitsStopChild body cont

private theorem wrapper_exit_not_in_decode_execution (args : DecodeInlineArgs) {pc : BitVec 64}
    (inside : functionInstanceExecutionPcs generatedProgram
      functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31 pc)
    (exit : functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw pc) :
    DecodeInlineExit args pc := by
  exfalso
  let geometry := programGeometry_of_check (program := generatedProgram) (by native_decide)
  have childExit := geometry.calleeExitContainment
    functionInstance_raw_decoder_root_zesu_decode_raw wrapper_is_generated
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31
    decode_is_wrapper_callee pc inside exit
  simp [functionInstanceExitPred, FunctionInstance.isExit,
    functionInstance_raw_decoder_root_zesu_decode_raw,
    functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31] at childExit exit
  omega

/-- Every selected Level 2 child summary expands inside the generated `zesu_decode_raw` wrapper
execution extent. -/
theorem level2ChildSummary_composes_decodeRaw :
    SummariesCompose
      (functionInstanceExecutionPcs generatedProgram
        functionInstance_raw_decoder_root_zesu_decode_raw)
      (functionInstanceExitPred functionInstance_raw_decoder_root_zesu_decode_raw)
      Level2ChildSummary := by
  intro child fromStep used count before after final run cont
  cases run with
  | allocator run =>
      rcases run with ⟨_, trace⟩
      exact generated_child_composes wrapper_is_generated allocator_is_wrapper_callee
        trace.toFunctionTrace cont
  | decode run =>
      rcases run with ⟨_, args, pre, bound, scopedTrace, flat, post, machine, outgoing⟩
      exact generated_child_composes_with_child_exit (childExit := DecodeInlineExit args)
        wrapper_is_generated decode_is_wrapper_callee
        (fun pc inside exit => wrapper_exit_not_in_decode_execution args inside exit)
        flat cont
  | memcpy run =>
      rcases run with ⟨_, args, pre, bound, trace, post⟩
      exact generated_child_composes wrapper_is_generated memcpy_is_wrapper_callee trace.trace cont

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
