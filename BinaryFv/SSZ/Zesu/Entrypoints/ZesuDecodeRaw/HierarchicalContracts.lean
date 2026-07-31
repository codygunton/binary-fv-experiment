import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Assembly

/-!
# Level 1 contract selection

The first refinement level names the exported decoder and the seven immediate emitted routines used
at the outermost execution layer. Numeric selections are guarded by their full source identities.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated

abbrev level1RequireCanonicalOffsets := generatedProgram.functionInstances[134]!
abbrev level1AllocatorResize := generatedProgram.functionInstances[135]!
abbrev level1AllocatorAlloc := generatedProgram.functionInstances[136]!
abbrev level1RawError := generatedProgram.functionInstances[137]!
abbrev level1RawResult := generatedProgram.functionInstances[138]!
abbrev level1Memcpy := generatedProgram.functionInstances[139]!
abbrev level1Memmove := generatedProgram.functionInstances[140]!

/-- Drift gate for the reviewed Level 1 selection. -/
theorem level1_tail_identities :
    level1RequireCanonicalOffsets.id.function.declaration.qualifiedName
      = "ssz_raw.requireCanonicalOffsets" ∧
    level1AllocatorResize.id.function.declaration.qualifiedName
      = "raw_decoder_root.allocatorResize" ∧
    level1AllocatorAlloc.id.function.declaration.qualifiedName
      = "raw_decoder_root.allocatorAlloc" ∧
    level1RawError.id.function.declaration.qualifiedName
      = "raw_decoder_root.zesu_raw_error" ∧
    level1RawResult.id.function.declaration.qualifiedName
      = "raw_decoder_root.zesu_raw_result" ∧
    level1Memcpy.id.function.declaration.qualifiedName = "memcpy" ∧
    level1Memmove.id.function.declaration.qualifiedName = "memmove" := by
  native_decide

/-- The Level 1 conditions: the exported wrapper/accessor seam plus the five remaining immediate
tail routines. The two accessors are already fields of `ExportedContractAssumptions`, giving eight
conditions in total: `zesu_decode_raw` and seven tail routines. -/
structure Level1ContractAssumptions : Prop extends ExportedContractAssumptions where
  requireCanonicalOffsets :
    routineObligation canonicalContractParams level1RequireCanonicalOffsets
      (functionInstanceReachedPcs generatedProgram level1RequireCanonicalOffsets)
      .requireCanonicalOffsets
  allocatorResize :
    routineObligation canonicalContractParams level1AllocatorResize
      (functionInstanceReachedPcs generatedProgram level1AllocatorResize) .allocatorResize
  allocatorAlloc :
    routineObligation canonicalContractParams level1AllocatorAlloc
      (functionInstanceReachedPcs generatedProgram level1AllocatorAlloc) .allocatorAlloc
  memcpy : routineObligation canonicalContractParams level1Memcpy
    (functionInstanceReachedPcs generatedProgram level1Memcpy) .memcpy
  memmove : routineObligation canonicalContractParams level1Memmove
    (functionInstanceReachedPcs generatedProgram level1Memmove) .memmove

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
