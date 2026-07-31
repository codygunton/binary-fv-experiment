import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Assembly

/-!
# The exported-contract seam for hierarchical proofs

The runner does not intrinsically need 141 DWARF-occurrence obligations. It needs three closed machine
contracts: the exported decoder and the two exported accessors it invokes afterward. This structure
names that interface directly.

`ofLocals` is a compatibility theorem, not the intended final construction. It shows that the old
flat `LocalContractAssumptions` can still produce the new seam while A′–C′ develop a hierarchical
producer that bypasses the old decomposition.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated

/-- The seven emitted routines at the tail of the generated program.  The numeric selection is
guarded below by their full source identities, so a regenerated ordering cannot silently retarget an
L1 premise. -/
abbrev level1RequireCanonicalOffsets := generatedProgram.functionInstances[134]!
abbrev level1AllocatorResize := generatedProgram.functionInstances[135]!
abbrev level1AllocatorAlloc := generatedProgram.functionInstances[136]!
abbrev level1RawError := generatedProgram.functionInstances[137]!
abbrev level1RawResult := generatedProgram.functionInstances[138]!
abbrev level1Memcpy := generatedProgram.functionInstances[139]!
abbrev level1Memmove := generatedProgram.functionInstances[140]!

/-- Drift gate for the reviewed L1 tail selection. -/
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

/-- Depth 1: the exported decoder contract plus the seven reviewed small tail routines.

The five non-accessor tail contracts are not consumed by the runner directly.  They are explicit
inputs to the next refinement edge, where the large decoder contract will be proved from its selected
children. -/
structure Level1ContractAssumptions : Prop extends ExportedContractAssumptions where
  requireCanonicalOffsets :
    functionInstanceObligation canonicalContractParams generatedProgram
      level1RequireCanonicalOffsets
  allocatorResize :
    functionInstanceObligation canonicalContractParams generatedProgram level1AllocatorResize
  allocatorAlloc :
    functionInstanceObligation canonicalContractParams generatedProgram level1AllocatorAlloc
  memcpy : functionInstanceObligation canonicalContractParams generatedProgram level1Memcpy
  memmove : functionInstanceObligation canonicalContractParams generatedProgram level1Memmove

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
