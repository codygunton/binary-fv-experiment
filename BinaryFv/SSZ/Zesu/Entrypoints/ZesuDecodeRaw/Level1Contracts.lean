import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Assembly

/-!
# Level 1 contracts

The first refinement level contains the exported decoder and the seven immediate emitted routines
used at the outermost execution layer. Function instances have source-derived generated names; this
file contains no array-position or string-based identity selection.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated

/-- The Level 1 conditions: the exported wrapper/accessor seam plus the five remaining immediate
tail routines. The two accessors are already fields of `ExportedContractAssumptions`, giving eight
conditions in total: `zesu_decode_raw` and seven tail routines. -/
structure Level1ContractAssumptions : Prop extends ExportedContractAssumptions where
  requireCanonicalOffsets :
    routineObligation canonicalContractParams functionInstance_ssz_raw_requireCanonicalOffsets
      (functionInstanceReachedPcs generatedProgram functionInstance_ssz_raw_requireCanonicalOffsets)
      .requireCanonicalOffsets
  allocatorResize :
    routineObligation canonicalContractParams functionInstance_raw_decoder_root_allocatorResize
      (functionInstanceReachedPcs generatedProgram
        functionInstance_raw_decoder_root_allocatorResize) .allocatorResize
  allocatorAlloc :
    routineObligation canonicalContractParams functionInstance_raw_decoder_root_allocatorAlloc
      (functionInstanceReachedPcs generatedProgram
        functionInstance_raw_decoder_root_allocatorAlloc) .allocatorAlloc
  memcpy : routineObligation canonicalContractParams functionInstance_memcpy
    (functionInstanceReachedPcs generatedProgram functionInstance_memcpy) .memcpy
  memmove : routineObligation canonicalContractParams functionInstance_memmove
    (functionInstanceReachedPcs generatedProgram functionInstance_memmove) .memmove

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
