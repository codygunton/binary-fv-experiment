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

/-- The three real exported machine contracts consumed by the public runner. -/
structure ExportedContractAssumptions : Prop where
  decode :
    ∀ {functionInstance : FunctionInstance},
      Program.find? generatedProgram generatedProgram.entry = some functionInstance →
        FunctionInstanceContract.Implements
          (functionInstanceExecutionPcs generatedProgram functionInstance)
          (functionInstanceExitPred functionInstance)
          (functionInstanceEntryWord functionInstance)
          (functionInstanceZesuDecodeRaw canonicalContractParams.env
            canonicalContractParams.globals canonicalContractParams.resultBuffer
            canonicalContractParams.repRawV4 DecoderGlobalsModel.fresh)
  rawResult :
    ∀ {functionInstance : FunctionInstance},
      functionInstance ∈ generatedProgram.functionInstances →
      functionInstance.entryPc = resolvedSymbols.rawResult →
        Implements (functionInstanceExecutionPcs generatedProgram functionInstance)
          (functionInstanceExitPred functionInstance)
          (functionInstanceEntryWord functionInstance)
          (contractRawResult canonicalContractParams.env canonicalContractParams.globals
            canonicalContractParams.resultBuffer)
  rawError :
    ∀ {functionInstance : FunctionInstance},
      functionInstance ∈ generatedProgram.functionInstances →
      functionInstance.entryPc = resolvedSymbols.rawError →
        Implements (functionInstanceExecutionPcs generatedProgram functionInstance)
          (functionInstanceExitPred functionInstance)
          (functionInstanceEntryWord functionInstance)
          (contractRawError canonicalContractParams.env canonicalContractParams.globals)

namespace ExportedContractAssumptions

/--
The old flat seam implies the exported seam. This keeps the landed global proof usable while the new
hierarchical decomposition learns to construct `ExportedContractAssumptions` directly.
-/
theorem ofLocals (locals : Validation.LocalContractAssumptions) :
    ExportedContractAssumptions where
  decode hfind := entry_implements_of_locals locals hfind
  rawResult hmem hentry := rawResult_implements_of_locals locals hmem hentry
  rawError hmem hentry := rawError_implements_of_locals locals hmem hentry

end ExportedContractAssumptions

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
