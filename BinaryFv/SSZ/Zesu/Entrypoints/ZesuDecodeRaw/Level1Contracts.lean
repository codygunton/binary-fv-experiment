import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Assembly

/-!
# Contracts for the three functions called by `program`

The runner calls `zesu_decode_raw`, then `zesu_raw_result` and `zesu_raw_error`. These are the three
children of `program` in the corrected call-dominator flamegraph. Allocator-vtable functions are
called inside the decoder and therefore belong in later resolutions of `zesu_decode_raw`.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated

/-- Complete machine contract for the exported decoder instance. -/
abbrev ZesuDecodeRawContract : Prop :=
  ∀ {functionInstance : FunctionInstance},
    Program.find? generatedProgram generatedProgram.entry = some functionInstance →
      BinaryFv.RiscV.Elfling.FunctionInstanceContract.Implements
        (functionInstanceExecutionPcs generatedProgram functionInstance)
        (functionInstanceExitPred functionInstance)
        (functionInstanceEntryWord functionInstance)
        (functionInstanceZesuDecodeRaw canonicalContractParams.env canonicalContractParams.globals
          canonicalContractParams.resultBuffer canonicalContractParams.repRawV4
          DecoderGlobalsModel.fresh)

/-- Contract for `zesu_raw_result` at the symbol selected by the runner. -/
abbrev RawResultContract : Prop :=
  ∀ {functionInstance : FunctionInstance},
    functionInstance ∈ generatedProgram.functionInstances →
    functionInstance.entryPc = resolvedSymbols.rawResult →
      BinaryFv.RiscV.Elfling.Implements
        (functionInstanceExecutionPcs generatedProgram functionInstance)
        (functionInstanceExitPred functionInstance)
        (functionInstanceEntryWord functionInstance)
        (contractRawResult canonicalContractParams.env canonicalContractParams.globals
          canonicalContractParams.resultBuffer)

/-- Contract for `zesu_raw_error` at the symbol selected by the runner. -/
abbrev RawErrorContract : Prop :=
  ∀ {functionInstance : FunctionInstance},
    functionInstance ∈ generatedProgram.functionInstances →
    functionInstance.entryPc = resolvedSymbols.rawError →
      BinaryFv.RiscV.Elfling.Implements
        (functionInstanceExecutionPcs generatedProgram functionInstance)
        (functionInstanceExitPred functionInstance)
        (functionInstanceEntryWord functionInstance)
        (contractRawError canonicalContractParams.env canonicalContractParams.globals)

/-- Put the three contracts called by the runner into the exact structure consumed by its execution
proof. Every argument is copied directly; no deeper decoder contract is smuggled into Level 1. -/
def exportedContracts_of_level1
    (decode : ZesuDecodeRawContract)
    (rawResult : RawResultContract)
    (rawError : RawErrorContract) : ExportedContractAssumptions where
  decode := decode
  rawResult := rawResult
  rawError := rawError

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
