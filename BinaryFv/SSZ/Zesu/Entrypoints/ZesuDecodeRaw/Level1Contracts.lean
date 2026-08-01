import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Assembly

/-!
# Contracts for the eight functions selected at Level 1

The Level 1 flamegraph selection contains `zesu_decode_raw`, the five allocator functions, and the two
result accessors below `program`. This file states that exact selection. It does not replace those
functions with descendants of `zesu_decode_raw`.
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

abbrev RawAllocContract : Prop :=
  routineObligation canonicalContractParams functionInstance_raw_allocator_zesu_raw_alloc
    (functionInstanceReachedPcs generatedProgram functionInstance_raw_allocator_zesu_raw_alloc)
    .rawAlloc

abbrev AllocatorFreeContract : Prop :=
  routineObligation canonicalContractParams functionInstance_raw_decoder_root_allocatorFree
    (functionInstanceReachedPcs generatedProgram functionInstance_raw_decoder_root_allocatorFree)
    .allocatorFree

abbrev AllocatorRemapContract : Prop :=
  routineObligation canonicalContractParams functionInstance_raw_decoder_root_allocatorRemap
    (functionInstanceReachedPcs generatedProgram functionInstance_raw_decoder_root_allocatorRemap)
    .allocatorRemap

abbrev AllocatorResizeContract : Prop :=
  routineObligation canonicalContractParams functionInstance_raw_decoder_root_allocatorResize
    (functionInstanceReachedPcs generatedProgram functionInstance_raw_decoder_root_allocatorResize)
    .allocatorResize

abbrev AllocatorAllocContract : Prop :=
  routineObligation canonicalContractParams functionInstance_raw_decoder_root_allocatorAlloc
    (functionInstanceReachedPcs generatedProgram functionInstance_raw_decoder_root_allocatorAlloc)
    .allocatorAlloc

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

/-- Convert the contracts for all eight Level 1 functions into the three complete contracts used by
the runner.

The `zesu_decode_raw` argument is deliberately conditional on all five allocator arguments. This
records the proof still required for the decoder's own instructions: compose its local execution with
the five runtime functions to obtain its complete machine contract. Every argument below is therefore
used to derive the result; none is retained only as coverage metadata. -/
def exportedContracts_of_level1
    (decode : RawAllocContract → AllocatorFreeContract → AllocatorRemapContract →
      AllocatorResizeContract → AllocatorAllocContract → ZesuDecodeRawContract)
    (rawAlloc : RawAllocContract)
    (allocatorFree : AllocatorFreeContract)
    (allocatorRemap : AllocatorRemapContract)
    (allocatorResize : AllocatorResizeContract)
    (allocatorAlloc : AllocatorAllocContract)
    (rawResult : RawResultContract)
    (rawError : RawErrorContract) : ExportedContractAssumptions where
  decode := decode rawAlloc allocatorFree allocatorRemap allocatorResize allocatorAlloc
  rawResult := rawResult
  rawError := rawError

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
