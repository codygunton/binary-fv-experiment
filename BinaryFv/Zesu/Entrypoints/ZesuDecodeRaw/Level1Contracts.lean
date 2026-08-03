import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.CompiledAccessorAssembly

/-!
# Contracts for the three functions called by `program`

The runner calls `zesu_decode_raw`, then `zesu_raw_result` and `zesu_raw_error`. These are the three
children of `program` in the corrected call-dominator flamegraph. Allocator-vtable functions are
called inside the decoder and therefore belong in later resolutions of `zesu_decode_raw`.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings
open BinaryFv.Zesu.Elflings.Generated

/-- Complete machine contract for the exported decoder instance. -/
abbrev ZesuDecodeRawContract : Prop :=
  DecodeInstanceObligation

/-- Source contract plus compiled entry conditions for `zesu_raw_result` at the selected symbol. -/
abbrev RawResultContract : Prop :=
  ∀ {functionInstance : FunctionInstance},
    functionInstance ∈ generatedProgram.instances →
    functionInstance.entryPc = resolvedSymbols.rawResult →
      RawResultInstanceObligation functionInstance

/-- Source contract plus compiled entry conditions for `zesu_raw_error` at the selected symbol. -/
abbrev RawErrorContract : Prop :=
  ∀ {functionInstance : FunctionInstance},
    functionInstance ∈ generatedProgram.instances →
    functionInstance.entryPc = resolvedSymbols.rawError →
      RawErrorInstanceObligation functionInstance

/-- Put the three contracts called by the runner into the exact structure consumed by its execution
proof. Every argument is copied directly; no deeper decoder contract is smuggled into Level 1. -/
def contracts_of_level1
    (decode : ZesuDecodeRawContract)
    (rawResult : RawResultContract)
    (rawError : RawErrorContract) : CompiledLevel1Assumptions where
  decode := decode
  rawResult := rawResult
  rawError := rawError

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
