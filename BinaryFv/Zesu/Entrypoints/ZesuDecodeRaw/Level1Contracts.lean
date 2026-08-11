import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.CompiledAccessorAssembly
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Assembly

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
  CompiledZesuDecodeRawInstanceContract

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

/-- Convert the reviewed Level 2 child contracts into the decoder contract consumed by the runner.
Both accessors are discharged by concrete Sail execution. -/
def contracts_of_level1 (hLevel2 : Level2ContractAssumptions) : CompiledLevel1Assumptions where
  decode := exportedContracts_of_level2 (selectedContracts_of_level2 hLevel2)

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
