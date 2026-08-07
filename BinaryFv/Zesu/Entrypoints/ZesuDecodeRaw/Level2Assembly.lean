import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2ConditionalCapstone
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2RouteProduction

/-!
# Level 2 assumptions for `raw_decoder_root.zesu_decode_raw`

The reviewed immediate children are the inlined allocator, inlined `ssz_raw.decode`, and emitted
`memcpy`.  The Level 2 premise names exactly those three contracts.  The allocator and `memcpy`
contracts also have unconditional machine proofs, but keeping all three fields visible makes the
call relation explicit at the public refinement boundary.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Zesu.MachineExecution

/-- Exactly the three immediate machine contracts selected at Level 2. -/
structure Level2ContractAssumptions : Prop where
  allocator : AllocatorInlineContract
  decode : Level3DecodeInlineContract
  memcpy : MemcpyInstanceContract

/-- The complete set of contracts selected by the reviewed Level 2 call relation. The refinement
edge destructures this bundle. Its route proofs use the unconditional emitted-`memcpy` machine
theorem, which is stronger than requiring the bundle's `memcpy` field at each copy call site. -/
structure Level2SelectedContracts : Prop where
  allocator : AllocatorInlineContract
  decode : Level3DecodeInlineContract
  memcpy : MemcpyInstanceContract

/-- Expose the Level 2 premise as the selected immediate-child bundle. -/
def selectedContracts_of_level2 (hLevel2 : Level2ContractAssumptions) : Level2SelectedContracts where
  allocator := hLevel2.allocator
  decode := hLevel2.decode
  memcpy := hLevel2.memcpy

/-- Convert the three reviewed Level 2 child contracts into the exported wrapper contract. The
route proofs already discharge each emitted `memcpy` call from its unconditional machine theorem,
so `selected.memcpy` remains visible in the selected-call bundle without becoming a weaker duplicate
premise of those route proofs. -/
theorem exportedContracts_of_level2 (selected : Level2SelectedContracts) :
    CompiledZesuDecodeRawInstanceContract :=
  compiledZesuDecodeRawContract_of_level2_routes selected.allocator selected.decode
    firstSuccessRouteToExportedPost
    (nonFirstRoutesFromEntry_of_level2 selected.allocator selected.decode)
    nonFirstRouteToExportedPost

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
