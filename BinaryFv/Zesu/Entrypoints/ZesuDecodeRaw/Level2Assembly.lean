import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level3Contracts
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2ConditionalCapstone
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2RouteProduction

/-!
# Level 2 assumptions for `raw_decoder_root.zesu_decode_raw`

The reviewed immediate children are the inlined allocator, inlined `ssz_raw.decode`, and emitted
`memcpy`. The public premise contains only the unresolved `decode` contract. The refinement edge
constructs the complete selected-child bundle with the unconditional allocator and `memcpy` proofs.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Zesu.MachineExecution

/-- The sole outstanding contract at reviewed UI Level 2. -/
structure Level2ContractAssumptions : Prop where
  decode : Level3DecodeInlineContract

/-- The complete set of contracts selected by the reviewed Level 2 call relation. -/
structure Level2SelectedContracts : Prop where
  allocator : AllocatorInlineContract
  decode : Level3DecodeInlineContract
  memcpy : MemcpyInstanceContract

/-- Fill the proved immediate children while retaining only unresolved `decode` from `hLevel2`. -/
def selectedContracts_of_level2
    (hLevel2 : Level2ContractAssumptions) : Level2SelectedContracts where
  allocator := allocatorInlineContract_proved
  decode := hLevel2.decode
  memcpy := MachineExecution.compiledMemcpyInstanceContract_proved

/-- Convert every reviewed Level 2 child contract into the exported wrapper contract. -/
theorem exportedContracts_of_level2 (selected : Level2SelectedContracts) :
    CompiledZesuDecodeRawInstanceContract :=
  compiledZesuDecodeRawContract_of_level2_routes selected.allocator selected.decode selected.memcpy
    firstSuccessRouteToExportedPost
    (nonFirstRoutesFromEntry_of_level2 selected.allocator selected.decode selected.memcpy)
    nonFirstRouteToExportedPost

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
