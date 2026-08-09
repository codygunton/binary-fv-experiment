import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Assembly
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryFinish
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof

/-!
# Level 3 assumptions for inlined `ssz_raw.decode`

The reviewed immediate children are emitted `decodeRaw`, inlined `hasExactErePrefix`, and emitted
`memcpy`. The prefix and copy contracts have unconditional Sail proofs, so the public progress gauge
contains only the outstanding contract for the selected `decodeRaw` instance.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Zesu.MachineExecution

/-- The sole outstanding function-instance contract at reviewed UI Level 3. -/
structure Level3ContractAssumptions : Prop where
  decodeRaw : CompiledDecodeRawInstanceContract

/-- The complete set of contracts selected by the reviewed Level 3 call relation. -/
structure Level3SelectedContracts : Prop where
  decodeRaw : CompiledDecodeRawInstanceContract
  hasExactErePrefix : HasExactErePrefixInlineContract
  memcpy : MemcpyInstanceContract

/-- Fill the proved immediate children while retaining only unresolved `decodeRaw` from `hLevel3`. -/
def selectedContracts_of_level3
    (hLevel3 : Level3ContractAssumptions) : Level3SelectedContracts where
  decodeRaw := hLevel3.decodeRaw
  hasExactErePrefix := hasExactErePrefixInlineContract_proved
  memcpy := compiledMemcpyInstanceContract_proved

/-- Convert every reviewed Level 3 child contract into the preceding level's assumptions. -/
def level2Contracts_of_level3 (selected : Level3SelectedContracts) :
    Level2ContractAssumptions where
  decode := MachineExecution.level3DecodeInlineContract selected.decodeRaw
    selected.hasExactErePrefix selected.memcpy

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
