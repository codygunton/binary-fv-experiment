import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.DecodeInlineRetryFinish

/-!
# Embedding the complete Level 3 decode theorem as the Level 2 `decode` child

`Level2Contracts` states every Level 2 contract, including the `Level2ChildSummary` relation, and
deliberately does not depend on the proved inlined-`decode` machine execution. Only the step that
*discharges* the `decode` arm from the complete Level 3 theorem needs
`MachineExecution.level3DecodeInlineContract`, so it lives here instead: that keeps the whole Level 2
contract spine off `DecodeInlineProof`'s import closure, which is the longest serial segment of the
build.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions

/-- The complete Level 3 theorem embeds as the selected Level 2 `decode` child. The only remaining
condition is the emitted `decodeRaw` contract that Level 4 will refine. -/
theorem level2DecodeChildSummary_of_decodeRaw
    (decodeRaw : CompiledDecodeRawInstanceContract)
    (args : DecodeInlineArgs) (fromStep : Nat) (before : State)
    (pre : DecodeInlinePre args before) :
    ∃ used after,
      Level2ChildSummary
        functionInstance_ssz_raw_decode_in_raw_decoder_root_zesu_decode_raw_at_112_31Id
        fromStep used before after := by
  obtain ⟨used, after, run⟩ := level3DecodeChildSummary_of_contract
    (MachineExecution.level3DecodeInlineContract decodeRaw) args fromStep before pre
  exact ⟨used, after, .decode run⟩

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
