import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level4CfgPartition

namespace ZesuVerification

open BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

example : decodeRawDirectPcs.length = 172 := decodeRawDirectPcs_count

example : decodeRawAbsorbedExcludedPcs.length = 74 := decodeRawAbsorbedExcludedPcs_count

example : decodeRawPhasePartitionB = true := decodeRawPhasePartition_exact

example : decodeRawPhasePcs.length = 172 := by native_decide

example : decodeRawEntryEnvelopeOffsetsPcs.length = 45 :=
  decodeRawEntryEnvelopeOffsetsPcs_count

example : decodeRawSpecializedDispatchReturnsSuccessPcs.length = 67 :=
  decodeRawSpecializedDispatchReturnsSuccessPcs_count

example : decodeRawRejectionCleanupStatusCopyEpiloguePcs.length = 60 :=
  decodeRawRejectionCleanupStatusCopyEpiloguePcs_count

example : decodeRawAbsorbedExcludedPcs.all fun pc => !decodeRawDirectPcs.contains pc = true := by
  native_decide

end ZesuVerification
