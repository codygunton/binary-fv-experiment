import ZesuSszAbi

namespace BinaryFv.SSZ.Zesu.Artifact

/-- Lookup a compiler-produced RV64 ABI datum by its qualified Zig type and field key. -/
def abiDatum (key : String) : Option Nat :=
  (ZesuSszAbi.manifest.toList.find? fun entry => entry.1 == key).map Prod.snd

def rawStatelessInputSize : Option Nat := abiDatum "ssz_raw.RawStatelessInput|size"
def rawStatelessInputAlign : Option Nat := abiDatum "ssz_raw.RawStatelessInput|align"
def rawStatelessInputNewPayloadRequestOffset : Option Nat :=
  abiDatum "ssz_raw.RawStatelessInput|new_payload_request"
def rawStatelessInputWitnessOffset : Option Nat := abiDatum "ssz_raw.RawStatelessInput|witness"
def rawStatelessInputChainConfigOffset : Option Nat := abiDatum "ssz_raw.RawStatelessInput|chain_config"
def rawStatelessInputPublicKeysOffset : Option Nat := abiDatum "ssz_raw.RawStatelessInput|public_keys"
def optionalU64Size : Option Nat := abiDatum "?u64|size"
def optionalU64Align : Option Nat := abiDatum "?u64|align"
def optionalU64PayloadOffset : Option Nat := abiDatum "?u64|payload"
def optionalU64TagOffset : Option Nat := abiDatum "?u64|tag"
def optionalBlobScheduleSize : Option Nat := abiDatum "?ssz_raw.RawBlobSchedule|size"
def optionalBlobScheduleAlign : Option Nat := abiDatum "?ssz_raw.RawBlobSchedule|align"
def optionalBlobSchedulePayloadOffset : Option Nat := abiDatum "?ssz_raw.RawBlobSchedule|payload"
def optionalBlobScheduleTagOffset : Option Nat := abiDatum "?ssz_raw.RawBlobSchedule|tag"

theorem raw_stateless_input_layout :
    rawStatelessInputSize = some 832 ∧ rawStatelessInputAlign = some 16 ∧
      rawStatelessInputNewPayloadRequestOffset = some 0 ∧ rawStatelessInputWitnessOffset = some 688 ∧
        rawStatelessInputChainConfigOffset = some 736 ∧ rawStatelessInputPublicKeysOffset = some 816 := by
  native_decide

theorem optional_u64_layout :
    optionalU64Size = some 16 ∧ optionalU64Align = some 8 ∧
      optionalU64PayloadOffset = some 0 ∧ optionalU64TagOffset = some 8 := by
  native_decide

theorem optional_blob_schedule_layout :
    optionalBlobScheduleSize = some 32 ∧ optionalBlobScheduleAlign = some 8 ∧
      optionalBlobSchedulePayloadOffset = some 0 ∧ optionalBlobScheduleTagOffset = some 24 := by
  native_decide

/-- Nested descriptor offsets used by the guarded native `RawV4` observer. -/
def rawV4DescriptorOffsetsValid : Bool :=
  abiDatum "ssz_raw.RawNewPayloadRequest|versioned_hashes" == some 592 &&
    abiDatum "ssz_raw.RawNewPayloadRequest|execution_requests" == some 608 &&
    abiDatum "ssz_raw.RawExecutionPayload|transactions" == some 80 &&
    abiDatum "ssz_raw.RawExecutionPayload|withdrawals" == some 96 &&
    abiDatum "ssz_raw.RawExecutionRequests|deposits" == some 0 &&
    abiDatum "ssz_raw.RawExecutionRequests|withdrawals" == some 16 &&
    abiDatum "ssz_raw.RawExecutionRequests|consolidations" == some 32 &&
    abiDatum "ssz_raw.RawExecutionWitness|state" == some 0 &&
    abiDatum "ssz_raw.RawExecutionWitness|codes" == some 16 &&
    abiDatum "ssz_raw.RawExecutionWitness|headers" == some 32

theorem raw_v4_descriptor_offsets_valid : rawV4DescriptorOffsetsValid = true := by
  native_decide

/-- Compiler-reflected element sizes for every heap-backed fixed-record collection in `RawV4`. -/
def rawV4HeapElementSizesValid : Bool :=
  abiDatum "ssz_raw.RawWithdrawal|size" == some 48 &&
    abiDatum "ssz_raw.RawDepositRequest|size" == some 192 &&
    abiDatum "ssz_raw.RawWithdrawalRequest|size" == some 80 &&
    abiDatum "ssz_raw.RawConsolidationRequest|size" == some 116

theorem raw_v4_heap_element_sizes_valid : rawV4HeapElementSizesValid = true := by
  native_decide

/-- Compiler-reflected offsets for the inline fixed fields represented by `RawV4FixedFieldsRep`. -/
def rawV4FixedFieldOffsetsValid : Bool :=
  abiDatum "ssz_raw.RawExecutionPayload|parent_hash" == some 152 &&
    abiDatum "ssz_raw.RawExecutionPayload|fee_recipient" == some 184 &&
    abiDatum "ssz_raw.RawExecutionPayload|state_root" == some 204 &&
    abiDatum "ssz_raw.RawExecutionPayload|receipts_root" == some 236 &&
    abiDatum "ssz_raw.RawExecutionPayload|logs_bloom" == some 268 &&
    abiDatum "ssz_raw.RawExecutionPayload|prev_randao" == some 524 &&
    abiDatum "ssz_raw.RawExecutionPayload|block_hash" == some 556 &&
    abiDatum "ssz_raw.RawNewPayloadRequest|parent_beacon_block_root" == some 656 &&
    abiDatum "ssz_raw.RawChainConfig|chain_id" == some 0 &&
    abiDatum "ssz_raw.RawChainConfig|active_fork" == some 8 &&
    abiDatum "ssz_raw.RawForkConfig|fork" == some 0

theorem raw_v4_fixed_field_offsets_valid : rawV4FixedFieldOffsetsValid = true := by
  native_decide

/-- Every queried member is produced by Zig reflection over every field of each raw result type. -/
def completeRawV4AbiManifest : Bool :=
  ZesuSszAbi.manifest.size == 92 && ZesuSszAbi.manifest.all fun entry => entry.2 < 1024

theorem complete_raw_v4_abi_manifest : completeRawV4AbiManifest = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Artifact
