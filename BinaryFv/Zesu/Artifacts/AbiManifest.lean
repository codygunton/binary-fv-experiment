import ZesuSszAbi

namespace BinaryFv.Zesu.Artifacts

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
/-- The `stored_result` global is `?RawStatelessInput`: an inline 848-byte optional result object. -/
def storedResultSize : Option Nat := abiDatum "?ssz_raw.RawStatelessInput|size"
def storedResultAlign : Option Nat := abiDatum "?ssz_raw.RawStatelessInput|align"
def storedResultPayloadOffset : Option Nat := abiDatum "?ssz_raw.RawStatelessInput|payload"
def storedResultTagOffset : Option Nat := abiDatum "?ssz_raw.RawStatelessInput|tag"

theorem raw_stateless_input_layout :
    rawStatelessInputSize = some 832 ∧ rawStatelessInputAlign = some 16 ∧
      rawStatelessInputNewPayloadRequestOffset = some 0 ∧ rawStatelessInputWitnessOffset = some 688 ∧
        rawStatelessInputChainConfigOffset = some 736 ∧ rawStatelessInputPublicKeysOffset = some 816 := by
  native_decide

theorem optional_u64_layout :
    optionalU64Size = some 16 ∧ optionalU64Align = some 8 ∧
      optionalU64PayloadOffset = some 0 ∧ optionalU64TagOffset = some 8 := by
  native_decide

def forkActivationSize : Option Nat := abiDatum "ssz_raw.RawForkActivation|size"
def forkActivationAlign : Option Nat := abiDatum "ssz_raw.RawForkActivation|align"
def forkActivationBlockNumberOffset : Option Nat :=
  abiDatum "ssz_raw.RawForkActivation|block_number"
def forkActivationTimestampOffset : Option Nat := abiDatum "ssz_raw.RawForkActivation|timestamp"

/-- `RawForkActivation`: two 16-byte `?u64`s. Pinned here so a footprint stating the record boundary
takes its size from the compiler-reflected manifest rather than from a hand-written literal — a
literal size is unfalsifiable, since an over-large one proves exactly as easily. -/
theorem fork_activation_layout :
    forkActivationSize = some 32 ∧ forkActivationAlign = some 8 ∧
      forkActivationBlockNumberOffset = some 0 ∧ forkActivationTimestampOffset = some 16 := by
  native_decide

def forkConfigSize : Option Nat := abiDatum "ssz_raw.RawForkConfig|size"
def forkConfigForkOffset : Option Nat := abiDatum "ssz_raw.RawForkConfig|fork"
def forkConfigActivationOffset : Option Nat := abiDatum "ssz_raw.RawForkConfig|activation"
def forkConfigBlobScheduleOffset : Option Nat := abiDatum "ssz_raw.RawForkConfig|blob_schedule"

def chainConfigSize : Option Nat := abiDatum "ssz_raw.RawChainConfig|size"
def chainConfigChainIdOffset : Option Nat := abiDatum "ssz_raw.RawChainConfig|chain_id"
def chainConfigActiveForkOffset : Option Nat := abiDatum "ssz_raw.RawChainConfig|active_fork"

/-- The two nesting containers. **Both are exactly packed**: `72 = 8 + 32 + 32` and `80 = 8 + 72`,
so the nesting introduces no padding of its own — every padding byte in the chain lives inside an
option leaf. Pinned here so a footprint stating either record boundary derives its size. -/
theorem fork_chain_config_layout :
    forkConfigSize = some 72 ∧ forkConfigForkOffset = some 0 ∧
      forkConfigActivationOffset = some 8 ∧ forkConfigBlobScheduleOffset = some 40 ∧
        chainConfigSize = some 80 ∧ chainConfigChainIdOffset = some 0 ∧
          chainConfigActiveForkOffset = some 8 := by
  native_decide

theorem optional_blob_schedule_layout :
    optionalBlobScheduleSize = some 32 ∧ optionalBlobScheduleAlign = some 8 ∧
      optionalBlobSchedulePayloadOffset = some 0 ∧ optionalBlobScheduleTagOffset = some 24 := by
  native_decide

/-- The `stored_result` object: 848 bytes, the 832-byte `RawStatelessInput` payload at offset 0, the
discriminant at 832. -/
theorem stored_result_layout :
    storedResultSize = some 848 ∧ storedResultAlign = some 16 ∧
      storedResultPayloadOffset = some 0 ∧ storedResultTagOffset = some 832 := by
  native_decide

/-- Nested descriptor offsets used by the guarded native `StatelessInput` observer. -/
def statelessInputDescriptorOffsetsValid : Bool :=
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

theorem stateless_input_descriptor_offsets_valid : statelessInputDescriptorOffsetsValid = true := by
  native_decide

/-- Compiler-reflected element sizes for every heap-backed fixed-record collection in `StatelessInput`. -/
def statelessInputHeapElementSizesValid : Bool :=
  abiDatum "ssz_raw.RawWithdrawal|size" == some 48 &&
    abiDatum "ssz_raw.RawDepositRequest|size" == some 192 &&
    abiDatum "ssz_raw.RawWithdrawalRequest|size" == some 80 &&
    abiDatum "ssz_raw.RawConsolidationRequest|size" == some 116

theorem stateless_input_heap_element_sizes_valid : statelessInputHeapElementSizesValid = true := by
  native_decide

/-! ### The same four sizes as `Option Nat`

`statelessInputHeapElementSizesValid` pins the four heap element sizes as a `Bool`, which is the form the
guarded native observer wants. A footprint wants the size itself, so that `range base recordSize`
takes its bound from the manifest instead of a written literal.

**Derived from the existing pinning, not from a second `native_decide`.** A fresh `native_decide` here
would be a second appeal to `ofReduceBool` asserting the same four facts, so a manifest change could
in principle move one and not the other. Going through `stateless_input_heap_element_sizes_valid` keeps one
trust door for one fact. -/

def rawWithdrawalSize : Option Nat := abiDatum "ssz_raw.RawWithdrawal|size"
def rawDepositRequestSize : Option Nat := abiDatum "ssz_raw.RawDepositRequest|size"
def rawWithdrawalRequestSize : Option Nat := abiDatum "ssz_raw.RawWithdrawalRequest|size"
def rawConsolidationRequestSize : Option Nat := abiDatum "ssz_raw.RawConsolidationRequest|size"

theorem heap_element_size_layout :
    rawWithdrawalSize = some 48 ∧ rawDepositRequestSize = some 192 ∧
      rawWithdrawalRequestSize = some 80 ∧ rawConsolidationRequestSize = some 116 := by
  have h := stateless_input_heap_element_sizes_valid
  simp only [statelessInputHeapElementSizesValid, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Compiler-reflected offsets for the inline fixed fields represented by `StatelessInputFixedFieldsRep`. -/
def statelessInputFixedFieldOffsetsValid : Bool :=
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

theorem stateless_input_fixed_field_offsets_valid : statelessInputFixedFieldOffsetsValid = true := by
  native_decide

/-! ### The four allocating containers' record sizes

One reflection covering all four, for the same reason `heap_element_size_layout` derives rather than
re-asserts: four separate `native_decide`s over one manifest are four things that can drift apart,
and a footprint stating the wrong record boundary proves exactly as easily as one stating the right
boundary. -/

def allocatingContainerSizesValid : Bool :=
  abiDatum "ssz_raw.RawExecutionRequests|size" == some 48 &&
    abiDatum "ssz_raw.RawExecutionWitness|size" == some 48 &&
      abiDatum "ssz_raw.RawExecutionPayload|size" == some 592 &&
        abiDatum "ssz_raw.RawNewPayloadRequest|size" == some 688

theorem allocating_container_sizes_valid : allocatingContainerSizesValid = true := by native_decide

def executionRequestsSize : Option Nat := abiDatum "ssz_raw.RawExecutionRequests|size"
def executionWitnessSize : Option Nat := abiDatum "ssz_raw.RawExecutionWitness|size"
def executionPayloadSize : Option Nat := abiDatum "ssz_raw.RawExecutionPayload|size"
def newPayloadRequestSize : Option Nat := abiDatum "ssz_raw.RawNewPayloadRequest|size"

theorem allocating_container_size_layout :
    executionRequestsSize = some 48 ∧ executionWitnessSize = some 48 ∧
      executionPayloadSize = some 592 ∧ newPayloadRequestSize = some 688 := by
  have h := allocating_container_sizes_valid
  simp only [allocatingContainerSizesValid, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Every queried member is produced by Zig reflection over every field of each raw result type. -/
def completeStatelessInputAbiManifest : Bool :=
  ZesuSszAbi.manifest.size == 96 && ZesuSszAbi.manifest.all fun entry => entry.2 < 1024

theorem complete_stateless_input_abi_manifest : completeStatelessInputAbiManifest = true := by
  native_decide

end BinaryFv.Zesu.Artifacts
