import BinaryFv.Zesu.MemoryRepresentation.StatelessInput

/-!
# The seven Zesu container types in RISC-V memory

Each predicate in this file says when bytes in Sail memory represent one decoded Zig container.
Fields are combined from reusable word, vector, slice, and array predicates. The final offset audit
checks the handwritten field offsets against the ABI manifest produced by the pinned Zig compiler.

The first three containers contain only inline data. The other four include heap arrays or slices
that borrow bytes from the caller's input, so those predicates also receive the input address and
`ByteArray`. These definitions describe memory after decoding; they do not perform the decode.
-/

namespace BinaryFv.Zesu.MemoryRepresentation

open BinaryFv.RiscV

/-! ## The three fixed (non-allocating) containers

`OptionU64Rep`, `BlobScheduleRep`, `OptionBlobScheduleRep`, `ForkActivationRep`, `ForkConfigRep`, and
`ChainConfigRep` now live in `StatelessInput.lean`. They were moved there unchanged so that
`StatelessInputFixedFieldsRep` can state the chain config with `ChainConfigRep`; this file imports `StatelessInput`, so
the definitions are still in scope here and every use below is unaffected. -/

/-! ## The four allocating containers -/

/-- `RawExecutionRequests` (48 bytes): three slice descriptors (deposits@0, withdrawals@16,
consolidations@32), each pointing at a disjoint heap array of fixed-width records. No input aliasing. -/
def ExecutionRequestsRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawExecutionRequests) :
    Prop :=
  ∃ depositsBase withdrawalsBase consolidationsBase,
    SliceDescriptorRep state base depositsBase value.deposits.size ∧
      HeapArrayRep state depositsBase value.deposits.size 192 ∧
        HeapDepositRequestArrayRep state depositsBase value.deposits ∧
    SliceDescriptorRep state (base + 16) withdrawalsBase value.withdrawals.size ∧
      HeapArrayRep state withdrawalsBase value.withdrawals.size 80 ∧
        HeapWithdrawalRequestArrayRep state withdrawalsBase value.withdrawals ∧
    SliceDescriptorRep state (base + 32) consolidationsBase value.consolidations.size ∧
      HeapArrayRep state consolidationsBase value.consolidations.size 116 ∧
        HeapConsolidationRequestArrayRep state consolidationsBase value.consolidations

/-- `RawExecutionWitness` (48 bytes): three slice descriptors (state@0, codes@16, headers@32), each
pointing at a heap array of 16-byte input-slice descriptors that alias the caller's input bytes. -/
def ExecutionWitnessRep (state : State) (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawExecutionWitness) : Prop :=
  ∃ stateBase codesBase headersBase,
    SliceDescriptorRep state base stateBase value.state.size ∧
      HeapArrayRep state stateBase value.state.size 16 ∧
        InputSliceDescriptorArrayRep state inputBase input stateBase value.state ∧
    SliceDescriptorRep state (base + 16) codesBase value.codes.size ∧
      HeapArrayRep state codesBase value.codes.size 16 ∧
        InputSliceDescriptorArrayRep state inputBase input codesBase value.codes ∧
    SliceDescriptorRep state (base + 32) headersBase value.headers.size ∧
      HeapArrayRep state headersBase value.headers.size 16 ∧
        InputSliceDescriptorArrayRep state inputBase input headersBase value.headers

/-- The inline fixed-vector, scalar, and `u256` fields of a standalone `RawExecutionPayload`. The
offsets are the same compiler-reflected values `StatelessInputFixedFieldsRep` uses, because the execution
payload sits at offset 0 of both the new-payload request and the root object. -/
structure ExecutionPayloadFixedRep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawExecutionPayload) : Prop where
  baseFeePerGas : BitVectorLERep state base value.baseFeePerGas
  parentHash : FixedByteVectorRep state (base + 152) value.parentHash
  feeRecipient : FixedByteVectorRep state (base + 184) value.feeRecipient
  stateRoot : FixedByteVectorRep state (base + 204) value.stateRoot
  receiptsRoot : FixedByteVectorRep state (base + 236) value.receiptsRoot
  logsBloom : FixedByteVectorRep state (base + 268) value.logsBloom
  prevRandao : FixedByteVectorRep state (base + 524) value.prevRandao
  blockHash : FixedByteVectorRep state (base + 556) value.blockHash
  blockNumber : Word64LERep state (base + 32) value.blockNumber.toNat
  gasLimit : Word64LERep state (base + 40) value.gasLimit.toNat
  gasUsed : Word64LERep state (base + 48) value.gasUsed.toNat
  timestamp : Word64LERep state (base + 56) value.timestamp.toNat
  blobGasUsed : Word64LERep state (base + 112) value.blobGasUsed.toNat
  excessBlobGas : Word64LERep state (base + 120) value.excessBlobGas.toNat
  slotNumber : Word64LERep state (base + 144) value.slotNumber.toNat

/-- `RawExecutionPayload` (592 bytes): the inline fixed fields, the two borrowed single-byte slices
(`extra_data`@64, `block_access_list`@128), the transaction list (`transactions`@80, borrowed), and
the withdrawal list (`withdrawals`@96, a heap array of fixed records). -/
def ExecutionPayloadRep (state : State) (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawExecutionPayload) : Prop :=
  ExecutionPayloadFixedRep state base value ∧
  (∃ inputOffset sliceBase,
    InputSliceDescriptorRep state inputBase input (base + 64) inputOffset sliceBase value.extraData) ∧
  (∃ inputOffset sliceBase,
    InputSliceDescriptorRep state inputBase input (base + 128) inputOffset sliceBase
      value.blockAccessList) ∧
  (∃ transactionsBase,
    SliceDescriptorRep state (base + 80) transactionsBase value.transactions.size ∧
      HeapArrayRep state transactionsBase value.transactions.size 16 ∧
        InputSliceDescriptorArrayRep state inputBase input transactionsBase value.transactions) ∧
  (∃ withdrawalsBase,
    SliceDescriptorRep state (base + 96) withdrawalsBase value.withdrawals.size ∧
      HeapArrayRep state withdrawalsBase value.withdrawals.size 48 ∧
        HeapWithdrawalArrayRep state withdrawalsBase value.withdrawals)

/-- `RawNewPayloadRequest` (688 bytes): the execution payload inline at 0, the versioned-hash heap
array (`versioned_hashes`@592), the inline `parent_beacon_block_root`@656, and the execution requests
inline at 608. -/
def NewPayloadRequestRep (state : State) (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawNewPayloadRequest) : Prop :=
  ExecutionPayloadRep state inputBase input base value.executionPayload ∧
  (∃ versionedHashesBase,
    SliceDescriptorRep state (base + 592) versionedHashesBase value.versionedHashes.size ∧
      HeapArrayRep state versionedHashesBase value.versionedHashes.size 32 ∧
        HeapFixedVectorArrayRep state versionedHashesBase value.versionedHashes) ∧
  FixedByteVectorRep state (base + 656) value.parentBeaconBlockRoot ∧
  ExecutionRequestsRep state (base + 608) value.executionRequests

/-! ## Offset audit

Every literal field offset used above is pinned against the compiler-reflected ABI manifest. The
offsets `StatelessInput.lean` already re-uses (fixed fields, root descriptors, heap element sizes) are audited
by `Artifacts.stateless_input_*` ; these are the additional container-relative offsets this module introduces. -/

open BinaryFv.Zesu.Artifacts in
def containerFieldOffsetsValid : Bool :=
  abiDatum "ssz_raw.RawForkActivation|block_number" == some 0 &&
    abiDatum "ssz_raw.RawForkActivation|timestamp" == some 16 &&
      abiDatum "ssz_raw.RawForkConfig|activation" == some 8 &&
        abiDatum "ssz_raw.RawForkConfig|blob_schedule" == some 40 &&
          abiDatum "ssz_raw.RawExecutionPayload|extra_data" == some 64 &&
            abiDatum "ssz_raw.RawExecutionPayload|block_access_list" == some 128 &&
              abiDatum "ssz_raw.RawExecutionPayload|base_fee_per_gas" == some 0 &&
                abiDatum "ssz_raw.RawNewPayloadRequest|execution_payload" == some 0 &&
                  abiDatum "ssz_raw.RawBlobSchedule|target" == some 0 &&
                    abiDatum "ssz_raw.RawBlobSchedule|max" == some 8 &&
                      abiDatum "ssz_raw.RawBlobSchedule|base_fee_update_fraction" == some 16

theorem container_field_offsets_valid : containerFieldOffsetsValid = true := by native_decide

end BinaryFv.Zesu.MemoryRepresentation
