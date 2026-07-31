import BinaryFv.Zesu.MemoryRepresentation.RawV4

/-!
# Native RV64 representations of the seven decoder containers

Each container decoder writes its result as a fixed Zig record at its own `resultBase`. These
predicates say exactly how that record is laid out in generated Sail sparse memory, composing the
leaf/collection representations from `RawV4.lean` at the compiler-reflected field offsets. Every
literal offset here is pinned against the pinned ABI manifest by `containerFieldOffsetsValid`.

The four *allocating* containers borrow byte slices from the caller's input, so — like `RawV4Rep` —
their predicates take the input base and bytes. The three *fixed* containers do not allocate and do
not alias input; they accept the same arguments for a uniform `ContainerRepresentation` shape but
ignore them.
-/

namespace BinaryFv.Zesu.MemoryRepresentation

open BinaryFv.RiscV

/-- A `?u64` (16 bytes): the `u64` payload at offset 0 and the discriminant byte at offset 8. When
absent, only the discriminant is constrained; the payload bytes are undefined. -/
def OptionU64Rep (state : State) (base : Nat) (value : Option UInt64) : Prop :=
  match value with
  | some v => Word64LERep state base v.toNat ∧ OptionTagRep state (base + 8) true
  | none => OptionTagRep state (base + 8) false

/-- A `RawBlobSchedule` (24 bytes): three consecutive little-endian `u64` fields. -/
def BlobScheduleRep (state : State) (base : Nat) (value : SszBridge.RawBlobSchedule) : Prop :=
  Word64LERep state base value.target.toNat ∧
    Word64LERep state (base + 8) value.max.toNat ∧
      Word64LERep state (base + 16) value.baseFeeUpdateFraction.toNat

/-- A `?RawBlobSchedule` (32 bytes): the 24-byte payload at offset 0 and the discriminant at 24. -/
def OptionBlobScheduleRep (state : State) (base : Nat) (value : Option SszBridge.RawBlobSchedule) :
    Prop :=
  match value with
  | some v => BlobScheduleRep state base v ∧ OptionTagRep state (base + 24) true
  | none => OptionTagRep state (base + 24) false

/-! ## The three fixed (non-allocating) containers -/

/-- `RawForkActivation` (32 bytes): `block_number : ?u64` at 0, `timestamp : ?u64` at 16. -/
def ForkActivationRep (state : State) (base : Nat) (value : SszBridge.RawForkActivation) : Prop :=
  OptionU64Rep state base value.blockNumber ∧ OptionU64Rep state (base + 16) value.timestamp

/-- `RawForkConfig` (72 bytes): `fork : u64` at 0, `activation` at 8, `blob_schedule : ?…` at 40. -/
def ForkConfigRep (state : State) (base : Nat) (value : SszBridge.RawForkConfig) : Prop :=
  Word64LERep state base value.fork.toNat ∧
    ForkActivationRep state (base + 8) value.activation ∧
      OptionBlobScheduleRep state (base + 40) value.blobSchedule

/-- `RawChainConfig` (80 bytes): `chain_id : u64` at 0, `active_fork` at 8. -/
def ChainConfigRep (state : State) (base : Nat) (value : SszBridge.RawChainConfig) : Prop :=
  Word64LERep state base value.chainId.toNat ∧ ForkConfigRep state (base + 8) value.activeFork

/-! ## The four allocating containers -/

/-- `RawExecutionRequests` (48 bytes): three slice descriptors (deposits@0, withdrawals@16,
consolidations@32), each pointing at a disjoint heap array of fixed-width records. No input aliasing. -/
def ExecutionRequestsRep (state : State) (base : Nat) (value : SszBridge.RawExecutionRequests) :
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
    (value : SszBridge.RawExecutionWitness) : Prop :=
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
offsets are the same compiler-reflected values `RawV4FixedFieldsRep` uses, because the execution
payload sits at offset 0 of both the new-payload request and the root object. -/
structure ExecutionPayloadFixedRep (state : State) (base : Nat)
    (value : SszBridge.RawExecutionPayload) : Prop where
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
    (value : SszBridge.RawExecutionPayload) : Prop :=
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
    (value : SszBridge.RawNewPayloadRequest) : Prop :=
  ExecutionPayloadRep state inputBase input base value.executionPayload ∧
  (∃ versionedHashesBase,
    SliceDescriptorRep state (base + 592) versionedHashesBase value.versionedHashes.size ∧
      HeapArrayRep state versionedHashesBase value.versionedHashes.size 32 ∧
        HeapFixedVectorArrayRep state versionedHashesBase value.versionedHashes) ∧
  FixedByteVectorRep state (base + 656) value.parentBeaconBlockRoot ∧
  ExecutionRequestsRep state (base + 608) value.executionRequests

/-! ## Offset audit

Every literal field offset used above is pinned against the compiler-reflected ABI manifest. The
offsets `RawV4.lean` already re-uses (fixed fields, root descriptors, heap element sizes) are audited
by `Artifact.raw_v4_*` ; these are the additional container-relative offsets this module introduces. -/

open BinaryFv.Zesu.Artifact in
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
