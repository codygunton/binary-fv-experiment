import BinaryFv.SSZ.Zesu.MemoryRepresentation.RawV4

namespace BinaryFv.SSZ.Zesu.MemoryRepresentation

open BinaryFv.RiscV

/-- Guarded sparse-memory observer for a variable-length byte sequence. -/
def observeBytes? (state : State) (base : Nat) : Nat → Option (List UInt8)
  | 0 => some []
  | length + 1 => do
    let byte ← state.mem.get? base
    let tail ← observeBytes? state (base + 1) length
    pure (UInt8.ofNat byte.toNat :: tail)

/-- Pointwise byte ownership for a list observed from Sail sparse memory. -/
def MemoryListBytes (state : State) (base : Nat) (bytes : List UInt8) : Prop :=
  ∀ index (h : index < bytes.length),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (bytes[index].toNat))

private def ObservedInputSliceRep (state : State) (inputBase : Nat) (input : ByteArray)
    (inputOffset sliceBase : Nat) (bytes : Array UInt8) : Prop :=
  InputSliceRep state inputBase inputOffset bytes.size sliceBase ∧
    ∀ index (h : index < bytes.size),
      ∃ hinput : inputOffset + index < input.size,
        bytes[index] = input[inputOffset + index]'hinput

theorem observe_bytes_of_memory (state : State) (base : Nat) :
    ∀ bytes : List UInt8, MemoryListBytes state base bytes →
      observeBytes? state base bytes.length = some bytes := by
  intro bytes
  induction bytes generalizing base with
  | nil => intro _; rfl
  | cons byte tail inductionHypothesis =>
    intro memory
    simp only [List.length_cons, observeBytes?]
    have headMemory : state.mem.get? base = some (BitVec.ofNat 8 byte.toNat) := by
      simpa [MemoryListBytes] using memory 0 (by simp)
    rw [headMemory]
    have tailMemory : MemoryListBytes state (base + 1) tail := by
      intro index indexBound
      simpa [MemoryListBytes, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        memory (index + 1) (by simp [indexBound])
    rw [inductionHypothesis (base + 1) tailMemory]
    simp

/-- Observe a compiler-reflected fixed byte vector from its inline native representation. -/
theorem observe_fixed_byte_vector_of_rep {length : Nat} (state : State) (base : Nat)
    (value : SszBridge.RawByteVector length)
    (representation : FixedByteVectorRep state base value) :
    observeBytes? state base length = some value.toArray.toList := by
  have memory : MemoryListBytes state base value.toArray.toList := by
    intro index indexBound
    have vectorBound : index < length := by
      simpa using indexBound
    simpa [FixedByteVectorRep] using representation index vectorBound
  simpa using observe_bytes_of_memory state base value.toArray.toList memory

/-- The little-endian bytes of a bridge bit vector, least-significant byte first. -/
def bitVectorLEBytes {width : Nat} (value : BitVec width) : List UInt8 :=
  (List.range (width / 8)).map fun index =>
    UInt8.ofNat ((value.toNat / 256 ^ index) % 256)

theorem bit_vector_le_memory_list {width : Nat} (state : State) (base : Nat)
    (value : BitVec width) (representation : BitVectorLERep state base value) :
    MemoryListBytes state base (bitVectorLEBytes value) := by
  intro index indexBound
  have byteBound : index < width / 8 := by
    simpa [bitVectorLEBytes] using indexBound
  simpa [bitVectorLEBytes] using representation index byteBound

theorem observe_bit_vector_le_of_rep {width : Nat} (state : State) (base : Nat)
    (value : BitVec width) (representation : BitVectorLERep state base value) :
    observeBytes? state base (width / 8) = some (bitVectorLEBytes value) := by
  simpa [bitVectorLEBytes] using
    observe_bytes_of_memory state base (bitVectorLEBytes value)
      (bit_vector_le_memory_list state base value representation)

/-- The fixed byte vectors embedded in the root's execution-payload portion. -/
structure RawV4FixedVectorObservation where
  parentHash : List UInt8
  feeRecipient : List UInt8
  stateRoot : List UInt8
  receiptsRoot : List UInt8
  logsBloom : List UInt8
  prevRandao : List UInt8
  blockHash : List UInt8
  parentBeaconBlockRoot : List UInt8

def observeRawV4FixedVectors? (state : State) (rootBase : Nat) :
    Option RawV4FixedVectorObservation := do
  let parentHash ← observeBytes? state (rootBase + 152) 32
  let feeRecipient ← observeBytes? state (rootBase + 184) 20
  let stateRoot ← observeBytes? state (rootBase + 204) 32
  let receiptsRoot ← observeBytes? state (rootBase + 236) 32
  let logsBloom ← observeBytes? state (rootBase + 268) 256
  let prevRandao ← observeBytes? state (rootBase + 524) 32
  let blockHash ← observeBytes? state (rootBase + 556) 32
  let parentBeaconBlockRoot ← observeBytes? state (rootBase + 656) 32
  pure ⟨parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao, blockHash,
    parentBeaconBlockRoot⟩

theorem observe_raw_v4_fixed_vectors_of_rep (state : State) (rootBase : Nat)
    (value : SszBridge.RawV4) (representation : RawV4FixedFieldsRep state rootBase value) :
    observeRawV4FixedVectors? state rootBase = some
      { parentHash := value.newPayloadRequest.executionPayload.parentHash.toArray.toList,
        feeRecipient := value.newPayloadRequest.executionPayload.feeRecipient.toArray.toList,
        stateRoot := value.newPayloadRequest.executionPayload.stateRoot.toArray.toList,
        receiptsRoot := value.newPayloadRequest.executionPayload.receiptsRoot.toArray.toList,
        logsBloom := value.newPayloadRequest.executionPayload.logsBloom.toArray.toList,
        prevRandao := value.newPayloadRequest.executionPayload.prevRandao.toArray.toList,
        blockHash := value.newPayloadRequest.executionPayload.blockHash.toArray.toList,
        parentBeaconBlockRoot :=
          value.newPayloadRequest.parentBeaconBlockRoot.toArray.toList } := by
  unfold observeRawV4FixedVectors?
  rw [observe_fixed_byte_vector_of_rep state (rootBase + 152) _ representation.parentHash,
    observe_fixed_byte_vector_of_rep state (rootBase + 184) _ representation.feeRecipient,
    observe_fixed_byte_vector_of_rep state (rootBase + 204) _ representation.stateRoot,
    observe_fixed_byte_vector_of_rep state (rootBase + 236) _ representation.receiptsRoot,
    observe_fixed_byte_vector_of_rep state (rootBase + 268) _ representation.logsBloom,
    observe_fixed_byte_vector_of_rep state (rootBase + 524) _ representation.prevRandao,
    observe_fixed_byte_vector_of_rep state (rootBase + 556) _ representation.blockHash,
    observe_fixed_byte_vector_of_rep state (rootBase + 656) _ representation.parentBeaconBlockRoot]
  rfl

/-- Observe the exact 32-byte little-endian representation of the V4 base fee. -/
def observeRawV4BaseFee? (state : State) (rootBase : Nat) : Option (List UInt8) :=
  observeBytes? state rootBase 32

theorem observe_raw_v4_base_fee_of_rep (state : State) (rootBase : Nat)
    (value : SszBridge.RawV4) (representation : RawV4FixedFieldsRep state rootBase value) :
    observeRawV4BaseFee? state rootBase = some
      (bitVectorLEBytes value.newPayloadRequest.executionPayload.baseFeePerGas) := by
  unfold observeRawV4BaseFee?
  simpa using observe_bit_vector_le_of_rep state rootBase
    value.newPayloadRequest.executionPayload.baseFeePerGas representation.baseFeePerGas

/-- The inline 64-bit scalar fields embedded in the root's execution payload. -/
structure RawV4ScalarObservation where
  blockNumber : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  blobGasUsed : Nat
  excessBlobGas : Nat
  slotNumber : Nat
  chainId : Nat
  activeFork : Nat

def observeRawV4Scalars? (state : State) (rootBase : Nat) : Option RawV4ScalarObservation := do
  let blockNumber ← observeWord64? state (rootBase + 32)
  let gasLimit ← observeWord64? state (rootBase + 40)
  let gasUsed ← observeWord64? state (rootBase + 48)
  let timestamp ← observeWord64? state (rootBase + 56)
  let blobGasUsed ← observeWord64? state (rootBase + 112)
  let excessBlobGas ← observeWord64? state (rootBase + 120)
  let slotNumber ← observeWord64? state (rootBase + 144)
  let chainId ← observeWord64? state (rootBase + 736)
  let activeFork ← observeWord64? state (rootBase + 744)
  pure ⟨blockNumber, gasLimit, gasUsed, timestamp, blobGasUsed, excessBlobGas, slotNumber,
    chainId, activeFork⟩

theorem observe_raw_v4_scalars_of_rep (state : State) (rootBase : Nat)
    (value : SszBridge.RawV4) (representation : RawV4FixedFieldsRep state rootBase value) :
    observeRawV4Scalars? state rootBase = some
      { blockNumber := value.newPayloadRequest.executionPayload.blockNumber.toNat,
        gasLimit := value.newPayloadRequest.executionPayload.gasLimit.toNat,
        gasUsed := value.newPayloadRequest.executionPayload.gasUsed.toNat,
        timestamp := value.newPayloadRequest.executionPayload.timestamp.toNat,
        blobGasUsed := value.newPayloadRequest.executionPayload.blobGasUsed.toNat,
        excessBlobGas := value.newPayloadRequest.executionPayload.excessBlobGas.toNat,
        slotNumber := value.newPayloadRequest.executionPayload.slotNumber.toNat,
        chainId := value.chainConfig.chainId.toNat,
        activeFork := value.chainConfig.activeFork.fork.toNat } := by
  unfold observeRawV4Scalars?
  rw [observe_word64_of_rep state (rootBase + 32) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.blockNumber) representation.blockNumber,
    observe_word64_of_rep state (rootBase + 40) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.gasLimit) representation.gasLimit,
    observe_word64_of_rep state (rootBase + 48) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.gasUsed) representation.gasUsed,
    observe_word64_of_rep state (rootBase + 56) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.timestamp) representation.timestamp,
    observe_word64_of_rep state (rootBase + 112) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.blobGasUsed) representation.blobGasUsed,
    observe_word64_of_rep state (rootBase + 120) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.excessBlobGas)
      representation.excessBlobGas,
    observe_word64_of_rep state (rootBase + 144) _
      (UInt64.toNat_lt value.newPayloadRequest.executionPayload.slotNumber) representation.slotNumber,
    observe_word64_of_rep state (rootBase + 736) _ (UInt64.toNat_lt value.chainConfig.chainId)
      representation.chainConfig.1,
    observe_word64_of_rep state (rootBase + 744) _ (UInt64.toNat_lt value.chainConfig.activeFork.fork)
      (by simpa [Nat.add_assoc] using representation.chainConfig.2.1)]
  rfl

theorem input_slice_descriptor_memory_list (state : State) (inputBase : Nat) (input : ByteArray)
    (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : ObservedInputSliceRep state inputBase input inputOffset sliceBase bytes) :
    MemoryListBytes state sliceBase bytes.toList := by
  intro index indexBound
  have arrayBound : index < bytes.size := by simpa using indexBound
  rcases representation.2 index arrayBound with ⟨inputIndexBound, bytesEq⟩
  calc
    state.mem.get? (sliceBase + index) = state.mem.get? (inputBase + inputOffset + index) :=
      representation.1.2 index arrayBound
    _ = some (BitVec.ofNat 8 (input[inputOffset + index]'inputIndexBound).toNat) := by
      simpa [Nat.add_assoc] using inputMemory (inputOffset + index) inputIndexBound
    _ = some (BitVec.ofNat 8 (bytes.toList[index].toNat)) := by
      congr 1
      exact congrArg (fun byte : UInt8 => BitVec.ofNat 8 byte.toNat) (by simpa using bytesEq.symm)

theorem observe_input_slice_descriptor (state : State) (inputBase : Nat) (input : ByteArray)
    (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : ObservedInputSliceRep state inputBase input inputOffset sliceBase bytes) :
    observeBytes? state sliceBase bytes.size = some bytes.toList := by
  have owned := input_slice_descriptor_memory_list state inputBase input descriptorBase inputOffset
    sliceBase bytes inputMemory representation
  simpa using observe_bytes_of_memory state sliceBase bytes.toList owned

theorem input_slice_descriptor_memory_list_of_rep (state : State) (inputBase : Nat)
    (input : ByteArray) (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : InputSliceDescriptorRep state inputBase input descriptorBase inputOffset sliceBase bytes) :
    MemoryListBytes state sliceBase bytes.toList :=
  input_slice_descriptor_memory_list state inputBase input descriptorBase inputOffset sliceBase bytes
    inputMemory ⟨representation.2.1, representation.2.2⟩

theorem observe_input_slice_descriptor_of_rep (state : State) (inputBase : Nat) (input : ByteArray)
    (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : InputSliceDescriptorRep state inputBase input descriptorBase inputOffset sliceBase bytes) :
    observeBytes? state sliceBase bytes.size = some bytes.toList := by
  have owned := input_slice_descriptor_memory_list_of_rep state inputBase input descriptorBase inputOffset
    sliceBase bytes inputMemory representation
  simpa using observe_bytes_of_memory state sliceBase bytes.toList owned

theorem raw_v4_extra_data_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) :
    ∃ inputOffset : Nat, ∃ sliceBase : Nat,
      observeBytes? state sliceBase value.newPayloadRequest.executionPayload.extraData.size =
        some value.newPayloadRequest.executionPayload.extraData.toList := by
  rcases representation.layout with ⟨_, _, _, inputSlices⟩
  rcases inputSlices.extraData with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input (rootBase + 64) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.extraData inputMemory sliceRepresentation⟩

theorem raw_v4_block_access_list_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) :
    ∃ inputOffset : Nat, ∃ sliceBase : Nat,
      observeBytes? state sliceBase value.newPayloadRequest.executionPayload.blockAccessList.size =
        some value.newPayloadRequest.executionPayload.blockAccessList.toList := by
  rcases representation.layout with ⟨_, _, _, inputSlices⟩
  rcases inputSlices.blockAccessList with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input (rootBase + 128) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.blockAccessList inputMemory sliceRepresentation⟩

theorem raw_v4_transaction_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.executionPayload.transactions.size) :
    ∃ inputOffset : Nat, ∃ sliceBase : Nat,
      observeBytes? state sliceBase value.newPayloadRequest.executionPayload.transactions[index].size =
        some value.newPayloadRequest.executionPayload.transactions[index].toList := by
  rcases representation.layout with ⟨bases, _, _, inputSlices⟩
  rcases inputSlices.transactions index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (bases.transactionsBase + 16 * index) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.transactions[index] inputMemory sliceRepresentation⟩

theorem raw_v4_witness_state_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.witness.state.size) :
    ∃ inputOffset : Nat, ∃ sliceBase : Nat,
      observeBytes? state sliceBase value.witness.state[index].size =
        some value.witness.state[index].toList := by
  rcases representation.layout with ⟨bases, _, _, inputSlices⟩
  rcases inputSlices.witnessState index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (bases.witnessStateBase + 16 * index) inputOffset sliceBase
      value.witness.state[index] inputMemory sliceRepresentation⟩

theorem raw_v4_witness_codes_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.witness.codes.size) :
    ∃ inputOffset : Nat, ∃ sliceBase : Nat,
      observeBytes? state sliceBase value.witness.codes[index].size =
        some value.witness.codes[index].toList := by
  rcases representation.layout with ⟨bases, _, _, inputSlices⟩
  rcases inputSlices.witnessCodes index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (bases.witnessCodesBase + 16 * index) inputOffset sliceBase
      value.witness.codes[index] inputMemory sliceRepresentation⟩

theorem raw_v4_witness_headers_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.witness.headers.size) :
    ∃ inputOffset : Nat, ∃ sliceBase : Nat,
      observeBytes? state sliceBase value.witness.headers[index].size =
        some value.witness.headers[index].toList := by
  rcases representation.layout with ⟨bases, _, _, inputSlices⟩
  rcases inputSlices.witnessHeaders index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (bases.witnessHeadersBase + 16 * index) inputOffset sliceBase
      value.witness.headers[index] inputMemory sliceRepresentation⟩

theorem raw_v4_public_key_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.publicKeys.size) :
    ∃ base,
      observeBytes? state (base + 65 * index) 65 = some value.publicKeys[index].toArray.toList := by
  rcases representation.layout with ⟨bases, allocations, _, _⟩
  exact ⟨bases.publicKeysBase,
    observe_fixed_byte_vector_of_rep state (bases.publicKeysBase + 65 * index)
      value.publicKeys[index] (allocations.publicKeyContents index indexBound)⟩

theorem raw_v4_versioned_hash_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.versionedHashes.size) :
    ∃ base,
      observeBytes? state (base + 32 * index) 32 =
        some value.newPayloadRequest.versionedHashes[index].toArray.toList := by
  rcases representation.layout with ⟨bases, allocations, _, _⟩
  exact ⟨bases.versionedHashesBase,
    observe_fixed_byte_vector_of_rep state (bases.versionedHashesBase + 32 * index)
      value.newPayloadRequest.versionedHashes[index]
      (allocations.versionedHashContents index indexBound)⟩

/-- Observable fields of one native withdrawal record. -/
structure RawWithdrawalObservation where
  index : Nat
  validatorIndex : Nat
  amount : Nat
  address : List UInt8

def observeRawWithdrawal? (state : State) (base : Nat) : Option RawWithdrawalObservation := do
  let index ← observeWord64? state base
  let validatorIndex ← observeWord64? state (base + 8)
  let amount ← observeWord64? state (base + 16)
  let address ← observeBytes? state (base + 24) 20
  pure ⟨index, validatorIndex, amount, address⟩

theorem observe_raw_withdrawal_of_rep (state : State) (base : Nat) (value : SszBridge.RawWithdrawal)
    (representation : RawWithdrawalRep state base value) :
    observeRawWithdrawal? state base = some
      ⟨value.index.toNat, value.validatorIndex.toNat, value.amount.toNat, value.address.toArray.toList⟩ := by
  unfold observeRawWithdrawal?
  rw [observe_word64_of_rep state base _ (UInt64.toNat_lt value.index) representation.1,
    observe_word64_of_rep state (base + 8) _ (UInt64.toNat_lt value.validatorIndex)
      representation.2.1,
    observe_word64_of_rep state (base + 16) _ (UInt64.toNat_lt value.amount) representation.2.2.1,
    observe_fixed_byte_vector_of_rep state (base + 24) value.address representation.2.2.2]
  rfl

theorem raw_v4_withdrawal_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.executionPayload.withdrawals.size) :
    ∃ base,
      observeRawWithdrawal? state (base + 48 * index) = some
        ⟨value.newPayloadRequest.executionPayload.withdrawals[index].index.toNat,
          value.newPayloadRequest.executionPayload.withdrawals[index].validatorIndex.toNat,
          value.newPayloadRequest.executionPayload.withdrawals[index].amount.toNat,
          value.newPayloadRequest.executionPayload.withdrawals[index].address.toArray.toList⟩ := by
  rcases representation.layout with ⟨bases, allocations, _, _⟩
  exact ⟨bases.withdrawalsBase,
    observe_raw_withdrawal_of_rep state (bases.withdrawalsBase + 48 * index)
      value.newPayloadRequest.executionPayload.withdrawals[index]
      (allocations.withdrawalContents index indexBound)⟩

structure RawWithdrawalRequestObservation where
  amount : Nat
  sourceAddress : List UInt8
  validatorPubkey : List UInt8

def observeRawWithdrawalRequest? (state : State) (base : Nat) :
    Option RawWithdrawalRequestObservation := do
  let amount ← observeWord64? state base
  let sourceAddress ← observeBytes? state (base + 8) 20
  let validatorPubkey ← observeBytes? state (base + 28) 48
  pure ⟨amount, sourceAddress, validatorPubkey⟩

theorem observe_raw_withdrawal_request_of_rep (state : State) (base : Nat)
    (value : SszBridge.RawWithdrawalRequest)
    (representation : RawWithdrawalRequestRep state base value) :
    observeRawWithdrawalRequest? state base = some
      ⟨value.amount.toNat, value.sourceAddress.toArray.toList, value.validatorPubkey.toArray.toList⟩ := by
  unfold observeRawWithdrawalRequest?
  rw [observe_word64_of_rep state base _ (UInt64.toNat_lt value.amount) representation.1,
    observe_fixed_byte_vector_of_rep state (base + 8) value.sourceAddress representation.2.1,
    observe_fixed_byte_vector_of_rep state (base + 28) value.validatorPubkey representation.2.2]
  rfl

theorem raw_v4_withdrawal_request_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.executionRequests.withdrawals.size) :
    ∃ base,
      observeRawWithdrawalRequest? state (base + 80 * index) = some
        ⟨value.newPayloadRequest.executionRequests.withdrawals[index].amount.toNat,
          value.newPayloadRequest.executionRequests.withdrawals[index].sourceAddress.toArray.toList,
          value.newPayloadRequest.executionRequests.withdrawals[index].validatorPubkey.toArray.toList⟩ := by
  rcases representation.layout with ⟨bases, allocations, _, _⟩
  exact ⟨bases.withdrawalRequestsBase,
    observe_raw_withdrawal_request_of_rep state (bases.withdrawalRequestsBase + 80 * index)
      value.newPayloadRequest.executionRequests.withdrawals[index]
      (allocations.withdrawalRequestContents index indexBound)⟩

structure RawConsolidationRequestObservation where
  sourceAddress : List UInt8
  sourcePubkey : List UInt8
  targetPubkey : List UInt8

def observeRawConsolidationRequest? (state : State) (base : Nat) :
    Option RawConsolidationRequestObservation := do
  let sourceAddress ← observeBytes? state base 20
  let sourcePubkey ← observeBytes? state (base + 20) 48
  let targetPubkey ← observeBytes? state (base + 68) 48
  pure ⟨sourceAddress, sourcePubkey, targetPubkey⟩

theorem observe_raw_consolidation_request_of_rep (state : State) (base : Nat)
    (value : SszBridge.RawConsolidationRequest)
    (representation : RawConsolidationRequestRep state base value) :
    observeRawConsolidationRequest? state base = some
      ⟨value.sourceAddress.toArray.toList, value.sourcePubkey.toArray.toList,
        value.targetPubkey.toArray.toList⟩ := by
  unfold observeRawConsolidationRequest?
  rw [observe_fixed_byte_vector_of_rep state base value.sourceAddress representation.1,
    observe_fixed_byte_vector_of_rep state (base + 20) value.sourcePubkey representation.2.1,
    observe_fixed_byte_vector_of_rep state (base + 68) value.targetPubkey representation.2.2]
  rfl

theorem raw_v4_consolidation_request_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.executionRequests.consolidations.size) :
    ∃ base,
      observeRawConsolidationRequest? state (base + 116 * index) = some
        ⟨value.newPayloadRequest.executionRequests.consolidations[index].sourceAddress.toArray.toList,
          value.newPayloadRequest.executionRequests.consolidations[index].sourcePubkey.toArray.toList,
          value.newPayloadRequest.executionRequests.consolidations[index].targetPubkey.toArray.toList⟩ := by
  rcases representation.layout with ⟨bases, allocations, _, _⟩
  exact ⟨bases.consolidationRequestsBase,
    observe_raw_consolidation_request_of_rep state (bases.consolidationRequestsBase + 116 * index)
      value.newPayloadRequest.executionRequests.consolidations[index]
      (allocations.consolidationRequestContents index indexBound)⟩

structure RawDepositRequestObservation where
  amount : Nat
  index : Nat
  pubkey : List UInt8
  withdrawalCredentials : List UInt8
  signature : List UInt8

def observeRawDepositRequest? (state : State) (base : Nat) : Option RawDepositRequestObservation := do
  let amount ← observeWord64? state base
  let index ← observeWord64? state (base + 8)
  let pubkey ← observeBytes? state (base + 16) 48
  let withdrawalCredentials ← observeBytes? state (base + 64) 32
  let signature ← observeBytes? state (base + 96) 96
  pure ⟨amount, index, pubkey, withdrawalCredentials, signature⟩

theorem observe_raw_deposit_request_of_rep (state : State) (base : Nat)
    (value : SszBridge.RawDepositRequest) (representation : RawDepositRequestRep state base value) :
    observeRawDepositRequest? state base = some
      ⟨value.amount.toNat, value.index.toNat, value.pubkey.toArray.toList,
        value.withdrawalCredentials.toArray.toList, value.signature.toArray.toList⟩ := by
  unfold observeRawDepositRequest?
  rw [observe_word64_of_rep state base _ (UInt64.toNat_lt value.amount) representation.1,
    observe_word64_of_rep state (base + 8) _ (UInt64.toNat_lt value.index) representation.2.1,
    observe_fixed_byte_vector_of_rep state (base + 16) value.pubkey representation.2.2.1,
    observe_fixed_byte_vector_of_rep state (base + 64) value.withdrawalCredentials
      representation.2.2.2.1,
    observe_fixed_byte_vector_of_rep state (base + 96) value.signature representation.2.2.2.2]
  rfl

theorem raw_v4_deposit_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.executionRequests.deposits.size) :
    ∃ base,
      observeRawDepositRequest? state (base + 192 * index) = some
        ⟨value.newPayloadRequest.executionRequests.deposits[index].amount.toNat,
          value.newPayloadRequest.executionRequests.deposits[index].index.toNat,
          value.newPayloadRequest.executionRequests.deposits[index].pubkey.toArray.toList,
          value.newPayloadRequest.executionRequests.deposits[index].withdrawalCredentials.toArray.toList,
          value.newPayloadRequest.executionRequests.deposits[index].signature.toArray.toList⟩ := by
  rcases representation.layout with ⟨bases, allocations, _, _⟩
  exact ⟨bases.depositsBase,
    observe_raw_deposit_request_of_rep state (bases.depositsBase + 192 * index)
      value.newPayloadRequest.executionRequests.deposits[index]
      (allocations.depositContents index indexBound)⟩

end BinaryFv.SSZ.Zesu.MemoryRepresentation
