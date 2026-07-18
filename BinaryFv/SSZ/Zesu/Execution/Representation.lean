import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Logic.ImageMemory
import BinaryFv.SSZ.Zesu.Artifact.AbiManifest
import SszBridge.Core

namespace BinaryFv.SSZ.Zesu.Execution

open BinaryFv.RiscV

/-- A half-open, bytewise region of generated Sail sparse memory. -/
def MemoryBytes (state : State) (base : Nat) (bytes : ByteArray) : Prop :=
  ∀ index (h : index < bytes.size),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (bytes[index]'h).toNat)

/-- An inline fixed-size bridge byte vector in native sparse memory. -/
def FixedByteVectorRep {length : Nat} (state : State) (base : Nat)
    (value : SszBridge.RawByteVector length) : Prop :=
  ∀ index (h : index < length),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (value[index].toNat))

/-- Inline little-endian bytes for an SSZ integer represented as a Lean bit vector. -/
def BitVectorLERep {width : Nat} (state : State) (base : Nat) (value : BitVec width) : Prop :=
  ∀ index (h : index < width / 8),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 ((value.toNat / 256 ^ index) % 256))

/-- A decoder slice that aliases caller-owned input rather than copying it into the heap. -/
def InputSliceRep (state : State) (inputBase inputOffset length sliceBase : Nat) : Prop :=
  sliceBase = inputBase + inputOffset ∧
    ∀ index, index < length → state.mem.get? (sliceBase + index) = state.mem.get? (inputBase + inputOffset + index)

/-- A bridge byte array is exactly a bounded subrange of the caller-provided input. -/
def InputBytesAt (input : ByteArray) (inputOffset : Nat) (bytes : Array UInt8) : Prop :=
  ∀ index (h : index < bytes.size),
    ∃ hinput : inputOffset + index < input.size,
      bytes[index] = input[inputOffset + index]'hinput

/-- A heap array is a disjoint materialized sequence of fixed-width records. -/
def HeapArrayRep (state : State) (base count elementSize : Nat) : Prop :=
  base + count * elementSize ≤ 2 ^ 64 ∧
    ∀ index, index < count * elementSize → (state.mem.get? (base + index)).isSome

/-- A heap array whose elements are inline fixed-width bridge byte vectors. -/
def HeapFixedVectorArrayRep {length : Nat} (state : State) (base : Nat)
    (values : Array (SszBridge.RawByteVector length)) : Prop :=
  ∀ index (h : index < values.size),
    FixedByteVectorRep state (base + length * index) values[index]

/-- A concrete little-endian RV64 word in Sail sparse memory. -/
def Word64LERep (state : State) (base value : Nat) : Prop :=
  ∀ index, index < 8 →
    state.mem.get? (base + index) = some (BitVec.ofNat 8 ((value / 256 ^ index) % 256))

/-- Guarded, executable RV64 little-endian observer for a sparse-memory word. -/
def observeWord64? (state : State) (base : Nat) : Option Nat := do
  let b0 ← state.mem.get? base
  let b1 ← state.mem.get? (base + 1)
  let b2 ← state.mem.get? (base + 2)
  let b3 ← state.mem.get? (base + 3)
  let b4 ← state.mem.get? (base + 4)
  let b5 ← state.mem.get? (base + 5)
  let b6 ← state.mem.get? (base + 6)
  let b7 ← state.mem.get? (base + 7)
  pure (b0.toNat + 256 * b1.toNat + 256 ^ 2 * b2.toNat + 256 ^ 3 * b3.toNat +
    256 ^ 4 * b4.toNat + 256 ^ 5 * b5.toNat + 256 ^ 6 * b6.toNat + 256 ^ 7 * b7.toNat)

theorem observe_word64_of_rep (state : State) (base value : Nat)
    (bound : value < 2 ^ 64) (representation : Word64LERep state base value) :
    observeWord64? state base = some value := by
  have byte0 : state.mem.get? base = some (BitVec.ofNat 8 (value % 256)) := by
    simpa using representation 0 (by omega)
  have byte1 := representation 1 (by omega)
  have byte2 := representation 2 (by omega)
  have byte3 := representation 3 (by omega)
  have byte4 := representation 4 (by omega)
  have byte5 := representation 5 (by omega)
  have byte6 := representation 6 (by omega)
  have byte7 := representation 7 (by omega)
  simp only [observeWord64?, byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]
  simp
  omega

/-- The two-word Zig `std.mem.Allocator` object: context followed by its vtable pointer. -/
def AllocatorObjectRep (state : State) (base context vtable : Nat) : Prop :=
  Word64LERep state base context ∧ Word64LERep state (base + 8) vtable

/-- The four-entry Zig allocator vtable in its compiler-reflected order. -/
def AllocatorVtableRep (state : State) (base alloc resize remap free : Nat) : Prop :=
  Word64LERep state base alloc ∧ Word64LERep state (base + 8) resize ∧
    Word64LERep state (base + 16) remap ∧ Word64LERep state (base + 24) free

/-- The six parser-owned indirect tail transfers read Zig's `free` slot at offset 24. -/
def AllocatorDispatchRep (state : State) (allocatorBase context vtable target : Nat) : Prop :=
  AllocatorObjectRep state allocatorBase context vtable ∧
    Word64LERep state (vtable + 24) target

theorem allocator_dispatch_target (state : State) (allocatorBase context vtable target : Nat)
    (representation : AllocatorDispatchRep state allocatorBase context vtable target) :
    Word64LERep state (allocatorBase + 8) vtable ∧ Word64LERep state (vtable + 24) target := by
  exact ⟨representation.1.2, representation.2⟩

/-- RV64 Zig slice descriptor: a data pointer followed by a `usize` element count. -/
def SliceDescriptorRep (state : State) (base data count : Nat) : Prop :=
  data < 2 ^ 64 ∧ count < 2 ^ 64 ∧
    Word64LERep state base data ∧ Word64LERep state (base + 8) count

/-- A slice descriptor aliases an exact bridge byte array in the caller's input memory. -/
def InputSliceDescriptorRep (state : State) (inputBase : Nat) (input : ByteArray) (descriptorBase : Nat)
    (inputOffset sliceBase : Nat) (bytes : Array UInt8) : Prop :=
  SliceDescriptorRep state descriptorBase sliceBase bytes.size ∧
    InputSliceRep state inputBase inputOffset bytes.size sliceBase ∧ InputBytesAt input inputOffset bytes

def InputSliceDescriptorArrayRep (state : State) (inputBase : Nat) (input : ByteArray)
    (descriptorBase : Nat) (slices : Array (Array UInt8)) : Prop :=
  ∀ index (h : index < slices.size),
    ∃ inputOffset sliceBase,
      InputSliceDescriptorRep state inputBase input (descriptorBase + 16 * index) inputOffset sliceBase
        slices[index]

/-- Guarded observer for the pointer/count pair in a Zig slice descriptor. -/
def observeSliceDescriptor? (state : State) (base : Nat) : Option (Nat × Nat) := do
  let data ← observeWord64? state base
  let count ← observeWord64? state (base + 8)
  pure (data, count)

theorem observe_slice_descriptor_of_rep (state : State) (base data count : Nat)
    (representation : SliceDescriptorRep state base data count) :
    observeSliceDescriptor? state base = some (data, count) := by
  unfold observeSliceDescriptor?
  rw [observe_word64_of_rep state base data representation.1 representation.2.2.1,
    observe_word64_of_rep state (base + 8) count representation.2.1 representation.2.2.2]
  rfl

/-- The decoded root object occupies precisely the compiler-reflected RV64 ABI size. -/
def RawStatelessInputRep (state : State) (base : Nat) : Prop :=
  ∃ size, Artifact.rawStatelessInputSize = some size ∧ HeapArrayRep state base 1 size

theorem raw_stateless_input_rep_size (state : State) (base : Nat)
    (representation : RawStatelessInputRep state base) : HeapArrayRep state base 1 832 := by
  rcases representation with ⟨size, sizeH, representation⟩
  rw [Artifact.raw_stateless_input_layout.1] at sizeH
  injection sizeH with sizeH
  subst size
  exact representation

/-- Heap bases carried by the root's ten slice descriptors. -/
structure RawV4DescriptorBases where
  versionedHashesBase : Nat
  transactionsBase : Nat
  withdrawalsBase : Nat
  depositsBase : Nat
  withdrawalRequestsBase : Nat
  consolidationRequestsBase : Nat
  witnessStateBase : Nat
  witnessCodesBase : Nat
  witnessHeadersBase : Nat
  publicKeysBase : Nat

/-- Heap-allocation portion of the native representation of a complete bridge `RawV4` value.

Fixed records are sized from the pinned RV64 ABI manifest. The eventual observer additionally
connects these bases to the corresponding slice descriptors stored in the root object. -/
structure RawV4AllocationRep (state : State) (rootBase : Nat) (value : SszBridge.RawV4)
    (bases : RawV4DescriptorBases) : Prop where
  root : RawStatelessInputRep state rootBase
  versionedHashes : HeapArrayRep state bases.versionedHashesBase
    value.newPayloadRequest.versionedHashes.size 32
  transactions : HeapArrayRep state bases.transactionsBase
    value.newPayloadRequest.executionPayload.transactions.size 16
  withdrawals : HeapArrayRep state bases.withdrawalsBase
    value.newPayloadRequest.executionPayload.withdrawals.size 48
  deposits : HeapArrayRep state bases.depositsBase
    value.newPayloadRequest.executionRequests.deposits.size 192
  withdrawalRequests : HeapArrayRep state bases.withdrawalRequestsBase
    value.newPayloadRequest.executionRequests.withdrawals.size 80
  consolidationRequests : HeapArrayRep state bases.consolidationRequestsBase
    value.newPayloadRequest.executionRequests.consolidations.size 116
  witnessState : HeapArrayRep state bases.witnessStateBase value.witness.state.size 16
  witnessCodes : HeapArrayRep state bases.witnessCodesBase value.witness.codes.size 16
  witnessHeaders : HeapArrayRep state bases.witnessHeadersBase value.witness.headers.size 16
  publicKeys : HeapArrayRep state bases.publicKeysBase value.publicKeys.size 65
  publicKeyContents : HeapFixedVectorArrayRep state bases.publicKeysBase value.publicKeys

theorem raw_v4_allocation_root_size (state : State) (rootBase : Nat) (value : SszBridge.RawV4)
    (bases : RawV4DescriptorBases)
    (representation : RawV4AllocationRep state rootBase value bases) : HeapArrayRep state rootBase 1 832 :=
  raw_stateless_input_rep_size state rootBase representation.root

/-- Descriptor-level portion of the root layout, with every collection count tied to `RawV4`. -/
structure RawV4DescriptorRep (state : State) (rootBase : Nat) (value : SszBridge.RawV4)
    (bases : RawV4DescriptorBases) : Prop where
  versionedHashes : SliceDescriptorRep state (rootBase + 592) bases.versionedHashesBase
    value.newPayloadRequest.versionedHashes.size
  transactions : SliceDescriptorRep state (rootBase + 80) bases.transactionsBase
    value.newPayloadRequest.executionPayload.transactions.size
  withdrawals : SliceDescriptorRep state (rootBase + 96) bases.withdrawalsBase
    value.newPayloadRequest.executionPayload.withdrawals.size
  deposits : SliceDescriptorRep state (rootBase + 608) bases.depositsBase
    value.newPayloadRequest.executionRequests.deposits.size
  withdrawalRequests : SliceDescriptorRep state (rootBase + 624) bases.withdrawalRequestsBase
    value.newPayloadRequest.executionRequests.withdrawals.size
  consolidationRequests : SliceDescriptorRep state (rootBase + 640) bases.consolidationRequestsBase
    value.newPayloadRequest.executionRequests.consolidations.size
  witnessState : SliceDescriptorRep state (rootBase + 688) bases.witnessStateBase value.witness.state.size
  witnessCodes : SliceDescriptorRep state (rootBase + 704) bases.witnessCodesBase value.witness.codes.size
  witnessHeaders : SliceDescriptorRep state (rootBase + 720) bases.witnessHeadersBase value.witness.headers.size
  publicKeys : SliceDescriptorRep state (rootBase + 816) bases.publicKeysBase value.publicKeys.size

/-- Borrowed byte slices in `RawV4`, including every transaction and witness element. -/
structure RawV4InputSlicesRep (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : SszBridge.RawV4) (bases : RawV4DescriptorBases)
    (descriptors : RawV4DescriptorRep state rootBase value bases) : Prop where
  extraData : ∃ inputOffset sliceBase,
    InputSliceDescriptorRep state inputBase input (rootBase + 64) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.extraData
  blockAccessList : ∃ inputOffset sliceBase,
    InputSliceDescriptorRep state inputBase input (rootBase + 128) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.blockAccessList
  transactions : InputSliceDescriptorArrayRep state inputBase input bases.transactionsBase
    value.newPayloadRequest.executionPayload.transactions
  witnessState : InputSliceDescriptorArrayRep state inputBase input bases.witnessStateBase value.witness.state
  witnessCodes : InputSliceDescriptorArrayRep state inputBase input bases.witnessCodesBase value.witness.codes
  witnessHeaders : InputSliceDescriptorArrayRep state inputBase input bases.witnessHeadersBase
    value.witness.headers

/-- Inline fixed vectors and scalar fields in the root's nested execution payload. -/
structure RawV4FixedFieldsRep (state : State) (rootBase : Nat) (value : SszBridge.RawV4) : Prop where
  baseFeePerGas : BitVectorLERep state rootBase value.newPayloadRequest.executionPayload.baseFeePerGas
  parentHash : FixedByteVectorRep state (rootBase + 152) value.newPayloadRequest.executionPayload.parentHash
  feeRecipient : FixedByteVectorRep state (rootBase + 184)
    value.newPayloadRequest.executionPayload.feeRecipient
  stateRoot : FixedByteVectorRep state (rootBase + 204) value.newPayloadRequest.executionPayload.stateRoot
  receiptsRoot : FixedByteVectorRep state (rootBase + 236)
    value.newPayloadRequest.executionPayload.receiptsRoot
  logsBloom : FixedByteVectorRep state (rootBase + 268) value.newPayloadRequest.executionPayload.logsBloom
  prevRandao : FixedByteVectorRep state (rootBase + 524) value.newPayloadRequest.executionPayload.prevRandao
  blockHash : FixedByteVectorRep state (rootBase + 556) value.newPayloadRequest.executionPayload.blockHash
  parentBeaconBlockRoot : FixedByteVectorRep state (rootBase + 656)
    value.newPayloadRequest.parentBeaconBlockRoot
  blockNumber : Word64LERep state (rootBase + 32) value.newPayloadRequest.executionPayload.blockNumber.toNat
  gasLimit : Word64LERep state (rootBase + 40) value.newPayloadRequest.executionPayload.gasLimit.toNat
  gasUsed : Word64LERep state (rootBase + 48) value.newPayloadRequest.executionPayload.gasUsed.toNat
  timestamp : Word64LERep state (rootBase + 56) value.newPayloadRequest.executionPayload.timestamp.toNat
  blobGasUsed : Word64LERep state (rootBase + 112) value.newPayloadRequest.executionPayload.blobGasUsed.toNat
  excessBlobGas : Word64LERep state (rootBase + 120)
    value.newPayloadRequest.executionPayload.excessBlobGas.toNat
  slotNumber : Word64LERep state (rootBase + 144) value.newPayloadRequest.executionPayload.slotNumber.toNat
  chainId : Word64LERep state (rootBase + 736) value.chainConfig.chainId.toNat
  activeFork : Word64LERep state (rootBase + 744) value.chainConfig.activeFork.fork.toNat

/-- Native `RawV4` ownership representation: root allocation, all heap arrays, and borrowed slices.

Scalar and fixed-vector byte contents are added by the later field observer; this layer establishes
the ownership and aliasing boundary used by all parser and runtime contracts. -/
structure RawV4Rep (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : SszBridge.RawV4) : Prop where
  layout : ∃ bases : RawV4DescriptorBases,
    RawV4AllocationRep state rootBase value bases ∧
      ∃ descriptors : RawV4DescriptorRep state rootBase value bases,
        RawV4InputSlicesRep state inputBase input rootBase value bases descriptors
  fixedFields : RawV4FixedFieldsRep state rootBase value

/-- The executable descriptor-only observation of the native root object. -/
structure RawV4DescriptorObservation where
  versionedHashes : Nat × Nat
  transactions : Nat × Nat
  withdrawals : Nat × Nat
  deposits : Nat × Nat
  withdrawalRequests : Nat × Nat
  consolidationRequests : Nat × Nat
  witnessState : Nat × Nat
  witnessCodes : Nat × Nat
  witnessHeaders : Nat × Nat
  publicKeys : Nat × Nat

def observeRawV4Descriptors? (state : State) (rootBase : Nat) : Option RawV4DescriptorObservation := do
  let versionedHashes ← observeSliceDescriptor? state (rootBase + 592)
  let transactions ← observeSliceDescriptor? state (rootBase + 80)
  let withdrawals ← observeSliceDescriptor? state (rootBase + 96)
  let deposits ← observeSliceDescriptor? state (rootBase + 608)
  let withdrawalRequests ← observeSliceDescriptor? state (rootBase + 624)
  let consolidationRequests ← observeSliceDescriptor? state (rootBase + 640)
  let witnessState ← observeSliceDescriptor? state (rootBase + 688)
  let witnessCodes ← observeSliceDescriptor? state (rootBase + 704)
  let witnessHeaders ← observeSliceDescriptor? state (rootBase + 720)
  let publicKeys ← observeSliceDescriptor? state (rootBase + 816)
  pure ⟨versionedHashes, transactions, withdrawals, deposits, withdrawalRequests,
    consolidationRequests, witnessState, witnessCodes, witnessHeaders, publicKeys⟩

theorem observe_raw_v4_descriptors_of_rep (state : State) (rootBase : Nat) (value : SszBridge.RawV4)
    (bases : RawV4DescriptorBases)
    (representation : RawV4DescriptorRep state rootBase value bases) :
    observeRawV4Descriptors? state rootBase = some
      { versionedHashes := (bases.versionedHashesBase, value.newPayloadRequest.versionedHashes.size),
        transactions := (bases.transactionsBase,
          value.newPayloadRequest.executionPayload.transactions.size),
        withdrawals := (bases.withdrawalsBase,
          value.newPayloadRequest.executionPayload.withdrawals.size),
        deposits := (bases.depositsBase, value.newPayloadRequest.executionRequests.deposits.size),
        withdrawalRequests := (bases.withdrawalRequestsBase,
          value.newPayloadRequest.executionRequests.withdrawals.size),
        consolidationRequests := (bases.consolidationRequestsBase,
          value.newPayloadRequest.executionRequests.consolidations.size),
        witnessState := (bases.witnessStateBase, value.witness.state.size),
        witnessCodes := (bases.witnessCodesBase, value.witness.codes.size),
        witnessHeaders := (bases.witnessHeadersBase, value.witness.headers.size),
        publicKeys := (bases.publicKeysBase, value.publicKeys.size) } := by
  unfold observeRawV4Descriptors?
  rw [observe_slice_descriptor_of_rep state (rootBase + 592) bases.versionedHashesBase
      value.newPayloadRequest.versionedHashes.size representation.versionedHashes,
    observe_slice_descriptor_of_rep state (rootBase + 80) bases.transactionsBase
      value.newPayloadRequest.executionPayload.transactions.size representation.transactions,
    observe_slice_descriptor_of_rep state (rootBase + 96) bases.withdrawalsBase
      value.newPayloadRequest.executionPayload.withdrawals.size representation.withdrawals,
    observe_slice_descriptor_of_rep state (rootBase + 608) bases.depositsBase
      value.newPayloadRequest.executionRequests.deposits.size representation.deposits,
    observe_slice_descriptor_of_rep state (rootBase + 624) bases.withdrawalRequestsBase
      value.newPayloadRequest.executionRequests.withdrawals.size representation.withdrawalRequests,
    observe_slice_descriptor_of_rep state (rootBase + 640) bases.consolidationRequestsBase
      value.newPayloadRequest.executionRequests.consolidations.size representation.consolidationRequests,
    observe_slice_descriptor_of_rep state (rootBase + 688) bases.witnessStateBase value.witness.state.size
      representation.witnessState,
    observe_slice_descriptor_of_rep state (rootBase + 704) bases.witnessCodesBase value.witness.codes.size
      representation.witnessCodes,
    observe_slice_descriptor_of_rep state (rootBase + 720) bases.witnessHeadersBase
      value.witness.headers.size representation.witnessHeaders,
    observe_slice_descriptor_of_rep state (rootBase + 816) bases.publicKeysBase value.publicKeys.size
      representation.publicKeys]
  rfl

end BinaryFv.SSZ.Zesu.Execution
