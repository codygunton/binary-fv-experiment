import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Logic.ImageMemory
import BinaryFv.SSZ.Zesu.Artifact.AbiManifest
import BinaryFv.SSZ.Zesu.Analysis.AllocatorCalls
import SszBridge.Core

namespace BinaryFv.SSZ.Zesu.Execution

open BinaryFv.RiscV

/-- A half-open, bytewise region of generated Sail sparse memory. -/
def MemoryBytes (state : State) (base : Nat) (bytes : ByteArray) : Prop :=
  ∀ index (h : index < bytes.size),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (bytes[index]'h).toNat)

/-- A decoder slice that aliases caller-owned input rather than copying it into the heap. -/
def InputSliceRep (state : State) (inputBase inputOffset length sliceBase : Nat) : Prop :=
  sliceBase = inputBase + inputOffset ∧
    ∀ index, index < length → state.mem.get? (sliceBase + index) = state.mem.get? (inputBase + inputOffset + index)

/-- A bridge byte array is exactly a bounded subrange of the caller-provided input. -/
def InputBytesAt (input : ByteArray) (inputOffset : Nat) (bytes : Array UInt8) : Prop :=
  inputOffset + bytes.size ≤ input.size ∧
    ∀ index (h : index < bytes.size), bytes[index] = input[inputOffset + index]'(by omega)

/-- A heap array is a disjoint materialized sequence of fixed-width records. -/
def HeapArrayRep (state : State) (base count elementSize : Nat) : Prop :=
  base + count * elementSize ≤ 2 ^ 64 ∧
    ∀ index, index < count * elementSize → (state.mem.get? (base + index)).isSome

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
  simp only [observeWord64?, Option.bind_eq_bind, Option.pure_eq_some]
  rw [representation 0 (by omega), representation 1 (by omega), representation 2 (by omega),
    representation 3 (by omega), representation 4 (by omega), representation 5 (by omega),
    representation 6 (by omega), representation 7 (by omega)]
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

/-- Loading the immutable ELF vtable makes every slot-24 cleanup dispatch target its pinned stub. -/
theorem loaded_vtable_free_target (state : State)
    (loaded : Artifact.programImage.matchesMemory state.mem) :
    Word64LERep state (Analysis.allocatorVtableAddress + Analysis.allocatorVtableCallSlotOffset)
      0x10440 := by
  intro index indexBound
  interval_cases index <;>
    exact loaded _ _ (by native_decide)

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

/-- Heap-allocation portion of the native representation of a complete bridge `RawV4` value.

Fixed records are sized from the pinned RV64 ABI manifest. The eventual observer additionally
connects these bases to the corresponding slice descriptors stored in the root object. -/
structure RawV4AllocationRep (state : State) (rootBase : Nat) (value : SszBridge.RawV4) : Prop where
  root : RawStatelessInputRep state rootBase
  versionedHashes : ∃ base, HeapArrayRep state base value.newPayloadRequest.versionedHashes.size 32
  transactions : ∃ base,
    HeapArrayRep state base value.newPayloadRequest.executionPayload.transactions.size 16
  withdrawals : ∃ base,
    HeapArrayRep state base value.newPayloadRequest.executionPayload.withdrawals.size 48
  deposits : ∃ base,
    HeapArrayRep state base value.newPayloadRequest.executionRequests.deposits.size 192
  withdrawalRequests : ∃ base,
    HeapArrayRep state base value.newPayloadRequest.executionRequests.withdrawals.size 80
  consolidationRequests : ∃ base,
    HeapArrayRep state base value.newPayloadRequest.executionRequests.consolidations.size 116
  witnessState : ∃ base, HeapArrayRep state base value.witness.state.size 16
  witnessCodes : ∃ base, HeapArrayRep state base value.witness.codes.size 16
  witnessHeaders : ∃ base, HeapArrayRep state base value.witness.headers.size 16
  publicKeys : ∃ base, HeapArrayRep state base value.publicKeys.size 65

theorem raw_v4_allocation_root_size (state : State) (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4AllocationRep state rootBase value) : HeapArrayRep state rootBase 1 832 :=
  raw_stateless_input_rep_size state rootBase representation.root

/-- Descriptor-level portion of the root layout, with every collection count tied to `RawV4`. -/
structure RawV4DescriptorRep (state : State) (rootBase : Nat) (value : SszBridge.RawV4) : Prop where
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
  versionedHashes : SliceDescriptorRep state (rootBase + 592) versionedHashesBase
    value.newPayloadRequest.versionedHashes.size
  transactions : SliceDescriptorRep state (rootBase + 80) transactionsBase
    value.newPayloadRequest.executionPayload.transactions.size
  withdrawals : SliceDescriptorRep state (rootBase + 96) withdrawalsBase
    value.newPayloadRequest.executionPayload.withdrawals.size
  deposits : SliceDescriptorRep state (rootBase + 608) depositsBase
    value.newPayloadRequest.executionRequests.deposits.size
  withdrawalRequests : SliceDescriptorRep state (rootBase + 624) withdrawalRequestsBase
    value.newPayloadRequest.executionRequests.withdrawals.size
  consolidationRequests : SliceDescriptorRep state (rootBase + 640) consolidationRequestsBase
    value.newPayloadRequest.executionRequests.consolidations.size
  witnessState : SliceDescriptorRep state (rootBase + 688) witnessStateBase value.witness.state.size
  witnessCodes : SliceDescriptorRep state (rootBase + 704) witnessCodesBase value.witness.codes.size
  witnessHeaders : SliceDescriptorRep state (rootBase + 720) witnessHeadersBase value.witness.headers.size
  publicKeys : SliceDescriptorRep state (rootBase + 816) publicKeysBase value.publicKeys.size

/-- Borrowed byte slices in `RawV4`, including every transaction and witness element. -/
structure RawV4InputSlicesRep (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : SszBridge.RawV4) (descriptors : RawV4DescriptorRep state rootBase value) : Prop where
  extraData : ∃ inputOffset sliceBase,
    InputSliceDescriptorRep state inputBase input (rootBase + 64) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.extraData
  blockAccessList : ∃ inputOffset sliceBase,
    InputSliceDescriptorRep state inputBase input (rootBase + 128) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.blockAccessList
  transactions : InputSliceDescriptorArrayRep state inputBase input descriptors.transactionsBase
    value.newPayloadRequest.executionPayload.transactions
  witnessState : InputSliceDescriptorArrayRep state inputBase input descriptors.witnessStateBase value.witness.state
  witnessCodes : InputSliceDescriptorArrayRep state inputBase input descriptors.witnessCodesBase value.witness.codes
  witnessHeaders : InputSliceDescriptorArrayRep state inputBase input descriptors.witnessHeadersBase
    value.witness.headers

/-- Native `RawV4` ownership representation: root allocation, all heap arrays, and borrowed slices.

Scalar and fixed-vector byte contents are added by the later field observer; this layer establishes
the ownership and aliasing boundary used by all parser and runtime contracts. -/
structure RawV4Rep (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : SszBridge.RawV4) : Prop where
  allocations : RawV4AllocationRep state rootBase value
  descriptors : RawV4DescriptorRep state rootBase value
  inputSlices : RawV4InputSlicesRep state inputBase input rootBase value descriptors

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
  pure { versionedHashes, transactions, withdrawals, deposits, withdrawalRequests,
    consolidationRequests, witnessState, witnessCodes, witnessHeaders, publicKeys }

theorem observe_raw_v4_descriptors_of_rep (state : State) (rootBase : Nat) (value : SszBridge.RawV4)
    (representation : RawV4DescriptorRep state rootBase value) :
    observeRawV4Descriptors? state rootBase = some
      { versionedHashes := (representation.versionedHashesBase, value.newPayloadRequest.versionedHashes.size),
        transactions := (representation.transactionsBase,
          value.newPayloadRequest.executionPayload.transactions.size),
        withdrawals := (representation.withdrawalsBase,
          value.newPayloadRequest.executionPayload.withdrawals.size),
        deposits := (representation.depositsBase, value.newPayloadRequest.executionRequests.deposits.size),
        withdrawalRequests := (representation.withdrawalRequestsBase,
          value.newPayloadRequest.executionRequests.withdrawals.size),
        consolidationRequests := (representation.consolidationRequestsBase,
          value.newPayloadRequest.executionRequests.consolidations.size),
        witnessState := (representation.witnessStateBase, value.witness.state.size),
        witnessCodes := (representation.witnessCodesBase, value.witness.codes.size),
        witnessHeaders := (representation.witnessHeadersBase, value.witness.headers.size),
        publicKeys := (representation.publicKeysBase, value.publicKeys.size) } := by
  unfold observeRawV4Descriptors?
  rw [observe_slice_descriptor_of_rep state (rootBase + 592) representation.versionedHashes,
    observe_slice_descriptor_of_rep state (rootBase + 80) representation.transactions,
    observe_slice_descriptor_of_rep state (rootBase + 96) representation.withdrawals,
    observe_slice_descriptor_of_rep state (rootBase + 608) representation.deposits,
    observe_slice_descriptor_of_rep state (rootBase + 624) representation.withdrawalRequests,
    observe_slice_descriptor_of_rep state (rootBase + 640) representation.consolidationRequests,
    observe_slice_descriptor_of_rep state (rootBase + 688) representation.witnessState,
    observe_slice_descriptor_of_rep state (rootBase + 704) representation.witnessCodes,
    observe_slice_descriptor_of_rep state (rootBase + 720) representation.witnessHeaders,
    observe_slice_descriptor_of_rep state (rootBase + 816) representation.publicKeys]
  rfl

end BinaryFv.SSZ.Zesu.Execution
