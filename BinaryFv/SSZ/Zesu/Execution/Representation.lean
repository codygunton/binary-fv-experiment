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

/-- A heap array is a disjoint materialized sequence of fixed-width records. -/
def HeapArrayRep (state : State) (base count elementSize : Nat) : Prop :=
  base + count * elementSize ≤ 2 ^ 64 ∧
    ∀ index, index < count * elementSize → (state.mem.get? (base + index)).isSome

/-- A concrete little-endian RV64 word in Sail sparse memory. -/
def Word64LERep (state : State) (base value : Nat) : Prop :=
  ∀ index, index < 8 →
    state.mem.get? (base + index) = some (BitVec.ofNat 8 ((value / 256 ^ index) % 256))

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

end BinaryFv.SSZ.Zesu.Execution
