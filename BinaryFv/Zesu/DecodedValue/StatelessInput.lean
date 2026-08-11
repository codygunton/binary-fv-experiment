import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Logic.SepLogic
import BinaryFv.RiscV.Logic.LoadedImage
import BinaryFv.Zesu.Artifacts.AbiManifest
import BinaryFv.Specs.SSZ.AmsterdamV4

namespace BinaryFv.Zesu.DecodedValue

open BinaryFv.RiscV

/-- Byte-for-byte relocation of a half-open memory window. Keeping the source and destination
explicit lets representation theorems move values without unfolding their ABI layouts. -/
def ByteWindowRelocation (before after : State) (source destination width : Nat) : Prop :=
  ∀ index, index < width →
    after.mem.get? (destination + index) = before.mem.get? (source + index)

namespace ByteWindowRelocation

/-- Restrict a relocation to a sub-window. ABI offsets are supplied once at the use site instead of
being re-derived inside every representation proof. -/
theorem atOffset {before after : State} {source destination total : Nat}
    (memory : ByteWindowRelocation before after source destination total)
    (offset width : Nat) (fits : offset + width ≤ total) :
    ByteWindowRelocation before after (source + offset) (destination + offset) width := by
  intro index bound
  simpa [Nat.add_assoc] using memory (offset + index) (by omega)

/-- Transport any pointwise byte predicate through a relocated window. -/
theorem transport {before after : State} {source destination width : Nat}
    {expected : ∀ index, index < width → BitVec 8}
    (memory : ByteWindowRelocation before after source destination width)
    (representation : ∀ index (h : index < width),
      before.mem.get? (source + index) = some (expected index h)) :
    ∀ index (h : index < width),
      after.mem.get? (destination + index) = some (expected index h) := by
  intro index bound
  rw [memory index bound]
  exact representation index bound

end ByteWindowRelocation

/-- A half-open, bytewise region of generated Sail sparse memory. -/
def MemoryBytes (state : State) (base : Nat) (bytes : ByteArray) : Prop :=
  ∀ index (h : index < bytes.size),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (bytes[index]'h).toNat)

/-- Two equal byte snapshots give a bytewise relocation from one memory interval to another. -/
theorem MemoryBytes.rebase {before after : State} {source destination : Nat} {bytes : ByteArray}
    (sourceBytes : MemoryBytes before source bytes)
    (destinationBytes : MemoryBytes after destination bytes) :
    ByteWindowRelocation before after source destination bytes.size := by
  intro index bound
  rw [destinationBytes index bound, sourceBytes index bound]

/-- Transport a byte representation when memory agrees throughout the represented interval. -/
theorem MemoryBytes.of_mem_eq {before after : State} {base : Nat} {bytes : ByteArray}
    (representation : MemoryBytes before base bytes)
    (memory : ∀ index, index < bytes.size →
      after.mem.get? (base + index) = before.mem.get? (base + index)) :
    MemoryBytes after base bytes := by
  intro index bound
  rw [memory index bound]
  exact representation index bound

/-- An inline fixed-size specification byte vector in native sparse memory. -/
def FixedByteVectorRep {length : Nat} (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawByteVector length) : Prop :=
  ∀ index (h : index < length),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 (value[index].toNat))

/-- Rebase a fixed byte vector along a bytewise relocation. -/
theorem FixedByteVectorRep.rebase {length : Nat} {before after : State} {source destination : Nat}
    {value : BinaryFv.Specs.SSZ.RawByteVector length}
    (memory : ByteWindowRelocation before after source destination length)
    (representation : FixedByteVectorRep before source value) :
    FixedByteVectorRep after destination value :=
  ByteWindowRelocation.transport memory representation

/-- Inline little-endian bytes for an SSZ integer represented as a Lean bit vector. -/
def BitVectorLERep {width : Nat} (state : State) (base : Nat) (value : BitVec width) : Prop :=
  ∀ index (h : index < width / 8),
    state.mem.get? (base + index) = some (BitVec.ofNat 8 ((value.toNat / 256 ^ index) % 256))

/-- A byte represented by `BitVectorLERep` is the corresponding byte in Sail's little-endian
encoding.  Machine load proofs consume this form directly. -/
theorem BitVectorLERep.leBytes {n : Nat} {state : State} {base : Nat} {value : BitVec (8 * n)}
    (representation : BitVectorLERep state base value) (index : Nat) (bound : index < n) :
    state.mem.get? (base + index) =
      some (getElem (BinaryFv.RiscV.Sep.leBytes n value) index (by
        simpa only [BinaryFv.RiscV.Sep.leBytes_length] using bound)) := by
  rw [representation index (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BinaryFv.RiscV.Sep.leBytes, Nat.shiftRight_eq_div_pow]
  rw [show 256 = 2 ^ 8 by decide, ← Nat.pow_mul]

/-- Rebase an inline little-endian bit vector along a bytewise relocation. -/
theorem BitVectorLERep.rebase {width : Nat} {before after : State} {source destination : Nat}
    {value : BitVec width}
    (memory : ByteWindowRelocation before after source destination (width / 8))
    (representation : BitVectorLERep before source value) :
    BitVectorLERep after destination value :=
  ByteWindowRelocation.transport memory representation

/-- A decoder slice that aliases caller-owned input rather than copying it into the heap. -/
def InputSliceRep (state : State) (inputBase inputOffset length sliceBase : Nat) : Prop :=
  sliceBase = inputBase + inputOffset ∧
    ∀ index, index < length → state.mem.get? (sliceBase + index) = state.mem.get? (inputBase + inputOffset + index)

/-- An input-slice alias is independent of the state once its address equality is known. -/
theorem InputSliceRep.rebase {before after : State} {inputBase inputOffset length sliceBase : Nat}
    (representation : InputSliceRep before inputBase inputOffset length sliceBase) :
    InputSliceRep after inputBase inputOffset length sliceBase := by
  refine ⟨representation.1, fun index bound => ?_⟩
  rw [representation.1]

/-- A specification byte array is exactly a bounded subrange of the caller-provided input. -/
def InputBytesAt (input : ByteArray) (inputOffset : Nat) (bytes : Array UInt8) : Prop :=
  ∀ index (h : index < bytes.size),
    ∃ hinput : inputOffset + index < input.size,
      bytes[index] = input[inputOffset + index]'hinput

/-- Reindex a byte slice from an extracted input suffix to its original input. -/
theorem InputBytesAt.reindex_extract_suffix {input : ByteArray} {start inputOffset : Nat}
    {bytes : Array UInt8}
    (representation : InputBytesAt (input.extract start input.size) inputOffset bytes) :
    InputBytesAt input (start + inputOffset) bytes := by
  intro index indexBound
  obtain ⟨tailBound, byte⟩ := representation index indexBound
  have inputBound : start + (inputOffset + index) < input.size := by
    rw [ByteArray.size_extract] at tailBound
    omega
  refine ⟨by simpa [Nat.add_assoc] using inputBound, ?_⟩
  calc
    bytes[index] = (input.extract start input.size)[inputOffset + index] := byte
    _ = input[start + (inputOffset + index)] := by
      rw [ByteArray.getElem_extract tailBound]
    _ = input[start + inputOffset + index] := by simp [Nat.add_assoc]

/-- Reindex a machine input-slice alias from an extracted suffix to its original input. -/
theorem InputSliceRep.reindex_extract_suffix {state : State} {inputBase start inputOffset length sliceBase : Nat}
    (representation : InputSliceRep state (inputBase + start) inputOffset length sliceBase) :
    InputSliceRep state inputBase (start + inputOffset) length sliceBase := by
  refine ⟨by simpa [Nat.add_assoc] using representation.1, ?_⟩
  intro index indexBound
  simpa [Nat.add_assoc] using representation.2 index indexBound

/-- A heap array is a disjoint materialized sequence of fixed-width records. -/
def HeapArrayRep (state : State) (base count elementSize : Nat) : Prop :=
  base + count * elementSize ≤ 2 ^ 64 ∧
    ∀ index, index < count * elementSize → (state.mem.get? (base + index)).isSome

/-- Rebase an allocated byte interval along a bytewise relocation. -/
theorem HeapArrayRep.rebase {before after : State} {source destination count elementSize : Nat}
    (destinationFits : destination + count * elementSize ≤ 2 ^ 64)
    (memory : ByteWindowRelocation before after source destination (count * elementSize))
    (representation : HeapArrayRep before source count elementSize) :
    HeapArrayRep after destination count elementSize := by
  refine ⟨destinationFits, fun index bound => ?_⟩
  rw [memory index bound]
  exact representation.2 index bound

/-- A heap array whose elements are inline fixed-width specification byte vectors. -/
def HeapFixedVectorArrayRep {length : Nat} (state : State) (base : Nat)
    (values : Array (BinaryFv.Specs.SSZ.RawByteVector length)) : Prop :=
  ∀ index (h : index < values.size),
    FixedByteVectorRep state (base + length * index) values[index]

/-- The one-byte discriminant of a Zig non-pointer optional: `1` when present, `0` when absent. -/
def OptionTagRep (state : State) (base : Nat) (present : Bool) : Prop :=
  state.mem.get? base = some (BitVec.ofNat 8 (if present then 1 else 0))

/-- Rebase an option discriminant along a bytewise relocation. -/
theorem OptionTagRep.rebase {before after : State} {source destination : Nat} {present : Bool}
    (memory : ByteWindowRelocation before after source destination 1)
    (representation : OptionTagRep before source present) : OptionTagRep after destination present := by
  unfold OptionTagRep at representation ⊢
  simpa using (memory 0 (by omega)).trans representation

/-- A concrete little-endian RV64 word in Sail sparse memory. -/
def Word64LERep (state : State) (base value : Nat) : Prop :=
  ∀ index, index < 8 →
    state.mem.get? (base + index) = some (BitVec.ofNat 8 ((value / 256 ^ index) % 256))

/-- Rebase a little-endian word along a bytewise relocation. -/
theorem Word64LERep.rebase {before after : State} {source destination value : Nat}
    (memory : ByteWindowRelocation before after source destination 8)
    (representation : Word64LERep before source value) : Word64LERep after destination value :=
  ByteWindowRelocation.transport memory representation

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

/-- Native RV64 layout of one specification withdrawal record. -/
def RawWithdrawalRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawWithdrawal) : Prop :=
  Word64LERep state base value.index.toNat ∧
    Word64LERep state (base + 8) value.validatorIndex.toNat ∧
      Word64LERep state (base + 16) value.amount.toNat ∧
        FixedByteVectorRep state (base + 24) value.address

def HeapWithdrawalArrayRep (state : State) (base : Nat)
    (values : Array BinaryFv.Specs.SSZ.RawWithdrawal) : Prop :=
  ∀ index (h : index < values.size), RawWithdrawalRep state (base + 48 * index) values[index]

/-- Native RV64 layout of one specification withdrawal-request record. -/
def RawWithdrawalRequestRep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawWithdrawalRequest) : Prop :=
  Word64LERep state base value.amount.toNat ∧
    FixedByteVectorRep state (base + 8) value.sourceAddress ∧
      FixedByteVectorRep state (base + 28) value.validatorPubkey

def HeapWithdrawalRequestArrayRep (state : State) (base : Nat)
    (values : Array BinaryFv.Specs.SSZ.RawWithdrawalRequest) : Prop :=
  ∀ index (h : index < values.size),
    RawWithdrawalRequestRep state (base + 80 * index) values[index]

/-- Native RV64 layout of one specification consolidation-request record. -/
def RawConsolidationRequestRep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawConsolidationRequest) : Prop :=
  FixedByteVectorRep state base value.sourceAddress ∧
    FixedByteVectorRep state (base + 20) value.sourcePubkey ∧
      FixedByteVectorRep state (base + 68) value.targetPubkey

def HeapConsolidationRequestArrayRep (state : State) (base : Nat)
    (values : Array BinaryFv.Specs.SSZ.RawConsolidationRequest) : Prop :=
  ∀ index (h : index < values.size),
    RawConsolidationRequestRep state (base + 116 * index) values[index]

/-- Native RV64 layout of one specification deposit-request record. -/
def RawDepositRequestRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawDepositRequest) : Prop :=
  Word64LERep state base value.amount.toNat ∧
    Word64LERep state (base + 8) value.index.toNat ∧
      FixedByteVectorRep state (base + 16) value.pubkey ∧
        FixedByteVectorRep state (base + 64) value.withdrawalCredentials ∧
          FixedByteVectorRep state (base + 96) value.signature

def HeapDepositRequestArrayRep (state : State) (base : Nat)
    (values : Array BinaryFv.Specs.SSZ.RawDepositRequest) : Prop :=
  ∀ index (h : index < values.size), RawDepositRequestRep state (base + 192 * index) values[index]

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

/-- Rebase a 16-byte RV64 slice descriptor along a bytewise relocation. -/
theorem SliceDescriptorRep.rebase {before after : State} {source destination data count : Nat}
    (memory : ByteWindowRelocation before after source destination 16)
    (representation : SliceDescriptorRep before source data count) :
    SliceDescriptorRep after destination data count := by
  refine ⟨representation.1, representation.2.1, ?_, ?_⟩
  · exact representation.2.2.1.rebase (ByteWindowRelocation.atOffset memory 0 8 (by omega))
  · exact representation.2.2.2.rebase (ByteWindowRelocation.atOffset memory 8 8 (by omega))

/-- A slice descriptor aliases an exact specification byte array in the caller's input memory. -/
def InputSliceDescriptorRep (state : State) (inputBase : Nat) (input : ByteArray) (descriptorBase : Nat)
    (inputOffset sliceBase : Nat) (bytes : Array UInt8) : Prop :=
  SliceDescriptorRep state descriptorBase sliceBase bytes.size ∧
    InputSliceRep state inputBase inputOffset bytes.size sliceBase ∧ InputBytesAt input inputOffset bytes

/-- Rebase an input-slice descriptor along its 16-byte descriptor record. -/
theorem InputSliceDescriptorRep.rebase {before after : State} {inputBase descriptorSource descriptorDestination : Nat}
    {input : ByteArray} {inputOffset sliceBase : Nat} {bytes : Array UInt8}
    (memory : ByteWindowRelocation before after descriptorSource descriptorDestination 16)
    (representation : InputSliceDescriptorRep before inputBase input descriptorSource inputOffset sliceBase bytes) :
    InputSliceDescriptorRep after inputBase input descriptorDestination inputOffset sliceBase bytes := by
  refine ⟨representation.1.rebase memory, representation.2.1.rebase, representation.2.2⟩

/-- Reindex a descriptor's borrowed slice from an extracted suffix to its original input. -/
theorem InputSliceDescriptorRep.reindex_extract_suffix {state : State}
    {inputBase start descriptorBase inputOffset sliceBase : Nat} {input : ByteArray} {bytes : Array UInt8}
    (representation : InputSliceDescriptorRep state (inputBase + start) (input.extract start input.size)
      descriptorBase inputOffset sliceBase bytes) :
    InputSliceDescriptorRep state inputBase input descriptorBase (start + inputOffset) sliceBase bytes := by
  exact ⟨representation.1, representation.2.1.reindex_extract_suffix,
    representation.2.2.reindex_extract_suffix⟩

def InputSliceDescriptorArrayRep (state : State) (inputBase : Nat) (input : ByteArray)
    (descriptorBase : Nat) (slices : Array (Array UInt8)) : Prop :=
  ∀ index (h : index < slices.size),
    ∃ inputOffset sliceBase,
      InputSliceDescriptorRep state inputBase input (descriptorBase + 16 * index) inputOffset sliceBase
        slices[index]

/-- Preserve an array of input-slice descriptors when its descriptor bytes agree. -/
theorem InputSliceDescriptorArrayRep.of_mem_eq {before after : State} {inputBase descriptorBase : Nat}
    {input : ByteArray} {slices : Array (Array UInt8)}
    (memory : ∀ index, index < slices.size * 16 →
      after.mem.get? (descriptorBase + index) = before.mem.get? (descriptorBase + index))
    (representation : InputSliceDescriptorArrayRep before inputBase input descriptorBase slices) :
    InputSliceDescriptorArrayRep after inputBase input descriptorBase slices := by
  intro index bound
  obtain ⟨inputOffset, sliceBase, descriptor⟩ := representation index bound
  refine ⟨inputOffset, sliceBase, descriptor.rebase ?_⟩
  intro offset offsetBound
  have shifted := memory (16 * index + offset) (by omega)
  simpa [Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using shifted

/-- Reindex every borrowed descriptor slice from an extracted suffix to its original input. -/
theorem InputSliceDescriptorArrayRep.reindex_extract_suffix {state : State}
    {inputBase start descriptorBase : Nat} {input : ByteArray} {slices : Array (Array UInt8)}
    (representation : InputSliceDescriptorArrayRep state (inputBase + start)
      (input.extract start input.size) descriptorBase slices) :
    InputSliceDescriptorArrayRep state inputBase input descriptorBase slices := by
  intro index indexBound
  obtain ⟨inputOffset, sliceBase, descriptor⟩ := representation index indexBound
  exact ⟨start + inputOffset, sliceBase, descriptor.reindex_extract_suffix⟩

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
  ∃ size, Artifacts.rawStatelessInputSize = some size ∧ HeapArrayRep state base 1 size

/-- A complete byte snapshot at a bounded destination establishes the native root allocation. -/
theorem rawStatelessInputRep_of_memoryBytes {state : State} {base : Nat} {bytes : ByteArray}
    (bytesSize : bytes.size = 832) (baseFits : base + 832 ≤ 2 ^ 64)
    (memory : MemoryBytes state base bytes) : RawStatelessInputRep state base := by
  refine ⟨832, Artifacts.raw_stateless_input_layout.1, ⟨baseFits, ?_⟩⟩
  intro index bound
  have byte := memory index (by simpa [bytesSize] using bound)
  rw [byte]
  exact Option.isSome_some

theorem raw_stateless_input_rep_size (state : State) (base : Nat)
    (representation : RawStatelessInputRep state base) : HeapArrayRep state base 1 832 := by
  rcases representation with ⟨size, sizeH, representation⟩
  rw [Artifacts.raw_stateless_input_layout.1] at sizeH
  injection sizeH with sizeH
  subst size
  exact representation

/-- Heap bases carried by the root's ten slice descriptors. -/
structure StatelessInputDescriptorBases where
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

/-- Heap-allocation portion of the native representation of a complete specification `StatelessInput` value.

Fixed records are sized from the pinned RV64 ABI manifest. The eventual observer additionally
connects these bases to the corresponding slice descriptors stored in the root object. -/
structure StatelessInputAllocationRep (state : State) (rootBase : Nat) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (bases : StatelessInputDescriptorBases) : Prop where
  root : RawStatelessInputRep state rootBase
  versionedHashes : HeapArrayRep state bases.versionedHashesBase
    value.newPayloadRequest.versionedHashes.size 32
  versionedHashContents : HeapFixedVectorArrayRep state bases.versionedHashesBase
    value.newPayloadRequest.versionedHashes
  transactions : HeapArrayRep state bases.transactionsBase
    value.newPayloadRequest.executionPayload.transactions.size 16
  withdrawals : HeapArrayRep state bases.withdrawalsBase
    value.newPayloadRequest.executionPayload.withdrawals.size 48
  withdrawalContents : HeapWithdrawalArrayRep state bases.withdrawalsBase
    value.newPayloadRequest.executionPayload.withdrawals
  deposits : HeapArrayRep state bases.depositsBase
    value.newPayloadRequest.executionRequests.deposits.size 192
  depositContents : HeapDepositRequestArrayRep state bases.depositsBase
    value.newPayloadRequest.executionRequests.deposits
  withdrawalRequests : HeapArrayRep state bases.withdrawalRequestsBase
    value.newPayloadRequest.executionRequests.withdrawals.size 80
  withdrawalRequestContents : HeapWithdrawalRequestArrayRep state bases.withdrawalRequestsBase
    value.newPayloadRequest.executionRequests.withdrawals
  consolidationRequests : HeapArrayRep state bases.consolidationRequestsBase
    value.newPayloadRequest.executionRequests.consolidations.size 116
  consolidationRequestContents : HeapConsolidationRequestArrayRep state bases.consolidationRequestsBase
    value.newPayloadRequest.executionRequests.consolidations
  witnessState : HeapArrayRep state bases.witnessStateBase value.witness.state.size 16
  witnessCodes : HeapArrayRep state bases.witnessCodesBase value.witness.codes.size 16
  witnessHeaders : HeapArrayRep state bases.witnessHeadersBase value.witness.headers.size 16
  publicKeys : HeapArrayRep state bases.publicKeysBase value.publicKeys.size 65
  publicKeyContents : HeapFixedVectorArrayRep state bases.publicKeysBase value.publicKeys

theorem stateless_input_allocation_root_size (state : State) (rootBase : Nat) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (bases : StatelessInputDescriptorBases)
    (representation : StatelessInputAllocationRep state rootBase value bases) : HeapArrayRep state rootBase 1 832 :=
  raw_stateless_input_rep_size state rootBase representation.root

/-- Descriptor-level portion of the root layout, with every collection count tied to `StatelessInput`. -/
structure StatelessInputDescriptorRep (state : State) (rootBase : Nat) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (bases : StatelessInputDescriptorBases) : Prop where
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

/-- Borrowed byte slices in `StatelessInput`, including every transaction and witness element. -/
structure StatelessInputInputSlicesRep (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (bases : StatelessInputDescriptorBases)
    (descriptors : StatelessInputDescriptorRep state rootBase value bases) : Prop where
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

/-- Reindex all caller-borrowed `StatelessInput` slices from an extracted suffix to the original input. -/
theorem StatelessInputInputSlicesRep.reindex_extract_suffix {state : State}
    {inputBase start rootBase : Nat} {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    {bases : StatelessInputDescriptorBases}
    {descriptors : StatelessInputDescriptorRep state rootBase value bases}
    (representation : StatelessInputInputSlicesRep state (inputBase + start)
      (input.extract start input.size) rootBase value bases descriptors) :
    StatelessInputInputSlicesRep state inputBase input rootBase value bases descriptors :=
  { extraData := by
      obtain ⟨inputOffset, sliceBase, descriptor⟩ := representation.extraData
      exact ⟨start + inputOffset, sliceBase, descriptor.reindex_extract_suffix⟩
    blockAccessList := by
      obtain ⟨inputOffset, sliceBase, descriptor⟩ := representation.blockAccessList
      exact ⟨start + inputOffset, sliceBase, descriptor.reindex_extract_suffix⟩
    transactions := representation.transactions.reindex_extract_suffix
    witnessState := representation.witnessState.reindex_extract_suffix
    witnessCodes := representation.witnessCodes.reindex_extract_suffix
    witnessHeaders := representation.witnessHeaders.reindex_extract_suffix }

/-! ## The chain-config representation

These six predicates were moved here unchanged from `Containers.lean` (which imports this file) so
that `StatelessInputFixedFieldsRep` below can state the root's chain config with `ChainConfigRep` instead of
pinning only two of its words. Every existing use in `Containers.lean` still resolves. -/

/-- A `?u64` (16 bytes): the `u64` payload at offset 0 and the discriminant byte at offset 8. When
absent, only the discriminant is constrained; the payload bytes are undefined. -/
def OptionU64Rep (state : State) (base : Nat) (value : Option UInt64) : Prop :=
  match value with
  | some v => Word64LERep state base v.toNat ∧ OptionTagRep state (base + 8) true
  | none => OptionTagRep state (base + 8) false

/-- A `RawBlobSchedule` (24 bytes): three consecutive little-endian `u64` fields. -/
def BlobScheduleRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawBlobSchedule) : Prop :=
  Word64LERep state base value.target.toNat ∧
    Word64LERep state (base + 8) value.max.toNat ∧
      Word64LERep state (base + 16) value.baseFeeUpdateFraction.toNat

/-- A `?RawBlobSchedule` (32 bytes): the 24-byte payload at offset 0 and the discriminant at 24. -/
def OptionBlobScheduleRep (state : State) (base : Nat) (value : Option BinaryFv.Specs.SSZ.RawBlobSchedule) :
    Prop :=
  match value with
  | some v => BlobScheduleRep state base v ∧ OptionTagRep state (base + 24) true
  | none => OptionTagRep state (base + 24) false

/-- `RawForkActivation` (32 bytes): `block_number : ?u64` at 0, `timestamp : ?u64` at 16. -/
def ForkActivationRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawForkActivation) : Prop :=
  OptionU64Rep state base value.blockNumber ∧ OptionU64Rep state (base + 16) value.timestamp

/-- `RawForkConfig` (72 bytes): `fork : u64` at 0, `activation` at 8, `blob_schedule : ?…` at 40. -/
def ForkConfigRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawForkConfig) : Prop :=
  Word64LERep state base value.fork.toNat ∧
    ForkActivationRep state (base + 8) value.activation ∧
      OptionBlobScheduleRep state (base + 40) value.blobSchedule

/-- `RawChainConfig` (80 bytes): `chain_id : u64` at 0, `active_fork` at 8. -/
def ChainConfigRep (state : State) (base : Nat) (value : BinaryFv.Specs.SSZ.RawChainConfig) : Prop :=
  Word64LERep state base value.chainId.toNat ∧ ForkConfigRep state (base + 8) value.activeFork

/-- Rebase an optional `u64` ABI object along its 16-byte record interval. -/
theorem OptionU64Rep.rebase {before after : State} {source destination : Nat} {value : Option UInt64}
    (memory : ByteWindowRelocation before after source destination 16)
    (representation : OptionU64Rep before source value) : OptionU64Rep after destination value := by
  cases value with
  | none =>
      exact OptionTagRep.rebase (ByteWindowRelocation.atOffset memory 8 1 (by omega))
        (by simpa [OptionU64Rep] using representation)
  | some value =>
      refine ⟨representation.1.rebase ?_, representation.2.rebase ?_⟩
      · exact ByteWindowRelocation.atOffset memory 0 8 (by omega)
      · exact ByteWindowRelocation.atOffset memory 8 1 (by omega)

/-- Rebase a `RawBlobSchedule` along its 24-byte ABI record interval. -/
theorem BlobScheduleRep.rebase {before after : State} {source destination : Nat}
    {value : BinaryFv.Specs.SSZ.RawBlobSchedule}
    (memory : ByteWindowRelocation before after source destination 24)
    (representation : BlobScheduleRep before source value) : BlobScheduleRep after destination value := by
  refine ⟨representation.1.rebase ?_, representation.2.1.rebase ?_, representation.2.2.rebase ?_⟩
  · exact ByteWindowRelocation.atOffset memory 0 8 (by omega)
  · exact ByteWindowRelocation.atOffset memory 8 8 (by omega)
  · exact ByteWindowRelocation.atOffset memory 16 8 (by omega)

/-- Rebase an optional blob-schedule ABI object along its 32-byte record interval. -/
theorem OptionBlobScheduleRep.rebase {before after : State} {source destination : Nat}
    {value : Option BinaryFv.Specs.SSZ.RawBlobSchedule}
    (memory : ByteWindowRelocation before after source destination 32)
    (representation : OptionBlobScheduleRep before source value) :
    OptionBlobScheduleRep after destination value := by
  cases value with
  | none =>
      exact OptionTagRep.rebase (ByteWindowRelocation.atOffset memory 24 1 (by omega))
        (by simpa [OptionBlobScheduleRep] using representation)
  | some value =>
      refine ⟨representation.1.rebase ?_, representation.2.rebase ?_⟩
      · exact ByteWindowRelocation.atOffset memory 0 24 (by omega)
      · exact ByteWindowRelocation.atOffset memory 24 1 (by omega)

/-- Rebase a fork activation along its 32-byte ABI record interval. -/
theorem ForkActivationRep.rebase {before after : State} {source destination : Nat}
    {value : BinaryFv.Specs.SSZ.RawForkActivation}
    (memory : ByteWindowRelocation before after source destination 32)
    (representation : ForkActivationRep before source value) : ForkActivationRep after destination value := by
  refine ⟨representation.1.rebase ?_, representation.2.rebase ?_⟩
  · exact ByteWindowRelocation.atOffset memory 0 16 (by omega)
  · exact ByteWindowRelocation.atOffset memory 16 16 (by omega)

/-- Rebase a fork configuration along its 72-byte ABI record interval. -/
theorem ForkConfigRep.rebase {before after : State} {source destination : Nat}
    {value : BinaryFv.Specs.SSZ.RawForkConfig}
    (memory : ByteWindowRelocation before after source destination 72)
    (representation : ForkConfigRep before source value) : ForkConfigRep after destination value := by
  refine ⟨representation.1.rebase ?_, representation.2.1.rebase ?_, representation.2.2.rebase ?_⟩
  · exact ByteWindowRelocation.atOffset memory 0 8 (by omega)
  · exact ByteWindowRelocation.atOffset memory 8 32 (by omega)
  · exact ByteWindowRelocation.atOffset memory 40 32 (by omega)

/-- Rebase a chain configuration along its 80-byte ABI record interval. -/
theorem ChainConfigRep.rebase {before after : State} {source destination : Nat}
    {value : BinaryFv.Specs.SSZ.RawChainConfig}
    (memory : ByteWindowRelocation before after source destination 80)
    (representation : ChainConfigRep before source value) : ChainConfigRep after destination value := by
  refine ⟨representation.1.rebase ?_, representation.2.rebase ?_⟩
  · exact ByteWindowRelocation.atOffset memory 0 8 (by omega)
  · exact ByteWindowRelocation.atOffset memory 8 72 (by omega)

/-- Inline fixed vectors and scalar fields in the root's nested execution payload. -/
structure StatelessInputFixedFieldsRep (state : State) (rootBase : Nat) (value : BinaryFv.Specs.SSZ.StatelessInput) : Prop where
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
  /-- The complete chain config at `rootBase + 736`.

  This replaces two narrower clauses that pinned only `chainId` (at `+736`) and `activeFork.fork` (at
  `+744`). `ChainConfigRep` subsumes both verbatim as its first two components and additionally pins
  `activeFork.activation` at `[752, 784)` and `activeFork.blobSchedule` at `[784, 816)`, after which
  the `publicKeys` slice descriptor at `+816` ends exactly at the pinned 832-byte root size.

  The narrower version left `activation` and `blobSchedule` completely unconstrained, so a single
  state satisfied `StatelessInputRep` for values differing in those fields. That made any *total* value
  observer impossible: `StatelessInputRep → observeStatelessInput? = some value` would have forced two different values
  to be observed from one state. Strengthening here is what makes the observer well-posed. -/
  chainConfig : ChainConfigRep state (rootBase + 736) value.chainConfig

/-- **Regression for the observer under-determination fix.** The representation now pins the fork
activation and the optional blob schedule, at the exact offsets the pinned ABI gives them. Before the
`chainConfig` clause replaced the two narrower `chainId`/`activeFork.fork` clauses, neither of these
was constrained anywhere in `StatelessInputRep`, so one state represented values differing in those fields and
no total value observer could exist. If someone narrows the clause again, this fails. -/
theorem statelessInputFixedFields_pins_fork_activation_and_blob_schedule (state : State) (rootBase : Nat)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (representation : StatelessInputFixedFieldsRep state rootBase value) :
    ForkActivationRep state (rootBase + 752) value.chainConfig.activeFork.activation ∧
      OptionBlobScheduleRep state (rootBase + 784) value.chainConfig.activeFork.blobSchedule := by
  refine ⟨?_, ?_⟩
  · simpa [Nat.add_assoc] using representation.chainConfig.2.2.1
  · simpa [Nat.add_assoc] using representation.chainConfig.2.2.2

/-- The strengthened clause still gives back the two words the narrower version pinned, at the same
addresses — so the change is a strict strengthening and nothing downstream lost a fact. -/
theorem statelessInputFixedFields_still_pins_chain_id_and_fork (state : State) (rootBase : Nat)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (representation : StatelessInputFixedFieldsRep state rootBase value) :
    Word64LERep state (rootBase + 736) value.chainConfig.chainId.toNat ∧
      Word64LERep state (rootBase + 744) value.chainConfig.activeFork.fork.toNat := by
  refine ⟨representation.chainConfig.1, ?_⟩
  simpa [Nat.add_assoc] using representation.chainConfig.2.1

/-- Native `StatelessInput` ownership representation: root allocation, all heap arrays, and borrowed slices.

Scalar and fixed-vector byte contents are added by the later field observer; this layer establishes
the ownership and aliasing boundary used by all parser and runtime contracts. -/
structure StatelessInputRep (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : BinaryFv.Specs.SSZ.StatelessInput) : Prop where
  layout : ∃ bases : StatelessInputDescriptorBases,
    StatelessInputAllocationRep state rootBase value bases ∧
      ∃ descriptors : StatelessInputDescriptorRep state rootBase value bases,
        StatelessInputInputSlicesRep state inputBase input rootBase value bases descriptors
  fixedFields : StatelessInputFixedFieldsRep state rootBase value

/-- Rebase the ten root-resident slice descriptors through a complete copied root record. -/
theorem StatelessInputDescriptorRep.rebase {state : State} {sourceRoot destinationRoot : Nat}
    {value : BinaryFv.Specs.SSZ.StatelessInput} {bases : StatelessInputDescriptorBases}
    (memory : ByteWindowRelocation state state sourceRoot destinationRoot 832)
    (representation : StatelessInputDescriptorRep state sourceRoot value bases) :
    StatelessInputDescriptorRep state destinationRoot value bases := by
  have atOffset := ByteWindowRelocation.atOffset memory
  exact
    { versionedHashes := representation.versionedHashes.rebase (atOffset 592 16 (by omega))
      transactions := representation.transactions.rebase (atOffset 80 16 (by omega))
      withdrawals := representation.withdrawals.rebase (atOffset 96 16 (by omega))
      deposits := representation.deposits.rebase (atOffset 608 16 (by omega))
      withdrawalRequests := representation.withdrawalRequests.rebase (atOffset 624 16 (by omega))
      consolidationRequests := representation.consolidationRequests.rebase (atOffset 640 16 (by omega))
      witnessState := representation.witnessState.rebase (atOffset 688 16 (by omega))
      witnessCodes := representation.witnessCodes.rebase (atOffset 704 16 (by omega))
      witnessHeaders := representation.witnessHeaders.rebase (atOffset 720 16 (by omega))
      publicKeys := representation.publicKeys.rebase (atOffset 816 16 (by omega)) }

/-- Rebase every scalar and fixed field in the 832-byte root record. -/
theorem StatelessInputFixedFieldsRep.rebase {state : State} {sourceRoot destinationRoot : Nat}
    {value : BinaryFv.Specs.SSZ.StatelessInput}
    (memory : ByteWindowRelocation state state sourceRoot destinationRoot 832)
    (representation : StatelessInputFixedFieldsRep state sourceRoot value) :
    StatelessInputFixedFieldsRep state destinationRoot value := by
  have atOffset := ByteWindowRelocation.atOffset memory
  exact
    { baseFeePerGas := representation.baseFeePerGas.rebase (atOffset 0 32 (by omega))
      parentHash := representation.parentHash.rebase (atOffset 152 32 (by omega))
      feeRecipient := representation.feeRecipient.rebase (atOffset 184 20 (by omega))
      stateRoot := representation.stateRoot.rebase (atOffset 204 32 (by omega))
      receiptsRoot := representation.receiptsRoot.rebase (atOffset 236 32 (by omega))
      logsBloom := representation.logsBloom.rebase (atOffset 268 256 (by omega))
      prevRandao := representation.prevRandao.rebase (atOffset 524 32 (by omega))
      blockHash := representation.blockHash.rebase (atOffset 556 32 (by omega))
      parentBeaconBlockRoot := representation.parentBeaconBlockRoot.rebase (atOffset 656 32 (by omega))
      blockNumber := representation.blockNumber.rebase (atOffset 32 8 (by omega))
      gasLimit := representation.gasLimit.rebase (atOffset 40 8 (by omega))
      gasUsed := representation.gasUsed.rebase (atOffset 48 8 (by omega))
      timestamp := representation.timestamp.rebase (atOffset 56 8 (by omega))
      blobGasUsed := representation.blobGasUsed.rebase (atOffset 112 8 (by omega))
      excessBlobGas := representation.excessBlobGas.rebase (atOffset 120 8 (by omega))
      slotNumber := representation.slotNumber.rebase (atOffset 144 8 (by omega))
      chainConfig := representation.chainConfig.rebase (atOffset 736 80 (by omega)) }

/-- Rebase the two root-resident input descriptors while retaining the four descriptor arrays at
their existing heap bases. -/
theorem StatelessInputInputSlicesRep.rebase {state : State} {inputBase sourceRoot destinationRoot : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput} {bases : StatelessInputDescriptorBases}
    {sourceDescriptors : StatelessInputDescriptorRep state sourceRoot value bases}
    {destinationDescriptors : StatelessInputDescriptorRep state destinationRoot value bases}
    (memory : ByteWindowRelocation state state sourceRoot destinationRoot 832)
    (representation : StatelessInputInputSlicesRep state inputBase input sourceRoot value bases sourceDescriptors) :
    StatelessInputInputSlicesRep state inputBase input destinationRoot value bases destinationDescriptors := by
  have atOffset (offset : Nat) (fits : offset + 16 ≤ 832) :=
    ByteWindowRelocation.atOffset memory offset 16 fits
  rcases representation.extraData with ⟨extraOffset, extraBase, extraData⟩
  rcases representation.blockAccessList with ⟨accessOffset, accessBase, accessList⟩
  exact
    { extraData := ⟨extraOffset, extraBase, extraData.rebase (atOffset 64 (by omega))⟩
      blockAccessList := ⟨accessOffset, accessBase, accessList.rebase (atOffset 128 (by omega))⟩
      transactions := representation.transactions
      witnessState := representation.witnessState
      witnessCodes := representation.witnessCodes
      witnessHeaders := representation.witnessHeaders }

/-- Move a complete `StatelessInputRep` to a new root after copying all 832 root bytes. The ten
allocator-chosen arrays remain at their descriptor-selected bases; their preservation is supplied by
the caller before invoking this root-only relocation. -/
theorem StatelessInputRep.rebase_root {state : State} {inputBase sourceRoot destinationRoot : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    (destinationFits : destinationRoot + 832 ≤ 2 ^ 64)
    (memory : ByteWindowRelocation state state sourceRoot destinationRoot 832)
    (representation : StatelessInputRep state inputBase input sourceRoot value) :
    StatelessInputRep state inputBase input destinationRoot value := by
  obtain ⟨bases, allocation, descriptors, slices⟩ := representation.layout
  obtain ⟨size, sizeEq, root⟩ := allocation.root
  have size832 : size = 832 := by
    rw [Artifacts.raw_stateless_input_layout.1] at sizeEq
    exact (Option.some.inj sizeEq).symm
  have destinationRoot : RawStatelessInputRep state destinationRoot := by
    refine ⟨size, sizeEq, root.rebase ?_ ?_⟩
    · simpa [size832] using destinationFits
    · intro index bound
      simpa [size832] using memory index (by simpa [size832] using bound)
  have destinationDescriptors := descriptors.rebase memory
  refine
    { layout := ⟨bases, { allocation with root := destinationRoot }, destinationDescriptors, ?_⟩
      fixedFields := representation.fixedFields.rebase memory }
  exact slices.rebase memory

/-- The executable descriptor-only observation of the native root object. -/
structure StatelessInputDescriptorObservation where
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

def observeStatelessInputDescriptors? (state : State) (rootBase : Nat) : Option StatelessInputDescriptorObservation := do
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

theorem observe_stateless_input_descriptors_of_rep (state : State) (rootBase : Nat) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (bases : StatelessInputDescriptorBases)
    (representation : StatelessInputDescriptorRep state rootBase value bases) :
    observeStatelessInputDescriptors? state rootBase = some
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
  unfold observeStatelessInputDescriptors?
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

end BinaryFv.Zesu.DecodedValue
