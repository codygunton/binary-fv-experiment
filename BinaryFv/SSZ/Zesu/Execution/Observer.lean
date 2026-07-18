import BinaryFv.SSZ.Zesu.Execution.Representation

namespace BinaryFv.SSZ.Zesu.Execution

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
    ∃ inputOffset sliceBase,
      observeBytes? state sliceBase value.newPayloadRequest.executionPayload.extraData.size =
        some value.newPayloadRequest.executionPayload.extraData.toList := by
  rcases representation.inputSlices.extraData with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input (rootBase + 64) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.extraData inputMemory sliceRepresentation⟩

theorem raw_v4_block_access_list_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) :
    ∃ inputOffset sliceBase,
      observeBytes? state sliceBase value.newPayloadRequest.executionPayload.blockAccessList.size =
        some value.newPayloadRequest.executionPayload.blockAccessList.toList := by
  rcases representation.inputSlices.blockAccessList with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input (rootBase + 128) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.blockAccessList inputMemory sliceRepresentation⟩

theorem raw_v4_transaction_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.newPayloadRequest.executionPayload.transactions.size) :
    ∃ inputOffset sliceBase,
      observeBytes? state sliceBase value.newPayloadRequest.executionPayload.transactions[index].size =
        some value.newPayloadRequest.executionPayload.transactions[index].toList := by
  rcases representation.inputSlices.transactions index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (representation.descriptors.transactionsBase + 16 * index) inputOffset sliceBase
      value.newPayloadRequest.executionPayload.transactions[index] inputMemory sliceRepresentation⟩

theorem raw_v4_witness_state_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.witness.state.size) :
    ∃ inputOffset sliceBase,
      observeBytes? state sliceBase value.witness.state[index].size =
        some value.witness.state[index].toList := by
  rcases representation.inputSlices.witnessState index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (representation.descriptors.witnessStateBase + 16 * index) inputOffset sliceBase
      value.witness.state[index] inputMemory sliceRepresentation⟩

theorem raw_v4_witness_codes_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.witness.codes.size) :
    ∃ inputOffset sliceBase,
      observeBytes? state sliceBase value.witness.codes[index].size =
        some value.witness.codes[index].toList := by
  rcases representation.inputSlices.witnessCodes index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (representation.descriptors.witnessCodesBase + 16 * index) inputOffset sliceBase
      value.witness.codes[index] inputMemory sliceRepresentation⟩

theorem raw_v4_witness_headers_observes (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : SszBridge.RawV4) (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) (index : Nat)
    (indexBound : index < value.witness.headers.size) :
    ∃ inputOffset sliceBase,
      observeBytes? state sliceBase value.witness.headers[index].size =
        some value.witness.headers[index].toList := by
  rcases representation.inputSlices.witnessHeaders index indexBound with
    ⟨inputOffset, sliceBase, sliceRepresentation⟩
  exact ⟨inputOffset, sliceBase,
    observe_input_slice_descriptor_of_rep state inputBase input
      (representation.descriptors.witnessHeadersBase + 16 * index) inputOffset sliceBase
      value.witness.headers[index] inputMemory sliceRepresentation⟩

end BinaryFv.SSZ.Zesu.Execution
