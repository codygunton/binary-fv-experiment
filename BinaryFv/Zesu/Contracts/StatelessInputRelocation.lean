import BinaryFv.Zesu.Contracts.Footprint
import BinaryFv.Zesu.Contracts.Runtime

/-! Transport the complete decoded-input representation across a byte copy that does not touch its
witnessed footprint. The separate root-rebasing theorem consumes the copied 832-byte payload; this
file handles the ten allocator-chosen arrays and makes their required separation explicit. -/

namespace BinaryFv.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.Zesu.DecodedValue
open BinaryFv.Zesu.Contracts.Footprint

/-- A complete `StatelessInput` representation whose ten descriptor-selected heap ranges are
contained in one allocator-cursor interval. The root record is deliberately absent from
`heapWithin`: it is caller-owned storage, whereas these ten ranges are the decoder allocations
that later copies must not overwrite. -/
structure StatelessInputRepInHeapInterval (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (cursorBefore cursorAfter : Nat) : Prop where
  layout : ∃ bases : StatelessInputDescriptorBases,
    StatelessInputAllocationRep state rootBase value bases ∧
      ∃ descriptors : StatelessInputDescriptorRep state rootBase value bases,
        StatelessInputInputSlicesRep state inputBase input rootBase value bases descriptors ∧
          ∀ address, statelessInputHeapRegion value bases address →
            cursorBefore ≤ address ∧ address < cursorAfter
  fixedFields : StatelessInputFixedFieldsRep state rootBase value

/-- Forget the cursor-placement evidence while retaining the complete representation it binds. -/
def StatelessInputRepInHeapInterval.representation {state : State} {inputBase rootBase : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    {cursorBefore cursorAfter : Nat}
    (allocated : StatelessInputRepInHeapInterval state inputBase input rootBase value
      cursorBefore cursorAfter) : StatelessInputRep state inputBase input rootBase value :=
  { layout := by
      obtain ⟨bases, allocation, descriptors, inputSlices, -⟩ := allocated.layout
      exact ⟨bases, allocation, descriptors, inputSlices⟩
    fixedFields := allocated.fixedFields }

/-- Reindex every borrowed input slice from an extracted suffix to the original input without
changing the represented root, heap allocations, fixed fields, or cursor interval. -/
theorem StatelessInputRepInHeapInterval.reindex_extract_suffix {state : State}
    {inputBase start rootBase : Nat} {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    {cursorBefore cursorAfter : Nat}
    (allocated : StatelessInputRepInHeapInterval state (inputBase + start)
      (input.extract start input.size) rootBase value cursorBefore cursorAfter) :
    StatelessInputRepInHeapInterval state inputBase input rootBase value cursorBefore cursorAfter := by
  obtain ⟨bases, allocation, descriptors, inputSlices, heapWithin⟩ := allocated.layout
  exact
    { layout := ⟨bases, allocation, descriptors, inputSlices.reindex_extract_suffix, heapWithin⟩
      fixedFields := allocated.fixedFields }

/-- The interval witness is memory-only, so it survives parent-owned register steps unchanged. -/
theorem StatelessInputRepInHeapInterval.of_mem_eq {before after : State} {inputBase rootBase : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    {cursorBefore cursorAfter : Nat} (memory : after.mem = before.mem)
    (allocated : StatelessInputRepInHeapInterval before inputBase input rootBase value
      cursorBefore cursorAfter) :
    StatelessInputRepInHeapInterval after inputBase input rootBase value cursorBefore cursorAfter := by
  obtain ⟨bases, allocation, descriptors, inputSlices, heapWithin⟩ := allocated.layout
  have agree : ∀ address, before.mem.get? address = after.mem.get? address :=
    fun address => (congrArg (fun mem => mem.get? address) memory).symm
  have allocationAfter : StatelessInputAllocationRep after rootBase value bases :=
    RepresentationAudit.memDetermined_statelessInputAllocation rootBase value bases before after agree
      allocation
  have descriptorsAfter : StatelessInputDescriptorRep after rootBase value bases :=
    statelessInputDescriptor_footprint rootBase 832 value bases (by omega) before after
      (fun address _ => agree address) descriptors
  have fixedFieldsAfter : StatelessInputFixedFieldsRep after rootBase value :=
    statelessInputFixedFields_footprint rootBase 832 value (by omega) before after
      (fun address _ => agree address) allocated.fixedFields
  have inputSlicesAfter :
      StatelessInputInputSlicesRep after inputBase input rootBase value bases descriptorsAfter :=
    statelessInputInputSlices_footprint inputBase input rootBase 832 value bases (by omega)
      (fun address _ => agree address) descriptors descriptorsAfter inputSlices
  exact
    { layout := ⟨bases, allocationAfter, descriptorsAfter, inputSlicesAfter, heapWithin⟩
      fixedFields := fixedFieldsAfter }

private theorem statelessInputRep_transport_at_bases {before after : State}
    (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : BinaryFv.Specs.SSZ.StatelessInput) (bases : StatelessInputDescriptorBases)
    (allocation : StatelessInputAllocationRep before rootBase value bases)
    (descriptors : StatelessInputDescriptorRep before rootBase value bases)
    (slices : StatelessInputInputSlicesRep before inputBase input rootBase value bases descriptors)
    (fixedFields : StatelessInputFixedFieldsRep before rootBase value)
    (cursorBefore cursorAfter : Nat)
    (heapWithin : ∀ address, statelessInputHeapRegion value bases address →
      cursorBefore ≤ address ∧ address < cursorAfter)
    (agree : ∀ address, statelessInputRegion rootBase 832 value bases address →
      before.mem.get? address = after.mem.get? address) :
    StatelessInputRepInHeapInterval after inputBase input rootBase value cursorBefore cursorAfter := by
  have agreeRecord : ∀ address, range rootBase 832 address →
      before.mem.get? address = after.mem.get? address :=
    fun address ha => agree address (Or.inl ha)
  have publicKeyContents :
      MemDeterminedOn (range bases.publicKeysBase (65 * value.publicKeys.size))
        (fun state => HeapFixedVectorArrayRep state bases.publicKeysBase value.publicKeys) :=
    heapFixedVectorArray_footprint _ _
  have descriptorsAfter : StatelessInputDescriptorRep after rootBase value bases :=
    statelessInputDescriptor_footprint rootBase 832 value bases (by omega) before after agreeRecord
      descriptors
  refine
    { layout := ⟨bases, ?_, descriptorsAfter,
        statelessInputInputSlices_footprint inputBase input rootBase 832 value bases (by omega) agree
          descriptors descriptorsAfter slices, heapWithin⟩
      fixedFields := statelessInputFixedFields_footprint rootBase 832 value (by omega) before after
        agreeRecord fixedFields }
  exact
    { root := rawStatelessInput_footprint rootBase 832
        BinaryFv.Zesu.Artifacts.raw_stateless_input_layout.1 before after agreeRecord allocation.root
      versionedHashes := heapArray_footprint bases.versionedHashesBase _ 32 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.versionedHashes
      versionedHashContents := heapFixedVectorArray_footprint bases.versionedHashesBase _ before after
        (fun address inside => heapRegionAgreement agree inside Footprint.versionedHashContentsHeapRegion_member)
        allocation.versionedHashContents
      transactions := heapArray_footprint bases.transactionsBase _ 16 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.transactions
      withdrawals := heapArray_footprint bases.withdrawalsBase _ 48 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.withdrawals
      withdrawalContents := heapWithdrawalArray_footprint bases.withdrawalsBase _ before after
        (fun address inside => heapRegionAgreement agree inside Footprint.withdrawalContentsHeapRegion_member)
        allocation.withdrawalContents
      deposits := heapArray_footprint bases.depositsBase _ 192 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.deposits
      depositContents := heapDepositRequestArray_footprint bases.depositsBase _ before after
        (fun address inside => heapRegionAgreement agree inside Footprint.depositContentsHeapRegion_member)
        allocation.depositContents
      withdrawalRequests := heapArray_footprint bases.withdrawalRequestsBase _ 80 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.withdrawalRequests
      withdrawalRequestContents :=
        heapWithdrawalRequestArray_footprint bases.withdrawalRequestsBase _ before after
          (fun address inside => heapRegionAgreement agree inside Footprint.withdrawalRequestContentsHeapRegion_member)
          allocation.withdrawalRequestContents
      consolidationRequests := heapArray_footprint bases.consolidationRequestsBase _ 116 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.consolidationRequests
      consolidationRequestContents :=
        heapConsolidationRequestArray_footprint bases.consolidationRequestsBase _ before after
          (fun address inside => heapRegionAgreement agree inside Footprint.consolidationRequestContentsHeapRegion_member)
          allocation.consolidationRequestContents
      witnessState := heapArray_footprint bases.witnessStateBase _ 16 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.witnessState
      witnessCodes := heapArray_footprint bases.witnessCodesBase _ 16 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.witnessCodes
      witnessHeaders := heapArray_footprint bases.witnessHeadersBase _ 16 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.witnessHeaders
      publicKeys := heapArray_footprint bases.publicKeysBase _ 65 before after
        (fun address inside => heapRegionAgreement agree inside)
        allocation.publicKeys
      publicKeyContents := publicKeyContents before after
        (fun address inside => heapRegionAgreement agree inside Footprint.publicKeyContentsHeapRegion_member) allocation.publicKeyContents }

/-- Expose the exact represented footprint as the sufficient memory agreement condition while
retaining its allocator interval. -/
theorem StatelessInputRepInHeapInterval.transport {before after : State}
    {inputBase rootBase : Nat} {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput}
    {cursorBefore cursorAfter : Nat}
    (allocated : StatelessInputRepInHeapInterval before inputBase input rootBase value
      cursorBefore cursorAfter) :
    ∃ bases : StatelessInputDescriptorBases,
      (∀ address, statelessInputHeapRegion value bases address →
        cursorBefore ≤ address ∧ address < cursorAfter) ∧
      ((∀ address, statelessInputRegion rootBase 832 value bases address →
        before.mem.get? address = after.mem.get? address) →
      StatelessInputRepInHeapInterval after inputBase input rootBase value cursorBefore cursorAfter) := by
  obtain ⟨bases, allocation, descriptors, slices, heapWithin⟩ := allocated.layout
  exact ⟨bases, heapWithin, fun agree => statelessInputRep_transport_at_bases inputBase input rootBase
    value bases allocation descriptors slices allocated.fixedFields cursorBefore cursorAfter heapWithin agree⟩

/-- Preserve the represented root and witnessed heap interval across a disjoint byte copy. -/
theorem StatelessInputRepInHeapInterval.survives_copy {before after : State}
    {inputBase rootBase : Nat} {input : ByteArray}
    {value : BinaryFv.Specs.SSZ.StatelessInput} {cursorBefore cursorAfter : Nat}
    (copyArgs : CopyArgs) (copyFrame : CopyDestinationFrame copyArgs before after)
    (rootOutside : ∀ address, range rootBase 832 address →
      address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address)
    (heapOutside : ∀ address, Contracts.interval cursorBefore cursorAfter address →
      address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address)
    (allocated : StatelessInputRepInHeapInterval before inputBase input rootBase value
      cursorBefore cursorAfter) :
    StatelessInputRepInHeapInterval after inputBase input rootBase value cursorBefore cursorAfter := by
  obtain ⟨bases, allocation, descriptors, slices, heapWithin⟩ := allocated.layout
  apply statelessInputRep_transport_at_bases inputBase input rootBase value bases allocation descriptors
    slices allocated.fixedFields cursorBefore cursorAfter heapWithin
  intro address footprint
  apply (copyFrame address ?_).symm
  rcases footprint with root | heap
  · exact rootOutside address root
  · exact heapOutside address (heapWithin address heap)

/-- Rebase only the 832-byte root while retaining the exact witnessed heap bases and interval. -/
theorem StatelessInputRepInHeapInterval.rebase_root {state : State}
    {inputBase sourceRoot destinationRoot : Nat} {input : ByteArray}
    {value : BinaryFv.Specs.SSZ.StatelessInput} {cursorBefore cursorAfter : Nat}
    (destinationFits : destinationRoot + 832 ≤ 2 ^ 64)
    (memory : ByteWindowRelocation state state sourceRoot destinationRoot 832)
    (allocated : StatelessInputRepInHeapInterval state inputBase input sourceRoot value
      cursorBefore cursorAfter) :
    StatelessInputRepInHeapInterval state inputBase input destinationRoot value
      cursorBefore cursorAfter := by
  obtain ⟨bases, allocation, descriptors, slices, heapWithin⟩ := allocated.layout
  obtain ⟨size, sizeEq, root⟩ := allocation.root
  have size832 : size = 832 := by
    rw [BinaryFv.Zesu.Artifacts.raw_stateless_input_layout.1] at sizeEq
    exact (Option.some.inj sizeEq).symm
  have destinationRootRep : RawStatelessInputRep state destinationRoot := by
    refine ⟨size, sizeEq, root.rebase ?_ ?_⟩
    · simpa [size832] using destinationFits
    · intro index bound
      simpa [size832] using memory index (by simpa [size832] using bound)
  have destinationDescriptors := descriptors.rebase memory
  exact
    { layout := ⟨bases, { allocation with root := destinationRootRep }, destinationDescriptors,
        slices.rebase memory, heapWithin⟩
      fixedFields := allocated.fixedFields.rebase memory }

/-- A copy frame preserves a `StatelessInputRep` at its existing root when the representation's
actual root-plus-ten-array footprint is outside the copied destination interval. The bases are
returned from the established representation, so callers cannot substitute guessed locations. -/
theorem statelessInputRep_survives_copy_away {before after : State} {inputBase rootBase : Nat}
    {input : ByteArray} {value : BinaryFv.Specs.SSZ.StatelessInput} (copyArgs : CopyArgs)
    (copyFrame : CopyDestinationFrame copyArgs before after)
    (representation : StatelessInputRep before inputBase input rootBase value) :
    ∃ bases : StatelessInputDescriptorBases,
      (∀ address, statelessInputRegion rootBase 832 value bases address →
        address < copyArgs.destination ∨ copyArgs.destination + copyArgs.length ≤ address) →
      StatelessInputRep after inputBase input rootBase value := by
  obtain ⟨bases, transport⟩ := statelessInput_footprint_abi inputBase input rootBase value before
    BinaryFv.Zesu.Artifacts.raw_stateless_input_layout.1 representation
  refine ⟨bases, fun outside => transport after fun address inFootprint => ?_⟩
  exact (copyFrame address (outside address inFootprint)).symm

end BinaryFv.Zesu.Contracts
