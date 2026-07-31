import BinaryFv.SSZ.Zesu.Contracts.Ownership
import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams

/-!
# Auditing the canonical representations against `LocalTo`

`Ownership.localTo_is_a_real_obligation` proves a representation reading any non-memory component of
`State` is `LocalTo` **no** region — not even the universal one. So the ownership discipline only
applies to a container once that container's representation has been shown memory-determined. This
module runs that audit.

## What is proved here, and what is not

`MemDetermined` is `LocalTo` at the universal region, stated directly on state predicates so it
composes bottom-up over the representation primitives. Proving it for a representation establishes
the representation is **memory-only** — it closes the `localTo_is_a_real_obligation` hole and makes
the container eligible for the discipline.

It does **not** give disjointness. That needs the representation's actual *footprint* — the region it
is local to — which is a strictly stronger and more laborious result: for `RawV4Rep` the footprint is
the root allocation, ten heap arrays, the descriptor table and every borrowed input slice. Footprints
are not computed here.

So a container appearing below is eligible for the discipline, not yet protected by it.

## Audit status

**All eight are memory-determined, proved below.** `canonicalRepForkActivation`,
`canonicalRepForkConfig`, `canonicalRepChainConfig`, `canonicalRepExecutionRequests`,
`canonicalRepExecutionWitness`, `canonicalRepExecutionPayload`, `canonicalRepNewPayloadRequest`,
`canonicalRepRawV4`. So the `localTo_is_a_real_obligation` hole is closed for every representation
the root actually uses, and no representation reads outside memory.

The earlier mechanical scan — no reference to `regs`, `pc`, `choiceState`, `tags`, `cycleCount` or
`sailOutput` under `MemoryRepresentation/` — predicted this, but is now superseded by proof rather
than relied on. Keeping the distinction visible is the point: the grep was evidence, not a result,
and one field (`RawV4FixedFieldsRep.chainConfig`) was in fact missed by the field-extraction grep used
to draft these proofs and surfaced only when the compiler demanded it.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.RepresentationAudit

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Contracts.Ownership

/-- A state predicate transports across states that agree on all of memory.

This is `LocalTo` at the universal region, phrased on bare state predicates so the representation
primitives can be composed bottom-up before being packaged back into a
`ContainerRepresentation`. -/
def MemDetermined (P : State → Prop) : Prop :=
  ∀ s1 s2, (∀ address, s1.mem.get? address = s2.mem.get? address) → P s1 → P s2

theorem memDetermined_and {P Q : State → Prop}
    (hp : MemDetermined P) (hq : MemDetermined Q) :
    MemDetermined (fun s => P s ∧ Q s) :=
  fun s1 s2 agree h => ⟨hp s1 s2 agree h.1, hq s1 s2 agree h.2⟩

/-- A state-independent proposition is trivially memory-determined. Needed because several
representations carry pure side conditions (`data < 2 ^ 64`, `InputBytesAt …`) alongside their
memory claims. -/
theorem memDetermined_const {p : Prop} : MemDetermined (fun _ => p) :=
  fun _ _ _ h => h

theorem memDetermined_forall {α : Sort u} {P : α → State → Prop}
    (h : ∀ x, MemDetermined (P x)) : MemDetermined (fun s => ∀ x, P x s) :=
  fun s1 s2 agree hp x => h x s1 s2 agree (hp x)

theorem memDetermined_exists {α : Sort u} {P : α → State → Prop}
    (h : ∀ x, MemDetermined (P x)) : MemDetermined (fun s => ∃ x, P x s) :=
  fun s1 s2 agree hp => hp.imp fun x hx => h x s1 s2 agree hx

/-! ## The primitives

Every container representation bottoms out in these two. Both are pointwise claims about
`state.mem.get?`, so both transport by rewriting with the agreement hypothesis — which is exactly
what "memory-only" means, made mechanical. -/

theorem memDetermined_optionTag (base : Nat) (present : Bool) :
    MemDetermined (fun s => OptionTagRep s base present) :=
  fun _ _ agree h => (agree base).symm.trans h

theorem memDetermined_word64 (base value : Nat) :
    MemDetermined (fun s => Word64LERep s base value) :=
  fun _ _ agree h index hindex => (agree _).symm.trans (h index hindex)

theorem memDetermined_fixedByteVector {length : Nat} (base : Nat)
    (value : SszBridge.RawByteVector length) :
    MemDetermined (fun s => FixedByteVectorRep s base value) :=
  fun _ _ agree h index hindex => (agree _).symm.trans (h index hindex)

theorem memDetermined_bitVectorLE {width : Nat} (base : Nat) (value : BitVec width) :
    MemDetermined (fun s => BitVectorLERep s base value) :=
  fun _ _ agree h index hindex => (agree _).symm.trans (h index hindex)

/-- `HeapArrayRep` claims each byte is *present* rather than equal to a value, and `InputSliceRep`
claims two addresses hold the *same* byte. Both still transport: agreement on all of memory carries
any predicate built from `get?` at named addresses, whatever the shape of the claim. -/
theorem memDetermined_heapArray (base count elementSize : Nat) :
    MemDetermined (fun s => HeapArrayRep s base count elementSize) :=
  fun _ _ agree h => ⟨h.1, fun index hindex => (agree _) ▸ h.2 index hindex⟩

theorem memDetermined_inputSlice (inputBase inputOffset length sliceBase : Nat) :
    MemDetermined (fun s => InputSliceRep s inputBase inputOffset length sliceBase) :=
  fun _ _ agree h =>
    ⟨h.1, fun index hindex => ((agree _).symm.trans (h.2 index hindex)).trans (agree _)⟩

theorem memDetermined_heapFixedVectorArray {length : Nat} (base : Nat)
    (values : Array (SszBridge.RawByteVector length)) :
    MemDetermined (fun s => HeapFixedVectorArrayRep s base values) :=
  memDetermined_forall fun index =>
    memDetermined_forall fun _ => memDetermined_fixedByteVector _ _

theorem memDetermined_sliceDescriptor (base data count : Nat) :
    MemDetermined (fun s => SliceDescriptorRep s base data count) :=
  memDetermined_and memDetermined_const
    (memDetermined_and memDetermined_const
      (memDetermined_and (memDetermined_word64 _ _) (memDetermined_word64 _ _)))

theorem memDetermined_inputSliceDescriptor (inputBase : Nat) (input : ByteArray)
    (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8) :
    MemDetermined (fun s =>
      InputSliceDescriptorRep s inputBase input descriptorBase inputOffset sliceBase bytes) :=
  memDetermined_and (memDetermined_sliceDescriptor _ _ _)
    (memDetermined_and (memDetermined_inputSlice _ _ _ _) memDetermined_const)

theorem memDetermined_inputSliceDescriptorArray (inputBase : Nat) (input : ByteArray)
    (descriptorBase : Nat) (slices : Array (Array UInt8)) :
    MemDetermined (fun s =>
      InputSliceDescriptorArrayRep s inputBase input descriptorBase slices) :=
  memDetermined_forall fun _ =>
    memDetermined_forall fun _ =>
      memDetermined_exists fun _ =>
        memDetermined_exists fun _ => memDetermined_inputSliceDescriptor _ _ _ _ _ _

/-! ## The heap record arrays

Four record shapes, each a conjunction of `Word64LERep` and `FixedByteVectorRep`, each wrapped in an
index-quantified array rep. Uniform enough that the proofs are pure composition. -/

theorem memDetermined_rawWithdrawal (base : Nat) (value : SszBridge.RawWithdrawal) :
    MemDetermined (fun s => RawWithdrawalRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_word64 _ _)
      (memDetermined_and (memDetermined_word64 _ _) (memDetermined_fixedByteVector _ _)))

theorem memDetermined_heapWithdrawalArray (base : Nat)
    (values : Array SszBridge.RawWithdrawal) :
    MemDetermined (fun s => HeapWithdrawalArrayRep s base values) :=
  memDetermined_forall fun _ => memDetermined_forall fun _ => memDetermined_rawWithdrawal _ _

theorem memDetermined_rawWithdrawalRequest (base : Nat)
    (value : SszBridge.RawWithdrawalRequest) :
    MemDetermined (fun s => RawWithdrawalRequestRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_fixedByteVector _ _) (memDetermined_fixedByteVector _ _))

theorem memDetermined_heapWithdrawalRequestArray (base : Nat)
    (values : Array SszBridge.RawWithdrawalRequest) :
    MemDetermined (fun s => HeapWithdrawalRequestArrayRep s base values) :=
  memDetermined_forall fun _ =>
    memDetermined_forall fun _ => memDetermined_rawWithdrawalRequest _ _

theorem memDetermined_rawConsolidationRequest (base : Nat)
    (value : SszBridge.RawConsolidationRequest) :
    MemDetermined (fun s => RawConsolidationRequestRep s base value) :=
  memDetermined_and (memDetermined_fixedByteVector _ _)
    (memDetermined_and (memDetermined_fixedByteVector _ _) (memDetermined_fixedByteVector _ _))

theorem memDetermined_heapConsolidationRequestArray (base : Nat)
    (values : Array SszBridge.RawConsolidationRequest) :
    MemDetermined (fun s => HeapConsolidationRequestArrayRep s base values) :=
  memDetermined_forall fun _ =>
    memDetermined_forall fun _ => memDetermined_rawConsolidationRequest _ _

theorem memDetermined_rawDepositRequest (base : Nat) (value : SszBridge.RawDepositRequest) :
    MemDetermined (fun s => RawDepositRequestRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_word64 _ _)
      (memDetermined_and (memDetermined_fixedByteVector _ _)
        (memDetermined_and (memDetermined_fixedByteVector _ _)
          (memDetermined_fixedByteVector _ _))))

theorem memDetermined_heapDepositRequestArray (base : Nat)
    (values : Array SszBridge.RawDepositRequest) :
    MemDetermined (fun s => HeapDepositRequestArrayRep s base values) :=
  memDetermined_forall fun _ =>
    memDetermined_forall fun _ => memDetermined_rawDepositRequest _ _

/-! ## The option and blob-schedule layers -/

theorem memDetermined_optionU64 (base : Nat) (value : Option UInt64) :
    MemDetermined (fun s => OptionU64Rep s base value) := by
  cases value with
  | none => exact memDetermined_optionTag _ _
  | some v =>
      exact memDetermined_and (memDetermined_word64 base v.toNat) (memDetermined_optionTag _ _)

theorem memDetermined_blobSchedule (base : Nat) (value : SszBridge.RawBlobSchedule) :
    MemDetermined (fun s => BlobScheduleRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_word64 _ _) (memDetermined_word64 _ _))

theorem memDetermined_optionBlobSchedule (base : Nat)
    (value : Option SszBridge.RawBlobSchedule) :
    MemDetermined (fun s => OptionBlobScheduleRep s base value) := by
  cases value with
  | none => exact memDetermined_optionTag _ _
  | some v => exact memDetermined_and (memDetermined_blobSchedule base v) (memDetermined_optionTag _ _)

/-! ## The three chain containers -/

theorem memDetermined_forkActivation (base : Nat) (value : SszBridge.RawForkActivation) :
    MemDetermined (fun s => ForkActivationRep s base value) :=
  memDetermined_and (memDetermined_optionU64 _ _) (memDetermined_optionU64 _ _)

theorem memDetermined_forkConfig (base : Nat) (value : SszBridge.RawForkConfig) :
    MemDetermined (fun s => ForkConfigRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _)
    (memDetermined_and (memDetermined_forkActivation _ _) (memDetermined_optionBlobSchedule _ _))

theorem memDetermined_chainConfig (base : Nat) (value : SszBridge.RawChainConfig) :
    MemDetermined (fun s => ChainConfigRep s base value) :=
  memDetermined_and (memDetermined_word64 _ _) (memDetermined_forkConfig _ _)

/-! ## The four remaining containers

`ExecutionPayloadFixedRep` is a structure rather than a conjunction, so its transport is written out
field by field — fifteen of them. Mechanical, but not automatable through the `_and` combinator. -/

theorem memDetermined_executionPayloadFixed (base : Nat)
    (value : SszBridge.RawExecutionPayload) :
    MemDetermined (fun s => ExecutionPayloadFixedRep s base value) :=
  fun s1 s2 agree h =>
    { baseFeePerGas := memDetermined_bitVectorLE _ _ s1 s2 agree h.baseFeePerGas
      parentHash := memDetermined_fixedByteVector _ _ s1 s2 agree h.parentHash
      feeRecipient := memDetermined_fixedByteVector _ _ s1 s2 agree h.feeRecipient
      stateRoot := memDetermined_fixedByteVector _ _ s1 s2 agree h.stateRoot
      receiptsRoot := memDetermined_fixedByteVector _ _ s1 s2 agree h.receiptsRoot
      logsBloom := memDetermined_fixedByteVector _ _ s1 s2 agree h.logsBloom
      prevRandao := memDetermined_fixedByteVector _ _ s1 s2 agree h.prevRandao
      blockHash := memDetermined_fixedByteVector _ _ s1 s2 agree h.blockHash
      blockNumber := memDetermined_word64 _ _ s1 s2 agree h.blockNumber
      gasLimit := memDetermined_word64 _ _ s1 s2 agree h.gasLimit
      gasUsed := memDetermined_word64 _ _ s1 s2 agree h.gasUsed
      timestamp := memDetermined_word64 _ _ s1 s2 agree h.timestamp
      blobGasUsed := memDetermined_word64 _ _ s1 s2 agree h.blobGasUsed
      excessBlobGas := memDetermined_word64 _ _ s1 s2 agree h.excessBlobGas
      slotNumber := memDetermined_word64 _ _ s1 s2 agree h.slotNumber }

theorem memDetermined_executionRequests (base : Nat)
    (value : SszBridge.RawExecutionRequests) :
    MemDetermined (fun s => ExecutionRequestsRep s base value) :=
  memDetermined_exists fun _ => memDetermined_exists fun _ => memDetermined_exists fun _ =>
    memDetermined_and (memDetermined_sliceDescriptor _ _ _)
      (memDetermined_and (memDetermined_heapArray _ _ _)
        (memDetermined_and (memDetermined_heapDepositRequestArray _ _)
          (memDetermined_and (memDetermined_sliceDescriptor _ _ _)
            (memDetermined_and (memDetermined_heapArray _ _ _)
              (memDetermined_and (memDetermined_heapWithdrawalRequestArray _ _)
                (memDetermined_and (memDetermined_sliceDescriptor _ _ _)
                  (memDetermined_and (memDetermined_heapArray _ _ _)
                    (memDetermined_heapConsolidationRequestArray _ _))))))))

theorem memDetermined_executionWitness (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionWitness) :
    MemDetermined (fun s => ExecutionWitnessRep s inputBase input base value) :=
  memDetermined_exists fun _ => memDetermined_exists fun _ => memDetermined_exists fun _ =>
    memDetermined_and (memDetermined_sliceDescriptor _ _ _)
      (memDetermined_and (memDetermined_heapArray _ _ _)
        (memDetermined_and (memDetermined_inputSliceDescriptorArray _ _ _ _)
          (memDetermined_and (memDetermined_sliceDescriptor _ _ _)
            (memDetermined_and (memDetermined_heapArray _ _ _)
              (memDetermined_and (memDetermined_inputSliceDescriptorArray _ _ _ _)
                (memDetermined_and (memDetermined_sliceDescriptor _ _ _)
                  (memDetermined_and (memDetermined_heapArray _ _ _)
                    (memDetermined_inputSliceDescriptorArray _ _ _ _))))))))

theorem memDetermined_executionPayload (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawExecutionPayload) :
    MemDetermined (fun s => ExecutionPayloadRep s inputBase input base value) :=
  memDetermined_and (memDetermined_executionPayloadFixed _ _)
    (memDetermined_and
      (memDetermined_exists fun _ => memDetermined_exists fun _ =>
        memDetermined_inputSliceDescriptor _ _ _ _ _ _)
      (memDetermined_and
        (memDetermined_exists fun _ => memDetermined_exists fun _ =>
          memDetermined_inputSliceDescriptor _ _ _ _ _ _)
        (memDetermined_and
          (memDetermined_exists fun _ =>
            memDetermined_and (memDetermined_sliceDescriptor _ _ _)
              (memDetermined_and (memDetermined_heapArray _ _ _)
                (memDetermined_inputSliceDescriptorArray _ _ _ _)))
          (memDetermined_exists fun _ =>
            memDetermined_and (memDetermined_sliceDescriptor _ _ _)
              (memDetermined_and (memDetermined_heapArray _ _ _)
                (memDetermined_heapWithdrawalArray _ _))))))

theorem memDetermined_newPayloadRequest (inputBase : Nat) (input : ByteArray) (base : Nat)
    (value : SszBridge.RawNewPayloadRequest) :
    MemDetermined (fun s => NewPayloadRequestRep s inputBase input base value) :=
  memDetermined_and (memDetermined_executionPayload _ _ _ _)
    (memDetermined_and
      (memDetermined_exists fun _ =>
        memDetermined_and (memDetermined_sliceDescriptor _ _ _)
          (memDetermined_and (memDetermined_heapArray _ _ _)
            (memDetermined_heapFixedVectorArray _ _)))
      (memDetermined_and (memDetermined_fixedByteVector _ _)
        (memDetermined_executionRequests _ _)))

/-! ## The root object

`RawV4Rep` is the last one and the only one that needed a shape the combinators do not reach. See
`memDetermined_rawV4` for why. -/

theorem memDetermined_rawStatelessInput (base : Nat) :
    MemDetermined (fun s => RawStatelessInputRep s base) :=
  memDetermined_exists fun _ =>
    memDetermined_and memDetermined_const (memDetermined_heapArray _ _ _)

theorem memDetermined_rawV4Allocation (rootBase : Nat) (value : SszBridge.RawV4)
    (bases : RawV4DescriptorBases) :
    MemDetermined (fun s => RawV4AllocationRep s rootBase value bases) :=
  fun s1 s2 agree h =>
    { root := memDetermined_rawStatelessInput _ s1 s2 agree h.root
      versionedHashes := memDetermined_heapArray _ _ _ s1 s2 agree h.versionedHashes
      versionedHashContents :=
        memDetermined_heapFixedVectorArray _ _ s1 s2 agree h.versionedHashContents
      transactions := memDetermined_heapArray _ _ _ s1 s2 agree h.transactions
      withdrawals := memDetermined_heapArray _ _ _ s1 s2 agree h.withdrawals
      withdrawalContents := memDetermined_heapWithdrawalArray _ _ s1 s2 agree h.withdrawalContents
      deposits := memDetermined_heapArray _ _ _ s1 s2 agree h.deposits
      depositContents := memDetermined_heapDepositRequestArray _ _ s1 s2 agree h.depositContents
      withdrawalRequests := memDetermined_heapArray _ _ _ s1 s2 agree h.withdrawalRequests
      withdrawalRequestContents :=
        memDetermined_heapWithdrawalRequestArray _ _ s1 s2 agree h.withdrawalRequestContents
      consolidationRequests := memDetermined_heapArray _ _ _ s1 s2 agree h.consolidationRequests
      consolidationRequestContents :=
        memDetermined_heapConsolidationRequestArray _ _ s1 s2 agree h.consolidationRequestContents
      witnessState := memDetermined_heapArray _ _ _ s1 s2 agree h.witnessState
      witnessCodes := memDetermined_heapArray _ _ _ s1 s2 agree h.witnessCodes
      witnessHeaders := memDetermined_heapArray _ _ _ s1 s2 agree h.witnessHeaders
      publicKeys := memDetermined_heapArray _ _ _ s1 s2 agree h.publicKeys
      publicKeyContents := memDetermined_heapFixedVectorArray _ _ s1 s2 agree h.publicKeyContents }

theorem memDetermined_rawV4Descriptor (rootBase : Nat) (value : SszBridge.RawV4)
    (bases : RawV4DescriptorBases) :
    MemDetermined (fun s => RawV4DescriptorRep s rootBase value bases) :=
  fun s1 s2 agree h =>
    { versionedHashes := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.versionedHashes
      transactions := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.transactions
      withdrawals := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.withdrawals
      deposits := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.deposits
      withdrawalRequests := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.withdrawalRequests
      consolidationRequests :=
        memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.consolidationRequests
      witnessState := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.witnessState
      witnessCodes := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.witnessCodes
      witnessHeaders := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.witnessHeaders
      publicKeys := memDetermined_sliceDescriptor _ _ _ s1 s2 agree h.publicKeys }

theorem memDetermined_rawV4InputSlices (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : SszBridge.RawV4) (bases : RawV4DescriptorBases)
    {s1 s2 : State} (agree : ∀ address, s1.mem.get? address = s2.mem.get? address)
    (d1 : RawV4DescriptorRep s1 rootBase value bases)
    (d2 : RawV4DescriptorRep s2 rootBase value bases)
    (h : RawV4InputSlicesRep s1 inputBase input rootBase value bases d1) :
    RawV4InputSlicesRep s2 inputBase input rootBase value bases d2 :=
  { extraData := h.extraData.imp fun _ h' => h'.imp fun _ h'' =>
      memDetermined_inputSliceDescriptor _ _ _ _ _ _ s1 s2 agree h''
    blockAccessList := h.blockAccessList.imp fun _ h' => h'.imp fun _ h'' =>
      memDetermined_inputSliceDescriptor _ _ _ _ _ _ s1 s2 agree h''
    transactions := memDetermined_inputSliceDescriptorArray _ _ _ _ s1 s2 agree h.transactions
    witnessState := memDetermined_inputSliceDescriptorArray _ _ _ _ s1 s2 agree h.witnessState
    witnessCodes := memDetermined_inputSliceDescriptorArray _ _ _ _ s1 s2 agree h.witnessCodes
    witnessHeaders := memDetermined_inputSliceDescriptorArray _ _ _ _ s1 s2 agree h.witnessHeaders }

theorem memDetermined_rawV4FixedFields (rootBase : Nat) (value : SszBridge.RawV4) :
    MemDetermined (fun s => RawV4FixedFieldsRep s rootBase value) :=
  fun s1 s2 agree h =>
    { baseFeePerGas := memDetermined_bitVectorLE _ _ s1 s2 agree h.baseFeePerGas
      parentHash := memDetermined_fixedByteVector _ _ s1 s2 agree h.parentHash
      feeRecipient := memDetermined_fixedByteVector _ _ s1 s2 agree h.feeRecipient
      stateRoot := memDetermined_fixedByteVector _ _ s1 s2 agree h.stateRoot
      receiptsRoot := memDetermined_fixedByteVector _ _ s1 s2 agree h.receiptsRoot
      logsBloom := memDetermined_fixedByteVector _ _ s1 s2 agree h.logsBloom
      prevRandao := memDetermined_fixedByteVector _ _ s1 s2 agree h.prevRandao
      blockHash := memDetermined_fixedByteVector _ _ s1 s2 agree h.blockHash
      parentBeaconBlockRoot :=
        memDetermined_fixedByteVector _ _ s1 s2 agree h.parentBeaconBlockRoot
      blockNumber := memDetermined_word64 _ _ s1 s2 agree h.blockNumber
      gasLimit := memDetermined_word64 _ _ s1 s2 agree h.gasLimit
      gasUsed := memDetermined_word64 _ _ s1 s2 agree h.gasUsed
      timestamp := memDetermined_word64 _ _ s1 s2 agree h.timestamp
      blobGasUsed := memDetermined_word64 _ _ s1 s2 agree h.blobGasUsed
      excessBlobGas := memDetermined_word64 _ _ s1 s2 agree h.excessBlobGas
      slotNumber := memDetermined_word64 _ _ s1 s2 agree h.slotNumber
      chainConfig := memDetermined_chainConfig _ _ s1 s2 agree h.chainConfig }

/-- **The root object, and the one case the combinators did not reach.**

`RawV4Rep.layout` is `∃ bases, RawV4AllocationRep … ∧ ∃ descriptors : RawV4DescriptorRep …,
RawV4InputSlicesRep … descriptors` — an existential over a **proof**, whose type mentions the state.
`memDetermined_exists` cannot apply: it quantifies over an `α` fixed independently of the state,
and here the binder's type changes as the state does.

So the transport is written by hand: build the descriptor witness at `s2` first, then carry the
input-slice facts across against *that* witness rather than the original. `RawV4InputSlicesRep` does
not use its `descriptors` argument in any field, so the two are interchangeable once both exist —
but that is a fact about this definition, not something the combinator could have known. -/
theorem memDetermined_rawV4 (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    (value : SszBridge.RawV4) :
    MemDetermined (fun s => RawV4Rep s inputBase input rootBase value) :=
  fun s1 s2 agree h =>
    { layout := by
        obtain ⟨bases, halloc, d1, hslices⟩ := h.layout
        have d2 := memDetermined_rawV4Descriptor rootBase value bases s1 s2 agree d1
        exact ⟨bases, memDetermined_rawV4Allocation rootBase value bases s1 s2 agree halloc, d2,
          memDetermined_rawV4InputSlices inputBase input rootBase value bases agree d1 d2 hslices⟩
      fixedFields := memDetermined_rawV4FixedFields _ _ s1 s2 agree h.fixedFields }

/-! ## The audit results, stated as `LocalTo`

`LocalTo` at the universal region is the eligibility fact the discipline needs. Stated on the
canonical representations themselves, so these are claims about the objects the root actually uses
rather than about the primitives. -/

theorem localTo_canonicalRepForkActivation :
    LocalTo canonicalRepForkActivation (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_forkActivation base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepForkConfig :
    LocalTo canonicalRepForkConfig (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_forkConfig base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepChainConfig :
    LocalTo canonicalRepChainConfig (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_chainConfig base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepExecutionRequests :
    LocalTo canonicalRepExecutionRequests (fun _ _ => True) :=
  fun _ _ value s1 s2 base agree h =>
    memDetermined_executionRequests base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepExecutionWitness :
    LocalTo canonicalRepExecutionWitness (fun _ _ => True) :=
  fun inputBase input value s1 s2 base agree h =>
    memDetermined_executionWitness inputBase input base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepExecutionPayload :
    LocalTo canonicalRepExecutionPayload (fun _ _ => True) :=
  fun inputBase input value s1 s2 base agree h =>
    memDetermined_executionPayload inputBase input base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepNewPayloadRequest :
    LocalTo canonicalRepNewPayloadRequest (fun _ _ => True) :=
  fun inputBase input value s1 s2 base agree h =>
    memDetermined_newPayloadRequest inputBase input base value s1 s2 (fun a => agree a trivial) h

theorem localTo_canonicalRepRawV4 :
    LocalTo canonicalRepRawV4 (fun _ _ => True) :=
  fun inputBase input value s1 s2 base agree h =>
    memDetermined_rawV4 inputBase input base value s1 s2 (fun a => agree a trivial) h

end BinaryFv.SSZ.Zesu.Contracts.RepresentationAudit
