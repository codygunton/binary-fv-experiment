import BinaryFv.Zesu.MemoryRepresentation.Observers

/-!
# Observing a complete `BinaryFv.Specs.SSZ.RawV4` value

The observers in `Observers.lean` return observation records (`Nat`, `List UInt8`) because they were
written to compare against captured evidence. This module builds the *value* observer item (d)
needs: one guarded, executable `observeRawV4?` that reconstructs the bridge's own `BinaryFv.Specs.SSZ.RawV4`
— every fixed scalar and vector, the 256-bit base fee, both borrowed input slices, all ten
descriptor-backed collections, and the full chain config — together with the correspondence

  `RawV4Rep state inputBase input rootBase value → observeRawV4? state rootBase = some value`.

The correspondence carries one extra hypothesis, `MemoryBytes state inputBase input`: the borrowed
slices of a represented `RawV4` alias the caller's input buffer, so reading them back requires the
input bytes to actually be in memory. `RawV4Rep` deliberately does not include that clause — it is a
separate conjunct of the entry/exit contracts — so the observer states it explicitly.

Nothing here is a partial observer: a single failed byte read, a bad option tag, or a short slice
makes the whole observation `none`.
-/

namespace BinaryFv.Zesu.MemoryRepresentation

open BinaryFv.RiscV

/-! ## Spec-typed leaf observers -/

/-- Observe a little-endian machine word as the bridge's own `UInt64`. -/
def observeUInt64? (state : State) (base : Nat) : Option UInt64 :=
  (observeWord64? state base).map UInt64.ofNat

theorem observe_uint64_of_rep (state : State) (base : Nat) (value : UInt64)
    (representation : Word64LERep state base value.toNat) :
    observeUInt64? state base = some value := by
  unfold observeUInt64?
  rw [observe_word64_of_rep state base value.toNat (UInt64.toNat_lt value) representation]
  simp [UInt64.ofNat_toNat]

/-- Observe a fixed-width byte region as the bridge's own `RawByteVector`. The length check always
succeeds on a successful observation (`observeBytes?_length`); the `dite` keeps the definition
total without a proof obligation at the call site. -/
def observeByteVector? (state : State) (base length : Nat) :
    Option (BinaryFv.Specs.SSZ.RawByteVector length) := do
  let bytes ← observeBytes? state base length
  if h : bytes.toArray.size = length then
    pure (Vector.cast h bytes.toArray.toVector)
  else
    none

theorem observe_byte_vector_value_of_rep {length : Nat} (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawByteVector length)
    (representation : FixedByteVectorRep state base value) :
    observeByteVector? state base length = some value := by
  unfold observeByteVector?
  rw [observe_fixed_byte_vector_of_rep state base value representation]
  have hsize : value.toArray.toList.toArray.size = length := by simp
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, dif_pos hsize,
    Option.some.injEq]
  ext i hi
  simp

/-- Little-endian byte-list valuation, least-significant byte first. -/
def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * bytesToNatLE rest

/-- `bytesToNatLE` inverts the little-endian digit expansion of any value below `256 ^ k`. -/
theorem bytesToNatLE_digits :
    ∀ (k n : Nat), n < 256 ^ k →
      bytesToNatLE ((List.range k).map fun i => UInt8.ofNat ((n / 256 ^ i) % 256)) = n := by
  intro k
  induction k with
  | zero =>
    intro n h
    have : n = 0 := by simpa using h
    simp [this, bytesToNatLE]
  | succ k ih =>
    intro n h
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, bytesToNatLE]
    have htail : ((List.range k).map fun i => UInt8.ofNat ((n / 256 ^ (i + 1)) % 256)) =
        (List.range k).map fun i => UInt8.ofNat ((n / 256 / 256 ^ i) % 256) := by
      refine List.map_congr_left fun i _ => ?_
      rw [Nat.pow_succ', Nat.div_div_eq_div_mul]
    have hquot : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ'] at h
      omega
    have hcomp : (fun i => UInt8.ofNat ((n / 256 ^ (i + 1)) % 256)) =
        ((fun i => UInt8.ofNat ((n / 256 ^ i) % 256)) ∘ (· + 1)) := rfl
    calc (UInt8.ofNat (n / 256 ^ 0 % 256)).toNat +
          256 * bytesToNatLE ((List.range k).map fun i => UInt8.ofNat ((n / 256 ^ (i + 1)) % 256))
        = n % 256 + 256 * (n / 256) := by
          rw [htail, ih (n / 256) hquot]
          simp [Nat.mod_mod_of_dvd]
      _ = n := by omega

/-- Observe the 256-bit little-endian base fee as the bridge's own `BitVec 256`. -/
def observeBaseFeePerGas? (state : State) (base : Nat) : Option (BitVec 256) := do
  let bytes ← observeBytes? state base 32
  pure (BitVec.ofNat 256 (bytesToNatLE bytes))

theorem observe_base_fee_of_rep (state : State) (base : Nat) (value : BitVec 256)
    (representation : BitVectorLERep state base value) :
    observeBaseFeePerGas? state base = some value := by
  unfold observeBaseFeePerGas?
  rw [show (32 : Nat) = 256 / 8 from rfl,
    observe_bit_vector_le_of_rep state base value representation]
  have hbound : value.toNat < 256 ^ 32 := by
    have h := value.isLt
    rw [show (256 : Nat) ^ 32 = 2 ^ 256 by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]
    exact h
  have hvaluation : bytesToNatLE (bitVectorLEBytes value) = value.toNat := by
    simpa [bitVectorLEBytes] using bytesToNatLE_digits 32 value.toNat hbound
  simp [hvaluation, BitVec.ofNat_toNat]

/-- Observe a slice descriptor's exact bytes as the bridge's own `RawBytes`: read the pointer/count
pair, then the pointed-to bytes. -/
def observeByteSlice? (state : State) (descriptorBase : Nat) : Option BinaryFv.Specs.SSZ.RawBytes := do
  let descriptor ← observeSliceDescriptor? state descriptorBase
  let bytes ← observeBytes? state descriptor.1 descriptor.2
  pure bytes.toArray

theorem observe_byte_slice_of_rep (state : State) (inputBase : Nat) (input : ByteArray)
    (descriptorBase inputOffset sliceBase : Nat) (bytes : Array UInt8)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : InputSliceDescriptorRep state inputBase input descriptorBase inputOffset
      sliceBase bytes) :
    observeByteSlice? state descriptorBase = some bytes := by
  unfold observeByteSlice?
  rw [observe_slice_descriptor_of_rep state descriptorBase sliceBase bytes.size representation.1]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [observe_input_slice_descriptor_of_rep state inputBase input descriptorBase inputOffset
    sliceBase bytes inputMemory representation]
  simp

/-! ## Spec-typed record observers

One observer per fixed-width heap record, each producing the bridge's own structure. Offsets repeat
the corresponding `…Rep` predicates in `RawV4.lean` field for field. -/

/-- Observe one native withdrawal record as the bridge's own `RawWithdrawal`. -/
def observeWithdrawalValue? (state : State) (base : Nat) : Option BinaryFv.Specs.SSZ.RawWithdrawal := do
  let index ← observeUInt64? state base
  let validatorIndex ← observeUInt64? state (base + 8)
  let amount ← observeUInt64? state (base + 16)
  let address ← observeByteVector? state (base + 24) 20
  pure { index, validatorIndex, address, amount }

theorem observe_withdrawal_value_of_rep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawWithdrawal) (representation : RawWithdrawalRep state base value) :
    observeWithdrawalValue? state base = some value := by
  obtain ⟨index, validatorIndex, amount, address⟩ := representation
  unfold observeWithdrawalValue?
  rw [observe_uint64_of_rep state base value.index index,
    observe_uint64_of_rep state (base + 8) value.validatorIndex validatorIndex,
    observe_uint64_of_rep state (base + 16) value.amount amount,
    observe_byte_vector_value_of_rep state (base + 24) value.address address]
  rfl

/-- Observe one native deposit-request record as the bridge's own `RawDepositRequest`. -/
def observeDepositRequestValue? (state : State) (base : Nat) :
    Option BinaryFv.Specs.SSZ.RawDepositRequest := do
  let amount ← observeUInt64? state base
  let index ← observeUInt64? state (base + 8)
  let pubkey ← observeByteVector? state (base + 16) 48
  let withdrawalCredentials ← observeByteVector? state (base + 64) 32
  let signature ← observeByteVector? state (base + 96) 96
  pure { pubkey, withdrawalCredentials, amount, signature, index }

theorem observe_deposit_request_value_of_rep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawDepositRequest)
    (representation : RawDepositRequestRep state base value) :
    observeDepositRequestValue? state base = some value := by
  obtain ⟨amount, index, pubkey, withdrawalCredentials, signature⟩ := representation
  unfold observeDepositRequestValue?
  rw [observe_uint64_of_rep state base value.amount amount,
    observe_uint64_of_rep state (base + 8) value.index index,
    observe_byte_vector_value_of_rep state (base + 16) value.pubkey pubkey,
    observe_byte_vector_value_of_rep state (base + 64) value.withdrawalCredentials
      withdrawalCredentials,
    observe_byte_vector_value_of_rep state (base + 96) value.signature signature]
  rfl

/-- Observe one native withdrawal-request record as the bridge's own `RawWithdrawalRequest`. -/
def observeWithdrawalRequestValue? (state : State) (base : Nat) :
    Option BinaryFv.Specs.SSZ.RawWithdrawalRequest := do
  let amount ← observeUInt64? state base
  let sourceAddress ← observeByteVector? state (base + 8) 20
  let validatorPubkey ← observeByteVector? state (base + 28) 48
  pure { sourceAddress, validatorPubkey, amount }

theorem observe_withdrawal_request_value_of_rep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawWithdrawalRequest)
    (representation : RawWithdrawalRequestRep state base value) :
    observeWithdrawalRequestValue? state base = some value := by
  obtain ⟨amount, sourceAddress, validatorPubkey⟩ := representation
  unfold observeWithdrawalRequestValue?
  rw [observe_uint64_of_rep state base value.amount amount,
    observe_byte_vector_value_of_rep state (base + 8) value.sourceAddress sourceAddress,
    observe_byte_vector_value_of_rep state (base + 28) value.validatorPubkey validatorPubkey]
  rfl

/-- Observe one native consolidation-request record as the bridge's own
`RawConsolidationRequest`. -/
def observeConsolidationRequestValue? (state : State) (base : Nat) :
    Option BinaryFv.Specs.SSZ.RawConsolidationRequest := do
  let sourceAddress ← observeByteVector? state base 20
  let sourcePubkey ← observeByteVector? state (base + 20) 48
  let targetPubkey ← observeByteVector? state (base + 68) 48
  pure { sourceAddress, sourcePubkey, targetPubkey }

theorem observe_consolidation_request_value_of_rep (state : State) (base : Nat)
    (value : BinaryFv.Specs.SSZ.RawConsolidationRequest)
    (representation : RawConsolidationRequestRep state base value) :
    observeConsolidationRequestValue? state base = some value := by
  obtain ⟨sourceAddress, sourcePubkey, targetPubkey⟩ := representation
  unfold observeConsolidationRequestValue?
  rw [observe_byte_vector_value_of_rep state base value.sourceAddress sourceAddress,
    observe_byte_vector_value_of_rep state (base + 20) value.sourcePubkey sourcePubkey,
    observe_byte_vector_value_of_rep state (base + 68) value.targetPubkey targetPubkey]
  rfl

/-! ## Descriptor-backed collections

Every one of the root's ten collections is stored the same way: a slice descriptor (data pointer and
element count) whose elements sit at a fixed stride. One combinator reads the descriptor and then
observes each element; one lemma lifts a descriptor representation plus an element-wise
correspondence to the whole collection. -/

/-- Observe a whole descriptor-backed collection: read the pointer/count descriptor at
`descriptorBase`, then observe `count` elements with `element heapBase index`. -/
def observeDescriptorArray? {α : Type} (state : State) (descriptorBase : Nat)
    (element : Nat → Nat → Option α) : Option (Array α) := do
  let descriptor ← observeSliceDescriptor? state descriptorBase
  let items ← observeElementsFrom? (element descriptor.1) 0 descriptor.2
  pure items.toArray

theorem observe_descriptor_array_of_rep {α : Type} (state : State) (descriptorBase heapBase : Nat)
    (values : Array α) (element : Nat → Nat → Option α)
    (descriptor : SliceDescriptorRep state descriptorBase heapBase values.size)
    (elements : ∀ i (h : i < values.size), element heapBase i = some values[i]) :
    observeDescriptorArray? state descriptorBase element = some values := by
  unfold observeDescriptorArray?
  rw [observe_slice_descriptor_of_rep state descriptorBase heapBase values.size descriptor]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  have hlist : ∀ i (hi : i < values.toList.length),
      element heapBase (0 + i) = some values.toList[i] := by
    intro i hi
    have hsize : i < values.size := by simpa using hi
    simpa using elements i hsize
  have hall := observeElementsFrom_of_all (element heapBase) values.toList 0 hlist
  simp only [Array.length_toList] at hall
  rw [hall]
  simp

/-! ## The complete value observer -/

/-- **One guarded observation of the complete `BinaryFv.Specs.SSZ.RawV4`.** Reconstructs every fixed scalar
and vector, the 256-bit base fee, the two borrowed input slices, all ten descriptor-backed
collections (with their nested records), and the full chain config, at the offsets pinned by the
compiler-reflected ABI. Any failed read makes the whole observation `none`. -/
def observeRawV4? (state : State) (rootBase : Nat) : Option BinaryFv.Specs.SSZ.RawV4 := do
  let baseFeePerGas ← observeBaseFeePerGas? state rootBase
  let blockNumber ← observeUInt64? state (rootBase + 32)
  let gasLimit ← observeUInt64? state (rootBase + 40)
  let gasUsed ← observeUInt64? state (rootBase + 48)
  let timestamp ← observeUInt64? state (rootBase + 56)
  let extraData ← observeByteSlice? state (rootBase + 64)
  let transactions ← observeDescriptorArray? state (rootBase + 80)
    (fun heapBase i => observeByteSlice? state (heapBase + 16 * i))
  let withdrawals ← observeDescriptorArray? state (rootBase + 96)
    (fun heapBase i => observeWithdrawalValue? state (heapBase + 48 * i))
  let blobGasUsed ← observeUInt64? state (rootBase + 112)
  let excessBlobGas ← observeUInt64? state (rootBase + 120)
  let blockAccessList ← observeByteSlice? state (rootBase + 128)
  let slotNumber ← observeUInt64? state (rootBase + 144)
  let parentHash ← observeByteVector? state (rootBase + 152) 32
  let feeRecipient ← observeByteVector? state (rootBase + 184) 20
  let stateRoot ← observeByteVector? state (rootBase + 204) 32
  let receiptsRoot ← observeByteVector? state (rootBase + 236) 32
  let logsBloom ← observeByteVector? state (rootBase + 268) 256
  let prevRandao ← observeByteVector? state (rootBase + 524) 32
  let blockHash ← observeByteVector? state (rootBase + 556) 32
  let versionedHashes ← observeDescriptorArray? state (rootBase + 592)
    (fun heapBase i => observeByteVector? state (heapBase + 32 * i) 32)
  let deposits ← observeDescriptorArray? state (rootBase + 608)
    (fun heapBase i => observeDepositRequestValue? state (heapBase + 192 * i))
  let withdrawalRequests ← observeDescriptorArray? state (rootBase + 624)
    (fun heapBase i => observeWithdrawalRequestValue? state (heapBase + 80 * i))
  let consolidationRequests ← observeDescriptorArray? state (rootBase + 640)
    (fun heapBase i => observeConsolidationRequestValue? state (heapBase + 116 * i))
  let parentBeaconBlockRoot ← observeByteVector? state (rootBase + 656) 32
  let witnessState ← observeDescriptorArray? state (rootBase + 688)
    (fun heapBase i => observeByteSlice? state (heapBase + 16 * i))
  let witnessCodes ← observeDescriptorArray? state (rootBase + 704)
    (fun heapBase i => observeByteSlice? state (heapBase + 16 * i))
  let witnessHeaders ← observeDescriptorArray? state (rootBase + 720)
    (fun heapBase i => observeByteSlice? state (heapBase + 16 * i))
  let chainConfig ← observeChainConfig? state (rootBase + 736)
  let publicKeys ← observeDescriptorArray? state (rootBase + 816)
    (fun heapBase i => observeByteVector? state (heapBase + 65 * i) 65)
  pure {
    newPayloadRequest := {
      executionPayload := {
        parentHash, feeRecipient, stateRoot, receiptsRoot, logsBloom, prevRandao,
        blockNumber, gasLimit, gasUsed, timestamp, extraData, baseFeePerGas, blockHash,
        transactions, withdrawals, blobGasUsed, excessBlobGas, blockAccessList, slotNumber }
      versionedHashes, parentBeaconBlockRoot
      executionRequests := {
        deposits, withdrawals := withdrawalRequests, consolidations := consolidationRequests } }
    witness := { state := witnessState, codes := witnessCodes, headers := witnessHeaders }
    chainConfig, publicKeys }

/-- **A represented `RawV4` observes back exactly.** The one extra hypothesis is the caller's input
in memory, which the borrowed slices alias; everything else is `RawV4Rep`. -/
theorem observe_raw_v4_of_rep (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : BinaryFv.Specs.SSZ.RawV4)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) :
    observeRawV4? state rootBase = some value := by
  obtain ⟨bases, allocations, descriptors, inputSlices⟩ := representation.layout
  obtain ⟨extraOffset, extraBase, extraRep⟩ := inputSlices.extraData
  obtain ⟨accessOffset, accessBase, accessRep⟩ := inputSlices.blockAccessList
  unfold observeRawV4?
  rw [observe_base_fee_of_rep state rootBase _ representation.fixedFields.baseFeePerGas,
    observe_uint64_of_rep state (rootBase + 32) _ representation.fixedFields.blockNumber,
    observe_uint64_of_rep state (rootBase + 40) _ representation.fixedFields.gasLimit,
    observe_uint64_of_rep state (rootBase + 48) _ representation.fixedFields.gasUsed,
    observe_uint64_of_rep state (rootBase + 56) _ representation.fixedFields.timestamp,
    observe_byte_slice_of_rep state inputBase input (rootBase + 64) extraOffset extraBase _
      inputMemory extraRep,
    observe_descriptor_array_of_rep state (rootBase + 80) bases.transactionsBase _ _
      descriptors.transactions
      (fun i h => by
        obtain ⟨sliceOffset, sliceBase, sliceRep⟩ := inputSlices.transactions i h
        exact observe_byte_slice_of_rep state inputBase input _ sliceOffset sliceBase _
          inputMemory sliceRep),
    observe_descriptor_array_of_rep state (rootBase + 96) bases.withdrawalsBase _ _
      descriptors.withdrawals
      (fun i h => observe_withdrawal_value_of_rep state _ _ (allocations.withdrawalContents i h)),
    observe_uint64_of_rep state (rootBase + 112) _ representation.fixedFields.blobGasUsed,
    observe_uint64_of_rep state (rootBase + 120) _ representation.fixedFields.excessBlobGas,
    observe_byte_slice_of_rep state inputBase input (rootBase + 128) accessOffset accessBase _
      inputMemory accessRep,
    observe_uint64_of_rep state (rootBase + 144) _ representation.fixedFields.slotNumber,
    observe_byte_vector_value_of_rep state (rootBase + 152) _
      representation.fixedFields.parentHash,
    observe_byte_vector_value_of_rep state (rootBase + 184) _
      representation.fixedFields.feeRecipient,
    observe_byte_vector_value_of_rep state (rootBase + 204) _
      representation.fixedFields.stateRoot,
    observe_byte_vector_value_of_rep state (rootBase + 236) _
      representation.fixedFields.receiptsRoot,
    observe_byte_vector_value_of_rep state (rootBase + 268) _
      representation.fixedFields.logsBloom,
    observe_byte_vector_value_of_rep state (rootBase + 524) _
      representation.fixedFields.prevRandao,
    observe_byte_vector_value_of_rep state (rootBase + 556) _
      representation.fixedFields.blockHash,
    observe_descriptor_array_of_rep state (rootBase + 592) bases.versionedHashesBase _ _
      descriptors.versionedHashes
      (fun i h => observe_byte_vector_value_of_rep state _ _
        (allocations.versionedHashContents i h)),
    observe_descriptor_array_of_rep state (rootBase + 608) bases.depositsBase _ _
      descriptors.deposits
      (fun i h => observe_deposit_request_value_of_rep state _ _
        (allocations.depositContents i h)),
    observe_descriptor_array_of_rep state (rootBase + 624) bases.withdrawalRequestsBase _ _
      descriptors.withdrawalRequests
      (fun i h => observe_withdrawal_request_value_of_rep state _ _
        (allocations.withdrawalRequestContents i h)),
    observe_descriptor_array_of_rep state (rootBase + 640) bases.consolidationRequestsBase _ _
      descriptors.consolidationRequests
      (fun i h => observe_consolidation_request_value_of_rep state _ _
        (allocations.consolidationRequestContents i h)),
    observe_byte_vector_value_of_rep state (rootBase + 656) _
      representation.fixedFields.parentBeaconBlockRoot,
    observe_descriptor_array_of_rep state (rootBase + 688) bases.witnessStateBase _ _
      descriptors.witnessState
      (fun i h => by
        obtain ⟨sliceOffset, sliceBase, sliceRep⟩ := inputSlices.witnessState i h
        exact observe_byte_slice_of_rep state inputBase input _ sliceOffset sliceBase _
          inputMemory sliceRep),
    observe_descriptor_array_of_rep state (rootBase + 704) bases.witnessCodesBase _ _
      descriptors.witnessCodes
      (fun i h => by
        obtain ⟨sliceOffset, sliceBase, sliceRep⟩ := inputSlices.witnessCodes i h
        exact observe_byte_slice_of_rep state inputBase input _ sliceOffset sliceBase _
          inputMemory sliceRep),
    observe_descriptor_array_of_rep state (rootBase + 720) bases.witnessHeadersBase _ _
      descriptors.witnessHeaders
      (fun i h => by
        obtain ⟨sliceOffset, sliceBase, sliceRep⟩ := inputSlices.witnessHeaders i h
        exact observe_byte_slice_of_rep state inputBase input _ sliceOffset sliceBase _
          inputMemory sliceRep),
    observe_chain_config_of_rep state (rootBase + 736) _
      representation.fixedFields.chainConfig,
    observe_descriptor_array_of_rep state (rootBase + 816) bases.publicKeysBase _ _
      descriptors.publicKeys
      (fun i h => observe_byte_vector_value_of_rep state _ _
        (allocations.publicKeyContents i h))]
  rfl

/-- **Observer failure is impossible under the representation.** A represented value is always
observable, so `none` from `observeRawV4?` is positive evidence that the memory does *not* represent
any value — which is what lets the runner report a failed observation as `malformedResult` rather
than having to treat it as inconclusive. -/
theorem observe_raw_v4_isSome_of_rep (state : State) (inputBase : Nat) (input : ByteArray)
    (rootBase : Nat) (value : BinaryFv.Specs.SSZ.RawV4)
    (inputMemory : MemoryBytes state inputBase input)
    (representation : RawV4Rep state inputBase input rootBase value) :
    (observeRawV4? state rootBase).isSome = true := by
  rw [observe_raw_v4_of_rep state inputBase input rootBase value inputMemory representation]
  rfl

/-- **A memory state represents at most one value.** `RawV4Rep` is a big conjunction of reads, and
nothing in its *definition* says two values cannot both satisfy it — that fact comes from the
observer: both would have to equal `observeRawV4? state rootBase`, which is a function.

It matters for reading `executeDecode_accepted_of_run`, whose `value` is a premise. Without this,
"the machine accepted *the* value memory represents" is only "…*a* value memory represents", and a
second representation of the same memory would be an equally licensed answer.

The `MemoryBytes` hypothesis is inherited from `observe_raw_v4_of_rep` and cannot be dropped: the
borrowed input slices are represented by an offset into the caller's `input`, so a state that does
not hold `input` at `inputBase` does not determine their contents. -/
theorem raw_v4_rep_unique (state : State) (inputBase : Nat) (input : ByteArray) (rootBase : Nat)
    {first second : BinaryFv.Specs.SSZ.RawV4} (inputMemory : MemoryBytes state inputBase input)
    (firstRep : RawV4Rep state inputBase input rootBase first)
    (secondRep : RawV4Rep state inputBase input rootBase second) : first = second :=
  Option.some.inj
    ((observe_raw_v4_of_rep state inputBase input rootBase first inputMemory firstRep).symm.trans
      (observe_raw_v4_of_rep state inputBase input rootBase second inputMemory secondRep))

end BinaryFv.Zesu.MemoryRepresentation
