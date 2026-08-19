import BinaryFv.Zesu.DecodedValue.Observers
import BinaryFv.Zesu.Contracts.KnownBugs

/-! The common decoded-result surface shared by Zesu and EVM-Sail. -/

namespace BinaryFv.Zesu

open BinaryFv.Specs.SSZ

def sailSliceBytes (source : Array UInt8) : Evm.Defs.StatelessInputSlice → Array UInt8
  | ⟨offset, ⟨length, _⟩⟩ => source.extract offset (offset + length)

private def listMatches (relation : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | left :: lefts, right :: rights => relation left right && listMatches relation lefts rights
  | _, _ => false

private theorem listMatches_eq_true_iff_map_eq (relation : α → β → Bool)
    (leftMap : α → γ) (rightMap : β → γ)
    (related : ∀ left right, relation left right = true ↔ leftMap left = rightMap right) :
    ∀ left right, listMatches relation left right = true ↔
      left.map leftMap = right.map rightMap
  | [], [] => by simp [listMatches]
  | [], _ :: _ => by simp [listMatches]
  | _ :: _, [] => by simp [listMatches]
  | left :: lefts, right :: rights => by
      simp [listMatches, related, listMatches_eq_true_iff_map_eq relation leftMap rightMap related]

private def arrayRel (relation : α → β → Bool) (left : Array α) (right : Array β) : Prop :=
  listMatches relation left.toList right.toList = true

def sailBytes (bytes : Array Evm.Defs.byte) : Array UInt8 :=
  bytes.map fun byte => UInt8.ofNat byte.toNat

def littleEndianNat : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * littleEndianNat rest

private def txTypeCode : Evm.Defs.TxType → Nat
  | .LegacyTx => 0
  | .AccessListTx => 1
  | .FeeMarketTx => 2
  | .BlobTx => 3
  | .SetCodeTx => 4

structure CanonicalTransaction where
  txType : Nat
  chainId : Option Nat
  nonce : Nat
  gasLimit : Nat
  recipient : Option (Array UInt8)
  value : Nat
  data : Array UInt8
  gasPrice : Nat
  maxFeePerBlobGas : Nat
  v : Nat
  r : Nat
  s : Nat
  deriving BEq, DecidableEq, Repr

structure CanonicalWithdrawal where
  index : Nat
  validatorIndex : Nat
  address : Array UInt8
  amount : Nat
  deriving BEq, DecidableEq, Repr

structure CanonicalPayload where
  parentHash : Array UInt8
  feeRecipient : Array UInt8
  stateRoot : Array UInt8
  receiptsRoot : Array UInt8
  logsBloom : Array UInt8
  prevRandao : Nat
  blockNumber : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : Array UInt8
  baseFeePerGas : Nat
  blockHash : Array UInt8
  transactions : List CanonicalTransaction
  rawTransactions : List (Array UInt8)
  withdrawals : List CanonicalWithdrawal
  blobGasUsed : Nat
  excessBlobGas : Nat
  slotNumber : Option Nat
  blockAccessList : Array UInt8
  deriving BEq, DecidableEq, Repr

/-- The fields decoded by both Zesu and EVM-Sail. Fields outside this structure are not part of the
reviewed common-output relation. -/
structure CanonicalDecodedResult where
  payload : CanonicalPayload
  parentBeaconBlockRoot : Array UInt8
  versionedHashes : List (Array UInt8)
  deposits : Array UInt8
  withdrawalRequests : Array UInt8
  consolidations : Array UInt8
  builderDeposits : Array UInt8
  builderExits : Array UInt8
  witnessNodes : List (Array UInt8)
  witnessCodes : List (Array UInt8)
  witnessHeaders : List (Array UInt8)
  publicKeys : List (Array UInt8)
  chainId : Nat
  deriving BEq, DecidableEq, Repr

def canonicalTransactionOfZesu (transaction : Transaction) : CanonicalTransaction := {
  txType := transaction.txType
  chainId := transaction.chainId
  nonce := transaction.nonce
  gasLimit := transaction.gasLimit
  recipient := transaction.recipient
  value := transaction.value
  data := transaction.data
  gasPrice := transaction.gasPrice
  maxFeePerBlobGas := transaction.maxFeePerBlobGas
  v := transaction.v
  r := transaction.r
  s := transaction.s
}

def canonicalTransactionOfSail (source : Array UInt8) :
    Evm.Defs.Transaction → CanonicalTransaction
  | ⟨_, fields⟩ => {
      txType := txTypeCode fields.tx_type
      chainId := some fields.chain_id
      nonce := fields.nonce
      gasLimit := fields.gas_limit
      recipient := if fields.is_create then none else some (sailBytes fields.recipient.toArray)
      value := fields.value
      data := sailSliceBytes source fields.input_src
      gasPrice := fields.max_fee
      maxFeePerBlobGas := fields.max_blob_fee
      v := fields.sig_v
      r := fields.sig_r
      s := fields.sig_s
    }

def canonicalWithdrawalOfZesu (withdrawal : Withdrawal) : CanonicalWithdrawal := {
  index := withdrawal.index
  validatorIndex := withdrawal.validatorIndex
  address := withdrawal.address
  amount := withdrawal.amount
}

def canonicalWithdrawalOfSail (withdrawal : Evm.Defs.Withdrawal) : CanonicalWithdrawal := {
  index := withdrawal.index
  validatorIndex := withdrawal.validator_index
  address := sailBytes withdrawal.address.toArray
  amount := withdrawal.amount
}

def canonicalPayloadOfZesu (payload : ExecutionPayload) : CanonicalPayload := {
  parentHash := payload.parentHash
  feeRecipient := payload.feeRecipient
  stateRoot := payload.stateRoot
  receiptsRoot := payload.receiptsRoot
  logsBloom := payload.logsBloom
  prevRandao := littleEndianNat payload.prevRandao.toList
  blockNumber := payload.blockNumber
  gasLimit := payload.gasLimit
  gasUsed := payload.gasUsed
  timestamp := payload.timestamp
  extraData := payload.extraData
  baseFeePerGas := payload.baseFeePerGas
  blockHash := payload.blockHash
  transactions := payload.transactions.toList.map canonicalTransactionOfZesu
  rawTransactions := payload.rawTransactions.toList
  withdrawals := payload.withdrawals.toList.map canonicalWithdrawalOfZesu
  blobGasUsed := payload.blobGasUsed
  excessBlobGas := payload.excessBlobGas
  slotNumber := payload.slotNumber
  blockAccessList := payload.blockAccessList
}

def canonicalPayloadOfSail (source : Array UInt8) (decoded : SailDecoded) : CanonicalPayload :=
  let payload := decoded.input.payload
  let header := payload.block'.header
  {
    parentHash := sailBytes header.parent_hash.toArray
    feeRecipient := sailBytes header.fee_recipient.toArray
    stateRoot := sailBytes header.state_root.toArray
    receiptsRoot := sailBytes header.receipts_root.toArray
    logsBloom := sailSliceBytes source header.logs_bloom
    prevRandao := header.prev_randao
    blockNumber := header.number
    gasLimit := header.gas_limit
    gasUsed := header.gas_used
    timestamp := header.timestamp
    extraData := sailSliceBytes source header.extra_data
    baseFeePerGas := header.base_fee
    blockHash := sailBytes payload.expected_block_hash.toArray
    transactions := decoded.transactions.toList.map (canonicalTransactionOfSail source)
    rawTransactions := decoded.rawTransactions.toList.map (sailSliceBytes source)
    withdrawals := decoded.withdrawals.toList.map canonicalWithdrawalOfSail
    blobGasUsed := header.blob_gas_used
    excessBlobGas := header.excess_blob_gas
    slotNumber := some header.slot_number
    blockAccessList := sailSliceBytes source decoded.inputRef.block_access_list
  }

def CanonicalDecodedResult.ofZesu (decoded : ZesuDecodedResult) : CanonicalDecodedResult := {
  payload := canonicalPayloadOfZesu decoded.payload
  parentBeaconBlockRoot := decoded.parentBeaconBlockRoot
  versionedHashes := decoded.versionedHashes.toList
  deposits := decoded.executionRequests.deposits
  withdrawalRequests := decoded.executionRequests.withdrawals
  consolidations := decoded.executionRequests.consolidations
  builderDeposits := decoded.executionRequests.builderDeposits
  builderExits := decoded.executionRequests.builderExits
  witnessNodes := decoded.witnessNodes.toList
  witnessCodes := decoded.witnessCodes.toList
  witnessHeaders := decoded.witnessHeaders.toList
  publicKeys := decoded.publicKeys.toList
  chainId := decoded.chainConfig.chainId
}

def CanonicalDecodedResult.ofEvmSail (source : Array UInt8)
    (decoded : SailDecoded) : CanonicalDecodedResult := {
  payload := canonicalPayloadOfSail source decoded
  parentBeaconBlockRoot := sailBytes decoded.input.payload.block'.header.parent_beacon_block_root.toArray
  versionedHashes := decoded.versionedHashes.toList.map (sailSliceBytes source)
  deposits := sailSliceBytes source decoded.inputRef.deposits
  withdrawalRequests := sailSliceBytes source decoded.inputRef.withdrawal_requests
  consolidations := sailSliceBytes source decoded.inputRef.consolidation_requests
  builderDeposits := sailSliceBytes source decoded.inputRef.builder_deposit_requests
  builderExits := sailSliceBytes source decoded.inputRef.builder_exit_requests
  witnessNodes := decoded.witnessNodes.toList.map (sailSliceBytes source)
  witnessCodes := decoded.witnessCodes.toList.map (sailSliceBytes source)
  witnessHeaders := decoded.witnessHeaders.toList.map (sailSliceBytes source)
  publicKeys := decoded.publicKeys.toList.map (sailSliceBytes source)
  chainId := decoded.input.chain_config.chain_id
}

private def recipientMatches (transaction : Transaction)
    (fields : Evm.Defs.TransactionFields limit) : Bool :=
  if fields.is_create then
    transaction.recipient.isNone
  else
    transaction.recipient == some (sailBytes fields.recipient.toArray)

/-- Fields decoded by both transaction implementations. Sender recovery and the
EVM-Sail signing hash are deliberately outside this relation. -/
def transactionMatches (source : Array UInt8) (transaction : Transaction) : Evm.Defs.Transaction → Bool
  | ⟨_, fields⟩ =>
      transaction.txType == txTypeCode fields.tx_type &&
      transaction.chainId == some fields.chain_id &&
      transaction.nonce == fields.nonce &&
      transaction.gasLimit == fields.gas_limit &&
      recipientMatches transaction fields &&
      transaction.value == fields.value &&
      transaction.data == sailSliceBytes source fields.input_src &&
      transaction.gasPrice == fields.max_fee &&
      transaction.maxFeePerBlobGas == fields.max_blob_fee &&
      transaction.v == fields.sig_v &&
      transaction.r == fields.sig_r &&
      transaction.s == fields.sig_s

private def withdrawalMatches (withdrawal : Withdrawal) (reference : Evm.Defs.Withdrawal) : Bool :=
  withdrawal.index == reference.index &&
  withdrawal.validatorIndex == reference.validator_index &&
  withdrawal.address == sailBytes reference.address.toArray &&
  withdrawal.amount == reference.amount

private theorem transactionMatches_eq_true_iff (source : Array UInt8)
    (transaction : Transaction) (reference : Evm.Defs.Transaction) :
    transactionMatches source transaction reference = true ↔
      canonicalTransactionOfZesu transaction = canonicalTransactionOfSail source reference := by
  cases reference
  simp [transactionMatches, canonicalTransactionOfZesu, canonicalTransactionOfSail,
    recipientMatches] <;> grind

private theorem withdrawalMatches_eq_true_iff (withdrawal : Withdrawal)
    (reference : Evm.Defs.Withdrawal) :
    withdrawalMatches withdrawal reference = true ↔
      canonicalWithdrawalOfZesu withdrawal = canonicalWithdrawalOfSail reference := by
  simp [withdrawalMatches, canonicalWithdrawalOfZesu, canonicalWithdrawalOfSail] <;> grind

private theorem bytesMatch_eq_true_iff (source : Array UInt8) (bytes : Array UInt8)
    (slice : Evm.Defs.StatelessInputSlice) :
    (bytes == sailSliceBytes source slice) = true ↔ bytes = sailSliceBytes source slice := by
  simp

private theorem arrayRel_iff_map_eq (relation : α → β → Bool)
    (leftMap : α → γ) (rightMap : β → γ)
    (related : ∀ left right, relation left right = true ↔ leftMap left = rightMap right)
    (left : Array α) (right : Array β) :
    arrayRel relation left right ↔ left.toList.map leftMap = right.toList.map rightMap := by
  exact listMatches_eq_true_iff_map_eq relation leftMap rightMap related left.toList right.toList

private def payloadRel (source : Array UInt8) (zesu : ExecutionPayload)
    (sail : SailDecoded) : Prop :=
  let payload := sail.input.payload
  let header := payload.block'.header
  zesu.parentHash = sailBytes header.parent_hash.toArray ∧
  zesu.feeRecipient = sailBytes header.fee_recipient.toArray ∧
  zesu.stateRoot = sailBytes header.state_root.toArray ∧
  zesu.receiptsRoot = sailBytes header.receipts_root.toArray ∧
  zesu.logsBloom = sailSliceBytes source header.logs_bloom ∧
  littleEndianNat zesu.prevRandao.toList = header.prev_randao ∧
  zesu.blockNumber = header.number ∧
  zesu.gasLimit = header.gas_limit ∧
  zesu.gasUsed = header.gas_used ∧
  zesu.timestamp = header.timestamp ∧
  zesu.extraData = sailSliceBytes source header.extra_data ∧
  zesu.baseFeePerGas = header.base_fee ∧
  zesu.blockHash = sailBytes payload.expected_block_hash.toArray ∧
  arrayRel (transactionMatches source) zesu.transactions sail.transactions ∧
  arrayRel (fun bytes slice => bytes == sailSliceBytes source slice)
    zesu.rawTransactions sail.rawTransactions ∧
  arrayRel withdrawalMatches zesu.withdrawals sail.withdrawals ∧
  zesu.blobGasUsed = header.blob_gas_used ∧
  zesu.excessBlobGas = header.excess_blob_gas ∧
  zesu.slotNumber = some header.slot_number ∧
  zesu.blockAccessList = sailSliceBytes source sail.inputRef.block_access_list

private theorem payloadRel_iff_canonical_eq (source : Array UInt8)
    (zesu : ExecutionPayload) (sail : SailDecoded) :
    payloadRel source zesu sail ↔
      canonicalPayloadOfZesu zesu = canonicalPayloadOfSail source sail := by
  simp only [payloadRel, canonicalPayloadOfZesu, canonicalPayloadOfSail,
    CanonicalPayload.mk.injEq]
  rw [arrayRel_iff_map_eq (transactionMatches source) canonicalTransactionOfZesu
      (canonicalTransactionOfSail source) (transactionMatches_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq withdrawalMatches canonicalWithdrawalOfZesu
      canonicalWithdrawalOfSail withdrawalMatches_eq_true_iff]
  simp only [List.map_id]

/-- Exact common output relation before applying any reviewed `KnownBug` clause.
Witness elements are compared only as byte strings; no RLP/MPT interpretation is claimed. -/
private def decodedResultRelExceptChainId (source : Array UInt8) (zesu : ZesuDecodedResult)
    (sail : SailDecoded) : Prop :=
  payloadRel source zesu.payload sail ∧
  zesu.parentBeaconBlockRoot =
    sailBytes sail.input.payload.block'.header.parent_beacon_block_root.toArray ∧
  arrayRel (fun bytes slice => bytes == sailSliceBytes source slice)
    zesu.versionedHashes sail.versionedHashes ∧
  zesu.executionRequests.deposits = sailSliceBytes source sail.inputRef.deposits ∧
  zesu.executionRequests.withdrawals = sailSliceBytes source sail.inputRef.withdrawal_requests ∧
  zesu.executionRequests.consolidations = sailSliceBytes source sail.inputRef.consolidation_requests ∧
  zesu.executionRequests.builderDeposits = sailSliceBytes source sail.inputRef.builder_deposit_requests ∧
  zesu.executionRequests.builderExits = sailSliceBytes source sail.inputRef.builder_exit_requests ∧
  arrayRel (fun bytes slice => bytes == sailSliceBytes source slice) zesu.witnessNodes sail.witnessNodes ∧
  arrayRel (fun bytes slice => bytes == sailSliceBytes source slice) zesu.witnessCodes sail.witnessCodes ∧
  arrayRel (fun bytes slice => bytes == sailSliceBytes source slice) zesu.witnessHeaders sail.witnessHeaders ∧
  arrayRel (fun bytes slice => bytes == sailSliceBytes source slice) zesu.publicKeys sail.publicKeys

def decodedResultRel (source : Array UInt8) (zesu : ZesuDecodedResult)
    (sail : SailDecoded) : Prop :=
  decodedResultRelExceptChainId source zesu sail ∧
  zesu.chainConfig.chainId = sail.input.chain_config.chain_id

theorem decodedResultRel_iff_canonical_eq (source : Array UInt8) (zesu : ZesuDecodedResult)
    (sail : SailDecoded) :
    decodedResultRel source zesu sail ↔
      CanonicalDecodedResult.ofZesu zesu = CanonicalDecodedResult.ofEvmSail source sail := by
  simp only [decodedResultRel, decodedResultRelExceptChainId, CanonicalDecodedResult.ofZesu,
    CanonicalDecodedResult.ofEvmSail, CanonicalDecodedResult.mk.injEq]
  rw [payloadRel_iff_canonical_eq]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  simp only [List.map_id]
  grind

/-- The only successful-result normalization currently admitted: Zesu maps an encoded chain id of
zero to one, while EVM-Sail retains zero. Other `KnownBug` cases concern accept/reject domains. -/
def decodedResultRelModuloKnownBugs (source : Array UInt8) (zesu : ZesuDecodedResult)
    (sail : SailDecoded) : Prop :=
  decodedResultRelExceptChainId source zesu sail ∧
  (zesu.chainConfig.chainId = sail.input.chain_config.chain_id ∨
    (sail.input.chain_config.chain_id = 0 ∧ zesu.chainConfig.chainId = 1))

/-- Canonicalize the one reviewed successful-result divergence on either decoder's own value. -/
def CanonicalDecodedResult.normalizeKnownBugs
    (decoded : CanonicalDecodedResult) : CanonicalDecodedResult :=
  { decoded with chainId := if decoded.chainId = 1 then 0 else decoded.chainId }

theorem normalized_eq_of_decodedResultRelModuloKnownBugs
    (source : Array UInt8) (zesu : ZesuDecodedResult) (sail : SailDecoded) :
    decodedResultRelModuloKnownBugs source zesu sail →
      (CanonicalDecodedResult.ofZesu zesu).normalizeKnownBugs =
        (CanonicalDecodedResult.ofEvmSail source sail).normalizeKnownBugs := by
  simp only [decodedResultRelModuloKnownBugs, decodedResultRelExceptChainId,
    CanonicalDecodedResult.normalizeKnownBugs, CanonicalDecodedResult.ofZesu,
    CanonicalDecodedResult.ofEvmSail, CanonicalDecodedResult.mk.injEq]
  rw [payloadRel_iff_canonical_eq]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  rw [arrayRel_iff_map_eq (fun bytes slice => bytes == sailSliceBytes source slice) id
      (sailSliceBytes source) (bytesMatch_eq_true_iff source)]
  simp only [List.map_id]
  grind

private def readU32LEAt (input : Array UInt8) (offset : Nat) : Option Nat := do
  let byte0 ← input[offset]?
  let byte1 ← input[offset + 1]?
  let byte2 ← input[offset + 2]?
  let byte3 ← input[offset + 3]?
  pure (byte0.toNat + 256 * byte1.toNat + 65536 * byte2.toNat +
    16777216 * byte3.toNat)

private def semanticPayload (source : Array UInt8) : Array UInt8 :=
  (stripErePrefix source).getD source

/-- The request-table arity encoded by Zesu's reviewed v0.4.1 outer layout. -/
def encodedRequestTypeCount (source : Array UInt8) : Option Nat := do
  let payload := semanticPayload source
  let newPayloadOffset ← readU32LEAt payload 2
  let requestsOffset ← readU32LEAt payload (2 + newPayloadOffset + 40)
  let fixedSize ← readU32LEAt payload (2 + newPayloadOffset + requestsOffset)
  if fixedSize % 4 = 0 then some (fixedSize / 4) else none

/--
The exact reviewed input/result condition for each compatibility exception.

The five result-shaped clauses use fields emitted by the injective observation. The legacy request
clause additionally reads only the three offsets needed to identify the old fixed table; it is not a
second SSZ decoder. Chain-id normalization is handled by `decodedResultRelModuloKnownBugs` and is
therefore not an accept/reject-domain exception.
-/
def KnownBugApplies (source : Array UInt8) (zesu : ZesuDecodedResult) : KnownBug → Prop
  | .chainIdZeroNormalization => False
  | .legacyRequestTableArity => encodedRequestTypeCount source = some 3
  | .legacyPayloadSize => zesu.payload.slotNumber = none
  | .futureForkActivation =>
      match zesu.chainConfig.activationBlock with
      | some activation => zesu.payload.blockNumber < activation
      | none => False
  | .extraDataLength => 32 < zesu.payload.extraData.size
  | .publicKeyCount => 32768 < zesu.publicKeys.size
  | .versionedHashCount => 4096 < zesu.versionedHashes.size

instance (source : Array UInt8) (zesu : ZesuDecodedResult) (bug : KnownBug) :
    Decidable (KnownBugApplies source zesu bug) := by
  cases bug <;> simp only [KnownBugApplies] <;> try infer_instance
  cases zesu.chainConfig.activationBlock <;> infer_instance

/-- None of the six reviewed accept/reject-domain divergences applies to this decoded value. -/
def AvoidsReviewedDomainDivergences (source : Array UInt8)
    (zesu : ZesuDecodedResult) : Prop :=
  ∀ bug ∈ knownBugs, ¬KnownBugApplies source zesu bug

instance (source : Array UInt8) (zesu : ZesuDecodedResult) (sail : SailDecoded) :
    Decidable (decodedResultRel source zesu sail) := by
  unfold decodedResultRel decodedResultRelExceptChainId payloadRel transactionMatches recipientMatches
    withdrawalMatches arrayRel
  infer_instance

instance (source : Array UInt8) (zesu : ZesuDecodedResult) (sail : SailDecoded) :
    Decidable (decodedResultRelModuloKnownBugs source zesu sail) := by
  unfold decodedResultRelModuloKnownBugs decodedResultRelExceptChainId payloadRel transactionMatches
    recipientMatches withdrawalMatches arrayRel
  infer_instance

end BinaryFv.Zesu
