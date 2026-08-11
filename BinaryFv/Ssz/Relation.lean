import BinaryFv.Ssz.ZesuObservation

/-! The common decoded-result surface shared by Zesu and EVM-Sail. -/

namespace BinaryFv.Ssz

def sailSliceBytes (source : Array UInt8) : Evm.Defs.StatelessInputSlice → Array UInt8
  | ⟨offset, ⟨length, _⟩⟩ => source.extract offset (offset + length)

private def listMatches (relation : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | left :: lefts, right :: rights => relation left right && listMatches relation lefts rights
  | _, _ => false

private def arrayRel (relation : α → β → Bool) (left : Array α) (right : Array β) : Prop :=
  listMatches relation left.toList right.toList = true

private def sailBytes (bytes : Array Evm.Defs.byte) : Array UInt8 :=
  bytes.map fun byte => UInt8.ofNat byte.toNat

private def littleEndianNat : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * littleEndianNat rest

private def txTypeCode : Evm.Defs.TxType → Nat
  | .LegacyTx => 0
  | .AccessListTx => 1
  | .FeeMarketTx => 2
  | .BlobTx => 3
  | .SetCodeTx => 4

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

/-- The only successful-result normalization currently admitted: Zesu maps an encoded chain id of
zero to one, while EVM-Sail retains zero. Other `KnownBug` cases concern accept/reject domains. -/
def decodedResultRelModuloKnownBugs (source : Array UInt8) (zesu : ZesuDecodedResult)
    (sail : SailDecoded) : Prop :=
  decodedResultRelExceptChainId source zesu sail ∧
  (zesu.chainConfig.chainId = sail.input.chain_config.chain_id ∨
    (sail.input.chain_config.chain_id = 0 ∧ zesu.chainConfig.chainId = 1))

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

end BinaryFv.Ssz
