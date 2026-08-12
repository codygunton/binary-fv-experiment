import BinaryFv.Zesu.DecodedValue.Observers

/-! Pure Lean definition of the version-one `ZSSZ` observation encoding emitted by Zesu. -/

namespace BinaryFv.Zesu

def encodeNatLE : Nat → Nat → Array UInt8
  | 0, _ => #[]
  | width + 1, value => #[UInt8.ofNat value] ++ encodeNatLE width (value / 256)

def encodeBytes (bytes : Array UInt8) : Array UInt8 :=
  encodeNatLE 8 bytes.size ++ bytes

def encodeOptional (encode : α → Array UInt8) : Option α → Array UInt8
  | none => #[0]
  | some value => #[1] ++ encode value

def encodeMany (encode : α → Array UInt8) (values : Array α) : Array UInt8 :=
  values.foldl (fun result value => result ++ encode value) (encodeNatLE 8 values.size)

def encodeAccessListEntry (entry : AccessListEntry) : Array UInt8 :=
  entry.address ++ encodeMany (fun key => key) entry.storageKeys

def encodeAuthorization (authorization : Authorization) : Array UInt8 :=
  encodeNatLE 32 authorization.chainId ++ authorization.address ++
  encodeNatLE 8 authorization.nonce ++ encodeNatLE 8 authorization.v ++
  encodeNatLE 32 authorization.r ++ encodeNatLE 32 authorization.s

def encodeTransaction (transaction : Transaction) : Array UInt8 :=
  encodeNatLE 1 transaction.txType ++ encodeOptional (encodeNatLE 8) transaction.chainId ++
  encodeNatLE 8 transaction.nonce ++ encodeNatLE 16 transaction.gasPrice ++
  encodeOptional (encodeNatLE 16) transaction.gasPriorityFee ++
  encodeNatLE 8 transaction.gasLimit ++ encodeOptional (fun address => address) transaction.recipient ++
  encodeNatLE 32 transaction.value ++ encodeBytes transaction.data ++
  encodeMany encodeAccessListEntry transaction.accessList ++
  encodeMany (fun hash => hash) transaction.blobHashes ++
  encodeNatLE 16 transaction.maxFeePerBlobGas ++
  encodeMany encodeAuthorization transaction.authorizations ++
  encodeNatLE 8 transaction.v ++ encodeNatLE 32 transaction.r ++ encodeNatLE 32 transaction.s

def encodeWithdrawal (withdrawal : Withdrawal) : Array UInt8 :=
  encodeNatLE 8 withdrawal.index ++ encodeNatLE 8 withdrawal.validatorIndex ++
  withdrawal.address ++ encodeNatLE 8 withdrawal.amount

def encodePayload (payload : ExecutionPayload) : Array UInt8 :=
  payload.parentHash ++ payload.feeRecipient ++ payload.stateRoot ++ payload.receiptsRoot ++
  payload.logsBloom ++ payload.prevRandao ++ encodeNatLE 8 payload.blockNumber ++
  encodeNatLE 8 payload.gasLimit ++ encodeNatLE 8 payload.gasUsed ++
  encodeNatLE 8 payload.timestamp ++ encodeBytes payload.extraData ++
  encodeNatLE 8 payload.baseFeePerGas ++ payload.blockHash ++
  encodeMany encodeTransaction payload.transactions ++ encodeMany encodeBytes payload.rawTransactions ++
  encodeMany encodeWithdrawal payload.withdrawals ++ encodeNatLE 8 payload.blobGasUsed ++
  encodeNatLE 8 payload.excessBlobGas ++ encodeOptional (encodeNatLE 8) payload.slotNumber ++
  encodeBytes payload.blockAccessList

def encodeRequests (requests : ExecutionRequests) : Array UInt8 :=
  encodeBytes requests.deposits ++ encodeBytes requests.withdrawals ++
  encodeBytes requests.consolidations ++ encodeBytes requests.builderDeposits ++
  encodeBytes requests.builderExits

def encodeChainConfig (config : ChainConfig) : Array UInt8 :=
  encodeNatLE 8 config.chainId ++ encodeOptional encodeBytes config.forkName ++
  encodeNatLE 8 config.activeForkIndex ++ encodeOptional (encodeNatLE 8) config.activationBlock ++
  encodeOptional (encodeNatLE 8) config.activationTimestamp

def encodeZesuDecodedResult (decoded : ZesuDecodedResult) : Array UInt8 :=
  encodePayload decoded.payload ++ decoded.parentBeaconBlockRoot ++
  encodeMany (fun hash => hash) decoded.versionedHashes ++ encodeRequests decoded.executionRequests ++
  encodeMany encodeBytes decoded.witnessNodes ++ encodeMany encodeBytes decoded.witnessCodes ++
  encodeMany encodeBytes decoded.witnessHeaders ++ encodeChainConfig decoded.chainConfig ++
  encodeMany encodeBytes decoded.publicKeys

def encodeZesuObservation : ZesuObservation → Array UInt8
  | .failure => #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x00]
  | .success decoded =>
      #[0x5a, 0x53, 0x53, 0x5a, 0x01, 0x01] ++ encodeZesuDecodedResult decoded

end BinaryFv.Zesu
