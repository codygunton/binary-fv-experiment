import BinaryFv.Ssz.Specification

/-! Typed decoder for the version-one `ZSSZ` endpoint observation stream. -/

namespace BinaryFv.Ssz

structure AccessListEntry where
  address : Array UInt8
  storageKeys : Array (Array UInt8)
  deriving BEq, Repr

structure Authorization where
  chainId : Nat
  address : Array UInt8
  nonce : Nat
  v : Nat
  r : Nat
  s : Nat
  deriving BEq, Repr

structure Transaction where
  txType : Nat
  chainId : Option Nat
  nonce : Nat
  gasPrice : Nat
  gasPriorityFee : Option Nat
  gasLimit : Nat
  recipient : Option (Array UInt8)
  value : Nat
  data : Array UInt8
  accessList : Array AccessListEntry
  blobHashes : Array (Array UInt8)
  maxFeePerBlobGas : Nat
  authorizations : Array Authorization
  v : Nat
  r : Nat
  s : Nat
  deriving BEq, Repr

structure Withdrawal where
  index : Nat
  validatorIndex : Nat
  address : Array UInt8
  amount : Nat
  deriving BEq, Repr

structure ExecutionPayload where
  parentHash : Array UInt8
  feeRecipient : Array UInt8
  stateRoot : Array UInt8
  receiptsRoot : Array UInt8
  logsBloom : Array UInt8
  prevRandao : Array UInt8
  blockNumber : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : Array UInt8
  baseFeePerGas : Nat
  blockHash : Array UInt8
  transactions : Array Transaction
  rawTransactions : Array (Array UInt8)
  withdrawals : Array Withdrawal
  blobGasUsed : Nat
  excessBlobGas : Nat
  slotNumber : Option Nat
  blockAccessList : Array UInt8
  deriving BEq, Repr

structure ExecutionRequests where
  deposits : Array UInt8
  withdrawals : Array UInt8
  consolidations : Array UInt8
  builderDeposits : Array UInt8
  builderExits : Array UInt8
  deriving BEq, Repr

structure ChainConfig where
  chainId : Nat
  forkName : Option (Array UInt8)
  activeForkIndex : Nat
  activationBlock : Option Nat
  activationTimestamp : Option Nat
  deriving BEq, Repr

structure ZesuDecodedResult where
  payload : ExecutionPayload
  parentBeaconBlockRoot : Array UInt8
  versionedHashes : Array (Array UInt8)
  executionRequests : ExecutionRequests
  witnessNodes : Array (Array UInt8)
  witnessCodes : Array (Array UInt8)
  witnessHeaders : Array (Array UInt8)
  chainConfig : ChainConfig
  publicKeys : Array (Array UInt8)
  deriving BEq, Repr

inductive ZesuObservation where
  | failure
  | success (decoded : ZesuDecodedResult)
  deriving BEq, Repr

private abbrev Parser (α : Type) := StateT Nat Option α

private def take (input : Array UInt8) (count : Nat) : Parser (Array UInt8) := fun position =>
  if position + count ≤ input.size then
    some (input.extract position (position + count), position + count)
  else
    none

private def littleEndian : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * littleEndian rest

private def unsigned (input : Array UInt8) (width : Nat) : Parser Nat := do
  pure (littleEndian (← take input width).toList)

private def byte (input : Array UInt8) : Parser Nat := unsigned input 1
private def u64 (input : Array UInt8) : Parser Nat := unsigned input 8
private def u128 (input : Array UInt8) : Parser Nat := unsigned input 16
private def u256 (input : Array UInt8) : Parser Nat := unsigned input 32

private def bytes (input : Array UInt8) : Parser (Array UInt8) := do
  take input (← u64 input)

private def optional (input : Array UInt8) (value : Parser α) : Parser (Option α) := do
  match ← byte input with
  | 0 => pure none
  | 1 => pure (some (← value))
  | _ => failure

private def many (input : Array UInt8) (value : Parser α) : Parser (Array α) := do
  let count ← u64 input
  let mut result := #[]
  for _ in [0:count] do
    result := result.push (← value)
  pure result

private def fixedMany (input : Array UInt8) (width : Nat) : Parser (Array (Array UInt8)) :=
  many input (take input width)

private def parseAccessListEntry (input : Array UInt8) : Parser AccessListEntry := do
  pure { address := ← take input 20, storageKeys := ← fixedMany input 32 }

private def parseAuthorization (input : Array UInt8) : Parser Authorization := do
  pure {
    chainId := ← u256 input
    address := ← take input 20
    nonce := ← u64 input
    v := ← u64 input
    r := ← u256 input
    s := ← u256 input
  }

private def parseTransaction (input : Array UInt8) : Parser Transaction := do
  pure {
    txType := ← byte input
    chainId := ← optional input (u64 input)
    nonce := ← u64 input
    gasPrice := ← u128 input
    gasPriorityFee := ← optional input (u128 input)
    gasLimit := ← u64 input
    recipient := ← optional input (take input 20)
    value := ← u256 input
    data := ← bytes input
    accessList := ← many input (parseAccessListEntry input)
    blobHashes := ← fixedMany input 32
    maxFeePerBlobGas := ← u128 input
    authorizations := ← many input (parseAuthorization input)
    v := ← u64 input
    r := ← u256 input
    s := ← u256 input
  }

private def parseWithdrawal (input : Array UInt8) : Parser Withdrawal := do
  pure {
    index := ← u64 input
    validatorIndex := ← u64 input
    address := ← take input 20
    amount := ← u64 input
  }

private def parsePayload (input : Array UInt8) : Parser ExecutionPayload := do
  pure {
    parentHash := ← take input 32
    feeRecipient := ← take input 20
    stateRoot := ← take input 32
    receiptsRoot := ← take input 32
    logsBloom := ← take input 256
    prevRandao := ← take input 32
    blockNumber := ← u64 input
    gasLimit := ← u64 input
    gasUsed := ← u64 input
    timestamp := ← u64 input
    extraData := ← bytes input
    baseFeePerGas := ← u64 input
    blockHash := ← take input 32
    transactions := ← many input (parseTransaction input)
    rawTransactions := ← many input (bytes input)
    withdrawals := ← many input (parseWithdrawal input)
    blobGasUsed := ← u64 input
    excessBlobGas := ← u64 input
    slotNumber := ← optional input (u64 input)
    blockAccessList := ← bytes input
  }

private def parseRequests (input : Array UInt8) : Parser ExecutionRequests := do
  pure {
    deposits := ← bytes input
    withdrawals := ← bytes input
    consolidations := ← bytes input
    builderDeposits := ← bytes input
    builderExits := ← bytes input
  }

private def parseChainConfig (input : Array UInt8) : Parser ChainConfig := do
  pure {
    chainId := ← u64 input
    forkName := ← optional input (bytes input)
    activeForkIndex := ← u64 input
    activationBlock := ← optional input (u64 input)
    activationTimestamp := ← optional input (u64 input)
  }

private def parseSuccess (input : Array UInt8) : Parser ZesuDecodedResult := do
  pure {
    payload := ← parsePayload input
    parentBeaconBlockRoot := ← take input 32
    versionedHashes := ← fixedMany input 32
    executionRequests := ← parseRequests input
    witnessNodes := ← many input (bytes input)
    witnessCodes := ← many input (bytes input)
    witnessHeaders := ← many input (bytes input)
    chainConfig := ← parseChainConfig input
    publicKeys := ← many input (bytes input)
  }

/-- Parse exactly one complete version-one endpoint observation. -/
def decodeZesuObservation (input : Array UInt8) : Option ZesuObservation := do
  let header := input.extract 0 5
  guard (header == #[0x5a, 0x53, 0x53, 0x5a, 0x01])
  let parser : Parser ZesuObservation := do
    set 5
    match ← byte input with
    | 0 => pure ZesuObservation.failure
    | 1 => pure (ZesuObservation.success (← parseSuccess input))
    | _ => failure
  let (observation, position) ← parser.run 0
  guard (position = input.size)
  pure observation

end BinaryFv.Ssz
