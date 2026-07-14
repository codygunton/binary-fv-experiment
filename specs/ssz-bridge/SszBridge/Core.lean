import SizzLean.Spec.Deserialize
import SizzLean.Spec.Serialize

/-!
# Amsterdam V4 SSZ bridge

This executable bridge delegates SSZ decoding to the pinned SizzLean package.
It owns only the outer schema identifier, raw/Ere framing, a canonical-wire
wrapper, and a lossless named projection boundary.  V3 is deliberately
quarantined: no V3 value is emitted because this project has no independently
pinned V3 oracle.

SizzLean's executable decoder accepts one non-canonical variable-list alias
(`00 00 00 00` for an empty `List[ByteList]`).  `decodeCanonical` closes that
gap by requiring exact reserialization after decoding.

-/

namespace SszBridge

open SizzLean.Spec

abbrev u8 : SSZType := .uintN 8
abbrev u64 : SSZType := .uintN 64
abbrev u256 : SSZType := .uintN 256

abbrev byteVector (length : Nat) : SSZType := .vector u8 length
abbrev byteList (capacity : Nat) : SSZType := .list u8 capacity

def maxExtraDataBytes : Nat := 32
def maxBytesPerTransaction : Nat := 2 ^ 30
def maxTransactionsPerPayload : Nat := 2 ^ 20
def maxWithdrawalsPerPayload : Nat := 2 ^ 4
def maxBlobCommitmentsPerBlock : Nat := 4096
def maxDepositRequestsPerPayload : Nat := 2 ^ 13
def maxWithdrawalRequestsPerPayload : Nat := 2 ^ 4
def maxConsolidationRequestsPerPayload : Nat := 2 ^ 1
def maxWitnessNodes : Nat := 2 ^ 22
def maxWitnessCodes : Nat := 2 ^ 18
def maxWitnessHeaders : Nat := 256
def maxBytesPerWitnessNode : Nat := 2 ^ 10
def maxBytesPerCode : Nat := 2 ^ 16
def maxBytesPerHeader : Nat := 2 ^ 10
def maxOptionalForkActivationValues : Nat := 1
def maxBlobSchedulesPerFork : Nat := 1
def maxPublicKeys : Nat := 2 ^ 15
def publicKeyBytes : Nat := 65

def withdrawalType : SSZType :=
  .container [u64, u64, byteVector 20, u64]

def executionPayloadType : SSZType :=
  .container [
    byteVector 32,
    byteVector 20,
    byteVector 32,
    byteVector 32,
    byteVector 256,
    byteVector 32,
    u64,
    u64,
    u64,
    u64,
    byteList maxExtraDataBytes,
    u256,
    byteVector 32,
    .list (byteList maxBytesPerTransaction) maxTransactionsPerPayload,
    .list withdrawalType maxWithdrawalsPerPayload,
    u64,
    u64,
    byteList maxBytesPerTransaction,
    u64,
  ]

def depositRequestType : SSZType :=
  .container [byteVector 48, byteVector 32, u64, byteVector 96, u64]

def withdrawalRequestType : SSZType :=
  .container [byteVector 20, byteVector 48, u64]

def consolidationRequestType : SSZType :=
  .container [byteVector 20, byteVector 48, byteVector 48]

def executionRequestsType : SSZType :=
  .container [
    .list depositRequestType maxDepositRequestsPerPayload,
    .list withdrawalRequestType maxWithdrawalRequestsPerPayload,
    .list consolidationRequestType maxConsolidationRequestsPerPayload,
  ]

def newPayloadRequestType : SSZType :=
  .container [
    executionPayloadType,
    .list (byteVector 32) maxBlobCommitmentsPerBlock,
    byteVector 32,
    executionRequestsType,
  ]

def witnessType : SSZType :=
  .container [
    .list (byteList maxBytesPerWitnessNode) maxWitnessNodes,
    .list (byteList maxBytesPerCode) maxWitnessCodes,
    .list (byteList maxBytesPerHeader) maxWitnessHeaders,
  ]

def forkActivationType : SSZType :=
  .container [
    .list u64 maxOptionalForkActivationValues,
    .list u64 maxOptionalForkActivationValues,
  ]

def blobScheduleType : SSZType :=
  .container [u64, u64, u64]

def forkConfigType : SSZType :=
  .container [
    u64,
    forkActivationType,
    .list blobScheduleType maxBlobSchedulesPerFork,
  ]

def chainConfigType : SSZType :=
  .container [u64, forkConfigType]

/-- The complete pinned Amsterdam V4 `SszStatelessInput` body schema. -/
def statelessInputV4Type : SSZType :=
  .container [
    newPayloadRequestType,
    witnessType,
    chainConfigType,
    .list (byteVector publicKeyBytes) maxPublicKeys,
  ]

inductive BridgeError where
  | tooLarge
  | tooShort
  | badSchema
  | unknownFork
  | v3Quarantined
  | ssz (error : SSZError)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except BridgeError α

abbrev RawByteVector (length : Nat) := Vector UInt8 length
abbrev RawBytes := Array UInt8

structure RawWithdrawal where
  index : UInt64
  validatorIndex : UInt64
  address : RawByteVector 20
  amount : UInt64
  deriving Repr

structure RawExecutionPayload where
  parentHash : RawByteVector 32
  feeRecipient : RawByteVector 20
  stateRoot : RawByteVector 32
  receiptsRoot : RawByteVector 32
  logsBloom : RawByteVector 256
  prevRandao : RawByteVector 32
  blockNumber : UInt64
  gasLimit : UInt64
  gasUsed : UInt64
  timestamp : UInt64
  extraData : RawBytes
  baseFeePerGas : BitVec 256
  blockHash : RawByteVector 32
  transactions : Array RawBytes
  withdrawals : Array RawWithdrawal
  blobGasUsed : UInt64
  excessBlobGas : UInt64
  blockAccessList : RawBytes
  slotNumber : UInt64
  deriving Repr

structure RawDepositRequest where
  pubkey : RawByteVector 48
  withdrawalCredentials : RawByteVector 32
  amount : UInt64
  signature : RawByteVector 96
  index : UInt64
  deriving Repr

structure RawWithdrawalRequest where
  sourceAddress : RawByteVector 20
  validatorPubkey : RawByteVector 48
  amount : UInt64
  deriving Repr

structure RawConsolidationRequest where
  sourceAddress : RawByteVector 20
  sourcePubkey : RawByteVector 48
  targetPubkey : RawByteVector 48
  deriving Repr

structure RawExecutionRequests where
  deposits : Array RawDepositRequest
  withdrawals : Array RawWithdrawalRequest
  consolidations : Array RawConsolidationRequest
  deriving Repr

structure RawNewPayloadRequest where
  executionPayload : RawExecutionPayload
  versionedHashes : Array (RawByteVector 32)
  parentBeaconBlockRoot : RawByteVector 32
  executionRequests : RawExecutionRequests
  deriving Repr

structure RawExecutionWitness where
  state : Array RawBytes
  codes : Array RawBytes
  headers : Array RawBytes
  deriving Repr

structure RawForkActivation where
  blockNumber : Option UInt64
  timestamp : Option UInt64
  deriving Repr

structure RawBlobSchedule where
  target : UInt64
  max : UInt64
  baseFeeUpdateFraction : UInt64
  deriving Repr

structure RawForkConfig where
  fork : UInt64
  activation : RawForkActivation
  blobSchedule : Option RawBlobSchedule
  deriving Repr

structure RawChainConfig where
  chainId : UInt64
  activeFork : RawForkConfig
  deriving Repr

/-- A named lossless representation of the complete Amsterdam V4 schema. -/
structure RawV4 where
  newPayloadRequest : RawNewPayloadRequest
  witness : RawExecutionWitness
  chainConfig : RawChainConfig
  publicKeys : Array (RawByteVector publicKeyBytes)
  deriving Repr

def rawWithdrawalOf (value : withdrawalType.interp) : RawWithdrawal :=
  {
    index := value.1
    validatorIndex := value.2.1
    address := value.2.2.1
    amount := value.2.2.2.1
  }

def rawExecutionPayloadOf (value : executionPayloadType.interp) : RawExecutionPayload :=
  {
    parentHash := value.1
    feeRecipient := value.2.1
    stateRoot := value.2.2.1
    receiptsRoot := value.2.2.2.1
    logsBloom := value.2.2.2.2.1
    prevRandao := value.2.2.2.2.2.1
    blockNumber := value.2.2.2.2.2.2.1
    gasLimit := value.2.2.2.2.2.2.2.1
    gasUsed := value.2.2.2.2.2.2.2.2.1
    timestamp := value.2.2.2.2.2.2.2.2.2.1
    extraData := value.2.2.2.2.2.2.2.2.2.2.1
    baseFeePerGas := value.2.2.2.2.2.2.2.2.2.2.2.1
    blockHash := value.2.2.2.2.2.2.2.2.2.2.2.2.1
    transactions := value.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.map (fun item => item.1)
    withdrawals := value.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.map rawWithdrawalOf
    blobGasUsed := value.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    excessBlobGas := value.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    blockAccessList := value.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    slotNumber := value.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  }

def rawDepositRequestOf (value : depositRequestType.interp) : RawDepositRequest :=
  {
    pubkey := value.1
    withdrawalCredentials := value.2.1
    amount := value.2.2.1
    signature := value.2.2.2.1
    index := value.2.2.2.2.1
  }

def rawWithdrawalRequestOf (value : withdrawalRequestType.interp) : RawWithdrawalRequest :=
  {
    sourceAddress := value.1
    validatorPubkey := value.2.1
    amount := value.2.2.1
  }

def rawConsolidationRequestOf (value : consolidationRequestType.interp) :
    RawConsolidationRequest :=
  {
    sourceAddress := value.1
    sourcePubkey := value.2.1
    targetPubkey := value.2.2.1
  }

def rawExecutionRequestsOf (value : executionRequestsType.interp) : RawExecutionRequests :=
  {
    deposits := value.1.1.map rawDepositRequestOf
    withdrawals := value.2.1.1.map rawWithdrawalRequestOf
    consolidations := value.2.2.1.1.map rawConsolidationRequestOf
  }

def rawNewPayloadRequestOf (value : newPayloadRequestType.interp) : RawNewPayloadRequest :=
  {
    executionPayload := rawExecutionPayloadOf value.1
    versionedHashes := value.2.1.1
    parentBeaconBlockRoot := value.2.2.1
    executionRequests := rawExecutionRequestsOf value.2.2.2.1
  }

def rawWitnessOf (value : witnessType.interp) : RawExecutionWitness :=
  {
    state := value.1.1.map (fun item => item.1)
    codes := value.2.1.1.map (fun item => item.1)
    headers := value.2.2.1.1.map (fun item => item.1)
  }

def rawForkActivationOf (value : forkActivationType.interp) : RawForkActivation :=
  {
    blockNumber := value.1.1[0]?
    timestamp := value.2.1.1[0]?
  }

def rawBlobScheduleOf (value : blobScheduleType.interp) : RawBlobSchedule :=
  {
    target := value.1
    max := value.2.1
    baseFeeUpdateFraction := value.2.2.1
  }

def rawForkConfigOf (value : forkConfigType.interp) : RawForkConfig :=
  {
    fork := value.1
    activation := rawForkActivationOf value.2.1
    blobSchedule := (value.2.2.1.1[0]?).map rawBlobScheduleOf
  }

def rawChainConfigOf (value : chainConfigType.interp) : RawChainConfig :=
  {
    chainId := value.1
    activeFork := rawForkConfigOf value.2.1
  }

def rawV4OfInterp (value : statelessInputV4Type.interp) : RawV4 :=
  {
    newPayloadRequest := rawNewPayloadRequestOf value.1
    witness := rawWitnessOf value.2.1
    chainConfig := rawChainConfigOf value.2.2.1
    publicKeys := value.2.2.2.1.1
  }

def readU32LE? (input : ByteArray) (offset : Nat) : Option Nat :=
  if offset + 4 > input.size then
    none
  else
    some <|
      (input.get! offset).toNat +
      (input.get! (offset + 1)).toNat * 256 +
      (input.get! (offset + 2)).toNat * 256 ^ 2 +
      (input.get! (offset + 3)).toNat * 256 ^ 3

/--
Decode a schema body and reject any accepted-but-noncanonical wire alias.
The serialize equality also catches the known all-zero first-offset alias for
an empty variable-element list.
-/
def decodeCanonical (schema : SSZType) (body : ByteArray) : Except SSZError schema.interp := do
  let (value, used) ← schema.deserialize body
  if used != body.size then
    throw .trailingBytes
  else if schema.serialize value == body then
    pure value
  else
    throw .invalidOffset

def hasSchemaId (input : ByteArray) : Bool :=
  input.size ≥ 2 && input.get! 0 == 0 && input.get! 1 == 1

/-- A narrow structural V3 classifier; it never produces a V3 semantic value. -/
def hasV3PayloadShape (input : ByteArray) : Bool :=
  if !hasSchemaId input then
    false
  else
    let body := input.extract 2 input.size
    match readU32LE? body 0, readU32LE? body 4 with
    | some requestOffset, some hashesOffset =>
        if requestOffset != 16 || requestOffset > hashesOffset || hashesOffset > body.size then
          false
        else
          let request := body.extract requestOffset hashesOffset
          match readU32LE? request 0, readU32LE? request 4 with
          | some payloadOffset, some payloadEnd =>
              if payloadOffset != 44 || payloadOffset > payloadEnd || payloadEnd > request.size then
                false
              else
                let payload := request.extract payloadOffset payloadEnd
                readU32LE? payload 436 == some 528
          | _, _ => false
    | _, _ => false

def decodeRawV4 (input : ByteArray) : Result RawV4 := do
  if input.size >= 2 ^ 32 then
    throw .tooLarge
  else if input.size < 2 then
    throw .tooShort
  else if !hasSchemaId input then
    throw .badSchema
  else
    match decodeCanonical statelessInputV4Type (input.extract 2 input.size) with
    | .ok value =>
        let raw := rawV4OfInterp value
        if raw.chainConfig.activeFork.fork > 20 then
          throw .unknownFork
        else
          pure raw
    | .error error => throw (.ssz error)

def decodeRawOrQuarantineV3 (input : ByteArray) : Result RawV4 :=
  if hasV3PayloadShape input then
    .error .v3Quarantined
  else
    decodeRawV4 input

/--
Decode V4 raw bytes first.  A length-prefixed Ere interpretation is attempted
only after raw failure and only when its little-endian declared length is exact.
-/
def decodeStatelessInput (input : ByteArray) : Result RawV4 :=
  if input.size >= 2 ^ 32 then
    .error .tooLarge
  else
    match decodeRawOrQuarantineV3 input with
    | .ok value => .ok value
    | .error rawError =>
        match rawError with
        | .v3Quarantined => .error rawError
        | _ =>
            match readU32LE? input 0 with
            | some declaredLength =>
                if declaredLength == input.size - 4 then
                  decodeRawOrQuarantineV3 (input.extract 4 input.size)
                else
                  .error rawError
            | none => .error rawError

def BridgeError.label : BridgeError → String
  | .tooLarge => "too_large"
  | .tooShort => "too_short"
  | .badSchema => "bad_schema"
  | .unknownFork => "unknown_fork"
  | .v3Quarantined => "v3_quarantined"
  | .ssz error => s!"ssz_{repr error}"

def valueRecord (path kind value : String) : String :=
  path ++ "\t" ++ kind ++ "\t" ++ value

def hexDigit (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + value - 10)

def renderByte (value : UInt8) : String :=
  let value := value.toNat
  String.ofList [hexDigit (value / 16), hexDigit (value % 16)]

def renderBytes (value : RawBytes) : String :=
  "0x" ++ String.join (value.toList.map renderByte)

def renderU64 (path : String) (value : UInt64) : List String :=
  [valueRecord path "scalar" (toString value)]

def renderU256 (path : String) (value : BitVec 256) : List String :=
  [valueRecord path "scalar" (toString value.toNat)]

def renderByteField (path : String) (value : RawBytes) : List String :=
  [valueRecord path "bytes" (renderBytes value)]

def renderVectorField {length : Nat} (path : String) (value : RawByteVector length) : List String :=
  renderByteField path value.toArray

def renderIndexed {α : Type} (path : String) (render : String → α → List String) :
    Nat → List α → List String
  | _, [] => []
  | index, value :: values =>
      render (path ++ "[" ++ toString index ++ "]") value ++
        renderIndexed path render (index + 1) values

def renderList {α : Type} (path : String) (values : Array α) (render : String → α → List String) :
    List String :=
  valueRecord path "count" (toString values.size) :: renderIndexed path render 0 values.toList

def renderOptionU64 (path : String) : Option UInt64 → List String
  | none => [valueRecord path "option" "none"]
  | some value => valueRecord path "option" "some" :: renderU64 (path ++ ".value") value

def renderWithdrawal (path : String) (value : RawWithdrawal) : List String :=
  renderU64 (path ++ ".index") value.index ++
    renderU64 (path ++ ".validator_index") value.validatorIndex ++
    renderVectorField (path ++ ".address") value.address ++
    renderU64 (path ++ ".amount") value.amount

def renderExecutionPayload (path : String) (value : RawExecutionPayload) : List String :=
  renderVectorField (path ++ ".parent_hash") value.parentHash ++
    renderVectorField (path ++ ".fee_recipient") value.feeRecipient ++
    renderVectorField (path ++ ".state_root") value.stateRoot ++
    renderVectorField (path ++ ".receipts_root") value.receiptsRoot ++
    renderVectorField (path ++ ".logs_bloom") value.logsBloom ++
    renderVectorField (path ++ ".prev_randao") value.prevRandao ++
    renderU64 (path ++ ".block_number") value.blockNumber ++
    renderU64 (path ++ ".gas_limit") value.gasLimit ++
    renderU64 (path ++ ".gas_used") value.gasUsed ++
    renderU64 (path ++ ".timestamp") value.timestamp ++
    renderByteField (path ++ ".extra_data") value.extraData ++
    renderU256 (path ++ ".base_fee_per_gas") value.baseFeePerGas ++
    renderVectorField (path ++ ".block_hash") value.blockHash ++
    renderList (path ++ ".transactions") value.transactions renderByteField ++
    renderList (path ++ ".withdrawals") value.withdrawals renderWithdrawal ++
    renderU64 (path ++ ".blob_gas_used") value.blobGasUsed ++
    renderU64 (path ++ ".excess_blob_gas") value.excessBlobGas ++
    renderByteField (path ++ ".block_access_list") value.blockAccessList ++
    renderU64 (path ++ ".slot_number") value.slotNumber

def renderDepositRequest (path : String) (value : RawDepositRequest) : List String :=
  renderVectorField (path ++ ".pubkey") value.pubkey ++
    renderVectorField (path ++ ".withdrawal_credentials") value.withdrawalCredentials ++
    renderU64 (path ++ ".amount") value.amount ++
    renderVectorField (path ++ ".signature") value.signature ++
    renderU64 (path ++ ".index") value.index

def renderWithdrawalRequest (path : String) (value : RawWithdrawalRequest) : List String :=
  renderVectorField (path ++ ".source_address") value.sourceAddress ++
    renderVectorField (path ++ ".validator_pubkey") value.validatorPubkey ++
    renderU64 (path ++ ".amount") value.amount

def renderConsolidationRequest (path : String) (value : RawConsolidationRequest) : List String :=
  renderVectorField (path ++ ".source_address") value.sourceAddress ++
    renderVectorField (path ++ ".source_pubkey") value.sourcePubkey ++
    renderVectorField (path ++ ".target_pubkey") value.targetPubkey

def renderExecutionRequests (path : String) (value : RawExecutionRequests) : List String :=
  renderList (path ++ ".deposits") value.deposits renderDepositRequest ++
    renderList (path ++ ".withdrawals") value.withdrawals renderWithdrawalRequest ++
    renderList (path ++ ".consolidations") value.consolidations renderConsolidationRequest

def renderNewPayloadRequest (path : String) (value : RawNewPayloadRequest) : List String :=
  renderExecutionPayload (path ++ ".execution_payload") value.executionPayload ++
    renderList (path ++ ".versioned_hashes") value.versionedHashes renderVectorField ++
    renderVectorField (path ++ ".parent_beacon_block_root") value.parentBeaconBlockRoot ++
    renderExecutionRequests (path ++ ".execution_requests") value.executionRequests

def renderWitness (path : String) (value : RawExecutionWitness) : List String :=
  renderList (path ++ ".state") value.state renderByteField ++
    renderList (path ++ ".codes") value.codes renderByteField ++
    renderList (path ++ ".headers") value.headers renderByteField

def renderBlobSchedule (path : String) (value : RawBlobSchedule) : List String :=
  renderU64 (path ++ ".target") value.target ++
    renderU64 (path ++ ".max") value.max ++
    renderU64 (path ++ ".base_fee_update_fraction") value.baseFeeUpdateFraction

def renderOptionBlobSchedule (path : String) : Option RawBlobSchedule → List String
  | none => [valueRecord path "option" "none"]
  | some value =>
      valueRecord path "option" "some" :: renderBlobSchedule (path ++ ".value") value

def renderForkActivation (path : String) (value : RawForkActivation) : List String :=
  renderOptionU64 (path ++ ".block_number") value.blockNumber ++
    renderOptionU64 (path ++ ".timestamp") value.timestamp

def renderForkConfig (path : String) (value : RawForkConfig) : List String :=
  renderU64 (path ++ ".fork") value.fork ++
    renderForkActivation (path ++ ".activation") value.activation ++
    renderOptionBlobSchedule (path ++ ".blob_schedule") value.blobSchedule

def renderChainConfig (path : String) (value : RawChainConfig) : List String :=
  renderU64 (path ++ ".chain_id") value.chainId ++
    renderForkConfig (path ++ ".active_fork") value.activeFork

def RawV4.renderLines (value : RawV4) : List String :=
  renderNewPayloadRequest "new_payload_request" value.newPayloadRequest ++
    renderWitness "witness" value.witness ++
    renderChainConfig "chain_config" value.chainConfig ++
    renderList "public_keys" value.publicKeys renderVectorField

/-- Deterministic, complete, versioned raw-value protocol for the V4 schema. -/
def RawV4.render (value : RawV4) : String :=
  "\n".intercalate ("version\tssz-value-v1" :: value.renderLines)

end SszBridge
