/-!
# Executable stateless-SSZ bridge

This is a deliberately small, executable normalization layer for Zesu's raw
`SszStatelessInput` candidate.  It accepts the schema prefix, optional Ere
length wrapper, canonical SSZ offset tables and bounds, then projects the
decoded input to dispatch and collection metadata.  It is designed for a
three-way acceptance corpus, not as a replacement for an SSZ implementation.

The V3/V4 split follows the fixed-section offset at byte 436 of an execution
payload: 528 denotes V3 and 540 denotes V4.  The normalized result retains no
transaction, witness, or request values; Zesu's raw ABI currently returns only
success/failure and does not expose a full value-level representation.

This file has no claimed refinement theorem.  SizzLean's executable decoder
has variable-offset support, but its `BasicSupported` theorem coverage excludes
mixed variable-size containers such as `SszStatelessInput`.
-/

namespace SszBridge

inductive SszError where
  | tooShort
  | badSchema
  | badOffset
  | badPayloadVersion
  | malformedList
  | outOfRange
  deriving Repr, DecidableEq

inductive PayloadVersion where
  | v3
  | v4
  deriving Repr, DecidableEq

structure Span where
  start : Nat
  finish : Nat
  deriving Repr, DecidableEq

structure NormalizedInput where
  erePrefixed : Bool
  payloadVersion : PayloadVersion
  chainId : Nat
  forkIndex : Nat
  transactions : Span
  withdrawals : Span
  blockAccessList : Span
  transactionCount : Nat
  witnessNodeCount : Nat
  witnessCodeCount : Nat
  witnessHeaderCount : Nat
  publicKeyCount : Nat
  deriving Repr, DecidableEq

structure PayloadProjection where
  version : PayloadVersion
  transactions : Span
  withdrawals : Span
  blockAccessList : Span
  transactionCount : Nat
  deriving Repr, DecidableEq

structure NewPayloadProjection where
  payloadStart : Nat
  payload : PayloadProjection
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except SszError α

def maxExtraDataBytes : Nat := 32
def maxBytesPerTransaction : Nat := 2 ^ 30
def maxTransactionsPerPayload : Nat := 2 ^ 20
def maxWithdrawalsPerPayload : Nat := 2 ^ 4
def maxBlobCommitmentsPerBlock : Nat := 4096
def maxWitnessNodes : Nat := 2 ^ 22
def maxWitnessCodes : Nat := 2 ^ 18
def maxWitnessHeaders : Nat := 256
def maxBytesPerWitnessNode : Nat := 2 ^ 10
def maxBytesPerCode : Nat := 2 ^ 16
def maxBytesPerHeader : Nat := 2 ^ 10
def maxPublicKeys : Nat := 2 ^ 15

def readU32LE (input : ByteArray) (offset : Nat) : Result Nat := do
  if offset + 4 > input.size then
    throw .tooShort
  else
    pure <|
      (input.get! offset).toNat +
      (input.get! (offset + 1)).toNat * 256 +
      (input.get! (offset + 2)).toNat * 256 ^ 2 +
      (input.get! (offset + 3)).toNat * 256 ^ 3

def readU64LE (input : ByteArray) (offset : Nat) : Result Nat := do
  if offset + 8 > input.size then
    throw .tooShort
  else
    pure <| (List.range 8).foldl
      (fun value index => value + (input.get! (offset + index)).toNat * 256 ^ index) 0

def checkedSpan (start finish limit : Nat) : Result Span :=
  if start ≤ finish ∧ finish ≤ limit then
    .ok { start, finish }
  else
    .error .badOffset

def Span.shift (span : Span) (amount : Nat) : Span :=
  { start := amount + span.start, finish := amount + span.finish }

def Span.bytes (span : Span) (input : ByteArray) : ByteArray :=
  input.extract span.start span.finish

def require (condition : Prop) (error : SszError) [Decidable condition] : Result Unit :=
  if condition then .ok () else .error error

/-- Check the wire form of `List[ByteList[maxBytes], maxCount]`. -/
def checkByteListOffsets (input : ByteArray) (maxBytes : Nat) :
    (remaining position previous : Nat) → Result Unit
  | 0, _, _ => .ok ()
  | remaining + 1, position, previous => do
      let current ← readU32LE input position
      let following ←
        if remaining = 0 then
          .ok input.size
        else
          readU32LE input (position + 4)
      let _ ← require (previous ≤ current ∧ current ≤ following ∧ following ≤ input.size)
        .badOffset
      let _ ← require (following - current ≤ maxBytes) .outOfRange
      checkByteListOffsets input maxBytes remaining (position + 4) current

def decodeByteListList (input : ByteArray) (maxCount maxBytes : Nat) : Result Nat := do
  if input.size = 0 then
    .ok 0
  else
    let firstOffset ← readU32LE input 0
    let _ ← require
      (firstOffset ≠ 0 ∧ firstOffset % 4 = 0 ∧ firstOffset ≤ input.size) .malformedList
    let count := firstOffset / 4
    let _ ← require (count ≤ maxCount) .outOfRange
    let _ ← checkByteListOffsets input maxBytes count 0 firstOffset
    .ok count

def decodeFixedList (input : ByteArray) (elementSize maxCount : Nat) : Result Nat := do
  let _ ← require (elementSize ≠ 0 ∧ input.size % elementSize = 0) .malformedList
  let count := input.size / elementSize
  let _ ← require (count ≤ maxCount) .outOfRange
  .ok count

def decodeExecutionRequests (input : ByteArray) : Result Unit := do
  let _ ← require (input.size ≥ 12) .tooShort
  let depositsOffset ← readU32LE input 0
  let withdrawalsOffset ← readU32LE input 4
  let consolidationsOffset ← readU32LE input 8
  let _ ← require
    (depositsOffset = 12 ∧ depositsOffset ≤ withdrawalsOffset ∧
      withdrawalsOffset ≤ consolidationsOffset ∧ consolidationsOffset ≤ input.size) .badOffset
  let deposits := input.extract depositsOffset withdrawalsOffset
  let withdrawals := input.extract withdrawalsOffset consolidationsOffset
  let consolidations := input.extract consolidationsOffset input.size
  let _ ← decodeFixedList deposits 192 (2 ^ 13)
  let _ ← decodeFixedList withdrawals 76 (2 ^ 4)
  let _ ← decodeFixedList consolidations 116 (2 ^ 1)
  .ok ()

def decodeExecutionPayload (input : ByteArray) : Result PayloadProjection := do
  let _ ← require (input.size ≥ 528) .tooShort
  let extraDataOffset ← readU32LE input 436
  let version ←
    if extraDataOffset = 528 then
      .ok PayloadVersion.v3
    else if extraDataOffset = 540 then
      let _ ← require (input.size ≥ 540) .tooShort
      .ok PayloadVersion.v4
    else
      .error .badPayloadVersion
  let fixedSize := match version with | .v3 => 528 | .v4 => 540
  let transactionsOffset ← readU32LE input 504
  let withdrawalsOffset ← readU32LE input 508
  let accessListOffset ← match version with
    | .v3 => .ok input.size
    | .v4 => readU32LE input 528
  let _ ← require
    (extraDataOffset = fixedSize ∧ extraDataOffset ≤ transactionsOffset ∧
      transactionsOffset ≤ withdrawalsOffset ∧ withdrawalsOffset ≤ accessListOffset ∧
      accessListOffset ≤ input.size) .badOffset
  let _ ← require (transactionsOffset - extraDataOffset ≤ maxExtraDataBytes) .outOfRange
  let transactions ← checkedSpan transactionsOffset withdrawalsOffset input.size
  let withdrawals ← checkedSpan withdrawalsOffset accessListOffset input.size
  let blockAccessList ← checkedSpan accessListOffset input.size input.size
  let transactionCount ← decodeByteListList (transactions.bytes input) maxTransactionsPerPayload
    maxBytesPerTransaction
  let _ ← decodeFixedList (withdrawals.bytes input) 44 maxWithdrawalsPerPayload
  let _ ← require ((blockAccessList.bytes input).size ≤ maxBytesPerTransaction) .outOfRange
  .ok { version, transactions, withdrawals, blockAccessList, transactionCount }

def decodeNewPayloadRequest (input : ByteArray) : Result NewPayloadProjection := do
  let _ ← require (input.size ≥ 44) .tooShort
  let payloadOffset ← readU32LE input 0
  let versionedHashesOffset ← readU32LE input 4
  let requestsOffset ← readU32LE input 40
  let _ ← require
    (payloadOffset = 44 ∧ payloadOffset ≤ versionedHashesOffset ∧
      versionedHashesOffset ≤ requestsOffset ∧ requestsOffset ≤ input.size) .badOffset
  let payload := input.extract payloadOffset versionedHashesOffset
  let versionedHashes := input.extract versionedHashesOffset requestsOffset
  let requests := input.extract requestsOffset input.size
  let _ ← decodeFixedList versionedHashes 32 maxBlobCommitmentsPerBlock
  let _ ← decodeExecutionRequests requests
  let payloadProjection ← decodeExecutionPayload payload
  .ok { payloadStart := payloadOffset, payload := payloadProjection }

def decodeWitness (input : ByteArray) : Result (Nat × Nat × Nat) := do
  let _ ← require (input.size ≥ 12) .tooShort
  let stateOffset ← readU32LE input 0
  let codesOffset ← readU32LE input 4
  let headersOffset ← readU32LE input 8
  let _ ← require
    (stateOffset = 12 ∧ stateOffset ≤ codesOffset ∧ codesOffset ≤ headersOffset ∧
      headersOffset ≤ input.size) .badOffset
  let state := input.extract stateOffset codesOffset
  let codes := input.extract codesOffset headersOffset
  let headers := input.extract headersOffset input.size
  let stateCount ← decodeByteListList state maxWitnessNodes maxBytesPerWitnessNode
  let codeCount ← decodeByteListList codes maxWitnessCodes maxBytesPerCode
  let headerCount ← decodeByteListList headers maxWitnessHeaders maxBytesPerHeader
  .ok (stateCount, codeCount, headerCount)

def decodeChainConfig (input : ByteArray) : Result (Nat × Nat) := do
  let _ ← require (input.size ≥ 12) .tooShort
  let chainId ← readU64LE input 0
  let activeForkOffset ← readU32LE input 8
  let _ ← require (activeForkOffset = 12) .badOffset
  let activeFork := input.extract activeForkOffset input.size
  let _ ← require (activeFork.size ≥ 16) .tooShort
  let forkIndex ← readU64LE activeFork 0
  let activationOffset ← readU32LE activeFork 8
  let blobScheduleOffset ← readU32LE activeFork 12
  let _ ← require
    (forkIndex ≤ 20 ∧ activationOffset = 16 ∧ activationOffset ≤ blobScheduleOffset ∧
      blobScheduleOffset ≤ activeFork.size) .badOffset
  let activation := activeFork.extract activationOffset blobScheduleOffset
  let _ ← require (activation.size ≥ 8) .tooShort
  let blockNumberOffset ← readU32LE activation 0
  let timestampOffset ← readU32LE activation 4
  let _ ← require
    (blockNumberOffset = 8 ∧ blockNumberOffset ≤ timestampOffset ∧
      timestampOffset ≤ activation.size) .badOffset
  let blockNumber := activation.extract blockNumberOffset timestampOffset
  let timestamp := activation.extract timestampOffset activation.size
  let blobSchedule := activeFork.extract blobScheduleOffset activeFork.size
  let _ ← decodeFixedList blockNumber 8 1
  let _ ← decodeFixedList timestamp 8 1
  let _ ← decodeFixedList blobSchedule 24 1
  .ok (chainId, forkIndex)

/-- Decode a schema-prefix payload with an already-resolved framing choice. -/
def decodePayload (erePrefixed : Bool) (payload : ByteArray) : Result NormalizedInput := do
  let _ ← require (payload.size ≥ 2) .tooShort
  let _ ← require (payload.get! 0 = 0 ∧ payload.get! 1 = 1) .badSchema
  let body := payload.extract 2 payload.size
  let _ ← require (body.size ≥ 16) .tooShort
  let newPayloadOffset ← readU32LE body 0
  let witnessOffset ← readU32LE body 4
  let chainConfigOffset ← readU32LE body 8
  let publicKeysOffset ← readU32LE body 12
  let _ ← require
    (newPayloadOffset = 16 ∧ newPayloadOffset ≤ witnessOffset ∧
      witnessOffset ≤ chainConfigOffset ∧ chainConfigOffset ≤ publicKeysOffset ∧
      publicKeysOffset ≤ body.size) .badOffset
  let newPayload ← checkedSpan newPayloadOffset witnessOffset body.size
  let witness ← checkedSpan witnessOffset chainConfigOffset body.size
  let chainConfig ← checkedSpan chainConfigOffset publicKeysOffset body.size
  let publicKeys ← checkedSpan publicKeysOffset body.size body.size
  let newPayloadProjection ← decodeNewPayloadRequest (newPayload.bytes body)
  let (witnessNodeCount, witnessCodeCount, witnessHeaderCount) ← decodeWitness (witness.bytes body)
  let (chainId, forkIndex) ← decodeChainConfig (chainConfig.bytes body)
  let publicKeyCount ← decodeFixedList (publicKeys.bytes body) 65 maxPublicKeys
  let executionPayloadStart := 2 + newPayload.start + newPayloadProjection.payloadStart
  let payloadProjection := newPayloadProjection.payload
  .ok {
    erePrefixed,
    payloadVersion := payloadProjection.version,
    chainId,
    forkIndex,
    transactions := payloadProjection.transactions.shift executionPayloadStart,
    withdrawals := payloadProjection.withdrawals.shift executionPayloadStart,
    blockAccessList := payloadProjection.blockAccessList.shift executionPayloadStart,
    transactionCount := payloadProjection.transactionCount,
    witnessNodeCount,
    witnessCodeCount,
    witnessHeaderCount,
    publicKeyCount,
  }

/--
Try raw SSZ before an Ere frame.  This makes a genuine raw schema payload win when its first four
bytes coincidentally equal `input.size - 4`; only a non-schema raw input can be reinterpreted as
Ere framing.
-/
def decodeStatelessInput (input : ByteArray) : Result NormalizedInput :=
  match decodePayload false input with
  | .ok normalized => .ok normalized
  | .error rawError =>
      if input.size < 4 then
        .error rawError
      else
        match readU32LE input 0 with
        | .error _ => .error rawError
        | .ok declaredLength =>
            if declaredLength = input.size - 4 then
              decodePayload true (input.extract 4 input.size)
            else
              .error rawError

def PayloadVersion.label : PayloadVersion → String
  | .v3 => "v3"
  | .v4 => "v4"

def SszError.label : SszError → String
  | .tooShort => "too_short"
  | .badSchema => "bad_schema"
  | .badOffset => "bad_offset"
  | .badPayloadVersion => "bad_payload_version"
  | .malformedList => "malformed_list"
  | .outOfRange => "out_of_range"

def NormalizedInput.render (input : NormalizedInput) : String :=
  s!"ok\tere={if input.erePrefixed then 1 else 0}\tversion={input.payloadVersion.label}\t" ++
    s!"chain_id={input.chainId}\tfork={input.forkIndex}\ttxs={input.transactionCount}\t" ++
    s!"witness={input.witnessNodeCount},{input.witnessCodeCount},{input.witnessHeaderCount}\t" ++
    s!"public_keys={input.publicKeyCount}"

end SszBridge
