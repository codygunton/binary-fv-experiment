import BinaryFv.Specs.SSZ.AmsterdamV4

open BinaryFv.Specs.SSZ

def bytes (values : List Nat) : ByteArray :=
  ByteArray.mk <| values.toArray.map Nat.toUInt8

def zeros (count : Nat) : ByteArray :=
  ByteArray.mk <| Array.replicate count 0

def le32 (value : Nat) : ByteArray :=
  bytes [value % 256, value / 256 % 256, value / 256 ^ 2 % 256, value / 256 ^ 3 % 256]

def le64 (value : Nat) : ByteArray :=
  ByteArray.mk <| (List.range 8).toArray.map fun index => (value / 256 ^ index).toUInt8

def executionPayloadV4 (transactions : ByteArray := .empty) : ByteArray :=
  let fixedSize := 540
  let withdrawalsOffset := fixedSize + transactions.size
  zeros 436 ++ le32 fixedSize ++ zeros 64 ++ le32 fixedSize ++ le32 withdrawalsOffset ++ zeros 16 ++
    le32 withdrawalsOffset ++ zeros 8 ++ transactions

def executionPayloadV3 : ByteArray :=
  let fixedSize := 528
  zeros 436 ++ le32 fixedSize ++ zeros 64 ++ le32 fixedSize ++ le32 fixedSize ++ zeros 16

def executionRequests : ByteArray :=
  le32 12 ++ le32 12 ++ le32 12

def newPayloadRequest (payload : ByteArray) : ByteArray :=
  let requests := executionRequests
  let requestsOffset := 44 + payload.size
  le32 44 ++ le32 requestsOffset ++ zeros 32 ++ le32 requestsOffset ++ payload ++ requests

def witness : ByteArray :=
  le32 12 ++ le32 12 ++ le32 12

def chainConfig (fork : Nat := 20) : ByteArray :=
  zeros 8 ++ le32 12 ++ le64 fork ++ le32 16 ++ le32 24 ++ le32 8 ++ le32 8

def rawInput (payload : ByteArray) (fork : Nat := 20) : ByteArray :=
  let request := newPayloadRequest payload
  let witnessBytes := witness
  let config := chainConfig fork
  let witnessOffset := 16 + request.size
  let configOffset := witnessOffset + witnessBytes.size
  let keysOffset := configOffset + config.size
  bytes [0, 1] ++ le32 16 ++ le32 witnessOffset ++ le32 configOffset ++ le32 keysOffset ++
    request ++ witnessBytes ++ config

def erePrefix (input : ByteArray) : ByteArray :=
  le32 input.size ++ input

def isOk {α : Type} : Except DecodeError α → Bool
  | .ok _ => true
  | .error _ => false

def isError {α : Type} : Except DecodeError α → Bool
  | .ok _ => false
  | .error _ => true

def isV3Quarantined (result : Except DecodeError RawV4) : Bool :=
  match result with
  | .error error =>
      match error with
      | .v3Quarantined => true
      | _ => false
  | .ok _ => false

def isUnknownFork (result : Except DecodeError RawV4) : Bool :=
  match result with
  | .error error =>
      match error with
      | .unknownFork => true
      | _ => false
  | .ok _ => false

def testV4Raw : Bool :=
  isOk <| decodeStatelessInput <| rawInput executionPayloadV4

def testV4Ere : Bool :=
  isOk <| decodeStatelessInput <| erePrefix <| rawInput executionPayloadV4

def testBadSchema : Bool :=
  let input := rawInput executionPayloadV4
  isError <| decodeStatelessInput (bytes [0, 2] ++ input.extract 2 input.size)

def testWrongEreLength : Bool :=
  let input := rawInput executionPayloadV4
  isError <| decodeStatelessInput (le32 (input.size + 1) ++ input)

/-- SizzLean alone accepts this alias; `decodeCanonical` must reject it. -/
def testNonCanonicalEmptyTransactionList : Bool :=
  isError <| decodeStatelessInput <| rawInput <| executionPayloadV4 (le32 0)

def testV3IsQuarantined : Bool :=
  isV3Quarantined <| decodeStatelessInput <| rawInput executionPayloadV3

def testEreV3IsQuarantined : Bool :=
  isV3Quarantined <| decodeStatelessInput <| erePrefix <| rawInput executionPayloadV3

def testUnknownForkIsRejected : Bool :=
  isUnknownFork <| decodeStatelessInput <| rawInput executionPayloadV4 21

def vector (length : Nat) (byte : UInt8) : RawByteVector length :=
  Vector.replicate length byte

def rendererSample : RawV4 :=
  {
    newPayloadRequest :=
      {
        executionPayload :=
          {
            parentHash := vector 32 1
            feeRecipient := vector 20 2
            stateRoot := vector 32 3
            receiptsRoot := vector 32 4
            logsBloom := vector 256 5
            prevRandao := vector 32 6
            blockNumber := 7
            gasLimit := 8
            gasUsed := 9
            timestamp := 10
            extraData := #[0xab, 0xcd]
            baseFeePerGas := BitVec.ofNat 256 (2 ^ 200 + 13)
            blockHash := vector 32 11
            transactions := #[#[0xde, 0xad]]
            withdrawals :=
              #[{ index := 12, validatorIndex := 13, address := vector 20 14, amount := 15 }]
            blobGasUsed := 16
            excessBlobGas := 17
            blockAccessList := #[0xbe, 0xef]
            slotNumber := 18
          }
        versionedHashes := #[vector 32 19]
        parentBeaconBlockRoot := vector 32 20
        executionRequests :=
          {
            deposits :=
              #[
                {
                  pubkey := vector 48 21
                  withdrawalCredentials := vector 32 22
                  amount := 23
                  signature := vector 96 24
                  index := 25
                },
              ]
            withdrawals :=
              #[{ sourceAddress := vector 20 26, validatorPubkey := vector 48 27, amount := 28 }]
            consolidations :=
              #[
                {
                  sourceAddress := vector 20 29
                  sourcePubkey := vector 48 30
                  targetPubkey := vector 48 31
                },
              ]
          }
      }
    witness := { state := #[#[32]], codes := #[#[33]], headers := #[#[34]] }
    chainConfig :=
      {
        chainId := 35
        activeFork :=
          {
            fork := 36
            activation := { blockNumber := some 37, timestamp := some 38 }
            blobSchedule := some { target := 39, max := 40, baseFeeUpdateFraction := 41 }
          }
      }
    publicKeys := #[vector 65 42]
  }

def testRenderer : Bool :=
  match decodeStatelessInput (rawInput executionPayloadV4) with
  | .error _ => false
  | .ok value =>
      let rendered := value.render
      rendered.startsWith "version\tssz-value-v1\n" &&
        rendered.contains
          ("new_payload_request.execution_payload." ++ "base_fee_per_gas\tscalar\t0") &&
        rendered.contains "new_payload_request.execution_payload.transactions\tcount\t0" &&
        rendered.contains "chain_config.active_fork.activation.block_number\toption\tnone" &&
        rendered.contains "public_keys\tcount\t0"

def testRendererNonemptyCoverage : Bool :=
  let rendered := rendererSample.render
  rendered.contains
      ("new_payload_request.execution_payload.base_fee_per_gas\tscalar\t" ++
        toString (2 ^ 200 + 13)) &&
    rendered.contains "new_payload_request.execution_payload.transactions\tcount\t1" &&
    rendered.contains
      ("new_payload_request.execution_payload." ++ "transactions[0]\tbytes\t0xdead") &&
    rendered.contains "new_payload_request.execution_requests.deposits\tcount\t1" &&
    rendered.contains "witness.codes[0]\tbytes\t0x21" &&
    rendered.contains "chain_config.active_fork.activation.block_number\toption\tsome" &&
    rendered.contains "chain_config.active_fork.activation.block_number.value\tscalar\t37" &&
    rendered.contains "chain_config.active_fork.blob_schedule.value.target\tscalar\t39" &&
    rendered.contains
      ("public_keys[0]\tbytes\t0x" ++ String.join (List.replicate 65 "2a"))

def allTests : Bool :=
  testV4Raw && testV4Ere && testBadSchema && testWrongEreLength &&
    testNonCanonicalEmptyTransactionList && testV3IsQuarantined && testEreV3IsQuarantined &&
    testUnknownForkIsRejected && testRenderer &&
    testRendererNonemptyCoverage

def main (_args : List String) : IO UInt32 := do
  if allTests then
    IO.println "Amsterdam V4 SizzLean specification tests: ok"
    pure 0
  else
    IO.eprintln "Amsterdam V4 SizzLean specification tests: failed"
    pure 1
