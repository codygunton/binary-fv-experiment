import SszBridge.Core

open SszBridge

def bytes (values : List Nat) : ByteArray :=
  ByteArray.mk <| values.toArray.map Nat.toUInt8

def zeros (count : Nat) : ByteArray :=
  ByteArray.mk <| Array.replicate count 0

def le32 (value : Nat) : ByteArray :=
  bytes [value % 256, value / 256 % 256, value / 256 ^ 2 % 256, value / 256 ^ 3 % 256]

def le64 (value : Nat) : ByteArray :=
  ByteArray.mk <| (List.range 8).toArray.map fun index => (value / 256 ^ index).toUInt8

def executionPayload (version : PayloadVersion) : ByteArray :=
  let fixedSize := match version with | .v3 => 528 | .v4 => 540
  let fixedPart := zeros 436 ++ le32 fixedSize ++ zeros 64 ++ le32 fixedSize ++ le32 fixedSize ++ zeros 16
  match version with
  | .v3 => fixedPart
  | .v4 => fixedPart ++ le32 fixedSize ++ zeros 8

def executionRequests : ByteArray :=
  le32 12 ++ le32 12 ++ le32 12

def newPayloadRequest (version : PayloadVersion) : ByteArray :=
  let payload := executionPayload version
  let requests := executionRequests
  let requestsOffset := 44 + payload.size
  le32 44 ++ le32 requestsOffset ++ zeros 32 ++ le32 requestsOffset ++ payload ++ requests

def witness : ByteArray :=
  le32 12 ++ le32 12 ++ le32 12

def chainConfig : ByteArray :=
  zeros 8 ++ le32 12 ++ le64 20 ++ le32 16 ++ le32 24 ++ le32 8 ++ le32 8

def rawInput (version : PayloadVersion) : ByteArray :=
  let request := newPayloadRequest version
  let witnessBytes := witness
  let config := chainConfig
  let witnessOffset := 16 + request.size
  let configOffset := witnessOffset + witnessBytes.size
  let keysOffset := configOffset + config.size
  bytes [0, 1] ++ le32 16 ++ le32 witnessOffset ++ le32 configOffset ++ le32 keysOffset ++
    request ++ witnessBytes ++ config

def erePrefix (input : ByteArray) : ByteArray :=
  le32 input.size ++ input

def replace32 (input : ByteArray) (offset value : Nat) : ByteArray :=
  input.extract 0 offset ++ le32 value ++ input.extract (offset + 4) input.size

def isVersion (expected : PayloadVersion) (result : Result NormalizedInput) : Bool :=
  match result with
  | .ok normalized => normalized.payloadVersion == expected
  | .error _ => false

def isError {α : Type} (result : Result α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

def testV3 : Bool := isVersion .v3 <| decodeStatelessInput <| rawInput .v3
def testV4Ere : Bool := isVersion .v4 <| decodeStatelessInput <| erePrefix <| rawInput .v4

def testSchemaRejection : Bool :=
  let input := rawInput .v4
  isError <| decodeStatelessInput (bytes [0, 2] ++ input.extract 2 input.size)

def testTopOffsetRejection : Bool :=
  let input := rawInput .v4
  isError <| decodeStatelessInput (bytes [0, 1] ++ le32 20 ++ input.extract 6 input.size)

def testTruncationRejection : Bool :=
  isError <| decodeStatelessInput ((rawInput .v4).extract 0 1)

def testDeclaredLengthRejection : Bool :=
  let input := rawInput .v4
  isError <| decodeStatelessInput (le32 (input.size + 1) ++ input)

def testDescendingOffsetRejection : Bool :=
  let input := rawInput .v4
  isError <| decodeStatelessInput (replace32 input 6 15)

def testOutOfRangeOffsetRejection : Bool :=
  let input := rawInput .v4
  isError <| decodeStatelessInput (replace32 input 14 999999)

def testFixedElementDivisibility : Bool :=
  isError <| decodeFixedList (bytes [0]) 44 maxWithdrawalsPerPayload

def testMalformedListTable : Bool :=
  isError <| decodeByteListList (le32 8 ++ le32 4) 2 32

def testVersionRejection : Bool :=
  let input := rawInput .v3
  -- schema (2) + top fixed section (16) + request fixed section (44) + offset 436
  isError <| decodeStatelessInput (replace32 input 498 529)

def allTests : Bool :=
  testV3 && testV4Ere && testSchemaRejection && testTopOffsetRejection &&
    testTruncationRejection && testDeclaredLengthRejection && testDescendingOffsetRejection &&
    testOutOfRangeOffsetRejection && testFixedElementDivisibility && testMalformedListTable &&
    testVersionRejection

def main (_args : List String) : IO UInt32 := do
  if allTests then
    IO.println "ssz-bridge tests: ok"
    pure 0
  else
    IO.eprintln "ssz-bridge tests: failed"
    pure 1
