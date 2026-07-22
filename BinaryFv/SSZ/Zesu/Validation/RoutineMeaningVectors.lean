import BinaryFv.SSZ.Zesu.Contracts.Leaves
import BinaryFv.SSZ.Zesu.Contracts.Options
import BinaryFv.SSZ.Zesu.Contracts.Canonicality
import BinaryFv.SSZ.Zesu.Contracts.Containers
import BinaryFv.SSZ.Zesu.Contracts.Collections
import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.SSZ.Zesu.Contracts.Runtime
import BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors

/-!
# Kernel-checked per-routine meaning agreement (Row B, item 3)

For every typed leaf-routine vector (`ssz-routine-vectors-v1`), the handwritten `meaning*` produces the
vector's exact expected success value or exact local error — checked in the kernel by `native_decide`.
The host probe checks the same vectors against the real Zig routine (`--routine-vectors`), so together
`expected ≡ Zig-routine` (probe) and `expected ≡ meaning` (here) give `Zig-routine ≡ handwritten meaning`
per routine, at the exact-value / exact-error granularity Row B requires.

This is a validation module — falsification evidence, not a proof premise — and is not imported by the
theorem umbrella `BinaryFv`. Leaf readers fail only with `invalidSsz`, so a `none` expectation pins that
exact error (there is only one).
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Validation.GeneratedRoutineVectors

/-- A single hex digit's value (`16` for a non-digit, which `hexToBytes` never receives). -/
private def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then 10 + (c.toNat - 'a'.toNat)
  else 16

/-- Decode a hex string to bytes (iterative, so large cases run without deep recursion). -/
def hexToBytes (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  let mut i := 0
  while _h : i + 1 < cs.size do
    out := out.push (UInt8.ofNat (hexVal cs[i]! * 16 + hexVal cs[i + 1]!))
    i := i + 2
  return out

/-- One hex nibble as a lowercase char. -/
def nibbleHex (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

/-- A byte as two lowercase hex chars. -/
def byteHex (b : UInt8) : String :=
  String.mk [nibbleHex (b.toNat / 16), nibbleHex (b.toNat % 16)]

/-- A byte list as a lowercase hex string (matches the probe's rendering). -/
def bytesToHex (bs : List UInt8) : String :=
  String.join (bs.map byteHex)

/-- A `UInt64` as 8-byte little-endian hex — the probe's `tb.u64le` token. -/
def u64ToHexLE (v : UInt64) : String :=
  bytesToHex ((List.range 8).map (fun i => UInt8.ofNat ((v.toNat >>> (8 * i)) % 256)))

/-- A fixed byte-vector field as hex. -/
def bvHex {n : Nat} (v : SszBridge.RawByteVector n) : String := bytesToHex v.toArray.toList

/-- A variable byte-list field as hex. -/
def rbHex (a : SszBridge.RawBytes) : String := bytesToHex a.toList

/-- A `BitVec 256` (base fee) as 32-byte little-endian hex — the probe's `tb.u256le` token. -/
def bitvec256ToHexLE (v : BitVec 256) : String :=
  bytesToHex ((List.range 32).map (fun i => UInt8.ofNat ((v.toNat >>> (8 * i)) % 256)))

/-- The scalar-read meaning selected by routine name, as an `Option Nat` (`none` = `invalidSsz`). -/
def scalarMeaning (routine : String) (bytes : ByteArray) (offset : Nat) : Option Nat :=
  if routine == "ssz_raw.readU32" then (meaningReadU32 bytes offset).toOption.map UInt32.toNat
  else if routine == "ssz_raw.readU64" then (meaningReadU64 bytes offset).toOption.map UInt64.toNat
  else if routine == "ssz_raw.readU256" then (meaningReadU256 bytes offset).toOption.map BitVec.toNat
  else (meaningReadOffset bytes offset).toOption

/-- The slice-read meaning selected by routine name (`bytesAt` vs `readArray[N]`, `len` = the width). -/
def sliceMeaning (routine : String) (bytes : ByteArray) (offset len : Nat) : Option ByteArray :=
  if routine == "ssz_raw.bytesAt" then (meaningBytesAt bytes offset len).toOption
  else (meaningReadArray len bytes offset).toOption

/-- **Scalar reads:** `readU32`/`readOffset`/`readU64` meanings match the expected value/error. -/
theorem scalar_meaning_agrees :
    scalarVectors.all
      (fun v => scalarMeaning v.1 (hexToBytes v.2.2.1) v.2.2.2.1 == v.2.2.2.2) = true := by
  native_decide

/-- **Slice reads:** `bytesAt`/`readArray[N]` meanings match the expected input-relative bytes/error. -/
theorem slice_meaning_agrees :
    sliceVectors.all
      (fun v => sliceMeaning v.1 (hexToBytes v.2.2.1) v.2.2.2.1 v.2.2.2.2.1
        == v.2.2.2.2.2.map hexToBytes) = true := by
  native_decide

/-- **`requireU32Length`:** the meaning accepts exactly when the vector expects `ok`. -/
theorem require_u32_meaning_agrees :
    requireU32Vectors.all
      (fun v => isAccepted (meaningRequireU32Length (hexToBytes v.2.1)) == v.2.2) = true := by
  native_decide

/-- **`requireCanonicalOffsets`:** the offset-table check accepts exactly when the vector expects it
(canonical prefix table), rejecting wrong-first, descending, out-of-range, short-slice, and empty. -/
theorem canonical_offsets_meaning_agrees :
    canonicalOffsetsVectors.all
      (fun v => isAccepted (meaningRequireCanonicalOffsets (hexToBytes v.2.1) v.2.2.1 v.2.2.2.1)
        == v.2.2.2.2) = true := by
  native_decide

/-- **`hasExactErePrefix`:** the total predicate meaning matches the expected boolean. -/
theorem ere_prefix_meaning_agrees :
    erePrefixVectors.all
      (fun v => meaningHasExactErePrefix (hexToBytes v.2.1) == v.2.2) = true := by
  native_decide

/-- `decodeOptionalU64` as `Option (Option Nat)`: `none` = error, `some none` = SSZ `none`,
`some (some v)` = present. Options fail only with `invalidSsz`, so the outer `none` pins that error. -/
def optionU64Meaning (bytes : ByteArray) : Option (Option Nat) :=
  (meaningOptionalU64 bytes).toOption.map (fun o => o.map UInt64.toNat)

/-- `decodeOptionalBlobSchedule` as `Option (Option (target, max, baseFeeUpdateFraction))`. -/
def optionBlobMeaning (bytes : ByteArray) : Option (Option (Nat × Nat × Nat)) :=
  (meaningOptionalBlobSchedule bytes).toOption.map
    (fun o => o.map (fun s => (s.target.toNat, s.max.toNat, s.baseFeeUpdateFraction.toNat)))

/-- **`decodeOptionalU64`:** the meaning matches the expected absent/present/malformed outcome. -/
theorem optional_u64_meaning_agrees :
    optionalU64Vectors.all
      (fun v => optionU64Meaning (hexToBytes v.2.1) == v.2.2) = true := by
  native_decide

/-- **`decodeOptionalBlobSchedule`:** the meaning matches the expected absent/present/malformed
outcome, with exact `(target, max, baseFeeUpdateFraction)` fields on the present arm. -/
theorem optional_blob_meaning_agrees :
    optionalBlobVectors.all
      (fun v => optionBlobMeaning (hexToBytes v.2.1) == v.2.2) = true := by
  native_decide

/-!
## Non-allocating containers

`decodeForkActivation` / `decodeForkConfig` / `decodeChainConfig` return nested structs. Each is
flattened to a fixed-order list of `Nat` scalars (every `UInt64` field, each `Option` preceded by a
0/1 presence bit) — the SAME order the Zig probe and `ssz_routine_vectors.py` use, so all three encode
the same struct value. The expected outcome is `(Option (List Nat) × String)`: `(some scalars, "")` on
success, `(none, label)` on error, so `unknownFork` is pinned distinctly from `invalidSsz`.
-/

/-- The local error label, matching the probe's `errLabel` and the vectors' error strings. -/
def errLabelOf : SszDecodeError → String
  | .invalidSsz => "invalidSsz"
  | .unknownFork => "unknownFork"
  | .outOfMemory => "outOfMemory"

/-- One option field: presence bit then value (0 when absent). -/
def flatOptU64 (v : Option UInt64) : List Nat :=
  match v with | some x => [1, x.toNat] | none => [0, 0]

def flatForkActivation (fa : SszBridge.RawForkActivation) : List Nat :=
  flatOptU64 fa.blockNumber ++ flatOptU64 fa.timestamp

def flatBlob : Option SszBridge.RawBlobSchedule → List Nat
  | some s => [1, s.target.toNat, s.max.toNat, s.baseFeeUpdateFraction.toNat]
  | none => [0, 0, 0, 0]

def flatForkConfig (fc : SszBridge.RawForkConfig) : List Nat :=
  fc.fork.toNat :: (flatForkActivation fc.activation ++ flatBlob fc.blobSchedule)

def flatChainConfig (cc : SszBridge.RawChainConfig) : List Nat :=
  cc.chainId.toNat :: flatForkConfig cc.activeFork

/-- Normalize a container meaning to the vectors' `(Option (List Nat) × String)` encoding. -/
def containerEnc {α} (flat : α → List Nat) (r : Except SszDecodeError α) : Option (List Nat) × String :=
  match r with
  | .ok v => (some (flat v), "")
  | .error e => (none, errLabelOf e)

/-- **`decodeForkActivation`:** the flattened meaning matches the expected value/error. -/
theorem fork_activation_meaning_agrees :
    forkActivationVectors.all
      (fun v => containerEnc flatForkActivation (meaningForkActivation (hexToBytes v.2.1)) == v.2.2)
      = true := by
  native_decide

/-- **`decodeForkConfig`:** value + exact `unknownFork`/`invalidSsz`, including fork-bound ordering. -/
theorem fork_config_meaning_agrees :
    forkConfigVectors.all
      (fun v => containerEnc flatForkConfig (meaningForkConfig (hexToBytes v.2.1)) == v.2.2)
      = true := by
  native_decide

/-- **`decodeChainConfig`:** value + propagated `unknownFork` from the nested fork config. -/
theorem chain_config_meaning_agrees :
    chainConfigVectors.all
      (fun v => containerEnc flatChainConfig (meaningChainConfig (hexToBytes v.2.1)) == v.2.2)
      = true := by
  native_decide

/-!
## Collections (allocating)

Each element is rendered to the same list of hex field tokens the probe emits (`u64` fields as
8-byte little-endian hex, byte-vector fields as raw hex), and the collection value is the list of
elements. Expected is `(Option (List (List String)) × String)`: `(some elements, "")` on success,
`(none, label)` on error.
-/

/-- Normalize a collection meaning to the vectors' `(Option (List (List String)) × String)` form. -/
def collEnc {α} (render : α → List String) (r : Except SszDecodeError (Array α)) :
    Option (List (List String)) × String :=
  match r with
  | .ok arr => (some (arr.toList.map render), "")
  | .error e => (none, errLabelOf e)

theorem versioned_hashes_meaning_agrees :
    versionedHashesVectors.all
      (fun v => collEnc (fun h => [bvHex h]) (meaningVersionedHashes (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem public_keys_meaning_agrees :
    publicKeysVectors.all
      (fun v => collEnc (fun k => [bvHex k]) (meaningPublicKeys (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem withdrawals_meaning_agrees :
    withdrawalsVectors.all
      (fun v => collEnc (fun w => [u64ToHexLE w.index, u64ToHexLE w.validatorIndex,
        bvHex w.address, u64ToHexLE w.amount]) (meaningWithdrawals (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem deposit_requests_meaning_agrees :
    depositRequestsVectors.all
      (fun v => collEnc (fun d => [bvHex d.pubkey, bvHex d.withdrawalCredentials, u64ToHexLE d.amount,
        bvHex d.signature, u64ToHexLE d.index]) (meaningDepositRequests (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem withdrawal_requests_meaning_agrees :
    withdrawalRequestsVectors.all
      (fun v => collEnc (fun wr => [bvHex wr.sourceAddress, bvHex wr.validatorPubkey,
        u64ToHexLE wr.amount]) (meaningWithdrawalRequests (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem consolidation_requests_meaning_agrees :
    consolidationRequestsVectors.all
      (fun v => collEnc (fun c => [bvHex c.sourceAddress, bvHex c.sourcePubkey, bvHex c.targetPubkey])
        (meaningConsolidationRequests (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem byte_list_list_meaning_agrees :
    byteListListVectors.all
      (fun v => collEnc (fun it => [rbHex it])
        (meaningByteListList v.2.2.1 v.2.2.2.1 (hexToBytes v.2.1)) == v.2.2.2.2)
      = true := by native_decide

/-!
## Allocating containers (recursive value trees)

Each nested container meaning renders to the same `VTree` the probe emits (`.leaf` = a hex field,
`.node` = subtrees), in the pinned source's field order. Expected is `(Option VTree × String)`.
-/

def treeU64 (v : UInt64) : VTree := .leaf (u64ToHexLE v)
def treeBv {n : Nat} (v : SszBridge.RawByteVector n) : VTree := .leaf (bvHex v)
def treeRb (a : SszBridge.RawBytes) : VTree := .leaf (rbHex a)
def treeU256 (v : BitVec 256) : VTree := .leaf (bitvec256ToHexLE v)

def renderWithdrawal (w : SszBridge.RawWithdrawal) : VTree :=
  .node [treeU64 w.index, treeU64 w.validatorIndex, treeBv w.address, treeU64 w.amount]
def renderDeposit (d : SszBridge.RawDepositRequest) : VTree :=
  .node [treeBv d.pubkey, treeBv d.withdrawalCredentials, treeU64 d.amount, treeBv d.signature, treeU64 d.index]
def renderWithdrawalReq (wr : SszBridge.RawWithdrawalRequest) : VTree :=
  .node [treeBv wr.sourceAddress, treeBv wr.validatorPubkey, treeU64 wr.amount]
def renderConsolidation (c : SszBridge.RawConsolidationRequest) : VTree :=
  .node [treeBv c.sourceAddress, treeBv c.sourcePubkey, treeBv c.targetPubkey]

def renderExecutionRequests (er : SszBridge.RawExecutionRequests) : VTree :=
  .node [.node (er.deposits.toList.map renderDeposit),
    .node (er.withdrawals.toList.map renderWithdrawalReq),
    .node (er.consolidations.toList.map renderConsolidation)]

def renderExecutionWitness (ew : SszBridge.RawExecutionWitness) : VTree :=
  .node [.node (ew.state.toList.map treeRb), .node (ew.codes.toList.map treeRb),
    .node (ew.headers.toList.map treeRb)]

def renderExecutionPayload (ep : SszBridge.RawExecutionPayload) : VTree :=
  .node [treeBv ep.parentHash, treeBv ep.feeRecipient, treeBv ep.stateRoot, treeBv ep.receiptsRoot,
    treeBv ep.logsBloom, treeBv ep.prevRandao, treeU64 ep.blockNumber, treeU64 ep.gasLimit,
    treeU64 ep.gasUsed, treeU64 ep.timestamp, treeRb ep.extraData, treeU256 ep.baseFeePerGas,
    treeBv ep.blockHash, .node (ep.transactions.toList.map treeRb),
    .node (ep.withdrawals.toList.map renderWithdrawal),
    treeU64 ep.blobGasUsed, treeU64 ep.excessBlobGas, treeRb ep.blockAccessList, treeU64 ep.slotNumber]

def renderNewPayloadRequest (npr : SszBridge.RawNewPayloadRequest) : VTree :=
  .node [renderExecutionPayload npr.executionPayload,
    .node (npr.versionedHashes.toList.map treeBv), treeBv npr.parentBeaconBlockRoot,
    renderExecutionRequests npr.executionRequests]

/-- Normalize a nested-container meaning to `(Option VTree × String)`. -/
def containerTreeEnc {α} (render : α → VTree) (r : Except SszDecodeError α) : Option VTree × String :=
  match r with
  | .ok v => (some (render v), "")
  | .error e => (none, errLabelOf e)

theorem exec_requests_meaning_agrees :
    execRequestsVectors.all
      (fun v => containerTreeEnc renderExecutionRequests (meaningExecutionRequests (hexToBytes v.2.1))
        == v.2.2) = true := by native_decide

theorem exec_witness_meaning_agrees :
    execWitnessVectors.all
      (fun v => containerTreeEnc renderExecutionWitness (meaningExecutionWitness (hexToBytes v.2.1))
        == v.2.2) = true := by native_decide

theorem exec_payload_meaning_agrees :
    execPayloadVectors.all
      (fun v => containerTreeEnc renderExecutionPayload (meaningExecutionPayload (hexToBytes v.2.1))
        == v.2.2) = true := by native_decide

theorem new_payload_request_meaning_agrees :
    newPayloadRequestVectors.all
      (fun v => containerTreeEnc renderNewPayloadRequest (meaningNewPayloadRequest (hexToBytes v.2.1))
        == v.2.2) = true := by native_decide

/-!
## Internal entry routines

`decodeRaw` / `decode` return the whole `RawV4`. An option renders as a node (empty = none). `decode`
adds the raw-first / exact-ERE-length retry, so the tree is identical to `decodeRaw` on the retried body.
-/

def treeOptU64 (v : Option UInt64) : VTree :=
  match v with | some x => .node [treeU64 x] | none => .node []
def treeOptBlob (v : Option SszBridge.RawBlobSchedule) : VTree :=
  match v with
  | some s => .node [treeU64 s.target, treeU64 s.max, treeU64 s.baseFeeUpdateFraction]
  | none => .node []

def renderForkActivation (fa : SszBridge.RawForkActivation) : VTree :=
  .node [treeOptU64 fa.blockNumber, treeOptU64 fa.timestamp]
def renderForkConfig (fc : SszBridge.RawForkConfig) : VTree :=
  .node [treeU64 fc.fork, renderForkActivation fc.activation, treeOptBlob fc.blobSchedule]
def renderChainConfig (cc : SszBridge.RawChainConfig) : VTree :=
  .node [treeU64 cc.chainId, renderForkConfig cc.activeFork]

def renderStatelessInput (si : SszBridge.RawV4) : VTree :=
  .node [renderNewPayloadRequest si.newPayloadRequest, renderExecutionWitness si.witness,
    renderChainConfig si.chainConfig, .node (si.publicKeys.toList.map treeBv)]

theorem decode_raw_meaning_agrees :
    decodeRawVectors.all
      (fun v => containerTreeEnc renderStatelessInput (meaningDecodeRaw (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

theorem decode_meaning_agrees :
    decodeVectors.all
      (fun v => containerTreeEnc renderStatelessInput (meaningDecode (hexToBytes v.2.1)) == v.2.2)
      = true := by native_decide

/-!
## Runtime / allocator / root routines

`meaningAlloc` is the pinned `BumpHeap` arithmetic (address or none); `meaningCopy` is the identity;
`allocatorResize`/`Remap` are the constants `false`/`none`. The root accessors are driven by
`meaningDecode`: `zesu_decode_raw` returns 1 on accept, `zesu_raw_error` returns the DecodeStatus code
(ok 1 / invalidSsz 2 / unknownFork 3 / outOfMemory 4), `zesu_raw_result` is present exactly on accept.
-/

open BinaryFv.SSZ.Zesu.Runtime (BumpHeap)

/-- The bump-allocation address (relative to the heap base), or `none`. -/
def allocAddr (pos top bytes alignment : Nat) : Option Nat :=
  (meaningAlloc { position := pos, limit := top } bytes alignment).map Prod.fst

/-- The DecodeStatus code the exported `zesu_raw_error` returns, matching the Zig enum values. -/
def decodeStatusCode : Except SszDecodeError SszBridge.RawV4 → Nat
  | .ok _ => 1
  | .error .invalidSsz => 2
  | .error .unknownFork => 3
  | .error .outOfMemory => 4

/-- **`zesu_raw_alloc` / `allocatorAlloc`:** the bump address / out-of-memory matches. -/
theorem runtime_alloc_meaning_agrees :
    runtimeAllocVectors.all
      (fun v => allocAddr v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1 == v.2.2.2.2.2) = true := by
  native_decide

/-- **`memcpy` / `memmove`:** the meaning delivers the first `len` source bytes. -/
theorem runtime_copy_meaning_agrees :
    runtimeCopyVectors.all
      (fun v => meaningCopy ((hexToBytes v.2.1).extract 0 v.2.2.1) == hexToBytes v.2.2.2) = true := by
  native_decide

/-- **`allocatorResize` / `allocatorRemap`:** the constant meanings the vtable thunks return. -/
theorem runtime_resize_remap_meanings :
    meaningAllocatorResize = false ∧ meaningAllocatorRemap = none := ⟨rfl, rfl⟩

/-- **`zesu_decode_raw`:** returns 1 exactly on accept. -/
theorem runtime_decode_ret_meaning_agrees :
    runtimeDecodeRetVectors.all
      (fun v => (if isAccepted (meaningDecode (hexToBytes v.2.1)) then 1 else 0) == v.2.2) = true := by
  native_decide

/-- **`zesu_raw_error`:** returns the DecodeStatus code of the decode. -/
theorem runtime_error_meaning_agrees :
    runtimeErrorVectors.all
      (fun v => decodeStatusCode (meaningDecode (hexToBytes v.2.1)) == v.2.2) = true := by
  native_decide

/-- **`zesu_raw_result`:** present exactly on accept. -/
theorem runtime_result_meaning_agrees :
    runtimeResultVectors.all
      (fun v => isAccepted (meaningDecode (hexToBytes v.2.1)) == v.2.2) = true := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation
