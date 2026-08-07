import BinaryFv.Zesu.Contracts.Catalog.Entries

namespace BinaryFv.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-! ## Typed per-instance dispatch -/

/--
Everything a per-instance obligation needs beyond the instance itself: the pinned environment, the
allocator heap, the status slot, and the container/RawV4 result representations.

Bundling these keeps `instanceObligation` a total function while letting each container assert its own
result layout. -/
structure ContractParams where
  env : DecoderEnvironment
  heap : BinaryFv.Zesu.Runtime.BumpHeap
  /-- The pinned addresses of the three private decoder globals (`attempted`, 32-bit `last_status`,
  optional `stored_result` pointer), read back through the exported accessors. This replaces the
  previous free public 64-bit `statusBase` slot, which the wrapper never writes. -/
  globals : DecoderGlobalsLayout
  /-- The canonical buffer the exported `stored_result` pointer points at on success. -/
  resultBuffer : Nat
  repForkActivation : ContainerRepresentation BinaryFv.Specs.SSZ.RawForkActivation
  repForkConfig : ContainerRepresentation BinaryFv.Specs.SSZ.RawForkConfig
  repChainConfig : ContainerRepresentation BinaryFv.Specs.SSZ.RawChainConfig
  repExecutionWitness : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionWitness
  repExecutionRequests : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionRequests
  repExecutionPayload : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionPayload
  repNewPayloadRequest : ContainerRepresentation BinaryFv.Specs.SSZ.RawNewPayloadRequest
  repRawV4 : ContainerRepresentation BinaryFv.Specs.SSZ.RawV4

/--
The correctness obligation a single generated occurrence owes, selected by its source function `tag`.

The entry PC and exit predicate come from the occurrence's generated data, never from an existential,
so a proof cannot pick a convenient entry or exit. Every branch returns the `correctnessClaim` for
exactly the source function the identity names; heterogeneous `Args`/`Result` types are erased to `Prop`
here, which is why one typed dispatch can cover the whole catalog. -/
def functionInstanceObligation (p : ContractParams) (instance_ : FunctionInstance) (tag : ContractTag) : Prop :=
  let entry : BitVec 64 := BitVec.ofNat 64 instance_.entryPc
  let exit : BitVec 64 → Prop := fun pc => instance_.isExit pc.toNat
  match tag with
  | .zesuDecodeRaw =>
      correctnessClaimZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4 instance_ entry exit
  | .decode => correctnessClaimDecode p.env p.repRawV4 instance_ entry exit
  | .decodeRaw => correctnessClaimDecodeRaw p.env p.repRawV4 instance_ entry exit
  | .newPayloadRequest =>
      correctnessClaimNewPayloadRequest p.env p.repNewPayloadRequest instance_ entry exit
  | .executionPayload =>
      correctnessClaimExecutionPayload p.env p.repExecutionPayload instance_ entry exit
  | .executionRequests =>
      correctnessClaimExecutionRequests p.env p.repExecutionRequests instance_ entry exit
  | .executionWitness =>
      correctnessClaimExecutionWitness p.env p.repExecutionWitness instance_ entry exit
  | .chainConfig => correctnessClaimChainConfig p.env p.repChainConfig instance_ entry exit
  | .forkConfig => correctnessClaimForkConfig p.env p.repForkConfig instance_ entry exit
  | .forkActivation => correctnessClaimForkActivation p.env p.repForkActivation instance_ entry exit
  | .optionalU64 => correctnessClaimOptionalU64 p.env instance_ entry exit
  | .optionalBlobSchedule => correctnessClaimOptionalBlobSchedule p.env instance_ entry exit
  | .versionedHashes => correctnessClaimVersionedHashes p.env instance_ entry exit
  | .withdrawals => correctnessClaimWithdrawals p.env instance_ entry exit
  | .depositRequests => correctnessClaimDepositRequests p.env instance_ entry exit
  | .withdrawalRequests => correctnessClaimWithdrawalRequests p.env instance_ entry exit
  | .consolidationRequests => correctnessClaimConsolidationRequests p.env instance_ entry exit
  | .publicKeys => correctnessClaimPublicKeys p.env instance_ entry exit
  | .byteListList => correctnessClaimByteListList p.env instance_ entry exit
  | .requireCanonicalOffsets => correctnessClaimRequireCanonicalOffsets p.env instance_ entry exit
  | .requireU32Length => correctnessClaimRequireU32Length p.env instance_ entry exit
  | .readOffset => correctnessClaimReadOffset p.env instance_ entry exit
  | .readU32 => correctnessClaimReadU32 p.env instance_ entry exit
  | .readU64 => correctnessClaimReadU64 p.env instance_ entry exit
  | .readU256 => correctnessClaimReadU256 p.env instance_ entry exit
  | .readArray =>
      correctnessClaimReadArray p.env (readArrayWidthOf instance_.id.function) instance_ entry exit
  | .bytesAt => correctnessClaimBytesAt p.env instance_ entry exit
  | .hasExactErePrefix => correctnessClaimHasExactErePrefix p.env instance_ entry exit
  | .rawAlloc => correctnessClaimAlloc p.env p.heap instance_ entry exit
  | .memcpy => correctnessClaimMemcpy p.env instance_ entry exit
  | .memmove => correctnessClaimMemmove p.env instance_ entry exit
  | .rawResult =>
      correctnessClaimRawResult p.env p.globals p.resultBuffer instance_ entry exit
  | .rawError => correctnessClaimRawError p.env p.globals instance_ entry exit
  | .allocatorAlloc => correctnessClaimAllocatorAlloc p.env p.heap instance_ entry exit
  | .allocatorResize => correctnessClaimAllocatorResize p.env instance_ entry exit
  | .allocatorRemap => correctnessClaimAllocatorRemap p.env instance_ entry exit
  | .allocatorFree => correctnessClaimAllocatorFree p.env instance_ entry exit
  | .allocatorCtor => correctnessClaimAllocatorCtor p.env instance_ entry exit

/-- The satisfiability obligation for a source function's contract, selected by the same `tag`.

Aggregating these through the dispatch is what makes anti-vacuity uniform: every live instance's
contract must have a satisfiable precondition under a valid environment, stated at the source function's own
parameter level. -/
def sourceFunctionContractSatisfiable (p : ContractParams) (function : FunctionId) (tag : ContractTag) : Prop :=
  match tag with
  | .zesuDecodeRaw => satisfiableZesuDecodeRaw p.env p.globals p.resultBuffer p.repRawV4
  | .decode => satisfiableDecode p.env p.repRawV4
  | .decodeRaw => satisfiableDecodeRaw p.env p.repRawV4
  | .newPayloadRequest => satisfiableNewPayloadRequest p.env p.repNewPayloadRequest
  | .executionPayload => satisfiableExecutionPayload p.env p.repExecutionPayload
  | .executionRequests => satisfiableExecutionRequests p.env p.repExecutionRequests
  | .executionWitness => satisfiableExecutionWitness p.env p.repExecutionWitness
  | .chainConfig => satisfiableChainConfig p.env p.repChainConfig
  | .forkConfig => satisfiableForkConfig p.env p.repForkConfig
  | .forkActivation => satisfiableForkActivation p.env p.repForkActivation
  | .optionalU64 => satisfiableOptionalU64 p.env
  | .optionalBlobSchedule => satisfiableOptionalBlobSchedule p.env
  | .versionedHashes => satisfiableVersionedHashes p.env
  | .withdrawals => satisfiableWithdrawals p.env
  | .depositRequests => satisfiableDepositRequests p.env
  | .withdrawalRequests => satisfiableWithdrawalRequests p.env
  | .consolidationRequests => satisfiableConsolidationRequests p.env
  | .publicKeys => satisfiablePublicKeys p.env
  | .byteListList => satisfiableByteListList p.env
  | .requireCanonicalOffsets => satisfiableRequireCanonicalOffsets p.env
  | .requireU32Length => satisfiableRequireU32Length p.env
  | .readOffset => satisfiableReadOffset p.env
  | .readU32 => satisfiableReadU32 p.env
  | .readU64 => satisfiableReadU64 p.env
  | .readU256 => satisfiableReadU256 p.env
  | .readArray => satisfiableReadArray p.env (readArrayWidthOf function)
  | .bytesAt => satisfiableBytesAt p.env
  | .hasExactErePrefix => satisfiableHasExactErePrefix p.env
  | .rawAlloc => satisfiableAlloc p.env p.heap
  | .memcpy => satisfiableMemcpy p.env
  | .memmove => satisfiableMemmove p.env
  | .rawResult => satisfiableRawResult p.env p.globals p.resultBuffer
  | .rawError => satisfiableRawError p.env p.globals
  | .allocatorAlloc => satisfiableAllocatorAlloc p.env p.heap
  | .allocatorResize => satisfiableAllocatorResize p.env
  | .allocatorRemap => satisfiableAllocatorRemap p.env
  | .allocatorFree => satisfiableAllocatorFree p.env
  | .allocatorCtor => satisfiableAllocatorCtor p.env



end BinaryFv.Zesu.Contracts
