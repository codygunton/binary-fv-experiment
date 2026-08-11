import BinaryFv.Zesu.Contracts.Catalog.Entries
import BinaryFv.RiscV.Elfling.ProgramGeometry

namespace BinaryFv.Zesu.Contracts

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling

/-! ## Typed per-function-instance dispatch -/

/--
Everything a per-function-instance obligation needs beyond the instance itself: the pinned environment, the
allocator heap, the status slot, and the container/StatelessInput result representations.

Bundling these keeps `functionInstanceObligation` a total function while letting each container assert its own
result layout. -/
structure ContractParams where
  env : DecoderEnvironment
  heap : BinaryFv.Zesu.Runtime.BumpHeap
  /-- The pinned addresses of the three private decoder globals (`attempted`, 32-bit `last_status`,
  and the inline optional `stored_result` object), read back through the exported accessors. This replaces the
  previous free public 64-bit `statusBase` slot, which the wrapper never writes. -/
  globals : DecoderGlobalsLayout
  /-- The payload address returned by `zesu_raw_result` when `stored_result` is present. -/
  resultBuffer : Nat
  repForkActivation : ContainerRepresentation BinaryFv.Specs.SSZ.RawForkActivation
  repForkConfig : ContainerRepresentation BinaryFv.Specs.SSZ.RawForkConfig
  repChainConfig : ContainerRepresentation BinaryFv.Specs.SSZ.RawChainConfig
  repExecutionWitness : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionWitness
  repExecutionRequests : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionRequests
  repExecutionPayload : ContainerRepresentation BinaryFv.Specs.SSZ.RawExecutionPayload
  repNewPayloadRequest : ContainerRepresentation BinaryFv.Specs.SSZ.RawNewPayloadRequest
  repStatelessInput : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput

/-- One source function's handwritten contract with its argument and outcome types packaged alongside it.

Heterogeneity is the whole reason this exists. The decoder's leaves produce
`Except DecodeError _` over half a dozen argument records, while the exported wrapper produces
`DecodeCallOutcome`; there is no single `FunctionInstanceContract Args Outcome` the catalog could return.
Packaging the types lets **one** total dispatch select the real typed contract, after which the
closed and the local obligation are both formed from that same selection — so they cannot drift, and
neither can be stated for a contract the other does not use. Erasure to `Prop` happens only after a
branch has chosen its contract, never before. -/
structure TaggedContract where
  Args : Type
  Outcome : Type
  contract : FunctionInstanceContract Args Outcome

/--
The typed contract a generated function instance's source function `tag` selects.

This is the single point at which a function instance's identity becomes a handwritten contract. A source function
whose contract is source-shaped is projected through `FunctionContract.toFunctionInstance`; the exported
wrapper, whose outcome is richer than `Except`, supplies its `FunctionInstanceContract` directly. -/
def sourceFunctionContract (p : ContractParams) (function : FunctionId) (tag : ContractTag) :
    TaggedContract :=
  match tag with
  | .zesuDecodeRaw =>
      ⟨_, _, functionInstanceZesuDecodeRaw p.env p.globals p.resultBuffer p.repStatelessInput
                DecoderGlobalsModel.fresh⟩
  | .decode => ⟨_, _, (contractDecode p.env p.repStatelessInput).toFunctionInstance⟩
  | .decodeRaw => ⟨_, _, (contractDecodeRaw p.env p.repStatelessInput).toFunctionInstance⟩
  | .newPayloadRequest => ⟨_, _, (contractNewPayloadRequest p.env p.repNewPayloadRequest).toFunctionInstance⟩
  | .executionPayload => ⟨_, _, (contractExecutionPayload p.env p.repExecutionPayload).toFunctionInstance⟩
  | .executionRequests => ⟨_, _, (contractExecutionRequests p.env p.repExecutionRequests).toFunctionInstance⟩
  | .executionWitness => ⟨_, _, (contractExecutionWitness p.env p.repExecutionWitness).toFunctionInstance⟩
  | .chainConfig => ⟨_, _, (contractChainConfig p.env p.repChainConfig).toFunctionInstance⟩
  | .forkConfig => ⟨_, _, (contractForkConfig p.env p.repForkConfig).toFunctionInstance⟩
  | .forkActivation => ⟨_, _, (contractForkActivation p.env p.repForkActivation).toFunctionInstance⟩
  | .optionalU64 => ⟨_, _, (contractOptionalU64 p.env).toFunctionInstance⟩
  | .optionalBlobSchedule => ⟨_, _, (contractOptionalBlobSchedule p.env).toFunctionInstance⟩
  | .versionedHashes => ⟨_, _, (contractVersionedHashes p.env).toFunctionInstance⟩
  | .withdrawals => ⟨_, _, (contractWithdrawals p.env).toFunctionInstance⟩
  | .depositRequests => ⟨_, _, (contractDepositRequests p.env).toFunctionInstance⟩
  | .withdrawalRequests => ⟨_, _, (contractWithdrawalRequests p.env).toFunctionInstance⟩
  | .consolidationRequests => ⟨_, _, (contractConsolidationRequests p.env).toFunctionInstance⟩
  | .publicKeys => ⟨_, _, (contractPublicKeys p.env).toFunctionInstance⟩
  | .byteListList => ⟨_, _, (contractByteListList p.env).toFunctionInstance⟩
  | .requireCanonicalOffsets => ⟨_, _, (contractRequireCanonicalOffsets p.env).toFunctionInstance⟩
  | .requireU32Length => ⟨_, _, (contractRequireU32Length p.env).toFunctionInstance⟩
  | .readOffset => ⟨_, _, (contractReadOffset p.env).toFunctionInstance⟩
  | .readU32 => ⟨_, _, (contractReadU32 p.env).toFunctionInstance⟩
  | .readU64 => ⟨_, _, (contractReadU64 p.env).toFunctionInstance⟩
  | .readU256 => ⟨_, _, (contractReadU256 p.env).toFunctionInstance⟩
  | .readArray => ⟨_, _, (contractReadArray p.env (readArrayWidthOf function)).toFunctionInstance⟩
  | .bytesAt => ⟨_, _, (contractBytesAt p.env).toFunctionInstance⟩
  | .hasExactErePrefix => ⟨_, _, (contractHasExactErePrefix p.env).toFunctionInstance⟩
  | .rawAlloc => ⟨_, _, (contractAlloc p.env p.heap).toFunctionInstance⟩
  | .memcpy => ⟨_, _, (contractMemcpy p.env).toFunctionInstance⟩
  | .memmove => ⟨_, _, (contractMemmove p.env).toFunctionInstance⟩
  | .rawResult => ⟨_, _, (contractRawResult p.env p.globals p.resultBuffer).toFunctionInstance⟩
  | .rawError => ⟨_, _, (contractRawError p.env p.globals).toFunctionInstance⟩
  | .allocatorAlloc => ⟨_, _, (contractAllocatorAlloc p.env p.heap).toFunctionInstance⟩
  | .allocatorResize => ⟨_, _, (contractAllocatorResize p.env).toFunctionInstance⟩
  | .allocatorRemap => ⟨_, _, (contractAllocatorRemap p.env).toFunctionInstance⟩
  | .allocatorFree => ⟨_, _, (contractAllocatorFree p.env).toFunctionInstance⟩
  | .allocatorCtor => ⟨_, _, (contractAllocatorCtor p.env).toFunctionInstance⟩

/-- The run one function instance supplies to whoever splices it, at this contract's own types.

Every component the splice needs is present and typed: the arguments it was called with, its step
bound, a confined entered run of *exactly* `used` machine steps from its generated entry to one of
its generated exits, and its exit binding at the outcome its `meaning` prescribes. Nothing here is a
bare state relation — the binding handoff survives into the summary rather than being erased before
it is proved. -/
def TaggedContract.summary (tc : TaggedContract) (region exit : BitVec 64 → Prop)
    (entry : BitVec 64) (fromStep used : Nat) (s s' : BinaryFv.RiscV.State) : Prop :=
  tc.contract.summary region exit entry fromStep used s s'

/-- The entry PC of a generated function instance, as a machine word. Read off the function instance, never
existentially chosen. -/
def functionInstanceEntryWord (functionInstance : FunctionInstance) : BitVec 64 :=
  BitVec.ofNat 64 functionInstance.entryPc

/--
The **closed** correctness obligation a single generated function instance owes, selected by its source function
`tag`: it implements its contract, confined to where it executes, entering at its generated entry and
stopping at a generated exit.

The entry PC, exit predicate and reachable address set all come from generated data, never from an
existential, so a proof cannot pick a convenient entry, exit, or confinement. `reached` is the
function instance's transfer-graph extent — see `FunctionInstanceExecutionPcs` for why an obligation confined to the
function instance's own regions alone would be false for every function instance that calls out. -/
def functionInstanceObligation (p : ContractParams) (functionInstance : FunctionInstance)
    (reached : BitVec 64 → Prop) (tag : ContractTag) : Prop :=
  (sourceFunctionContract p functionInstance.id.function tag).contract.ImplementsFunctionInstance functionInstance reached
    (functionInstanceEntryWord functionInstance) (functionInstanceExitPred functionInstance)

/-- The satisfiability obligation for a source function's contract, selected by the same `tag`.

Aggregating these through the dispatch is what makes anti-vacuity uniform: every live instance's
contract must have a satisfiable precondition under a valid environment, stated at the source function's own
parameter level. -/
def sourceFunctionContractSatisfiable (p : ContractParams) (function : FunctionId) (tag : ContractTag) : Prop :=
  match tag with
  | .zesuDecodeRaw => satisfiableZesuDecodeRaw p.env p.globals p.resultBuffer p.repStatelessInput
  | .decode => satisfiableDecode p.env p.repStatelessInput
  | .decodeRaw => satisfiableDecodeRaw p.env p.repStatelessInput
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
