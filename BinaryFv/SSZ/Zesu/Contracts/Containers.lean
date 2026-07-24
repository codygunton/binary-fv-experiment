import BinaryFv.SSZ.Zesu.Contracts.Collections
import BinaryFv.SSZ.Zesu.Contracts.Options

namespace BinaryFv.SSZ.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Container decoders

The seven containers, split two ways.

By allocation: `decodeChainConfig`, `decodeForkConfig`, and `decodeForkActivation` build fixed
records by value and **do not allocate**, so their postconditions deny allocation. The other four
allocate transitively through their collection children.

By meaning: the four allocating containers are `decodeCanonical` at their pinned schema followed by
the bridge's own `raw*Of` projection. The three non-allocating ones are **source-shaped**, because
their error ordering genuinely differs from the oracle's — see below.

`decodeForkConfig` is the decoder's only source of `UnknownFork`, and the audit recorded on issue #39
established that its *ordering* differs from the oracle: the binary raises `UnknownFork` after
validating offsets but before decoding activation and blob schedule, whereas the oracle checks
`fork > 20` only after a complete canonical decode. The two therefore disagree about which error a
malformed `fork = 21` payload yields, while always agreeing on rejection. `forkErrorOrderingDiffers`
records that explicitly so no container contract silently assumes error-constructor agreement.
-/

/-- Arguments of a container decoder that allocates through its children. -/
structure ContainerArgs where
  base : Nat
  bytes : ByteArray
  allocatorBase : Nat
  resultBase : Nat

/-- The representation obligation for a container result, to be discharged against the pinned ABI
manifest in the extraction row. Keeping it a parameter of the contract rather than a literal is what
lets these contracts stay address-free today.

It is applied as `rep inputBase input value state resultBase`: carrying the caller's input base and
bytes lets a representation describe the container's *input-relative borrowed slices* (`extra_data`,
transactions, witness nodes, …), not only its heap-owned and inline fields. Fixed containers ignore
the input arguments. -/
abbrev ContainerRepresentation (α : Type) := Nat → ByteArray → α → State → Nat → Prop

/-!
## Meanings
-/

/-!
The three non-allocating containers are **source-shaped**, not `decodeCanonical` at their schema.

That is a deliberate departure from the default rule, and the reason is a real ordering difference
rather than convenience. `decodeForkConfig` rejects `fork > 20` *after* validating its offset table
but *before* decoding its children, so a payload with `fork = 21` and a malformed activation yields
`unknownFork` from the binary. Writing the meaning as "decode canonically, then check the bound"
would yield `invalidSsz` on that input and the contract would be false — the compiler caught exactly
this when the first draft tried it.

Issue #39 permits "a small source-shaped Lean wrapper with an explicit equivalence theorem" for
precisely this case. The wrappers are built from cataloged leaf meanings, not from fresh byte
arithmetic, and `sourceShapedContainersAgreeWithOracle` below is the required equivalence obligation.
-/

/-- `decodeForkActivation`, source-shaped: fixed-size check, offset table, then two optional `u64`s. -/
def meaningForkActivation (bytes : ByteArray) :
    Except SszDecodeError SszBridge.RawForkActivation := do
  if bytes.size < 8 then throw .invalidSsz
  let first ← meaningReadOffset bytes 0
  let second ← meaningReadOffset bytes 4
  let _ ← meaningRequireCanonicalOffsets bytes 8 [first, second]
  let blockNumber ← meaningOptionalU64 (bytes.extract first second)
  let timestamp ← meaningOptionalU64 (bytes.extract second bytes.size)
  return { blockNumber := blockNumber, timestamp := timestamp }

/-- `decodeForkConfig`, source-shaped.

The `fork > 20` test sits between the offset-table check and the child decodes, exactly where the
source puts it. `LAST_PROTOCOL_FORK_INDEX` is pinned at the execution-specs Amsterdam revision. -/
def meaningForkConfig (bytes : ByteArray) : Except SszDecodeError SszBridge.RawForkConfig := do
  if bytes.size < 16 then throw .invalidSsz
  let first ← meaningReadOffset bytes 8
  let second ← meaningReadOffset bytes 12
  let _ ← meaningRequireCanonicalOffsets bytes 16 [first, second]
  let fork ← meaningReadU64 bytes 0
  if fork.toNat > 20 then throw .unknownFork
  let activation ← meaningForkActivation (bytes.extract first second)
  let blobSchedule ← meaningOptionalBlobSchedule (bytes.extract second bytes.size)
  return { fork := fork, activation := activation, blobSchedule := blobSchedule }

/-- `decodeChainConfig`, source-shaped. -/
def meaningChainConfig (bytes : ByteArray) : Except SszDecodeError SszBridge.RawChainConfig := do
  if bytes.size < 12 then throw .invalidSsz
  let activeForkOffset ← meaningReadOffset bytes 8
  let _ ← meaningRequireCanonicalOffsets bytes 12 [activeForkOffset]
  let chainId ← meaningReadU64 bytes 0
  let activeFork ← meaningForkConfig (bytes.extract activeForkOffset bytes.size)
  return { chainId := chainId, activeFork := activeFork }

def meaningExecutionWitness (bytes : ByteArray) :
    Except SszDecodeError SszBridge.RawExecutionWitness :=
  match SszBridge.decodeCanonical SszBridge.witnessType bytes with
  | .ok value => .ok (SszBridge.rawWitnessOf value)
  | .error error => .error (sszToDecodeError error)

def meaningExecutionRequests (bytes : ByteArray) :
    Except SszDecodeError SszBridge.RawExecutionRequests :=
  match SszBridge.decodeCanonical SszBridge.executionRequestsType bytes with
  | .ok value => .ok (SszBridge.rawExecutionRequestsOf value)
  | .error error => .error (sszToDecodeError error)

def meaningExecutionPayload (bytes : ByteArray) :
    Except SszDecodeError SszBridge.RawExecutionPayload :=
  match SszBridge.decodeCanonical SszBridge.executionPayloadType bytes with
  | .ok value => .ok (SszBridge.rawExecutionPayloadOf value)
  | .error error => .error (sszToDecodeError error)

def meaningNewPayloadRequest (bytes : ByteArray) :
    Except SszDecodeError SszBridge.RawNewPayloadRequest :=
  match SszBridge.decodeCanonical SszBridge.newPayloadRequestType bytes with
  | .ok value => .ok (SszBridge.rawNewPayloadRequestOf value)
  | .error error => .error (sszToDecodeError error)

/-!
## Pre- and postconditions
-/

def preContainer (env : DecoderEnvironment) (args : ContainerArgs) (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.resultBase) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size)

/-- A non-allocating container: builds a fixed record by value and touches no allocator state.

`representation` is supplied per container because each has its own field layout; making it a
parameter keeps this shared shape honest instead of collapsing distinct records into one vague
claim. It is applied at the result base with the caller's input base/bytes, so a representation may
describe input-relative borrowed slices. -/
def postFixedContainer {α : Type} (env : DecoderEnvironment) (args : ContainerArgs)
    (representation : ContainerRepresentation α)
    (result : Except SszDecodeError α) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.NoAllocation before after ∧
  match result with
  | .ok value => representation args.base args.bytes value after args.resultBase
  | .error error =>
      error = SszDecodeError.invalidSsz ∨ error = SszDecodeError.unknownFork

/-- An allocating container: its children allocate, so out-of-memory is reachable. -/
def postAllocatingContainer {α : Type} (env : DecoderEnvironment) (args : ContainerArgs)
    (representation : ContainerRepresentation α)
    (result : Except SszDecodeError α) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  match result with
  | .ok value => representation args.base args.bytes value after args.resultBase
  | .error error =>
      error = SszDecodeError.invalidSsz ∨ error = SszDecodeError.unknownFork ∨
        error = SszDecodeError.outOfMemory

/-!
## Contracts
-/

def contractForkActivation (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawForkActivation) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawForkActivation where
  meaning := fun args => meaningForkActivation args.bytes
  pre := preContainer env
  post := fun args => postFixedContainer env args rep
  stepBound := fun _ => 512

def contractForkConfig (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawForkConfig) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawForkConfig where
  meaning := fun args => meaningForkConfig args.bytes
  pre := preContainer env
  post := fun args => postFixedContainer env args rep
  stepBound := fun _ => 1024

def contractChainConfig (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawChainConfig) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawChainConfig where
  meaning := fun args => meaningChainConfig args.bytes
  pre := preContainer env
  post := fun args => postFixedContainer env args rep
  stepBound := fun _ => 2048

def contractExecutionWitness (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionWitness) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawExecutionWitness where
  meaning := fun args => meaningExecutionWitness args.bytes
  pre := preContainer env
  post := fun args => postAllocatingContainer env args rep
  stepBound := fun args => 1024 + 256 * args.bytes.size

def contractExecutionRequests (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionRequests) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawExecutionRequests where
  meaning := fun args => meaningExecutionRequests args.bytes
  pre := preContainer env
  post := fun args => postAllocatingContainer env args rep
  stepBound := fun args => 1024 + 256 * args.bytes.size

def contractExecutionPayload (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionPayload) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawExecutionPayload where
  meaning := fun args => meaningExecutionPayload args.bytes
  pre := preContainer env
  post := fun args => postAllocatingContainer env args rep
  stepBound := fun args => 4096 + 256 * args.bytes.size

def contractNewPayloadRequest (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawNewPayloadRequest) :
    FunctionContract SszDecodeError ContainerArgs SszBridge.RawNewPayloadRequest where
  meaning := fun args => meaningNewPayloadRequest args.bytes
  pre := preContainer env
  post := fun args => postAllocatingContainer env args rep
  stepBound := fun args => 8192 + 256 * args.bytes.size

/-!
## Correctness claims
-/

def correctnessClaimForkActivation (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawForkActivation)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractForkActivation env rep)

def correctnessClaimForkConfig (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawForkConfig)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractForkConfig env rep)

def correctnessClaimChainConfig (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawChainConfig)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractChainConfig env rep)

def correctnessClaimExecutionWitness (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionWitness)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractExecutionWitness env rep)

def correctnessClaimExecutionRequests (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionRequests)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractExecutionRequests env rep)

def correctnessClaimExecutionPayload (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionPayload)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractExecutionPayload env rep)

def correctnessClaimNewPayloadRequest (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawNewPayloadRequest)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractNewPayloadRequest env rep)

/-!
## Satisfiability

Container satisfiability is stated per representation: a representation whose field layout is
inconsistent has no witnessing state, so an unconditional claim would be exactly the impossible
assertion the review warned against. -/

def satisfiableForkActivation (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawForkActivation) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractForkActivation env rep)

def satisfiableForkConfig (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawForkConfig) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractForkConfig env rep)

def satisfiableChainConfig (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawChainConfig) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractChainConfig env rep)

def satisfiableExecutionWitness (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionWitness) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractExecutionWitness env rep)

def satisfiableExecutionRequests (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionRequests) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractExecutionRequests env rep)

def satisfiableExecutionPayload (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawExecutionPayload) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractExecutionPayload env rep)

def satisfiableNewPayloadRequest (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawNewPayloadRequest) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractNewPayloadRequest env rep)

/-!
## Characterizations
-/

/-- `decodeForkConfig` is the decoder's only source of `UnknownFork`. -/
def onlyForkConfigRaisesUnknownFork : Prop :=
  ∀ (bytes : ByteArray),
    meaningForkActivation bytes ≠ .error .unknownFork ∧
    meaningExecutionWitness bytes ≠ .error .unknownFork ∧
    meaningExecutionRequests bytes ≠ .error .unknownFork ∧
    meaningExecutionPayload bytes ≠ .error .unknownFork

/-- The three fixed containers never allocate, so out-of-memory is unreachable for them. -/
def fixedContainersNeverAllocate : Prop :=
  ∀ (bytes : ByteArray),
    meaningForkActivation bytes ≠ .error .outOfMemory ∧
    meaningForkConfig bytes ≠ .error .outOfMemory ∧
    meaningChainConfig bytes ≠ .error .outOfMemory

/--
The source-shaped container meanings agree with the oracle on acceptance.

They cannot agree on *error constructors* — that is the whole reason they are source-shaped — so the
obligation is stated at the granularity `root_compliance` actually observes.
-/
def sourceShapedContainersAgreeWithOracle : Prop :=
  ∀ (bytes : ByteArray),
    isAccepted (meaningChainConfig bytes) =
      (SszBridge.decodeCanonical SszBridge.chainConfigType bytes).toOption.isSome

/--
The binary and the oracle classify a malformed unknown-fork payload differently.

`meaningForkConfig` rejects on `fork > 20` before decoding children; the oracle decodes the whole
container canonically first and only then checks the bound. On a payload with `fork = 21` *and* a
malformed activation the source-shaped meaning yields `unknownFork` while the oracle yields a
structural error.

Both still reject, which is all `root_compliance` observes — but a container contract that claimed
the error constructors agreed would be false. Naming this is what stops that claim being made by
accident.
-/
def forkErrorOrderingDiffers : Prop :=
  ∃ (bytes : ByteArray),
    meaningForkConfig bytes = .error .unknownFork ∧
    (SszBridge.decodeCanonical SszBridge.forkConfigType bytes).toOption = none

end BinaryFv.SSZ.Zesu.Contracts
