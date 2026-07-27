import BinaryFv.SSZ.Zesu.Contracts.Containers
import BinaryFv.SSZ.SpecBridge.Decode

namespace BinaryFv.SSZ.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Entry points

`decodeRaw`, `decode`, and the exported `zesu_decode_raw`.

This is where the decoder's observable behaviour is finally compared against the oracle, and where
the equivalence audit recorded on issue #39 becomes machine-checkable rather than prose.

`decode` is raw-first with an ERE fallback, and the fallback is **not** symmetric with the oracle's:
the source retries the four-byte-stripped input only on `InvalidSsz`, never on `UnknownFork`, while
`SszBridge.decodeStatelessInput` retries on every `BridgeError` except `v3Quarantined`. That
difference is unreachable, and `retryTailNeverSchemaValid` below is the reason why — stated as an
obligation rather than left as a comment, because the whole root theorem leans on it.
-/

/-!
## Meanings

The entry points are source-shaped for the same reason the fixed containers are: their error
*ordering* and their retry *conditions* are observable, and an oracle-shaped meaning would be false
about the binary.
-/

/-- `decodeRaw`, source-shaped. -/
def meaningDecodeRaw (bytes : ByteArray) : Except SszDecodeError SszBridge.RawV4 := do
  let _ ← meaningRequireU32Length bytes
  if bytes.size < 2 then throw .invalidSsz
  if !(SszBridge.hasSchemaId bytes) then throw .invalidSsz
  let body := bytes.extract 2 bytes.size
  if body.size < 16 then throw .invalidSsz
  let zeroth ← meaningReadOffset body 0
  let first ← meaningReadOffset body 4
  let second ← meaningReadOffset body 8
  let third ← meaningReadOffset body 12
  let _ ← meaningRequireCanonicalOffsets body 16 [zeroth, first, second, third]
  let newPayloadRequest ← meaningNewPayloadRequest (body.extract zeroth first)
  let witness ← meaningExecutionWitness (body.extract first second)
  let chainConfig ← meaningChainConfig (body.extract second third)
  let publicKeys ← meaningPublicKeys (body.extract third body.size)
  return {
    newPayloadRequest := newPayloadRequest
    witness := witness
    chainConfig := chainConfig
    publicKeys := publicKeys
  }

/-- `decode`, source-shaped: raw first, then an exact-ERE-prefix retry **only** on `invalidSsz`.

`unknownFork` and `outOfMemory` propagate without a retry. That asymmetry is the source's, and
writing it any other way would make the contract false. -/
def meaningDecode (bytes : ByteArray) : Except SszDecodeError SszBridge.RawV4 :=
  match meaningDecodeRaw bytes with
  | .ok value => .ok value
  | .error .invalidSsz =>
      if meaningHasExactErePrefix bytes then
        meaningDecodeRaw (bytes.extract 4 bytes.size)
      else
        .error .invalidSsz
  | .error other => .error other

/-- `zesu_decode_raw`, the exported ABI boundary.

It normalizes every decoder error to a status code and returns `1` or `0`. The `alreadyDecoded`
status is reachable only on a second call, which is why the root theorem's precondition must pin
`attempted = false`. -/
inductive DecodeStatus where
  | notRun | ok | invalidSsz | unknownFork | outOfMemory | alreadyDecoded
deriving DecidableEq, Repr, Inhabited

/-- The pinned `DecodeStatus` enum values from the Zig source. -/
def DecodeStatus.code : DecodeStatus → Nat
  | .notRun => 0
  | .ok => 1
  | .invalidSsz => 2
  | .unknownFork => 3
  | .outOfMemory => 4
  | .alreadyDecoded => 5

def statusOfResult : Except SszDecodeError SszBridge.RawV4 → DecodeStatus
  | .ok _ => .ok
  | .error .invalidSsz => .invalidSsz
  | .error .unknownFork => .unknownFork
  | .error .outOfMemory => .outOfMemory

/-!
## Contracts
-/

structure EntryArgs where
  base : Nat
  bytes : ByteArray
  allocatorBase : Nat
  resultBase : Nat

def preEntry (env : DecoderEnvironment) (args : EntryArgs) (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.resultBase) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.allocatorBase) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x13 = some (BitVec.ofNat 64 args.bytes.size)

/-- The entry postcondition.

**`before` USED to be unused here, and the reason is worth keeping because it is what the ownership
clause changed.** It was ignored in all four postconditions that take it (`postEntry`,
`postAllocatingContainer`, `postCollection`, `postZesuDecodeRaw`) — the binder was required by
`FunctionContract`'s shape, not by the predicates. Three of the four now use it; `postZesuDecodeRaw`
alone still does not, for the reason its own docstring gives.

*Why it was not needed.* Preservation is stated **absolutely** — `MemoryBytes after args.base
args.bytes` and `env.CodeIntact after` — against values the precondition already pins to exactly the
same terms. So "unchanged from `before`" and "equal to `args.bytes`" coincide here, and the relative
form would say nothing more. Checked against each `pre` rather than assumed.

*What that does mean, and it is a real limitation rather than a tidy result.* A frame condition over
memory the precondition does **not** pin — "nothing outside the result buffer and the arena is
touched" — is **not expressible** in this form, and is not stated anywhere. Nothing in these contracts
forbids the decoder scribbling on unrelated memory.

**Why that is survivable here, corrected.** An earlier version of this note said `root_compliance` is
unaffected because it "observes only the classification and never reads memory". *That is false.*
`MemoryRepresentation.observeRawV4?` reads memory extensively — dozens of `observe*?` calls across the
result buffer and the heap descriptors. The argument that actually holds is different: the
representation is established **at the final state** (`rep … after …` here, `observeRawV4? state
canonicalResultBuffer` at the runner) rather than *preserved* from an intermediate one. Nothing has to
survive a later routine, so no frame condition is needed to connect two states.

**That question is now CLOSED, and this note is kept because it is the record of how.** The last
paragraph of the previous wording said a relative frame clause "would be a change to a reviewed
contract meaning and is the human's call", and asked that none be added on the strength of the note.
The call was made (`DECISIONS.md`, Row D): the settling fact is
`FrameGap.sibling_clobber_permitted_historical`, which made the clobber a theorem rather than a worry. So the clause is here —
`env.WritesOnlyWithinOwnAllocation`, the allocating form, since the entry allocates through its
children. The reasoning above is otherwise unchanged and still describes why this layer survived
without it.

**What is still true of the limitation above.** The clause confines writes to the entry's own record
and its own allocation, which is a frame condition over memory the precondition does not pin — so the
"not expressible in this form" paragraph no longer holds as written *for this predicate*. What it
still does not cover is the callee's stack frame; see `DecoderEnvironment.WritesOnlyWithinOwnAllocation`. -/
def postEntry (env : DecoderEnvironment) (args : EntryArgs)
    (rep : ContainerRepresentation SszBridge.RawV4)
    (result : Except SszDecodeError SszBridge.RawV4) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.WritesOnlyWithinOwnAllocation args.resultBase env.record.entryResult before after ∧
  match result with
  | .ok value => rep args.base args.bytes value after args.resultBase
  | .error error =>
      error = SszDecodeError.invalidSsz ∨ error = SszDecodeError.unknownFork ∨
        error = SszDecodeError.outOfMemory

def contractDecodeRaw (env : DecoderEnvironment) (rep : ContainerRepresentation SszBridge.RawV4) :
    FunctionContract SszDecodeError EntryArgs SszBridge.RawV4 where
  meaning := fun args => meaningDecodeRaw args.bytes
  pre := preEntry env
  post := fun args => postEntry env args rep
  stepBound := fun args => 16384 + 512 * args.bytes.size

def contractDecode (env : DecoderEnvironment) (rep : ContainerRepresentation SszBridge.RawV4) :
    FunctionContract SszDecodeError EntryArgs SszBridge.RawV4 where
  meaning := fun args => meaningDecode args.bytes
  pre := preEntry env
  -- Twice the raw bound: the ERE fallback can run `decodeRaw` a second time.
  stepBound := fun args => 2 * (16384 + 512 * args.bytes.size)
  post := fun args => postEntry env args rep

/-!
The exported `zesu_decode_raw` wrapper is **not** modelled here: its real interface is the C ABI plus
the three private decoder globals, and it lives in `Contracts.ExportedDecoder`. The `EntryArgs`
contracts below are the *internal* `decodeRaw`/`decode`, whose hidden result/error union genuinely
uses the `resultBase + 832` layout.
-/

/-!
## Correctness claims
-/

def correctnessClaimDecodeRaw (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawV4)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractDecodeRaw env rep)

def correctnessClaimDecode (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawV4)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractDecode env rep)

/-!
## Satisfiability
-/

def satisfiableDecodeRaw (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawV4) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractDecodeRaw env rep)

def satisfiableDecode (env : DecoderEnvironment)
    (rep : ContainerRepresentation SszBridge.RawV4) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractDecode env rep)

/-!
## The equivalence obligations

These are the statements the whole root theorem rests on, recorded as named `Prop`s so none of them
can quietly revert to prose. Each was established informally by the audit on issue #39; each still
owes a Lean proof.
-/

/-- The scope hypothesis of the root theorem, named rather than left implicit. -/
def rootComplianceScope (bytes : ByteArray) : Prop :=
  bytes.size < 2 * 1024 * 1024

/-- **The catalog's central obligation.** The source-shaped composition agrees with the oracle on the
**decoded value**, at the granularity `root_compliance` observes.

The binary decides canonicality by per-container offset checks plus `decodeByteListList`'s
zero-first-offset rejection; the oracle decides it globally by re-serializing. This says the two
coincide on the pinned V4 schema. If it were false, every individual contract would still be
provable — the machine faithfully implements its own weaker discipline — while the root theorem
quietly failed.

**Why this is an equality of results and not of acceptance, corrected.** It used to be
`isAccepted (meaningDecode bytes) = (decodeStatelessInput bytes).toOption.isSome`, justified as "the
granularity `root_compliance` observes". That justification was **false about the accepted branch**.
`root_compliance` concludes `RiscvSpec.execute binary input = .ok (SszSpec.decode input)`, and
`SszSpec.decode input = .accepted value` *is* `decodeStatelessInput input = .ok value` — so the root
must produce that exact `value`, while the machine stores `meaningDecode input`'s. From an acceptance
equation one can only conclude `meaningDecode input = .ok v'` for **some** `v'`; nothing tied `v'` to
`value`, and the accepted branch was therefore not provable from the catalog as it stood. The
acceptance equation is still available — it is a corollary
(`SemanticObligations.sourceShapedDecodeAgreesOnAcceptance`), not the obligation.

**The scope hypothesis is load-bearing, and its absence made the whole catalog unsatisfiable.**
Without `rootComplianceScope` this contradicts `ereGateDivergesAboveU32`, which asserts a witness —
outside the bound — that the composition accepts and the oracle rejects as `tooLarge`. At that
witness the unscoped biconditional makes the oracle return a value it does not, so
`catalogSemanticObligations ∧ knownDivergences` was jointly unsatisfiable and `root_compliance` was
vacuous. That is not an argument in a comment: `unscopedAgreement_contradicts_ereGate` in
`Contracts/SemanticObligations.lean` proves it **at this statement's own shape**, so the hypothesis
cannot be tidied away without breaking the build. `root_compliance` is itself stated under
`input.size < 2 * 1024 * 1024`, so nothing it consumes is lost. See `DECISIONS.md`. -/
def sourceShapedDecodeAgreesWithOracle : Prop :=
  ∀ (bytes : ByteArray), rootComplianceScope bytes → ∀ (value : SszBridge.RawV4),
    meaningDecode bytes = .ok value ↔ SszBridge.decodeStatelessInput bytes = .ok value

/-- The catalog's meanings are grounded in the pinned oracle, not in a private re-implementation:
the entry meaning determines exactly the public `SszSpec.decode` outcome — **including which value it
carries**.

This is `sourceShapedDecodeAgreesWithOracle` in the public spelling, and the two are now the same
statement rather than the same statement with the value dropped. The spelling is not cosmetic: it is
the one `root_compliance`'s accepted branch arrives holding, since that branch case-splits on
`SszSpec.decode input` and gets `= .accepted value` — so a consumer needs no unfolding of the bridge
to apply it.

Scoped for the same reason as `sourceShapedDecodeAgreesWithOracle`, and refuted unscoped by the same
`ereGateDivergesAboveU32` witness (`unscopedGrounds_contradicts_ereGate`). -/
def catalogGroundsInSpec : Prop :=
  ∀ (bytes : ByteArray), rootComplianceScope bytes → ∀ (value : SszBridge.RawV4),
    meaningDecode bytes = .ok value ↔ BinaryFv.SSZ.SszSpec.decode bytes = .accepted value

/--
Why the asymmetric ERE retry is unobservable.

Any input that reaches the top-level offset table must satisfy `hasSchemaId` and have a first offset
of exactly 16, which forces its bytes 2..6 to be `10 00 00 00`. Its four-byte-stripped tail therefore
begins `00 00` and fails `hasSchemaId`. So the retry can never succeed on precisely the inputs where
the binary and the oracle disagree about whether to attempt it.
-/
def retryTailNeverSchemaValid : Prop :=
  ∀ (bytes : ByteArray),
    SszBridge.hasSchemaId bytes = true →
    SszBridge.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16 →
      SszBridge.hasSchemaId (bytes.extract 4 bytes.size) = false

/-- A V3-shaped buffer is never a canonical V4 one: the V3 classifier demands the u32 at
execution-payload offset 436 be `528`, while a valid V4 payload demands `540`. This closes the
direct-accept route where the oracle quarantines and the binary would accept. -/
def v3ShapeExcludesCanonicalV4 : Prop :=
  ∀ (bytes : ByteArray),
    SszBridge.hasV3PayloadShape bytes = true →
      (SszBridge.decodeCanonical SszBridge.statelessInputV4Type
        (bytes.extract 2 bytes.size)).toOption = none

/--
A **known, bounded divergence** outside the root theorem's scope.

For `bytes.size ∈ [2^32, 2^32 + 3]` with an exact ERE prefix and a valid stripped tail, the binary
rejects the oversized buffer, then still passes `hasExactErePrefix` and accepts via the retry, while
`SszBridge.decodeStatelessInput` has a duplicate outer `size ≥ 2^32` gate that rejects with no retry.

`root_compliance` remains true — but *because of* `rootComplianceScope`, not incidentally. Recording
this as a `Prop` keeps the size bound's load-bearing role visible instead of looking like a
convenience. -/
def ereGateDivergesAboveU32 : Prop :=
  ∃ (bytes : ByteArray),
    ¬ rootComplianceScope bytes ∧
    isAccepted (meaningDecode bytes) = true ∧
    SszBridge.decodeStatelessInput bytes = .error .tooLarge

end BinaryFv.SSZ.Zesu.Contracts
