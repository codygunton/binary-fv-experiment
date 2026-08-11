import BinaryFv.Zesu.Contracts.Containers
import BinaryFv.Zesu.DecodedValue.Result
import BinaryFv.Specs.SSZ.Decode

namespace BinaryFv.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.DecodedValue
open LeanRV64DExecutable.Functions Register

/-!
# Entry points

`decodeRaw`, `decode`, and the exported `zesu_decode_raw`.

This is where the decoder's observable behaviour is finally compared against the spec, and where
the equivalence audit recorded on issue #39 becomes machine-checkable rather than prose.

`decode` is raw-first with an ERE fallback, and the fallback is **not** symmetric with the spec's:
the source retries the four-byte-stripped input only on `InvalidSsz`, never on `UnknownFork`, while
`BinaryFv.Specs.SSZ.decodeStatelessInput` retries on every `BridgeError` except `v3Quarantined`. That
difference is unreachable, and `retryTailNeverSchemaValid` below is the reason why — stated as an
obligation rather than left as a comment, because the whole root theorem leans on it.
-/

/-!
## Meanings

The entry points are source-shaped for the same reason the fixed containers are: their error
*ordering* and their retry *conditions* are observable, and a meaning defined directly from the specification would be false
about the binary.
-/

/-- `decodeRaw`, source-shaped. -/
def meaningDecodeRaw (bytes : ByteArray) : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput := do
  let _ ← meaningRequireU32Length bytes
  if bytes.size < 2 then throw .invalidSsz
  if !(BinaryFv.Specs.SSZ.hasSchemaId bytes) then throw .invalidSsz
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
def meaningDecode (bytes : ByteArray) : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput :=
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

def statusOfResult : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput → DecodeStatus
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

/-- The discriminant written by the internal `decodeRaw`/`decode` error union. This is not the
exported `DecodeStatus`: internal `outOfMemory` is tag `1`, while its exported status code is `4`. -/
def decodeInternalResultTag : Except DecodeError BinaryFv.Specs.SSZ.RawV4 → Nat
  | .ok _ => 0
  | .error .outOfMemory => 1
  | .error .invalidSsz => 2
  | .error .unknownFork => 3

/-- The entry postcondition.

**`before` USED to be unused here, and the reason is worth keeping because it is what the ownership
clause changed.** It was ignored in all four postconditions that take it (`postEntry`,
`postAllocatingContainer`, `postCollection`, `postZesuDecodeRaw`) — the binder was required by
`FunctionContract`'s shape, not by the predicates. All four now use it: three through the ownership
clause, and `postZesuDecodeRaw` — which still carries no ownership clause, for the reason its own
docstring gives — through its `ra`-preservation clause, which is relative by nature.

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
`DecodedValue.observeStatelessInput?` reads memory extensively — dozens of `observe*?` calls across the
result buffer and the heap descriptors. The argument that actually holds is different: the
representation is established **at the final state** (`rep … after …` here, `observeStatelessInput? state
canonicalResultBuffer` at the runner) rather than *preserved* from an intermediate one. Nothing has to
survive a later function instance, so no frame condition is needed to connect two states.

**That question is now CLOSED, and this note is kept because it is the record of how.** The last
paragraph of the previous wording said a relative frame clause "would be a change to a reviewed
contract meaning and is the human's call", and asked that none be added on the strength of the note.
The ownership requirement was adopted after `FrameGap.sibling_clobber_permitted_historical` made
the overwrite possible as a theorem rather than a concern. The settling fact is
`FrameGap.sibling_clobber_permitted_historical`, which made the clobber a theorem rather than a worry. So the clause is here —
`env.WritesOnlyWithinOwnAllocation`, the allocating form, since the entry allocates through its
children. The reasoning above is otherwise unchanged and still describes why this layer survived
without it.

**What is still true of the limitation above.** The clause confines writes to the entry's own record,
its own allocation, the allocator's state and the machine stack, which is a frame condition over
memory the precondition does not pin — so the "not expressible in this form" paragraph no longer holds
as written *for this predicate*. The stack is in that list because a compiled function instance writes its
frame and a clause omitting it would be false of the binary; see
`DecoderEnvironment.ownedRegion` for why each of the four is there and what permitting the stack gives
away. -/
def postEntry (env : DecoderEnvironment) (args : EntryArgs)
    (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.WritesOnlyWithinOwnAllocation args.resultBase env.record.entryResult before after ∧
  ResultStatusLERep after (args.resultBase + env.record.entryResultTagOffset)
    (decodeInternalResultTag result) ∧
  match result with
  | .ok value => rep args.base args.bytes value after args.resultBase
  | .error error =>
      error = DecodeError.invalidSsz ∨ error = DecodeError.unknownFork ∨
        error = DecodeError.outOfMemory

def contractDecodeRaw (env : DecoderEnvironment) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput) :
    FunctionContract DecodeError EntryArgs BinaryFv.Specs.SSZ.StatelessInput where
  meaning := fun args => meaningDecodeRaw args.bytes
  pre := preEntry env
  post := fun args => postEntry env args rep
  stepBound := fun args => 16384 + 512 * args.bytes.size

def contractDecode (env : DecoderEnvironment) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput) :
    FunctionContract DecodeError EntryArgs BinaryFv.Specs.SSZ.StatelessInput where
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
    (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractDecodeRaw env rep)

def correctnessClaimDecode (env : DecoderEnvironment)
    (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractDecode env rep)

/-!
## Satisfiability
-/

def satisfiableDecodeRaw (env : DecoderEnvironment)
    (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractDecodeRaw env rep)

def satisfiableDecode (env : DecoderEnvironment)
    (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput) : Prop :=
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

/-- **The catalog's central obligation.** The source-shaped composition agrees with the spec on the
**decoded value**, at the granularity `root_compliance` observes.

The binary decides canonicality by per-container offset checks plus `decodeByteListList`'s
zero-first-offset rejection; the spec decides it globally by re-serializing. This says the two
coincide on the pinned V4 schema. If it were false, every individual contract would still be
provable — the machine faithfully implements its own weaker discipline — while the root theorem
quietly failed.

**Why this is an equality of results and not of acceptance, corrected.** It used to be
`isAccepted (meaningDecode bytes) = (decodeStatelessInput bytes).toOption.isSome`, justified as "the
granularity `root_compliance` observes". That justification was **false about the accepted branch**.
`root_compliance` concludes `RiscvSpec.execute binary input = .ok (BinaryFv.Specs.SSZ.decode input)`, and
`BinaryFv.Specs.SSZ.decode input = .accepted value` *is* `decodeStatelessInput input = .ok value` — so the root
must produce that exact `value`, while the machine stores `meaningDecode input`'s. From an acceptance
equation one can only conclude `meaningDecode input = .ok v'` for **some** `v'`; nothing tied `v'` to
`value`, and the accepted branch was therefore not provable from the catalog as it stood. The
acceptance equation is still available — it is a corollary
(`SemanticObligations.sourceShapedDecodeAgreesOnAcceptance`), not the obligation.

**The scope hypothesis is load-bearing: without it this obligation is FALSE, not merely unproved.**
Dropped, it contradicts `ereGateDivergesAboveU32`, which asserts a witness — outside the bound — that
the composition accepts and the spec rejects as `tooLarge`. At that witness the unscoped
biconditional makes the spec return a value it does not. That is not an argument in a comment:
`unscopedAgreement_contradicts_ereGate` in `Contracts/SemanticObligations.lean` proves it **at this
statement's own shape**, so the hypothesis cannot be tidied away without breaking the build.
`root_compliance` is itself stated under `input.size < 2 * 1024 * 1024`, so nothing it consumes is
lost. See `DECISIONS.md`.

*Corrected once, and the correction is the reason the negative tests are worded the way they are.*
An earlier version of this note said the unscoped form made `catalogSemanticObligations ∧
knownDivergences` **jointly unsatisfiable**. That reading was only ever available because
`knownDivergences` then conjoined `ereGateDivergesAboveU32` itself; it now conjoins the weaker
`ereRetryReachedAboveU32Gate` (see the section note at the foot of this file), so the formal
conjunction is no longer the vehicle. The refutation above is unaffected, because it never went
through `knownDivergences` — it is a direct contradiction with the recorded acceptance-level
divergence, which is exactly why the two negative tests must keep citing that `Prop` and not the
provable one. -/
def sourceShapedDecodeAgreesWithSpec : Prop :=
  ∀ (bytes : ByteArray), rootComplianceScope bytes → ∀ (value : BinaryFv.Specs.SSZ.StatelessInput),
    meaningDecode bytes = .ok value ↔ BinaryFv.Specs.SSZ.decodeStatelessInput bytes = .ok value

/-- The catalog's meanings are grounded in the pinned spec, not in a private re-implementation:
the entry meaning determines exactly the public `BinaryFv.Specs.SSZ.decode` outcome — **including which value it
carries**.

This is `sourceShapedDecodeAgreesWithSpec` in the public spelling, and the two are now the same
statement rather than the same statement with the value dropped. The spelling is not cosmetic: it is
the one `root_compliance`'s accepted branch arrives holding, since that branch case-splits on
`BinaryFv.Specs.SSZ.decode input` and gets `= .accepted value` — so a consumer needs no unfolding of the bridge
to apply it.

Scoped for the same reason as `sourceShapedDecodeAgreesWithSpec`, and refuted unscoped by the same
`ereGateDivergesAboveU32` witness (`unscopedGrounds_contradicts_ereGate`). -/
def catalogGroundsInSpec : Prop :=
  ∀ (bytes : ByteArray), rootComplianceScope bytes → ∀ (value : BinaryFv.Specs.SSZ.StatelessInput),
    meaningDecode bytes = .ok value ↔ BinaryFv.Specs.SSZ.decode bytes = .accepted value

/--
Why the asymmetric ERE retry is unobservable.

Any input that reaches the top-level offset table must satisfy `hasSchemaId` and have a first offset
of exactly 16, which forces its bytes 2..6 to be `10 00 00 00`. Its four-byte-stripped tail therefore
begins `00 00` and fails `hasSchemaId`. So the retry can never succeed on precisely the inputs where
the binary and the spec disagree about whether to attempt it.
-/
def retryTailNeverSchemaValid : Prop :=
  ∀ (bytes : ByteArray),
    BinaryFv.Specs.SSZ.hasSchemaId bytes = true →
    BinaryFv.Specs.SSZ.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16 →
      BinaryFv.Specs.SSZ.hasSchemaId (bytes.extract 4 bytes.size) = false

/-- A V3-shaped buffer is never a canonical V4 one: the V3 classifier demands the u32 at
execution-payload offset 436 be `528`, while a valid V4 payload demands `540`. This closes the
direct-accept route where the spec quarantines and the binary would accept. -/
def v3ShapeExcludesCanonicalV4 : Prop :=
  ∀ (bytes : ByteArray),
    BinaryFv.Specs.SSZ.hasV3PayloadShape bytes = true →
      (BinaryFv.Specs.SSZ.decodeCanonical BinaryFv.Specs.SSZ.statelessInputV4Type
        (bytes.extract 2 bytes.size)).toOption = none

/-!
## The ERE-gate divergence, recorded twice

`decode`'s ERE retry sits above the spec's `size ≥ 2 ^ 32` gate, and the divergence there is
recorded at **two** strengths. That is deliberate, and this is the one place the relationship between
them is stated.

* `ereGateDivergesAboveU32` — the **acceptance-level** form: some oversized buffer the composition
  *accepts* while the spec rejects it as `tooLarge`. **True, and deliberately unproved**; its own
  docstring carries the evidence and the cost.
* `ereRetryReachedAboveU32Gate` — the **gate-level** form: some oversized buffer on which the binary
  *reaches* the ERE retry while the spec has already answered `tooLarge` without one. **Proved**,
  on an exhibited `2 ^ 32`-byte witness, in `Contracts/SemanticObligations`.

The gate-level form is strictly weaker: it says the two sides take different *paths*, not that they
arrive at different *answers*. That is not a hedge, it is a fact about the exhibited witness — at it
the retry does run and then fails on the stripped tail, so the composition rejects
(`ereGateWitness_not_accepted`), and no acceptance disagreement is available from that witness at all.

**Which one goes where, and why the weaker one is the one in `knownDivergences`.** A recorded
divergence carried as an *unproved conjunct* of the root's residue is a premise entering the residue
rather than leaving it. `knownDivergences` therefore conjoins the gate-level form, which can be
discharged (`knownDivergences_holds`), and the acceptance-level form is documented here rather than
assumed anywhere.

**And why the acceptance-level form must nevertheless stay.** The two negative tests in
`Contracts/SemanticObligations` — `unscopedAgreement_contradicts_ereGate` and
`unscopedGrounds_contradicts_ereGate` — need *acceptance*: they contradict an unscoped agreement by
pitting "the source accepts here" against a specification that rejects. The gate-level form supplies none,
and that is checked rather than asserted: at the witness discharging it the source rejects. So the
weaker fact was given a **new name** instead of being written over the old one. Restating
`ereGateDivergesAboveU32` in place would have left those two theorems reading identically while their
content collapsed to something strictly weaker — a check disarmed by a change made elsewhere, with
nothing to announce it. Both `Prop`s exist, and neither is redundant.
-/

/--
A **known, bounded divergence** outside the root theorem's scope, at acceptance granularity.

For `bytes.size ∈ [2^32, 2^32 + 3]` with an exact ERE prefix and a valid stripped tail, the binary
rejects the oversized buffer, then still passes `hasExactErePrefix` and accepts via the retry, while
`BinaryFv.Specs.SSZ.decodeStatelessInput` has a duplicate outer `size ≥ 2^32` gate that rejects with no retry.

`root_compliance` remains true — but *because of* `rootComplianceScope`, not incidentally. Recording
this as a `Prop` keeps the size bound's load-bearing role visible instead of looking like a
convenience.

**TRUE, and deliberately left unproved. It has no `_holds` and is not scheduled to get one.**
Recording why here, because "unproved" and "doubtful" are different states and only one of them is
the case:

* *It is satisfiable, so nothing downstream is vacuous.* `maxBytesPerTransaction = 2 ^ 30` and
  `maxTransactionsPerPayload = 2 ^ 20` (`BinaryFv/Specs/SSZ/AmsterdamV4.lean`), so
  accepted encodings reach roughly `2 ^ 50` — a factor of `2 ^ 18` above the `2 ^ 32` gate. The
  buffers this asserts to exist are admitted by the schema; they are merely enormous.
* *What a proof would cost.* The witness must be at least `2 ^ 32` bytes and, since
  `decodeStatelessInput` answers `tooLarge` exactly at `size ≥ 2 ^ 32`, its bulk has to sit inside a
  **mixed variable-size container**. The pinned spec's `SSZType.BasicSupported` has no such arm: its
  composite constructors are `vectorFixed`, `listFixed` and `containerFixed`, each demanding
  fixed-size elements or fields, and its own docstring puts mixed-field containers *outside* the
  predicate — "the offset-table decode path sits outside `Supported` itself; admitting it here is
  separate spec-layer work". `native_decide` is not an escape either: `decodeCanonical` re-serializes
  to check canonicality, and `SSZType.serializeFixedElems` is `serialize t x ++ serializeFixedElems t
  xs` — recursion depth proportional to the element count. The earlier investigation recorded
  evaluation dying near 170 KB, four orders of magnitude short of `2 ^ 32`. The estimate was one to
  three weeks, for documentation value about a divergence outside the root theorem's scope by
  construction.

So this stays a named `Prop`: consumed by the two negative tests, which need its acceptance content,
and by nothing that has to be discharged. -/
def ereGateDivergesAboveU32 : Prop :=
  ∃ (bytes : ByteArray),
    ¬ rootComplianceScope bytes ∧
    isAccepted (meaningDecode bytes) = true ∧
    BinaryFv.Specs.SSZ.decodeStatelessInput bytes = .error .tooLarge

/-- The same ERE/`tooLarge` divergence observed at the **gate** rather than at acceptance, stated
pointwise so a candidate witness can be refuted as well as exhibited.

Read as a description of one buffer: it is outside the root's scope; the binary's `decodeRaw` rejects
it as `invalidSsz` (its own `requireU32Length` is what fires); it nevertheless carries an exact ERE
prefix, so `decode` proceeds into the retry on the four-byte-stripped tail; and the spec has
already answered `tooLarge` at its outer gate, with no retry of any kind.

**The two sides therefore take different paths at the same buffer**, which is the whole of what this
records. It says nothing about which answers they end at — see the section note above. -/
def ereRetryAboveGateAt (bytes : ByteArray) : Prop :=
  ¬ rootComplianceScope bytes ∧
  meaningHasExactErePrefix bytes = true ∧
  meaningDecodeRaw bytes = .error .invalidSsz ∧
  meaningDecode bytes = meaningDecodeRaw (bytes.extract 4 bytes.size) ∧
  BinaryFv.Specs.SSZ.decodeStatelessInput bytes = .error .tooLarge

/-- **A known, bounded divergence at the ERE gate — the provable half.** Conjoined into
`knownDivergences`, and discharged by `ereRetryReachedAboveU32Gate_holds`. -/
def ereRetryReachedAboveU32Gate : Prop :=
  ∃ (bytes : ByteArray), ereRetryAboveGateAt bytes

end BinaryFv.Zesu.Contracts
