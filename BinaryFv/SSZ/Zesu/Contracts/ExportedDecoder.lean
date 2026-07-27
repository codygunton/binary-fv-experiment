import BinaryFv.SSZ.Zesu.Contracts.Entry
import BinaryFv.RiscV.Platform.NormalState

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Contract for the public decoder API

This file models the three functions visible to a caller:

- `zesu_decode_raw(input, len) -> i32` runs the decoder once and returns `1` for success or `0` for
  failure;
- `zesu_raw_result()` returns the address of the stored value after a successful call, or null;
- `zesu_raw_error()` returns the recorded 32-bit status.

The wrapper receives the input pointer in RISC-V register `a0` and its length in `a1`. It stores its
state in three private globals: a one-byte `attempted` flag, `last_status`, and an inline
`?RawStatelessInput` object named `stored_result`. That object is 848 bytes: its 832-byte payload
starts at offset 0 and its discriminant is at offset 832. It is not a pointer slot.

The internal Zig function `decodeRaw` uses a different hidden-result ABI. Its representation remains
in `MemoryRepresentation.Result`; none of that internal calling convention is used here.
-/

/-- The addresses of the three private decoder globals, as pinned by the linker map.

These are *addresses*, address-bearing and therefore an artifact fact — a contract names the layout
record, never the literals. -/
structure DecoderGlobalsLayout where
  /-- Address of the one-byte `attempted` flag. -/
  attempted : Nat
  /-- Address of the 32-bit `last_status` word. -/
  status : Nat
  /-- Address of the inline `stored_result` object (a `?RawStatelessInput`, not a pointer slot): the
  848-byte optional result whose 832-byte payload sits at `storedResult + storedResultObject.payloadOffset`
  and whose discriminant sits at `storedResult + storedResultObject.discriminantOffset`. -/
  storedResult : Nat
  /-- The compiler-reflected `?RawStatelessInput` layout of the `stored_result` object (size 848,
  payload at 0, discriminant at 832). -/
  storedResultObject : OptionLayout
deriving Repr, Inhabited

/-- The ghost model of the decoder globals: whether a decode was attempted, the recorded status, and
the stored result value if one was produced.

`stored` holds the decoded value; how that value is realized in the inline global object is the
representation's job. These are ghost values, not ABI
arguments: the exported accessors observe canonical global memory and this model is what that memory
represents. -/
structure DecoderGlobalsModel where
  attempted : Bool
  status : DecodeStatus
  stored : Option SszBridge.RawV4

/-- The real C ABI arguments of `zesu_decode_raw`: the borrowed input pointer and its length.

There is no result-buffer or allocator argument here — those belonged to the internal convention. -/
structure ZesuDecodeRawArgs where
  inputBase : Nat
  bytes : ByteArray

/-- The observable outcome of one call to the exported wrapper.

`alreadyDecoded` is not a decode result at all: it is what a *second* call produces, because the
wrapper refuses to run once `attempted` is set. Modelling it as a distinct outcome is what makes the
"second call" behaviour statable, and is why the root theorem's precondition must pin a fresh
`attempted = false`. -/
inductive DecodeCallOutcome
  | success (value : SszBridge.RawV4)
  | rejected (error : SszDecodeError)
  | alreadyDecoded

namespace DecodeCallOutcome

/-- The `a0` return code: `1` on a fresh successful decode, `0` otherwise (rejection or a refused
second call). -/
def returnCode : DecodeCallOutcome → Nat
  | success _ => 1
  | rejected _ => 0
  | alreadyDecoded => 0

/-- The `last_status` this outcome records. -/
def status : DecodeCallOutcome → DecodeStatus
  | success _ => .ok
  | rejected error => statusOfResult (.error error)
  | alreadyDecoded => .alreadyDecoded

/-- The stored result value this outcome leaves behind, if any. -/
def stored : DecodeCallOutcome → Option SszBridge.RawV4
  | success value => some value
  | rejected _ => none
  | alreadyDecoded => none

/-- Whether this outcome is a fresh acceptance (the only case that returns a non-null result). -/
def accepted : DecodeCallOutcome → Bool
  | success _ => true
  | rejected _ => false
  | alreadyDecoded => false

end DecodeCallOutcome

/-- The observable outcome of a wrapper call, given the incoming globals model and the pure decode
result.

If a decode was already attempted the call is refused and yields `alreadyDecoded`; otherwise the
decode result becomes `success`/`rejected`. -/
def callOutcome (incoming : DecoderGlobalsModel)
    (result : Except SszDecodeError SszBridge.RawV4) : DecodeCallOutcome :=
  if incoming.attempted then
    .alreadyDecoded
  else
    match result with
    | .ok value => .success value
    | .error error => .rejected error

/-- The globals model after a wrapper call: a fresh call records the attempt, its status, and its
stored value; a refused second call leaves the globals exactly as they were. -/
def resultingGlobals (incoming : DecoderGlobalsModel)
    (result : Except SszDecodeError SszBridge.RawV4) : DecoderGlobalsModel :=
  if incoming.attempted then
    incoming
  else
    { attempted := true
      status := (callOutcome incoming result).status
      stored := (callOutcome incoming result).stored }

/-!
## Representing the globals in canonical memory

An `attempted` flag is one byte; `last_status` is a 32-bit little-endian word. The inline
`stored_result` object — its discriminant byte and, on success, the `RawV4` payload laid out at the
object's payload address — is represented separately (`StoredResultRep`) because that ties a *value*
to memory and needs the canonical payload location.
-/

/-- A concrete little-endian 32-bit word in Sail sparse memory. -/
def Word32LERep (state : State) (base value : Nat) : Prop :=
  ∀ index, index < 4 →
    state.mem.get? (base + index) = some (BitVec.ofNat 8 ((value / 256 ^ index) % 256))

/-- A one-byte boolean flag in Sail sparse memory (`1` for `true`, `0` for `false`). -/
def FlagRep (state : State) (base : Nat) (value : Bool) : Prop :=
  state.mem.get? base = some (BitVec.ofNat 8 (if value then 1 else 0))

/-- The scalar part of the decoder globals — the `attempted` flag and the 32-bit `last_status` —
represents `model` at `layout`. The inline `stored_result` object is `StoredResultRep`. -/
def DecoderGlobalsScalarRep (layout : DecoderGlobalsLayout) (model : DecoderGlobalsModel)
    (state : State) : Prop :=
  FlagRep state layout.attempted model.attempted ∧
  Word32LERep state layout.status model.status.code

/-- The discriminant byte of the inline `stored_result` object (`?RawStatelessInput`): present exactly
when the ghost model holds a value. `zesu_raw_result` reads this — not a pointer word — to decide
whether to return the payload address or null, so the accessor needs neither the container
representation nor the input. -/
def StoredResultDiscriminantRep (layout : DecoderGlobalsLayout) (model : DecoderGlobalsModel)
    (state : State) : Prop :=
  MemoryRepresentation.OptionTagRep state
    (layout.storedResult + layout.storedResultObject.discriminantOffset) model.stored.isSome

/-- The complete inline `stored_result` object: its discriminant, and — on success — the `RawV4`
payload laid out at `resultBase` (the object's payload address) under the full container
representation. The value arm carries the caller's input base/bytes so the borrowed input slices of
the stored `RawV4` are represented. -/
def StoredResultRep (layout : DecoderGlobalsLayout) (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase : Nat) (input : ByteArray) (resultBase : Nat) (model : DecoderGlobalsModel)
    (state : State) : Prop :=
  StoredResultDiscriminantRep layout model state ∧
  match model.stored with
  | some value => rep inputBase input value state resultBase
  | none => True

/-- The complete incoming/outgoing representation of all three decoder globals against a ghost model:
the scalar `attempted`/`last_status` words and the full inline `stored_result` object. -/
def DecoderGlobalsRep (layout : DecoderGlobalsLayout) (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase : Nat) (input : ByteArray) (resultBase : Nat) (model : DecoderGlobalsModel)
    (state : State) : Prop :=
  DecoderGlobalsScalarRep layout model state ∧
  StoredResultRep layout rep inputBase input resultBase model state

/-!
## Model-level facts

These are `Prop`-level checks on the model, independent of any Sail execution — the definitional
half of Row A's vertical tests.
-/

/-- **Second decoder call produces `alreadyDecoded`.** Once `attempted` is set, any call outcome is
`alreadyDecoded` with status `.alreadyDecoded` and a `0` return, regardless of the input's decode
result, and the globals are left untouched. -/
theorem second_call_is_alreadyDecoded (incoming : DecoderGlobalsModel)
    (result : Except SszDecodeError SszBridge.RawV4) (h : incoming.attempted = true) :
    callOutcome incoming result = .alreadyDecoded ∧
    (callOutcome incoming result).status = .alreadyDecoded ∧
    (callOutcome incoming result).returnCode = 0 ∧
    resultingGlobals incoming result = incoming := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [callOutcome, resultingGlobals, DecodeCallOutcome.status, DecodeCallOutcome.returnCode, h]

/-- **A fresh successful call returns `1` and stores the value.** The exact stored-result tag and
payload and the accessor's return follow. -/
theorem fresh_success_stores_value (incoming : DecoderGlobalsModel) (value : SszBridge.RawV4)
    (hfresh : incoming.attempted = false) :
    callOutcome incoming (.ok value) = .success value ∧
    (callOutcome incoming (.ok value)).returnCode = 1 ∧
    (callOutcome incoming (.ok value)).status = .ok ∧
    (resultingGlobals incoming (.ok value)).stored = some value := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [callOutcome, resultingGlobals, DecodeCallOutcome.status, DecodeCallOutcome.returnCode,
      DecodeCallOutcome.stored, hfresh]

/-- **A fresh rejected call returns `0` and stores nothing**, recording the exact rejection status. -/
theorem fresh_rejection_stores_nothing (incoming : DecoderGlobalsModel) (error : SszDecodeError)
    (hfresh : incoming.attempted = false) :
    callOutcome incoming (.error error) = .rejected error ∧
    (callOutcome incoming (.error error)).returnCode = 0 ∧
    (resultingGlobals incoming (.error error)).stored = none := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [callOutcome, resultingGlobals, DecodeCallOutcome.returnCode, DecodeCallOutcome.stored,
      hfresh]

/-- The fresh decoder-global model the root theorem's runner starts from: nothing attempted, no
status, no stored result. -/
def DecoderGlobalsModel.fresh : DecoderGlobalsModel :=
  { attempted := false, status := .notRun, stored := none }

/-!
## The exported wrapper contract

The wrapper's shared meaning is the internal `decodeRaw`-then-`decode` composition, the same spec the
internal contracts use. Its binding is the real one: the C ABI on entry, and the three private
globals plus the return code on exit, read against an incoming ghost globals model. The catalog
instantiates it at `DecoderGlobalsModel.fresh`; a second call is the same binding at an already
`attempted` model.

### The callee-frame clauses, and why these two exactly

`postZesuDecodeRaw` here and `postRawResult`/`postRawError` in `Contracts.Runtime` each carry

```
after.regs.get? x1 = before.regs.get? x1     -- `ra` preserved across the call
NormalExecutionState after                    -- platform/CSR state survives the call
```

and this is the one place the reasoning is written out; the accessors' docstrings point here.

**What consumes them.** A `TraceToSentinel` — what the runner's fuel argument and the root theorem
are stated against — is built from a contract's `EnteredFunctionTrace` by
`RiscV/Elfling/SentinelBridge.lean`, which appends the function's final `ret`. That bridge has two
demands at the *exit* state, and they are not the same demand:

* `traceToSentinel_of_functionTrace_ret`'s `linkIsSentinel` needs the value `ret` reads out of the
  link register to be the sentinel. The runner put the sentinel there
  (`buildZesuEntryState_entry_binding_abi` exposes `x1 := canonicalRunnerLayout.sentinel` at the
  entry state), so what is missing is that the *call* did not disturb it — the `x1` clause.
* `tryStepRetRetires`, which supplies that bridge's `ret` premise, wants ~20 hypotheses about the
  exit state; `NormalExecutionState after` is the register/CSR-valued part of them.

Before this change the contract layer supplied **neither**: no `post*` predicate in this directory
mentioned `x1` at all, and `NormalExecutionState` was reachable only at the state the runner builds.

**Preservation, not equality with the sentinel.** The clause is deliberately *not*
`after.regs.get? x1 = some sentinelWord`. The sentinel is the **runner's** choice of an unmapped
address, and a contract in this layer may not name it — that is the same address-freedom rule the
rest of the file follows. Preservation is also the form that composes: it is what turns the entry
state's `x1 := sentinel` into the exit state's, and it stays true of a routine called from anywhere
else, which an equation naming one caller's sentinel would not.

**`NormalExecutionState` rather than a list of CSR reads.** It is `RiscV/Platform/NormalState.lean`'s
twelve-conjunct bundle — hart state, privilege, `satp`, `mideleg`/`mie`/`mip`, the PMP tables,
`mcountinhibit`, `minstretcfg`, the landing-pad expectation and the `misa` `Zca` bit — and spelling
those out per predicate would be the same clause written longer. It is a **value**-pinning predicate,
which is worth noting because one register read `tryStepRetRetires` wants is *not* of that kind:
`retiredRead : state.regs.get? minstret = some retired` is a presence claim at an existentially bound
value, so it is not expressible as a conjunct here and is not covered by this change.

**True of the binary, established before the clauses were accepted rather than after.** `ra` is
callee-saved under RV64 LP64; the whole-program disassembly found `zesu_raw_result` (8 instructions)
and `zesu_raw_error` (3) are leaves with no prologue and zero stores, so they cannot disturb `ra` or
any CSR, and `zesu_decode_raw` saves and restores `ra` conventionally. The decoder writes no CSRs.

**Satisfiability is exhibited, not argued.** `ExportedDecoderAudit` carries a run for each of the
three predicates that satisfies the strengthened form *and* refutes the unstrengthened one, plus
`normalExecutionState_of_agree`, the transport that carries `NormalExecutionState` from a state where
it is established to the `after` state these clauses assert it of. That order matters here: a
strengthening of an assumed hypothesis that is *false* of the implementation makes the root vacuous,
which is strictly worse than a missing clause, and "free because nothing discharges it yet" is the
same fact as "unverified" seen twice.
-/

/-- The shared specification of `zesu_decode_raw`: the pure `decode` outcome. Shared by every
function instance; it names no register, global, or address. -/
def specZesuDecodeRaw : RoutineSpec ZesuDecodeRawArgs (Except SszDecodeError SszBridge.RawV4) where
  meaning := fun args => meaningDecode args.bytes

/-- The wrapper entry binding: the real C ABI `zesu_decode_raw(input, len)` — the input pointer in
`a0`, the length in `a1` — over valid code and input, with the *complete* incoming decoder-globals
representation (the scalar words and the full inline `stored_result` object). -/
def preZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs) (state : State) : Prop :=
  MemoryBytes state args.inputBase args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) ∧
  DecoderGlobalsRep globals rep args.inputBase args.bytes resultBuffer incoming state

/-- The wrapper exit binding, after retiring the return: the exact `a0` return code, the complete
updated decoder globals (`attempted`, 32-bit status, and the inline `stored_result` object), and the
preserved input and code. Allocation effects and preserved frames are added when the runner is proved
(Row D); this fixes the observable interface.

**This is the one `post*` of the eighteen that does NOT carry the ownership clause, and the reason is
its shape rather than an omission.** `DecoderEnvironment.ownedRegion` names one contiguous record
range plus one allocation interval, the allocator state and the stack. The wrapper's owned set adds
*three separately addressed globals* — `globals.attempted`, `globals.status`, and the 848-byte
`globals.storedResult` object. `DecoderGlobalsLayout` carries the three addresses and no span relating
them, so no choice of `recordBase`/`recordSize` covers them; and a clause naming only `storedResult`
would be **false**, because the wrapper certainly writes `attempted`. Since the permission clause is
consumed only through an assumed `LocalContractAssumptions`, a false conjunct here would be a step
toward a vacuous root, which is strictly worse than a missing one.

**Re-examined when the stack region was added, and the exclusion stands.** The stack made the *other*
seventeen clauses satisfiable; it does nothing for this one, because what this predicate cannot name
is the private-globals block, not the frame. The clean fix is a span field on `DecoderGlobalsLayout`,
and that structure is instantiated by `Elfling/GeneratedDecoderGlobals.lean` from the generated
artifact — the same `bssBase`/`bssSize` the block already has — so it is a generated-layout change
rather than a contracts change, and inventing a span here would be guessing at it.

Nothing is lost at the composition either: the wrapper is the top-level routine with no siblings, so
no `SiblingChain` is ever built from its postcondition. `DECISIONS.md` records the same scope fact
from the other direction — the root's accepted branch closes without any ownership clause.

**`before` is now used, and this predicate is no longer the exception to that.** It was the last of
the four `before`-taking postconditions to ignore its `before` binder; the `ra` clause below is a
relative claim and cannot be stated absolutely, which is exactly the shape `Entry.lean`'s note said
was missing. -/
def postZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (result : Except SszDecodeError SszBridge.RawV4) (before after : State) : Prop :=
  MemoryBytes after args.inputBase args.bytes ∧
  env.CodeIntact after ∧
  after.regs.get? x10 = some (BitVec.ofNat 64 (callOutcome incoming result).returnCode) ∧
  -- **The two callee-frame clauses.** See the section note above: `ra` preserved across the call,
  -- and the platform/CSR state still normal at the exit.
  after.regs.get? x1 = before.regs.get? x1 ∧
  NormalExecutionState after ∧
  DecoderGlobalsRep globals rep args.inputBase args.bytes resultBuffer (resultingGlobals incoming result) after

/-- The wrapper as a full function instance contract: the shared spec paired with the real exported binding
at a given incoming globals model. -/
def functionInstanceZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) :
    FunctionInstanceContract ZesuDecodeRawArgs (Except SszDecodeError SszBridge.RawV4) where
  spec := specZesuDecodeRaw
  binding :=
    { entry := preZesuDecodeRaw env globals resultBuffer rep incoming
      exit := postZesuDecodeRaw env globals resultBuffer rep incoming
      stepBound := fun args => 2 * (16384 + 512 * args.bytes.size) + 1024 }

/-- The exported wrapper's correctness claim, at the fresh incoming model the root theorem uses. -/
def correctnessClaimZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  FunctionInstanceContract.ImplementsFunctionInstance functionInstance reached entry exit
    (functionInstanceZesuDecodeRaw env globals resultBuffer rep DecoderGlobalsModel.fresh)

/-- The exported wrapper's entry binding is satisfiable under a valid environment. -/
def satisfiableZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4) : Prop :=
  ValidEnvironment env →
    FunctionInstanceContract.PreSatisfiable
      (functionInstanceZesuDecodeRaw env globals resultBuffer rep DecoderGlobalsModel.fresh)

end BinaryFv.SSZ.Zesu.Contracts
