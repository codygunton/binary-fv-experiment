import BinaryFv.Zesu.Contracts.Entry
import BinaryFv.RiscV.Platform.NormalState

namespace BinaryFv.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MemoryRepresentation
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
  stored : Option BinaryFv.Specs.SSZ.StatelessInput

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
  | success (value : BinaryFv.Specs.SSZ.StatelessInput)
  | rejected (error : DecodeError)
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
def stored : DecodeCallOutcome → Option BinaryFv.Specs.SSZ.StatelessInput
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
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) : DecodeCallOutcome :=
  if incoming.attempted then
    .alreadyDecoded
  else
    match result with
    | .ok value => .success value
    | .error error => .rejected error

/-- The globals model after a wrapper call: a fresh call records the attempt, its status, and its
stored value; a refused second call leaves the globals exactly as they were. -/
def resultingGlobals (incoming : DecoderGlobalsModel)
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) : DecoderGlobalsModel :=
  if incoming.attempted then
    incoming
  else
    { attempted := true
      status := (callOutcome incoming result).status
      stored := (callOutcome incoming result).stored }

/-!
## Representing the globals in canonical memory

An `attempted` flag is one byte; `last_status` is a 32-bit little-endian word. The inline
`stored_result` object — its discriminant byte and, on success, the `StatelessInput` payload laid out at the
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

/-- The complete inline `stored_result` object: its discriminant, and — on success — the `StatelessInput`
payload laid out at `resultBase` (the object's payload address) under the full container
representation. The value arm carries the caller's input base/bytes so the borrowed input slices of
the stored `StatelessInput` are represented. -/
def StoredResultRep (layout : DecoderGlobalsLayout) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (inputBase : Nat) (input : ByteArray) (resultBase : Nat) (model : DecoderGlobalsModel)
    (state : State) : Prop :=
  StoredResultDiscriminantRep layout model state ∧
  match model.stored with
  | some value => rep inputBase input value state resultBase
  | none => True

/-- The complete incoming/outgoing representation of all three decoder globals against a ghost model:
the scalar `attempted`/`last_status` words and the full inline `stored_result` object. -/
def DecoderGlobalsRep (layout : DecoderGlobalsLayout) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (inputBase : Nat) (input : ByteArray) (resultBase : Nat) (model : DecoderGlobalsModel)
    (state : State) : Prop :=
  DecoderGlobalsScalarRep layout model state ∧
  StoredResultRep layout rep inputBase input resultBase model state

/-!
## Model-level facts

These are `Prop`-level checks on the model, independent of any Sail execution — the definitional
half of the exported-function contract tests.
-/

/-- **Second decoder call produces `alreadyDecoded`.** Once `attempted` is set, any call outcome is
`alreadyDecoded` with status `.alreadyDecoded` and a `0` return, regardless of the input's decode
result, and the globals are left untouched. -/
theorem second_call_is_alreadyDecoded (incoming : DecoderGlobalsModel)
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) (h : incoming.attempted = true) :
    callOutcome incoming result = .alreadyDecoded ∧
    (callOutcome incoming result).status = .alreadyDecoded ∧
    (callOutcome incoming result).returnCode = 0 ∧
    resultingGlobals incoming result = incoming := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [callOutcome, resultingGlobals, DecodeCallOutcome.status, DecodeCallOutcome.returnCode, h]

/-- **A fresh successful call returns `1` and stores the value.** The exact stored-result tag and
payload and the accessor's return follow. -/
theorem fresh_success_stores_value (incoming : DecoderGlobalsModel) (value : BinaryFv.Specs.SSZ.StatelessInput)
    (hfresh : incoming.attempted = false) :
    callOutcome incoming (.ok value) = .success value ∧
    (callOutcome incoming (.ok value)).returnCode = 1 ∧
    (callOutcome incoming (.ok value)).status = .ok ∧
    (resultingGlobals incoming (.ok value)).stored = some value := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [callOutcome, resultingGlobals, DecodeCallOutcome.status, DecodeCallOutcome.returnCode,
      DecodeCallOutcome.stored, hfresh]

/-- **A fresh rejected call returns `0` and stores nothing**, recording the exact rejection status. -/
theorem fresh_rejection_stores_nothing (incoming : DecoderGlobalsModel) (error : DecodeError)
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
Agree platformPreserved before after   -- the eighteen registers a `ret` needs, unchanged
RetiredCounterPresent after            -- `minstret` still readable
```

and this is the one place the reasoning is written out; the accessors' docstrings point here.

**What consumes them.** A `TraceToSentinel` — what the runner's fuel argument and the root theorem
are stated against — is built from a contract's `EnteredFunctionTrace` by
`RiscV/Elfling/SentinelBridge.lean`, which appends the function's final `ret`. That bridge has two
demands at the *exit* state, and they are not the same demand:

* `traceToSentinel_of_functionTrace_ret`'s `linkIsSentinel` needs the value `ret` reads out of the
  link register to be the sentinel. The runner put the sentinel there
  (`buildZesuEntryState_entry_binding_abi` exposes `x1 := canonicalRunnerLayout.sentinel` at the
  entry state), so what is missing is that the *call* did not disturb it.
* `tryStepRetRetires`, which supplies that bridge's `ret` premise, wants ~20 hypotheses about the
  exit state, and every one of them bottoms out in register reads.

Before these clauses existed the contract layer supplied **neither**: no `post*` predicate in this
directory mentioned `x1` at all, and `NormalExecutionState` was reachable only at the state the
runner builds.

**One frame clause rather than a list of predicates.** The first version of these clauses was
`after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after`. Walking `tryStepRetRetires`'
premises down to the registers they actually read — rather than reading its signature — showed that
pair leaves **five** registers open, not one: `mstatus` and `sig_meip` (`InterruptDisabled`),
`mstatus` again and `pma_regions` (`FetchBasePlatform`, through `FetchPmaAllows`), `mseccfg` (the
decode, and `update_elp_state`'s `Zicfilp` gate), and `htif_tohost_base` (`FetchMemoryNoMMIO`).
`RiscV/Platform/NormalState.lean`'s `platformPreserved` names all of them plus `x1` and
`NormalExecutionState`'s own twelve, and `Agree` — the register half of `RiscV/Elfling/Contract.lean`'s
`CalleeFrame`, already existing vocabulary — is the one clause that carries the lot.

It is not weaker than what it replaces. `normalExecutionState_of_platformPreserved` recovers
`NormalExecutionState after` from it given `NormalExecutionState before`, which the runner proves at
the state it builds; `platformPreserved_link` recovers the `x1` equation verbatim; and it *adds* the
five, at their values rather than merely present, which is what `FetchPmaAllows` needs
(it evaluates `matching_pma_region` on `pma_regions`) and what `update_elp_state` needs of `mseccfg`.

**The MMIO dispatch needs no conjunct of its own**, which is not obvious from its shape:
`FetchMemoryNoMMIO` is a *run* of `within_mmio_readable`, not a register equation. That run
dispatches to `within_clint`, `within_sig` and `within_htif_readable`; the first two read no register
and depend on the address alone, and the third reads exactly `htif_tohost_base`.
`Platform/FetchMmio.lean`'s `fetchMemoryNoMMIO_of_agree` proves the transport from this clause, so it
is a fact rather than an argument.

**`minstret` is a separate clause because preservation of it is false.** `retiredRead` reads the
retired-instruction counter, so the exit state must have it — but the machine writes `minstret` on
every retirement (`tryStepControlFlowAfterRetired` *is* `writeReg minstret (retired + 1)`), so a
callee that preserved it would have executed no instructions. Folding it into `platformPreserved`
would have made every one of these three postconditions false, and a false conjunct inside an assumed
hypothesis makes the root vacuous rather than merely under-specified. `RetiredCounterPresent` is the
claim that is true: presence at an existentially bound value, which is exactly the form `retiredRead`
consumes.

**Preservation, not equality with the sentinel.** The `x1` component is deliberately *not*
`after.regs.get? x1 = some sentinelWord`. The sentinel is the **runner's** choice of an unmapped
address, and a contract in this layer may not name it — that is the same address-freedom rule the
rest of the file follows. Preservation is also the form that composes: it is what turns the entry
state's `x1 := sentinel` into the exit state's, and it stays true of a function instance called from anywhere
else, which an equation naming one caller's sentinel would not. The same argument applies to the
platform registers, and is why the whole clause is relative.

**True of the binary, established before the clauses were accepted rather than after.** `ra` is
callee-saved under RV64 LP64; the whole-program disassembly found `zesu_raw_result` (8 instructions)
and `zesu_raw_error` (3) are leaves with no prologue and zero stores, so they cannot disturb `ra` or
any CSR, and `zesu_decode_raw` saves and restores `ra` conventionally. The decoder writes no CSRs,
and none of `sig_meip`, `pma_regions`, `mseccfg`, `htif_tohost_base` is writable by any instruction
the decoder contains.

**Satisfiability is exhibited, not argued.** `ExportedDecoderAudit` carries a run for each of the
three predicates that satisfies the strengthened form, and four clobbering runs — `x1`, a
`NormalExecutionState` register, one of the five, and the MMIO register — each of which the previous
form of the clauses **permitted** and this one refuses. The witnesses also *move* `minstret`, so a
future edit that folds the counter into `platformPreserved` stops them compiling rather than passing
silently. That order matters: a strengthening of an assumed hypothesis that is *false* of the
implementation makes the root vacuous, which is strictly worse than a missing clause, and "free
because nothing discharges it yet" is the same fact as "unverified" seen twice.
-/

/-- The shared specification of `zesu_decode_raw`: the pure `decode` outcome. Shared by every
function instance; it names no register, global, or address. -/
def specZesuDecodeRaw : SourceFunctionSpec ZesuDecodeRawArgs (Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) where
  meaning := fun args => meaningDecode args.bytes

/-- The wrapper entry binding: the real C ABI `zesu_decode_raw(input, len)` — the input pointer in
`a0`, the length in `a1` — over valid code and input, with the *complete* incoming decoder-globals
representation (the scalar words and the full inline `stored_result` object). -/
def preZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs) (state : State) : Prop :=
  MemoryBytes state args.inputBase args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.inputBase) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) ∧
  DecoderGlobalsRep globals rep args.inputBase args.bytes resultBuffer incoming state

/-- The wrapper exit binding, after retiring the return: the exact `a0` return code, the complete
updated decoder globals (`attempted`, 32-bit status, and the inline `stored_result` object), and the
preserved input and code. Allocation effects and preserved frames are added when the runner is proved
by the execution proof; this fixes the observable interface.

**This is the one `post*` of the eighteen that does NOT carry the ownership clause, and the reason is
its shape rather than an omission.** `DecoderEnvironment.ownedRegion` names one contiguous record
range plus one allocation interval, the allocator state and the stack. The wrapper's owned set adds
*three separately addressed globals* — `globals.attempted`, `globals.status`, and the 848-byte
`globals.storedResult` object. `DecoderGlobalsLayout` carries the three addresses and no span relating
them, so no choice of `recordBase`/`recordSize` covers them; and a clause naming only `storedResult`
would be **false**, because the wrapper certainly writes `attempted`. A false conjunct here would
make the exported-contract premise unsatisfiable and the conditional root vacuous.

**Re-examined when the stack region was added, and the exclusion stands.** The stack made the *other*
seventeen clauses satisfiable; it does nothing for this one, because what this predicate cannot name
is the private-globals block, not the frame. The clean fix is a span field on `DecoderGlobalsLayout`,
and that structure is instantiated by `Elfling/GeneratedDecoderGlobals.lean` from the generated
artifact — the same `bssBase`/`bssSize` the block already has — so it is a generated-layout change
rather than a contracts change, and inventing a span here would be guessing at it.

Nothing is lost at the composition either: the wrapper is the top-level function instance with no siblings, so
no `SiblingChain` is ever built from its postcondition. `DECISIONS.md` records the same scope fact
from the other direction — the root's accepted branch closes without any ownership clause.

**`before` is now used, and this predicate is no longer the exception to that.** It was the last of
the four `before`-taking postconditions to ignore its `before` binder; the `Agree` clause below is a
relative claim and cannot be stated absolutely, which is exactly the shape `Entry.lean`'s note said
was missing. -/
def postZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (result : Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) (before after : State) : Prop :=
  MemoryBytes after args.inputBase args.bytes ∧
  env.CodeIntact after ∧
  after.regs.get? x10 = some (BitVec.ofNat 64 (callOutcome incoming result).returnCode) ∧
  -- **The two callee-frame clauses.** See the section note above: the eighteen registers a retiring
  -- `ret` reads come back unchanged, and the retired counter is still readable.
  Agree platformPreserved before after ∧
  RetiredCounterPresent after ∧
  DecoderGlobalsRep globals rep args.inputBase args.bytes resultBuffer (resultingGlobals incoming result) after

/-- The wrapper as a full function instance contract: the shared spec paired with the real exported binding
at a given incoming globals model. -/
def functionInstanceZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (incoming : DecoderGlobalsModel) :
    FunctionInstanceContract ZesuDecodeRawArgs (Except DecodeError BinaryFv.Specs.SSZ.StatelessInput) where
  spec := specZesuDecodeRaw
  binding :=
    { entry := preZesuDecodeRaw env globals resultBuffer rep incoming
      exit := postZesuDecodeRaw env globals resultBuffer rep incoming
      stepBound := fun args => 2 * (16384 + 512 * args.bytes.size) + 1024 }

/-- The exported wrapper's correctness claim, at the fresh incoming model the root theorem uses. -/
def correctnessClaimZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  FunctionInstanceContract.ImplementsFunctionInstance functionInstance reached entry exit
    (functionInstanceZesuDecodeRaw env globals resultBuffer rep DecoderGlobalsModel.fresh)

/-- The exported wrapper's entry binding is satisfiable under a valid environment. -/
def satisfiableZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation BinaryFv.Specs.SSZ.StatelessInput) : Prop :=
  ValidEnvironment env →
    FunctionInstanceContract.PreSatisfiable
      (functionInstanceZesuDecodeRaw env globals resultBuffer rep DecoderGlobalsModel.fresh)

end BinaryFv.Zesu.Contracts
