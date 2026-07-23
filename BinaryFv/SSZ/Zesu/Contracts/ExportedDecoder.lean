import BinaryFv.SSZ.Zesu.Contracts.Entry

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# The real exported decoder

`zesu_decode_raw` is not the internal `decodeRaw`. Its machine interface was previously modelled with
the internal four-register hidden-result convention (`x10 = resultBase`, …), and its effect was
modelled as a free 64-bit status word written to an arbitrary `statusBase`. Both are wrong about the
shipped binary.

The exported wrapper's real interface is the C ABI `zesu_decode_raw(input, len) -> i32`: the input
pointer in `a0`, the length in `a1`, and a `1`/`0` return in `a0`. Its real effect is on three private
globals — an `attempted` flag, a 32-bit `last_status`, and an inline `stored_result` object
(`?RawStatelessInput`, 848 bytes: payload at offset 0, discriminant at 832 — not a pointer slot) —
read back out through the exported accessors `zesu_raw_result` and `zesu_raw_error`. `zesu_raw_result`
returns the *address* of that object's payload (or null); it does not write a caller result buffer,
and there is no free public status slot.

This module models that interface. The `resultBase + 832` 16-bit union stays where it belongs, on the
*internal* `decodeRaw` (see `MemoryRepresentation.Result`); nothing here uses it.
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

`stored` holds the decoded *value*; how a value is realized in memory (a canonical result buffer and a
pointer to it) is the representation's job, not the model's. These are ghost values, not ABI
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
-/

/-- The shared specification of `zesu_decode_raw`: the pure `decode` outcome. Shared by every
occurrence; it names no register, global, or address. -/
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
(Row D); this fixes the observable interface. -/
def postZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (result : Except SszDecodeError SszBridge.RawV4) (before after : State) : Prop :=
  MemoryBytes after args.inputBase args.bytes ∧
  env.CodeIntact after ∧
  after.regs.get? x10 = some (BitVec.ofNat 64 (callOutcome incoming result).returnCode) ∧
  DecoderGlobalsRep globals rep args.inputBase args.bytes resultBuffer (resultingGlobals incoming result) after

/-- The wrapper as a full occurrence contract: the shared spec paired with the real exported binding
at a given incoming globals model. -/
def occurrenceZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) :
    OccurrenceContract ZesuDecodeRawArgs (Except SszDecodeError SszBridge.RawV4) where
  spec := specZesuDecodeRaw
  binding :=
    { entry := preZesuDecodeRaw env globals resultBuffer rep incoming
      exit := postZesuDecodeRaw env globals resultBuffer rep incoming
      stepBound := fun args => 2 * (16384 + 512 * args.bytes.size) + 1024 }

/-- The exported wrapper's correctness claim, at the fresh incoming model the root theorem uses. -/
def correctnessClaimZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (instance_ : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  OccurrenceContract.ImplementsInstance instance_ reached entry exit
    (occurrenceZesuDecodeRaw env globals resultBuffer rep DecoderGlobalsModel.fresh)

/-- The exported wrapper's entry binding is satisfiable under a valid environment. -/
def satisfiableZesuDecodeRaw (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4) : Prop :=
  ValidEnvironment env →
    OccurrenceContract.PreSatisfiable
      (occurrenceZesuDecodeRaw env globals resultBuffer rep DecoderGlobalsModel.fresh)

end BinaryFv.SSZ.Zesu.Contracts
