import BinaryFv.Zesu.Contracts.Environment
import BinaryFv.Zesu.Contracts.Error

namespace BinaryFv.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Option decoders

`decodeOptionalU64` and `decodeOptionalBlobSchedule` are the zero-or-one-element option decoders.
Neither allocates, so their postconditions assert the *absence* of allocation rather than staying
silent about it — a `post` that only constrained the success arm would be satisfied by an
implementation that scribbled over caller memory on the way to an error.

`decodeOptionalBlobSchedule` is the first migration exemplar. The existing 66-step trace is a
fragment of its inline instance; deliberately, no program counter appears anywhere in this module,
because the binding lives in generated Elfling data and `ImplementsFunctionInstance` is the seam.
-/

/-- The SSZ schema `decodeOptionalBlobSchedule` decodes, as partial evaluation of the pinned specification's
fork-config field. Issue #39 writes this as `.list BinaryFv.Specs.SSZ.blobScheduleType 1`;
`maxBlobSchedulesPerFork` *is* `1`, and naming it keeps the constant pinned to the bridge. -/
def optionalBlobScheduleType : SSZType :=
  .list BinaryFv.Specs.SSZ.blobScheduleType BinaryFv.Specs.SSZ.maxBlobSchedulesPerFork

/-- The SSZ schema `decodeOptionalU64` decodes. -/
def optionalU64Type : SSZType :=
  .list BinaryFv.Specs.SSZ.u64 BinaryFv.Specs.SSZ.maxOptionalForkActivationValues

/--
Address-free arguments of a borrowed-slice decoder returning an aggregate indirectly.

`base` and `resultBase` are genuine runtime arguments of the source function, so they belong here. Program
counters and instruction words are not arguments and never appear in this module.
-/
structure SliceToResultArgs where
  base : Nat
  bytes : ByteArray
  resultBase : Nat

/-!
## Meanings

Each `meaning` is the pinned canonical decode at a closed schema literal followed by the specification's
projection. No new recursion and no mirror of the Zig control flow appears here: a hand-rolled
byte-walker would always be provable and would say nothing about the oracle.
-/

/-- `decodeOptionalBlobSchedule`: canonical decoding of a zero-or-one-element blob-schedule list,
converted to an `Option`. -/
def meaningOptionalBlobSchedule (bytes : ByteArray) :
    Except DecodeError (Option BinaryFv.Specs.SSZ.RawBlobSchedule) :=
  match BinaryFv.Specs.SSZ.decodeCanonical optionalBlobScheduleType bytes with
  | .ok value => .ok ((value.1[0]?).map BinaryFv.Specs.SSZ.rawBlobScheduleOf)
  | .error error => .error (sszToDecodeError error)

/-- `decodeOptionalU64`: canonical decoding of a zero-or-one-element `u64` list. -/
def meaningOptionalU64 (bytes : ByteArray) : Except DecodeError (Option UInt64) :=
  match BinaryFv.Specs.SSZ.decodeCanonical optionalU64Type bytes with
  | .ok value => .ok (value.1[0]?)
  | .error error => .error (sszToDecodeError error)

/-!
## Preconditions

Sail memory is sparse: an unmapped read throws rather than returning a default, so `pre` must
materialize every address the source function touches. That also makes it easy to write a `pre` no state
satisfies, which would make `Implements` vacuously true — hence `PreSatisfiable` below.

The Zig signature `(data: []const u8) -> ?T` lowers to a result pointer in `a0` and the slice's
pointer/length pair in `a1`/`a2`.
-/

def preSliceToResult (env : DecoderEnvironment) (args : SliceToResultArgs) (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.resultBase) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.bytes.size)

/-!
## Postconditions

Each `post` is total over `Except DecodeError _`: the error arm is constrained as tightly as the
success arm.
-/

/-- The blob-schedule result as it must appear on return.

The four conjuncts before the `match` hold on *every* path: the borrowed input is untouched, the
code image is intact, no allocation occurred, and every write landed inside the `?T` object at
`args.resultBase` or the function instance's own stack frame. The option layouts are the one family where the
record size was already in scope —
`env.optionalBlobSchedule.size` is the reflected `@sizeOf(?RawBlobSchedule)` — so the ownership clause
costs no new parameter here. -/
def postOptionalBlobSchedule (env : DecoderEnvironment) (args : SliceToResultArgs)
    (result : Except DecodeError (Option BinaryFv.Specs.SSZ.RawBlobSchedule))
    (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.NoAllocation before after ∧
  env.WritesOnlyWithinOwnRecord args.resultBase env.optionalBlobSchedule.size before after ∧
  match result with
  | .ok none => OptionNoneRep env.optionalBlobSchedule after args.resultBase
  | .ok (some schedule) =>
      OptionSomeRep env.optionalBlobSchedule after args.resultBase ∧
      RawBlobScheduleRep env.blobSchedule after
        (args.resultBase + env.optionalBlobSchedule.payloadOffset) schedule
  | .error error =>
      -- Only `invalidSsz` is reachable: this source function neither allocates nor reads a fork index.
      error = DecodeError.invalidSsz

def postOptionalU64 (env : DecoderEnvironment) (args : SliceToResultArgs)
    (result : Except DecodeError (Option UInt64)) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.NoAllocation before after ∧
  env.WritesOnlyWithinOwnRecord args.resultBase env.optionalU64.size before after ∧
  match result with
  | .ok none => OptionNoneRep env.optionalU64 after args.resultBase
  | .ok (some value) =>
      OptionSomeRep env.optionalU64 after args.resultBase ∧
      Word64LERep after (args.resultBase + env.optionalU64.payloadOffset) value.toNat
  | .error error => error = DecodeError.invalidSsz

/-!
## Contracts and correctness claims

`correctnessClaim` is a named `Prop`, never a theorem stub. Issue #39 requires the intended
exhaustive signature to exist before its proof does, and `nix/proof.nix` asserts an exact `sorry`
count per file, so an unfinished obligation must not be spelled as a `sorry`.
-/

/-- The exhaustive `decodeOptionalBlobSchedule` contract.

`stepBound` is a provisional magnitude until the generated instance fixes it. It is an upper bound,
so tightening it later strengthens the claim rather than invalidating this statement. -/
def contractOptionalBlobSchedule (env : DecoderEnvironment) :
    FunctionContract DecodeError SliceToResultArgs (Option BinaryFv.Specs.SSZ.RawBlobSchedule) where
  meaning := fun args => meaningOptionalBlobSchedule args.bytes
  pre := preSliceToResult env
  post := postOptionalBlobSchedule env
  stepBound := fun _ => 256

def contractOptionalU64 (env : DecoderEnvironment) :
    FunctionContract DecodeError SliceToResultArgs (Option UInt64) where
  meaning := fun args => meaningOptionalU64 args.bytes
  pre := preSliceToResult env
  post := postOptionalU64 env
  stepBound := fun _ => 128

/-- The obligation that a generated Elfling function instance implements the blob-schedule contract.

This is the point of the layering: the statement names no address, and the function instance supplies every
one of them. -/
def correctnessClaimOptionalBlobSchedule (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractOptionalBlobSchedule env)

def correctnessClaimOptionalU64 (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance) (reached : BitVec 64 → Prop)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance reached entry exit (contractOptionalU64 env)

/-- The blob-schedule precondition is satisfiable for a well-formed environment, so its contract is
not vacuous. Conditioned on `ValidEnvironment` rather than asserted unconditionally: the
postcondition reads the layout offsets, and an inconsistent layout has no representative state. -/
def satisfiableOptionalBlobSchedule (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractOptionalBlobSchedule env)

def satisfiableOptionalU64 (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractOptionalU64 env)

/-!
## Characterization of the meaning

These pin the input classes issue #39 enumerates for this source function, so the eventual instruction proof
has a specification-side target that is already fixed.
-/

/-- Zero bytes decode to `none`. -/
def meaningEmptyIsNone : Prop :=
  meaningOptionalBlobSchedule ByteArray.empty = .ok none

/-- Exactly 24 bytes decode to a present schedule.

No canonicality hypothesis, and none is needed: `blobScheduleType` is three fixed-width `u64`s, so
*every* 24-byte buffer is the canonical encoding of exactly one schedule. That is stronger than it
may look — it is the encode-after-decode direction, which is why it needs
`uint64LE_of_readUInt64LE` rather than upstream's `decode_encode`. -/
def meaningTwentyFourIsSome : Prop :=
  ∀ bytes : ByteArray, bytes.size = 24 →
    ∃ schedule, meaningOptionalBlobSchedule bytes = .ok (some schedule)

/-- Every other length is `invalidSsz`. -/
def meaningOtherLengthIsInvalid : Prop :=
  ∀ bytes : ByteArray, bytes.size ≠ 0 → bytes.size ≠ 24 →
    meaningOptionalBlobSchedule bytes = .error .invalidSsz

/-- Unknown-fork and allocation failure are unreachable for this source function. -/
def meaningNeverForkOrMemory : Prop :=
  ∀ bytes : ByteArray,
    meaningOptionalBlobSchedule bytes ≠ .error .unknownFork ∧
    meaningOptionalBlobSchedule bytes ≠ .error .outOfMemory

end BinaryFv.Zesu.Contracts
