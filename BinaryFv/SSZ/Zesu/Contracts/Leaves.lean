import BinaryFv.SSZ.Zesu.Contracts.Environment
import BinaryFv.SSZ.Zesu.Contracts.Error

namespace BinaryFv.SSZ.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Primitive readers and bounded slices

The reusable leaf family: `bytesAt`, the little-endian reads, `readArray`, `readOffset`,
`requireU32Length`, and `hasExactErePrefix`.

`decodeCanonical` is the wrong meaning for these. It demands `used = body.size` *and* reserialization
byte-equality, whereas a leaf reader reads *within* a buffer it does not own. Their meanings are
therefore the `Option`-valued SizzLean readers lifted through `Option.toDecodeResult`, which is
faithful because every Zig reader funnels through `bytesAt`, and `bytesAt` fails exactly when the
SizzLean reader returns `none`.

`bytesAt`'s Zig bound is written `offset > data.len or len > data.len - offset` rather than
`offset + len > data.len`, to avoid `usize` overflow. The two agree given `offset <= data.len`, but
the contract mirrors the source form.
-/

/-- Arguments of a read at an offset inside a borrowed slice. -/
structure ReadAtArgs where
  base : Nat
  bytes : ByteArray
  offset : Nat

/-- Arguments of a whole-slice predicate or check. -/
structure SliceArgs where
  base : Nat
  bytes : ByteArray

/-!
## Meanings
-/

/-- `bytesAt(data, offset, len)`: the sub-slice, or `InvalidSsz` when it does not fit.

Stated in the source's non-wrapping form. -/
def meaningBytesAt (bytes : ByteArray) (offset length : Nat) :
    Except SszDecodeError ByteArray :=
  if offset ≤ bytes.size ∧ length ≤ bytes.size - offset then
    .ok (bytes.extract offset (offset + length))
  else
    .error .invalidSsz

/-- `readU32(data, offset)`: a little-endian `u32`, or `InvalidSsz`. -/
def meaningReadU32 (bytes : ByteArray) (offset : Nat) : Except SszDecodeError UInt32 :=
  Option.toDecodeResult (readUInt32LE bytes offset)

/-- `readU64(data, offset)`: a little-endian `u64`, or `InvalidSsz`. -/
def meaningReadU64 (bytes : ByteArray) (offset : Nat) : Except SszDecodeError UInt64 :=
  Option.toDecodeResult (readUInt64LE bytes offset)

/-- `readOffset(data, offset)`: `readU32` widened to `usize`.

The Zig body is `@intCast(try readU32(data, offset))`, and on this target `usize` is 64-bit, so the
cast is total. Representing it as a distinct meaning rather than aliasing `meaningReadU32` keeps the
widening visible at the exact place the source performs it. -/
def meaningReadOffset (bytes : ByteArray) (offset : Nat) : Except SszDecodeError Nat :=
  (meaningReadU32 bytes offset).map UInt32.toNat

/-- `readU256(data, offset)`: a little-endian `u256`, or `InvalidSsz`.

SizzLean's underlying `readNatLE` is private, so this composes the public `bytesAt` meaning with an
explicit little-endian fold. The fold is a *primitive read*, not a re-implementation of decoder
control flow, which is why it is admissible here where a hand-rolled container walker would not be.
-/
def meaningReadU256 (bytes : ByteArray) (offset : Nat) : Except SszDecodeError (BitVec 256) :=
  match meaningBytesAt bytes offset 32 with
  | .ok slice =>
      .ok (BitVec.ofNat 256
        ((List.range 32).foldr (fun index acc => acc * 256 + (slice.get! (31 - index)).toNat) 0))
  | .error error => .error error

/-- `readArray(N, data, offset)`: `N` bytes copied out, or `InvalidSsz`.

`N` is `comptime` in Zig, so each width is a separately emitted instantiation with its own
`FunctionId.specialization`; the catalog records the widths the decoder actually uses. -/
def meaningReadArray (length : Nat) (bytes : ByteArray) (offset : Nat) :
    Except SszDecodeError ByteArray :=
  meaningBytesAt bytes offset length

/-- `requireU32Length(data)`: the slice length fits in a `u32`. -/
def meaningRequireU32Length (bytes : ByteArray) : Except SszDecodeError Unit :=
  if bytes.size ≤ 4294967295 then .ok () else .error .invalidSsz

/-- `hasExactErePrefix(data)`: a `Bool`, never an error.

Uses `SszBridge.readU32LE?`, the bridge's own framing reader. That is the correct choice here and
only here: this is a framing question about the outer envelope, not an SSZ field read. -/
def meaningHasExactErePrefix (bytes : ByteArray) : Bool :=
  match SszBridge.readU32LE? bytes 0 with
  | some declared => bytes.size ≥ 4 && declared == bytes.size - 4
  | none => false

/-!
## Preconditions and postconditions

A leaf reader is a pure read: it must preserve the borrowed slice, the code image, and the allocator
state on every path, and it returns its value in `a0`.
-/

def preReadAt (env : DecoderEnvironment) (args : ReadAtArgs) (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.offset)

def preSlice (env : DecoderEnvironment) (args : SliceArgs) (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size)

/-- Every leaf reader preserves input, code, and allocator state, on success and on failure alike. -/
def LeafFrame (env : DecoderEnvironment) (base : Nat) (bytes : ByteArray)
    (before after : State) : Prop :=
  MemoryBytes after base bytes ∧ env.CodeIntact after ∧ env.NoAllocation before after

/-- A scalar read returns its value zero-extended in `a0`; failure is always `invalidSsz`. -/
def postScalarRead (env : DecoderEnvironment) (args : ReadAtArgs) (width : Nat)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok value =>
      value < 2 ^ width ∧ after.regs.get? x10 = some (BitVec.ofNat 64 value)
  | .error error => error = SszDecodeError.invalidSsz

def contractReadU32 (env : DecoderEnvironment) :
    FunctionContract SszDecodeError ReadAtArgs Nat where
  meaning := fun args => (meaningReadU32 args.bytes args.offset).map UInt32.toNat
  pre := preReadAt env
  post := fun args => postScalarRead env args 32
  stepBound := fun _ => 64

def contractReadU64 (env : DecoderEnvironment) :
    FunctionContract SszDecodeError ReadAtArgs Nat where
  meaning := fun args => (meaningReadU64 args.bytes args.offset).map UInt64.toNat
  pre := preReadAt env
  post := fun args => postScalarRead env args 64
  stepBound := fun _ => 96

def contractReadOffset (env : DecoderEnvironment) :
    FunctionContract SszDecodeError ReadAtArgs Nat where
  meaning := fun args => meaningReadOffset args.bytes args.offset
  pre := preReadAt env
  post := fun args => postScalarRead env args 32
  stepBound := fun _ => 64

/-- `hasExactErePrefix` cannot fail, so its meaning is total and its result is a boolean in `a0`. -/
def postHasExactErePrefix (env : DecoderEnvironment) (args : SliceArgs)
    (result : Except SszDecodeError Bool) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok flag =>
      after.regs.get? x10 = some (BitVec.ofNat 64 (if flag then 1 else 0))
  | .error _ => False

def contractHasExactErePrefix (env : DecoderEnvironment) :
    FunctionContract SszDecodeError SliceArgs Bool where
  meaning := fun args => .ok (meaningHasExactErePrefix args.bytes)
  pre := preSlice env
  post := postHasExactErePrefix env
  stepBound := fun _ => 64

/-- `requireU32Length(data)`: returns a zero status on success. -/
def postRequireU32Length (env : DecoderEnvironment) (args : SliceArgs)
    (result : Except SszDecodeError Unit) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok () => after.regs.get? x10 = some (BitVec.ofNat 64 0)
  | .error error => error = SszDecodeError.invalidSsz

def contractRequireU32Length (env : DecoderEnvironment) :
    FunctionContract SszDecodeError SliceArgs Unit where
  meaning := fun args => meaningRequireU32Length args.bytes
  pre := preSlice env
  post := postRequireU32Length env
  stepBound := fun _ => 32

/-- Arguments of `bytesAt`: the `len` is a **runtime** argument (unlike `readArray`'s comptime `N`),
so it belongs in the args, keeping `bytesAt` a single routine with a single identity. -/
structure BytesAtArgs extends ReadAtArgs where
  length : Nat

/-- `bytesAt(data, offset, len)` returns a borrowed sub-slice; on success `a0`/`a1` carry its
pointer and length, and the bytes are those of the caller's input at `[offset, offset+len)`. -/
def postBytesAt (env : DecoderEnvironment) (args : BytesAtArgs)
    (result : Except SszDecodeError ByteArray) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok _ =>
      after.regs.get? x10 = some (BitVec.ofNat 64 (args.base + args.offset)) ∧
      after.regs.get? x11 = some (BitVec.ofNat 64 args.length)
  | .error error => error = SszDecodeError.invalidSsz

def contractBytesAt (env : DecoderEnvironment) :
    FunctionContract SszDecodeError BytesAtArgs ByteArray where
  meaning := fun args => meaningBytesAt args.bytes args.offset args.length
  pre := fun args => preReadAt env args.toReadAtArgs
  post := postBytesAt env
  stepBound := fun _ => 32

/-- `readU256(data, offset)`: the 256-bit little-endian value is written to a caller result slot,
because a `u256` does not fit in a single return register. -/
def postReadU256 (env : DecoderEnvironment) (args : ReadAtArgs) (resultBase : Nat)
    (result : Except SszDecodeError (BitVec 256)) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok value => BitVectorLERep after resultBase value
  | .error error => error = SszDecodeError.invalidSsz

/-- Arguments of `readU256`: like a read-at, plus the result slot the wide value is written to. -/
structure ReadU256Args extends ReadAtArgs where
  resultBase : Nat

def contractReadU256 (env : DecoderEnvironment) :
    FunctionContract SszDecodeError ReadU256Args (BitVec 256) where
  meaning := fun args => meaningReadU256 args.bytes args.offset
  pre := fun args => preReadAt env args.toReadAtArgs
  post := fun args => postReadU256 env args.toReadAtArgs args.resultBase
  stepBound := fun _ => 128

/-- `readArray(N, data, offset)`: `N` bytes copied to a caller result slot.

Each `N` is a separately emitted `comptime` instantiation, so the contract is parameterized by `N`
and the catalog records one entry per concrete width (20, 32, 48, 65, 96, 256). -/
def postReadArray (env : DecoderEnvironment) (args : ReadAtArgs) (length resultBase : Nat)
    (result : Except SszDecodeError ByteArray) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok copied => MemoryBytes after resultBase copied
  | .error error => error = SszDecodeError.invalidSsz

/-- Arguments of `readArray`: a read-at plus the destination the `N` bytes are copied to. -/
structure ReadArrayArgs extends ReadAtArgs where
  resultBase : Nat

def contractReadArray (env : DecoderEnvironment) (length : Nat) :
    FunctionContract SszDecodeError ReadArrayArgs ByteArray where
  meaning := fun args => meaningReadArray length args.bytes args.offset
  pre := fun args => preReadAt env args.toReadAtArgs
  post := fun args => postReadArray env args.toReadAtArgs length args.resultBase
  stepBound := fun _ => 32 + 4 * length

/-- The concrete `readArray` widths the pinned decoder instantiates. -/
def readArrayWidths : List Nat := [20, 32, 48, 65, 96, 256]

/-!
## Correctness claims
-/

def correctnessClaimReadU32 (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractReadU32 env)

def correctnessClaimReadU64 (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractReadU64 env)

def correctnessClaimReadOffset (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractReadOffset env)

def correctnessClaimHasExactErePrefix (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractHasExactErePrefix env)

def correctnessClaimRequireU32Length (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractRequireU32Length env)

def correctnessClaimBytesAt (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractBytesAt env)

def correctnessClaimReadU256 (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractReadU256 env)

/-- One correctness claim per concrete `readArray` width. -/
def correctnessClaimReadArray (env : DecoderEnvironment) (length : Nat)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractReadArray env length)

/-!
## Satisfiability

Each leaf precondition is satisfiable because its base pointer is a free argument: place the borrowed
slice at an address the image does not occupy and the state exists. Stated under `ValidEnvironment`
for uniformity with the parameterized families, even where a leaf does not consult the layout. -/

def satisfiableReadU32 (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractReadU32 env)

def satisfiableReadU64 (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractReadU64 env)

def satisfiableReadOffset (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractReadOffset env)

def satisfiableReadU256 (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractReadU256 env)

def satisfiableReadArray (env : DecoderEnvironment) (length : Nat) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractReadArray env length)

def satisfiableBytesAt (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractBytesAt env)

def satisfiableRequireU32Length (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractRequireU32Length env)

def satisfiableHasExactErePrefix (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractHasExactErePrefix env)

/-!
## Characterizations

`bytesAt` is the single bound every reader inherits, so stating it once is what lets each reader's
error case be discharged uniformly rather than re-derived.
-/

/-- A read succeeds exactly when its window fits, matching the Zig `bytesAt` guard. -/
def bytesAtSucceedsIffFits : Prop :=
  ∀ (bytes : ByteArray) (offset length : Nat),
    (∃ slice, meaningBytesAt bytes offset length = .ok slice) ↔
      (offset ≤ bytes.size ∧ length ≤ bytes.size - offset)

/-- `readOffset` is exactly `readU32` widened, with no additional failure mode. -/
def readOffsetIsWidenedReadU32 : Prop :=
  ∀ (bytes : ByteArray) (offset : Nat),
    meaningReadOffset bytes offset = (meaningReadU32 bytes offset).map UInt32.toNat

/-- Every leaf reader's only error is `invalidSsz`: none allocates and none inspects a fork index. -/
def leafReadsOnlyFailInvalid : Prop :=
  ∀ (bytes : ByteArray) (offset : Nat),
    meaningReadU32 bytes offset ≠ .error .unknownFork ∧
    meaningReadU32 bytes offset ≠ .error .outOfMemory ∧
    meaningReadU64 bytes offset ≠ .error .unknownFork ∧
    meaningReadU64 bytes offset ≠ .error .outOfMemory

end BinaryFv.SSZ.Zesu.Contracts
