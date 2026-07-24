import BinaryFv.SSZ.Zesu.Contracts.Leaves

namespace BinaryFv.SSZ.Zesu.Contracts

open SizzLean.Spec
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Canonical offset tables

`requireCanonicalOffsets` is the decoder's entire canonicality discipline, and it is where the
binary and the oracle check *different things* to reach the same conclusion.

The oracle's `decodeCanonical` decides canonicality globally: it decodes, then re-serializes and
demands byte equality. The Zig decoder never re-serializes. Instead each container calls
`requireCanonicalOffsets`, and `decodeByteListList` separately rejects a zero first offset — which
is exactly the `00 00 00 00` empty-list alias that the oracle's re-serialization check kills.

That those per-container checks together imply global re-serialization equality is the single
load-bearing lemma of the whole catalog. It needs the source-shaped composition to exist first, so
it is stated in `Contracts/Entry.lean` as `sourceShapedDecodeAgreesWithOracle` — named rather than
left implicit, because every container contract silently depends on it.
-/

/-- `requireCanonicalOffsets(data, fixedSize, offsets)`.

Transcribed from the source in its exact order: the first offset must *equal* the fixed size (not
merely be at least it), and offsets must be nondecreasing from there while staying within the slice.
-/
def meaningRequireCanonicalOffsets (bytes : ByteArray) (fixedSize : Nat) (offsets : List Nat) :
    Except SszDecodeError Unit :=
  if bytes.size < fixedSize ∨ offsets.isEmpty ∨ offsets.headD 0 ≠ fixedSize then
    .error .invalidSsz
  else
    let rec walk (previous : Nat) : List Nat → Except SszDecodeError Unit
      | [] => .ok ()
      | offset :: rest =>
          if offset < previous ∨ offset > bytes.size then .error .invalidSsz
          else walk offset rest
    walk fixedSize offsets

/-- Arguments of an offset-table check. -/
structure CanonicalOffsetsArgs where
  base : Nat
  bytes : ByteArray
  fixedSize : Nat
  offsets : List Nat

def preCanonicalOffsets (env : DecoderEnvironment) (args : CanonicalOffsetsArgs)
    (state : State) : Prop :=
  MemoryBytes state args.base args.bytes ∧
  env.CodeIntact state ∧
  state.regs.get? x10 = some (BitVec.ofNat 64 args.base) ∧
  state.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) ∧
  state.regs.get? x12 = some (BitVec.ofNat 64 args.fixedSize)

/-- The check reads only: it returns a status and disturbs nothing. -/
def postCanonicalOffsets (env : DecoderEnvironment) (args : CanonicalOffsetsArgs)
    (result : Except SszDecodeError Unit) (before after : State) : Prop :=
  LeafFrame env args.base args.bytes before after ∧
  match result with
  | .ok () => after.regs.get? x10 = some (BitVec.ofNat 64 0)
  | .error error => error = SszDecodeError.invalidSsz

def contractRequireCanonicalOffsets (env : DecoderEnvironment) :
    FunctionContract SszDecodeError CanonicalOffsetsArgs Unit where
  meaning := fun args => meaningRequireCanonicalOffsets args.bytes args.fixedSize args.offsets
  pre := preCanonicalOffsets env
  post := postCanonicalOffsets env
  stepBound := fun args => 32 + 32 * args.offsets.length

def correctnessClaimRequireCanonicalOffsets (env : DecoderEnvironment)
    (functionInstance : BinaryFv.Binary.Elfling.FunctionInstance)
    (entry : BitVec 64) (exit : BitVec 64 → Prop) : Prop :=
  ImplementsFunctionInstance functionInstance entry exit (contractRequireCanonicalOffsets env)

def satisfiableRequireCanonicalOffsets (env : DecoderEnvironment) : Prop :=
  ValidEnvironment env → PreSatisfiable (contractRequireCanonicalOffsets env)

/-!
## Characterization

The bridge from per-container offset checks to the oracle's global re-serialization test needs the
source-shaped composition to exist first, so it lives in `Contracts/Entry.lean` as
`sourceShapedDecodeAgreesWithOracle`. What belongs here is the exact acceptance condition of this
routine on its own.
-/

/-- A list of offsets is nondecreasing.

Spelled out rather than imported: this project does not depend on Mathlib. -/
def Nondecreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest => first ≤ second ∧ Nondecreasing (second :: rest)

/-- `requireCanonicalOffsets` accepts exactly the canonical prefix tables.

Note `offsets.headD 0 = fixedSize` is an *equality*: an offset table whose first entry merely
exceeds the fixed size is rejected, which is what forbids padding between the fixed section and the
first variable field. -/
def canonicalOffsetsCharacterization : Prop :=
  ∀ (bytes : ByteArray) (fixedSize : Nat) (offsets : List Nat),
    meaningRequireCanonicalOffsets bytes fixedSize offsets = .ok () ↔
      (fixedSize ≤ bytes.size ∧ offsets ≠ [] ∧ offsets.headD 0 = fixedSize ∧
        Nondecreasing offsets ∧ ∀ offset ∈ offsets, offset ≤ bytes.size)

/--
The `00 00 00 00` empty variable-element-list alias is rejected.

The oracle rejects it through `decodeCanonical`'s re-serialization equality; the binary rejects it
through `decodeByteListList`'s explicit `first_offset == 0` guard. This is the one alias where the
two otherwise-different canonicality mechanisms visibly coincide, which makes it the natural first
case of the composition bridge in `Contracts/Entry.lean`.
-/
def zeroFirstOffsetAliasRejected : Prop :=
  ∀ (bytes : ByteArray),
    bytes.size ≥ 4 → SszBridge.readU32LE? bytes 0 = some 0 →
      ∀ (elementType : SSZType) (capacity : Nat),
        (SszBridge.decodeCanonical (.list elementType capacity) bytes).toOption = none

end BinaryFv.SSZ.Zesu.Contracts
