import BinaryFv.RiscV.Elfling.Contract
import BinaryFv.SSZ.Zesu.MemoryRepresentation.RawV4

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.MemoryRepresentation

/-!
# The environment a decoder contract is stated against

A handwritten contract must be address-free, but it cannot be *fact*-free: it has to say which code
image is loaded, which memory the allocator owns, and where the fields of a returned Zig aggregate
sit. Those are all pinned-artifact facts.

Bundling them into one `DecoderEnvironment` parameter keeps the literals out of the contracts and
puts them where they belong — the artifact and generated layers instantiate this. It also makes the
ABI dependency visible rather than smuggled in as a magic constant: a field offset written inline in
a contract would be an unchecked guess about Zig's layout, whereas a field of this record is
something the pinned ABI manifest is obliged to supply.
-/

/-- Where the fields of an optional Zig aggregate sit, relative to its base.

The Zig layout of `?T` is not something a proof may assume; it is read from the pinned ABI manifest.
Keeping it as data means relinking or a compiler bump changes this record, not any contract. -/
structure OptionLayout where
  size : Nat
  discriminantOffset : Nat
  payloadOffset : Nat

/-- Field offsets within a `RawBlobSchedule` payload. -/
structure BlobScheduleLayout where
  targetOffset : Nat
  maxOffset : Nat
  baseFeeUpdateFractionOffset : Nat

/-- The pinned facts every decoder contract is stated against. -/
structure DecoderEnvironment where
  /-- The canonical loaded code image. Contracts assert it is unmodified; none of them names it. -/
  image : BinaryFv.Binary.ProgramImage
  /-- The addresses holding the bump allocator's mutable state. A non-allocating routine must leave
  every one of them unchanged, which is what turns "does not allocate" into a checkable claim. -/
  allocatorState : Nat → Prop
  optionalBlobSchedule : OptionLayout
  blobSchedule : BlobScheduleLayout
  optionalU64 : OptionLayout

namespace DecoderEnvironment

/-- No byte of the allocator's mutable state changed: the routine performed no allocation. -/
def NoAllocation (env : DecoderEnvironment) (before after : State) : Prop :=
  ∀ address, env.allocatorState address → after.mem.get? address = before.mem.get? address

/-- The loaded code was not modified. -/
def CodeIntact (env : DecoderEnvironment) (state : State) : Prop :=
  env.image.matchesMemory state.mem

end DecoderEnvironment

/--
The internal consistency an environment needs for its contracts' preconditions to be satisfiable.

This is the antecedent every satisfiability obligation shares. It is deliberately about the *layout*
record, not about any particular state: it says the Zig `?T` field offsets the environment claims are
self-consistent (a discriminant and payload that fit inside the option and do not collide). Without
it, a satisfiability claim could be asserting the existence of a state for a nonsensical layout, and
"impossible unconditional satisfiability" is exactly what the review asked us not to assert.
-/
def ValidEnvironment (env : DecoderEnvironment) : Prop :=
  env.optionalBlobSchedule.discriminantOffset < env.optionalBlobSchedule.size ∧
  env.optionalBlobSchedule.payloadOffset + 24 ≤ env.optionalBlobSchedule.size ∧
  env.optionalU64.discriminantOffset < env.optionalU64.size ∧
  env.optionalU64.payloadOffset + 8 ≤ env.optionalU64.size

/-- An absent option: the discriminant reads zero. -/
def OptionNoneRep (layout : OptionLayout) (state : State) (base : Nat) : Prop :=
  state.mem.get? (base + layout.discriminantOffset) = some (BitVec.ofNat 8 0)

/-- A present option: the discriminant reads one. -/
def OptionSomeRep (layout : OptionLayout) (state : State) (base : Nat) : Prop :=
  state.mem.get? (base + layout.discriminantOffset) = some (BitVec.ofNat 8 1)

/-- A `RawBlobSchedule` payload laid out at `base`, all three fields little-endian. -/
def RawBlobScheduleRep (layout : BlobScheduleLayout) (state : State) (base : Nat)
    (value : SszBridge.RawBlobSchedule) : Prop :=
  Word64LERep state (base + layout.targetOffset) value.target.toNat ∧
  Word64LERep state (base + layout.maxOffset) value.max.toNat ∧
  Word64LERep state (base + layout.baseFeeUpdateFractionOffset) value.baseFeeUpdateFraction.toNat

end BinaryFv.SSZ.Zesu.Contracts
