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
  deriving DecidableEq, Repr, Inhabited

/-- Field offsets within a `RawBlobSchedule` payload. -/
structure BlobScheduleLayout where
  targetOffset : Nat
  maxOffset : Nat
  baseFeeUpdateFractionOffset : Nat
  deriving DecidableEq, Repr

/-- The pinned facts every decoder contract is stated against. -/
structure DecoderEnvironment where
  /-- The canonical loaded code image. Contracts assert it is unmodified; none of them names it. -/
  image : BinaryFv.Binary.ProgramImage
  /-- The addresses holding the bump allocator's mutable state. A non-allocating routine must leave
  every one of them unchanged, which is what turns "does not allocate" into a checkable claim. -/
  allocatorState : Nat → Prop
  /-- Address of the bump cursor (`ZKVM_HEAP_POS`) and of the arena's base.

  These make "how much has been allocated" a statement about the machine rather than about a ghost
  counter. That matters because the decoder's own exhaustion branch compares the *real* cursor
  against the ceiling: a counter would only settle real unreachability once it had been proved equal
  to the cursor delta, so bounding the cursor directly skips a step rather than losing one. Both
  addresses must lie in `allocatorState`, which `ValidAllocatorAddresses` requires. -/
  heapPosAddr : Nat
  /-- Base of the arena the cursor advances through. -/
  arenaBase : Nat
  optionalBlobSchedule : OptionLayout
  blobSchedule : BlobScheduleLayout
  optionalU64 : OptionLayout

namespace DecoderEnvironment

/-- No byte of the allocator's mutable state changed: the routine performed no allocation. -/
def NoAllocation (env : DecoderEnvironment) (before after : State) : Prop :=
  ∀ address, env.allocatorState address → after.mem.get? address = before.mem.get? address

/-- The bump cursor's current value, read out of machine memory. -/
def cursor? (env : DecoderEnvironment) (state : State) : Option Nat :=
  observeWord64? state env.heapPosAddr

/-- How many bytes the allocator has handed out: how far the cursor has advanced past the arena
base. This is the quantity the arena bound is about. -/
def allocatedBytes? (env : DecoderEnvironment) (state : State) : Option Nat :=
  (env.cursor? state).map (· - env.arenaBase)

/-- **A routine that allocates nothing leaves the cursor exactly where it was.** The qualitative
`NoAllocation` already pins every allocator-state byte, so the quantitative fact falls out rather
than needing its own clause — which is why adding the cursor to the environment strengthens the
allocator's contract without touching any non-allocating routine's. -/
theorem cursor_eq_of_noAllocation {env : DecoderEnvironment} {before after : State}
    (inState : ∀ i, i < 8 → env.allocatorState (env.heapPosAddr + i))
    (noAlloc : env.NoAllocation before after) :
    env.cursor? after = env.cursor? before := by
  unfold cursor? observeWord64?
  have hbytes : ∀ i, i < 8 →
      after.mem.get? (env.heapPosAddr + i) = before.mem.get? (env.heapPosAddr + i) :=
    fun i hi => noAlloc _ (inState i hi)
  have h0 := hbytes 0 (by omega)
  have h1 := hbytes 1 (by omega)
  have h2 := hbytes 2 (by omega)
  have h3 := hbytes 3 (by omega)
  have h4 := hbytes 4 (by omega)
  have h5 := hbytes 5 (by omega)
  have h6 := hbytes 6 (by omega)
  have h7 := hbytes 7 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The loaded code and read-only constant data were not modified.

**This is the file-backed image, not the full image** — and that distinction is a correction, not a
convenience. The pinned Zesu ELF has a single RWX load segment whose file-backed bytes
(`[0x10000, 0x1500C)`) are the code and rodata, while its zero-filled BSS tail holds the *mutable*
runtime state: the host-provided heap globals `ZKVM_HEAP_POS`/`ZKVM_HEAP_TOP`, the 64 MiB arena, and
the decoder's private globals (`attempted`, `last_status`, `stored_result`). The freestanding
`zesu_raw_alloc` reads `ZKVM_HEAP_POS`/`ZKVM_HEAP_TOP` as host-provided `extern var`s and *writes*
`ZKVM_HEAP_POS` on every allocation; the wrapper writes all three decoder globals. So a full-image
`matchesMemory` — which pins every BSS byte to its static zero — is **unsatisfiable** on any
mutating path: `postAlloc`'s `CodeIntact after` would demand the cursor still be zero after the
allocator advanced it. `fileBytesMatchMemory` preserves exactly the code and rodata the decoder must
not corrupt, and leaves the mutable BSS to the predicates that actually pin it (`DecoderGlobalsRep`
for the decoder globals, the allocation ledger for the heap), which is the correct division. -/
def CodeIntact (env : DecoderEnvironment) (state : State) : Prop :=
  env.image.fileBytesMatchMemory state.mem

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
