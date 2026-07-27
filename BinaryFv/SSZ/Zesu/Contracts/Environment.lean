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

/-- The size of the result record each routine family writes at its `resultBase`.

The ownership clause below needs `range resultBase recordSize`, and the size is a Zig layout fact.
It arrives here for the reason every other layout fact does: a size written inline in a contract
would be an unchecked guess, and — because the clause is a *permission* — an over-large guess weakens
it silently while proving exactly as easily. `Artifact.AbiManifest` records the same warning about
footprints; it applies with the sign flipped here.

`sliceDescriptor` is the Zig `[]T` descriptor (pointer + length) every collection publishes at its
result base; it is the only entry that is not a named `ssz_raw.*` record. -/
structure ResultRecordSizes where
  forkActivation : Nat
  forkConfig : Nat
  chainConfig : Nat
  executionRequests : Nat
  executionWitness : Nat
  executionPayload : Nat
  newPayloadRequest : Nat
  /-- The internal `decodeRaw`/`decode` result/error union written at `EntryArgs.resultBase`: the
  `?RawStatelessInput` object, 832-byte payload plus discriminant. -/
  entryResult : Nat
  sliceDescriptor : Nat
  deriving DecidableEq, Repr, Inhabited

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
  /-- Result-record sizes, so the ownership clause names no literal. -/
  record : ResultRecordSizes

/-! ## Memory ownership vocabulary

`Contracts.Ownership` and `Contracts.Footprint` are where this vocabulary is *used*, but they sit
above every contract module in the import order, so the definitions live here — at the one point
every `post*` predicate can see them. Those modules pick these up by name resolution from the
enclosing `Contracts` namespace; there is exactly one definition of each.
-/

/-- A set of addresses. Kept as a predicate rather than a range because owned regions are not
contiguous in general — a container owns its result buffer and whatever it allocated. -/
abbrev Region := Nat → Prop

def Region.union (r1 r2 : Region) : Region := fun address => r1 address ∨ r2 address

/-- A half-open byte range, the shape every container record takes. -/
def range (base size : Nat) : Region := fun address => base ≤ address ∧ address < base + size

/-- A half-open cursor interval: the bytes one allocation consumed. -/
def interval (before after : Nat) : Region := fun address => before ≤ address ∧ address < after

/-- What a heap-allocated child owns: its record, plus what it allocated. -/
def allocatedRegion (recordBase recordSize before after : Nat) : Region :=
  Region.union (range recordBase recordSize) (interval before after)

/-- **The callee's obligation:** every write lands inside `owned`.

Note the direction. This is *not* "the routine writes all of `owned`" — it is permission, not
requirement, so a routine that writes nothing satisfies it for any region. -/
def WritesOnlyWithin (owned : Region) (before after : State) : Prop :=
  ∀ address, ¬ owned address → after.mem.get? address = before.mem.get? address

/-- **The exact clause the composition consumes.** A routine that produces a record at `recordBase`
and allocates from `cursorBefore` to `cursorAfter` writes nowhere outside those two regions.

`OwnershipComposition.siblingChain_of_writesOnlyWithinAllocation` turns one of these into a
`SiblingChain` step; that is the only reason the clause has this exact shape rather than a bare
`WritesOnlyWithin` at a hand-named region. -/
def WritesOnlyWithinAllocation (recordBase recordSize cursorBefore cursorAfter : Nat)
    (before after : State) : Prop :=
  WritesOnlyWithin (allocatedRegion recordBase recordSize cursorBefore cursorAfter) before after

/-- The clause a **non-allocating** routine carries: the allocation interval is empty, so the
permission is exactly "writes only within my own result record".

The empty interval is justified rather than assumed. Every routine carrying this also carries
`env.NoAllocation`, and `cursor_eq_of_noAllocation` below turns that into `cursor? after =
cursor? before` — the routine really did consume no arena, so an empty interval gives away nothing.
Definitionally `WritesOnlyWithinAllocation … 0 0`, so the composition lemma applies unchanged. -/
def WritesOnlyWithinRecord (recordBase recordSize : Nat) (before after : State) : Prop :=
  WritesOnlyWithinAllocation recordBase recordSize 0 0 before after

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

/-- The clause an **allocating** routine carries: its own result record, the arena interval its
allocations consumed, **and the allocator's own mutable state**.

*Why the cursor pair is read from the machine rather than taken as a ghost parameter.* An allocating
container does not receive the cursor; it is a fact about the two states, and stating it as
`env.cursor?` is what lets a caller line the interval up with `postAlloc`'s bounds — the same numbers,
read the same way — instead of relating a ghost to a memory word.

*Why `env.allocatorState` is in the region, and it is not slack.* `zesu_raw_alloc` advances
`ZKVM_HEAP_POS`, which lies outside both `range recordBase recordSize` and
`interval cursorBefore cursorAfter`. A clause omitting it would be **false of every allocating
routine in the decoder**, not merely weak — and false clauses on an assumed hypothesis are how a
conditional root goes vacuous. This corrects `OwnershipComposition`'s wording, which said an
allocating routine "writes nowhere outside those two regions".

*What it still does not cover, stated because it is the reason this is not yet dischargeable.* A
compiled routine also writes its **stack frame**, and no contract here names one: `sp` is restored
by the epilogue, so the frame is not recoverable from `before`/`after`, and a region large enough to
contain any frame ("everything below the caller's `sp`") would swallow the arena and make the clause
decorative. So this clause — like `WritesOnlyWithinRecord` — is currently *stronger* than the binary
satisfies. It is consumed only through `LocalContractAssumptions`, which is assumed and proved
nowhere, so nothing in the tree is broken today; the Rows E–I local proofs are where the stack region
has to be added, and until it is, no local proof can discharge this. -/
def WritesOnlyWithinOwnAllocation (env : DecoderEnvironment) (recordBase recordSize : Nat)
    (before after : State) : Prop :=
  ∃ cursorBefore cursorAfter,
    env.cursor? before = some cursorBefore ∧ env.cursor? after = some cursorAfter ∧
      WritesOnlyWithin
        (Region.union (allocatedRegion recordBase recordSize cursorBefore cursorAfter)
          env.allocatorState) before after

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
