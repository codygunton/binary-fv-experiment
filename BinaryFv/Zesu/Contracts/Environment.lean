import BinaryFv.RiscV.Elfling.Contract
import BinaryFv.Zesu.MemoryRepresentation.RawV4

namespace BinaryFv.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.Zesu.MemoryRepresentation

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

/-- The size of the result record each function instance family writes at its `resultBase`.

The ownership clause below needs `range resultBase recordSize`, and the size is a Zig layout fact.
It arrives here for the reason every other layout fact does: a size written inline in a contract
would be an unchecked guess, and — because the clause is a *permission* — an over-large guess weakens
it silently while proving exactly as easily. `Artifacts.AbiManifest` records the same warning about
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
  /-- Byte offset of the two-byte discriminant within `entryResult`. -/
  entryResultTagOffset : Nat
  sliceDescriptor : Nat
  /-- The two-word Zig `std.mem.Allocator` value the `allocator()` constructor writes at its result
  base: a context pointer followed by a vtable pointer, exactly the span
  `MemoryRepresentation.AllocatorObjectRep` pins. Unreflected for the same reason
  `sliceDescriptor` is — the manifest has no key for a `std.mem` type — and 16 for the same reason
  too: two pointers on this target. -/
  allocatorObject : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The pinned facts every decoder contract is stated against. -/
structure DecoderEnvironment where
  /-- The canonical loaded code image. Contracts assert it is unmodified; none of them names it. -/
  image : BinaryFv.Binary.ProgramImage
  /-- The addresses holding the bump allocator's mutable state. A non-allocating source function must leave
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
  /-- **The machine stack the function instances' frames live in.**

  The same kind of fact as `allocatorState` — a region of the machine that the contracts must be able
  to name but must not spell as a literal — and it is here for the same reason: without it the
  ownership clause is *false of every compiled function instance*, because a compiled function instance writes its stack
  frame and no other field of this record can name one.

  Note what makes this expressible where "the frame" is not. A frame is `[sp_final, sp_entry)`, and
  `sp` is restored by the epilogue, so the frame is unrecoverable from a `before`/`after` pair. The
  *stack* is not: it is a fixed region the caller of the whole program chose, it contains every frame
  of every function instance in the run, and — the part that makes it useful rather than decorative — it is
  disjoint from the arena, from the decoder's globals, and from the input buffer, because the runner
  places it far above everything the ELF loads. `CanonicalParams` pins it to the runner's stack and
  proves those disjointnesses; "everything below the caller's `sp`" would have swallowed the arena and
  bought nothing.

  **What permitting the whole stack gives away, stated because it is a real cost.** A callee may now
  scribble the *caller's* frame as far as these contracts are concerned, and a result record that is
  itself a stack temporary gets no protection from the ownership discipline. Neither loss touches
  anything the discipline currently protects — every representation it transports lives in the arena
  or in the decoder's globals — but both would be recovered by the sharper region
  `interval stackBase sp_before`, which is expressible here (`before.regs` is in scope) and is the
  obvious future strengthening. It is not taken now because it is only sound if no function instance ever writes
  at or above its entry `sp`, and that is a claim about the compiled code that is not yet checked;
  taking it on faith would risk re-introducing exactly the unsatisfiable clause this field removes. -/
  stack : Nat → Prop

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

Note the direction. This is *not* "the function instance writes all of `owned`" — it is permission, not
requirement, so a function instance that writes nothing satisfies it for any region. -/
def WritesOnlyWithin (owned : Region) (before after : State) : Prop :=
  ∀ address, ¬ owned address → after.mem.get? address = before.mem.get? address

/-- **The data half of what a function instance owns.** A function instance that produces a record at `recordBase` and
allocates from `cursorBefore` to `cursorAfter` writes nowhere outside those two regions *plus the
machine's own bookkeeping* — the allocator's state and the stack — which is why this is a component
of the contract clauses rather than one of them.

`OwnershipComposition.siblingChain_of_writesOnlyWithinAllocation` turns one of these into a
`SiblingChain` step; that is the only reason the clause has this exact shape rather than a bare
`WritesOnlyWithin` at a hand-named region.

**This form is stated of no compiled function instance and must not be.** It was the clause 17 `post*`
predicates carried until the stack region existed, and it is false of every one of them: a compiled
function instance writes its frame. It survives as the region-only core the composition consumes and as the
thing `DecoderEnvironment.WritesOnlyWithinOwnRecord` / `…OwnAllocation` are built from. -/
def WritesOnlyWithinAllocation (recordBase recordSize cursorBefore cursorAfter : Nat)
    (before after : State) : Prop :=
  WritesOnlyWithin (allocatedRegion recordBase recordSize cursorBefore cursorAfter) before after

/-- The same at an empty allocation interval: "writes only within my own result record". Retained for
the same reason as `WritesOnlyWithinAllocation`, and carrying the same warning — this is not the
clause any contract states. -/
def WritesOnlyWithinRecord (recordBase recordSize : Nat) (before after : State) : Prop :=
  WritesOnlyWithinAllocation recordBase recordSize 0 0 before after

namespace DecoderEnvironment

/-- No byte of the allocator's mutable state changed: the source function performed no allocation. -/
def NoAllocation (env : DecoderEnvironment) (before after : State) : Prop :=
  ∀ address, env.allocatorState address → after.mem.get? address = before.mem.get? address

/-- The bump cursor's current value, read out of machine memory. -/
def cursor? (env : DecoderEnvironment) (state : State) : Option Nat :=
  observeWord64? state env.heapPosAddr

/-- How many bytes the allocator has handed out: how far the cursor has advanced past the arena
base. This is the quantity the arena bound is about. -/
def allocatedBytes? (env : DecoderEnvironment) (state : State) : Option Nat :=
  (env.cursor? state).map (· - env.arenaBase)

/-- **A function instance that allocates nothing leaves the cursor exactly where it was.** The qualitative
`NoAllocation` already pins every allocator-state byte, so the quantitative fact falls out rather
than needing its own clause — which is why adding the cursor to the environment strengthens the
allocator's contract without touching any non-allocating function instance's. -/
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

/-- **Everything an allocating function instance may write:** its result record, the arena interval its
allocations consumed, the allocator's own mutable state, and the machine stack its frame lives in.

The four are here for one reason each, and none of them is slack:

* the **record** is the function instance's output — the only part a caller cares about;
* the **interval** is what it allocated, and `postAlloc`'s `cursorBefore ≤ address ∧
  address + bytes ≤ cursorAfter` is what makes the blocks it handed out lie inside it;
* **`env.allocatorState`** because `zesu_raw_alloc` advances `ZKVM_HEAP_POS`, which is in neither of
  the two above — a clause omitting it is *false of every allocating function instance in the decoder*;
* **`env.stack`** because a compiled function instance writes its frame, which is in none of the three — a
  clause omitting it is *false of every compiled function instance whatsoever*.

The last two entries were added by the same argument at two sittings, and the argument is the one
that matters here: a permission clause that no implementation can satisfy is worse than no clause,
because an unsatisfiable contract premise makes a conditional correctness theorem vacuous while
looking stronger. -/
def ownedRegion (env : DecoderEnvironment) (recordBase recordSize cursorBefore cursorAfter : Nat) :
    Region :=
  Region.union (allocatedRegion recordBase recordSize cursorBefore cursorAfter)
    (Region.union env.allocatorState env.stack)

/-- The clause a **non-allocating** function instance carries: its own result record and its stack frame.

**`env.allocatorState` is deliberately absent, and that is a strengthening rather than an
oversight.** Every function instance carrying this also carries `env.NoAllocation`, which pins every
allocator-state byte to its old value, so admitting those addresses here would be strictly weaker for
no gain. The empty allocation interval is justified the same way: `cursor_eq_of_noAllocation` turns
`NoAllocation` into `cursor? after = cursor? before`, so the function instance really did consume no arena.

`recordSize = 0` is therefore the *strongest* instance — "writes nothing outside its own stack frame"
— and it is what the leaf readers and the exported accessors carry. -/
def WritesOnlyWithinOwnRecord (env : DecoderEnvironment) (recordBase recordSize : Nat)
    (before after : State) : Prop :=
  WritesOnlyWithin (Region.union (allocatedRegion recordBase recordSize 0 0) env.stack) before after

/-- The clause an **allocating** function instance carries: `ownedRegion`, at the cursor pair read off the two
states.

*Why the cursor pair is read from the machine rather than taken as a ghost parameter.* An allocating
container does not receive the cursor; it is a fact about the two states, and stating it as
`env.cursor?` is what lets a caller line the interval up with `postAlloc`'s bounds — the same numbers,
read the same way — instead of relating a ghost to a memory word. -/
def WritesOnlyWithinOwnAllocation (env : DecoderEnvironment) (recordBase recordSize : Nat)
    (before after : State) : Prop :=
  ∃ cursorBefore cursorAfter,
    env.cursor? before = some cursorBefore ∧ env.cursor? after = some cursorAfter ∧
      WritesOnlyWithin (env.ownedRegion recordBase recordSize cursorBefore cursorAfter) before after

/-- **The non-allocating clause is the allocating one at an empty interval, minus the allocator
state.** Stated so the relationship between the two is a checked fact rather than a naming
convention: anything that satisfies the record clause satisfies the wider allocating region, which is
what lets one composition lemma serve both. -/
theorem writesOnlyWithinOwnRecord_le_ownedRegion (env : DecoderEnvironment)
    {recordBase recordSize cursorBefore cursorAfter : Nat} (address : Nat)
    (h : Region.union (allocatedRegion recordBase recordSize 0 0) env.stack address) :
    env.ownedRegion recordBase recordSize cursorBefore cursorAfter address := by
  rcases h with hrec | hstack
  · rcases hrec with hrange | hint
    · exact Or.inl (Or.inl hrange)
    · exact absurd hint.2 (Nat.not_lt_zero _)
  · exact Or.inr (Or.inr hstack)

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
    (value : BinaryFv.Specs.SSZ.RawBlobSchedule) : Prop :=
  Word64LERep state (base + layout.targetOffset) value.target.toNat ∧
  Word64LERep state (base + layout.maxOffset) value.max.toNat ∧
  Word64LERep state (base + layout.baseFeeUpdateFractionOffset) value.baseFeeUpdateFraction.toNat

end BinaryFv.Zesu.Contracts
