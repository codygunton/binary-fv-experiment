import BinaryFv.SSZ.Zesu.Validation.BoundarySatisfiability
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Runner
import BinaryFv.SSZ.Zesu.Validation.MeaningAgreement
import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams
import BinaryFv.SSZ.Zesu.Elfling.BindingInventory
import Std.Data.ExtHashMap.Lemmas

/-!
# Contract ground truth — the handwritten `pre`/`post` against real machine states

The 141 local obligations are `LocallyImplementsFunctionInstance`, i.e. for each instance

> from any state satisfying `contract.pre args`, entering at `entryPc`, the machine reaches a
> declared exit in at most `stepBound args` steps, in a state satisfying `contract.post args`.

Row C already checks structural and binding facts about captured entry states. It has never
evaluated `pre` or `post` themselves. This module does, by **running the pinned ELF in the Sail
model** (the same machine `RunnerExecution` uses) with the loop instrumented to snapshot the state
at every function instance's `entryPc` and at its first subsequent declared exit, and then applying
the **real handwritten predicates** — `preReadAt`, `postScalarRead` — to those states.

Everything here is falsification evidence. Nothing in the theorem graph imports it.

## The five questions, and what is actually answered

| # | question | how | decided / total |
| --- | --- | --- | --- |
| 1 | does the machine enter at the declared `entryPc`? | the instrumented run | 135 entered, 6 never reached |
| 2 | does `pre` hold at that state? | the real `preReadAt`, at Row A's `offset` | 102 decided, **100 refuted**, 2 pass `@witness-args` |
| 3 | does it leave at a declared exit, and is `entryPc` among the exits? | the run + `BoundarySatisfiability` | 136 decided, **33 refuted** |
| 4 | does `post` hold at the exit state? | the full real `postScalarRead` / `postBytesAt` | 10 decided, **10 refuted**, 0 pass |
| 5 | real retired steps vs `stepBound args` | `exitStep - entryStep` against the contract's own field | 105 decided, **1 refuted** |

Everything outside those counts is an explicit `gap` carrying its reason. **A gap is never a pass**,
and the gap counts are large: column 4 in particular is undecidable for 131 of 141 instances, which
is itself the finding recorded in `post_refutations_include_exact_frame_violation`.

## Where the arguments come from, and why that is the whole measurement

`pre` and `post` are functions of `args`, so the harness must supply them, and reading them out of
the registers the predicate constrains would make every check pass by construction. The `offset`
argument therefore comes from **Row A's binding inventory** (`GeneratedBindings.bindings`, DWARF
`.debug_loc` resolved at the entry PC) — an independent statement of where the Zig parameter lives,
which knows nothing about the contract. That disagreement *is* the finding: `preReadAt` demands the
offset in `x12`, and Row A binds it to `x9`/`x18`/`x19`/`x24`/`x27` or to a constant.

`base` and `bytes` are **not** independently pinned — Row A declares no binding for them (see
`read_family_declares_no_base_or_size_binding`). They are therefore taken from the state itself:
`base := x10`, `bytes := ` the memory content at `[base, base + x11)`. That choice makes three of
`preReadAt`'s five conjuncts true **by construction**. It is deliberate and one-directional:

* a `false` verdict is a genuine refutation — the surviving conjuncts are the ones the artifact
  cannot satisfy however the missing arguments are chosen;
* a `true` verdict is **not** evidence that `pre` holds at the arguments the caller really passed.
  It is rendered `ok@witness-args` for that reason and must never be read as a pass.

## Which conjuncts are checked, named exactly

`preReadAt` has five conjuncts and **all five are evaluated** (`preReadAtB`, tied to the predicate by
`preReadAtB_of_preReadAt`). The `x12 = offset` conjunct is additionally decided **on its own, first**,
because it is the one that does not depend on the two unpinned arguments: `offset` is fixed by Row A,
so a mismatch there refutes `preReadAt` at every `base`/`bytes`. That is why column 2 reaches 102
decided rows while column 4 reaches only 10.

`postScalarRead` has, expanded, six: `MemoryBytes after`, `CodeIntact after`, `NoAllocation`,
`WritesOnlyWithinOwnRecord`, `value < 2 ^ width`, and `after.regs x10 = value`. **All six are now
evaluated.** `WritesOnlyWithinOwnRecord` is an unbounded quantifier, while `State.mem` is an
extensional hash map that deliberately exposes no order-dependent iterator. `memorySupportAll`
resolves that mismatch without weakening the clause: it quotient-lifts a permutation-invariant
Boolean fold over each representation's keys, and `writesOnlyWithinB_iff` proves that checking both
finite supports is equivalent to the original universal predicate. A byte absent from both
supports reads `none` in both maps, which is exactly why the finite check is complete rather than
sampled.

`postBytesAt` has, expanded, six as well: the same four `LeafFrame … 0 0` conjuncts — `bytesAt`
returns a *borrowed* sub-slice and so has no result record either — plus
`after.regs x10 = base + offset` and `after.regs x11 = length`. **All six are now evaluated.** The
only argument beyond `preReadAt`'s is the runtime `len`, and Row A binds it (`lenBindingRow?`), so
these rows need no witness the harness did not already have. Before task 6a-v they were reported as
needing "a resultBase Row A does not pin", which was simply the wrong reason: `postBytesAt` mentions
no `resultBase` at all.

## The evaluation order, and why it matters

`post` evaluates the three **record-independent** `LeafFrame` conjuncts *before* dispatching on the
post shape. `leafFrameSharedB_of_leafFrame` quantifies over `recordBase`/`recordSize`, so refuting
one of them refutes the postcondition whatever result slot the caller really used. That is what lets
a `readU256`/`readArray` row be decided despite an unpinned `resultBase` — and on this arm none of
them is (`readU256_and_readArray_leave_only_the_record_clauses_open`), which is a recorded negative
result rather than an untried branch.

## What is not covered at all

* **33 tags outside the read family** (containers, collections, options, entry, runtime,
  allocator): their `pre`/`post` are equally decidable in principle, but their arguments
  (`resultBase`, `allocatorBase`, per-container records) have no Row A binding either, and
  reconstructing them is a separate piece of work. Reported as `gap`, per instance.
* **One arm.** The run is the rich accepted fixture. An instance the fixture never reaches is a
  `gap`, never a pass — the same discipline Row C uses.
* **First invocation only.** For an instance entered many times, the first entry and its first
  subsequent exit are captured. A later invocation could fail a check this one passes.
-/

namespace BinaryFv.SSZ.Zesu.Validation.GroundTruth

set_option maxRecDepth 100000

open BinaryFv.Binary
open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram generatedManifest)
open BinaryFv.SSZ.Zesu.Validation.Boundary (Verdict)
open PreSail LeanRV64DExecutable.Functions Register
open Std

/-! ## Executable mirrors of the predicate primitives

Each mirror is tied to the predicate it mirrors by a theorem in the *refutation* direction —
`Prop → mirror = true`, equivalently `mirror = false → ¬ Prop`. That is the direction falsification
evidence needs, and it is what a Python re-implementation cannot supply at all. -/

/-- Bounded mirror of `MemoryBytes`. -/
def memoryBytesB (s : State) (base : Nat) (bytes : ByteArray) : Bool :=
  (List.range bytes.size).all fun index =>
    match bytes[index]? with
    | some byte => s.mem.get? (base + index) == some (BitVec.ofNat 8 byte.toNat)
    | none => true

theorem memoryBytesB_of_memoryBytes {s : State} {base : Nat} {bytes : ByteArray}
    (h : MemoryBytes s base bytes) : memoryBytesB s base bytes = true := by
  simp only [memoryBytesB, List.all_eq_true, List.mem_range]
  intro index hindex
  have hget : bytes[index]? = some (bytes[index]'hindex) := getElem?_pos bytes index hindex
  rw [hget]
  simpa using h index hindex

/-- The file-backed addresses of the image, in segment order. `fileBytesMatchMemory` quantifies over
every address, but `readFileByte?` is `some` only inside a segment's file window, so this list covers
every address at which the predicate says anything. -/
def fileBackedAddresses (image : ProgramImage) : List Nat :=
  image.segments.toList.flatMap fun segment =>
    (List.range segment.initialBytes.size).map fun index => segment.virtualAddress + index

/-- Bounded mirror of `ProgramImage.fileBytesMatchMemory`, i.e. of `DecoderEnvironment.CodeIntact`.
It consults `image.readFileByte?` — the image-level reader `fileBytesMatchMemory` itself uses — so it
never asserts anything about a segment the predicate does not reach. -/
def codeIntactB (image : ProgramImage) (s : State) : Bool :=
  (fileBackedAddresses image).all fun address =>
    match image.readFileByte? address with
    | some byte => s.mem.get? address == some (BitVec.ofNat 8 byte.toNat)
    | none => true

theorem codeIntactB_of_fileBytesMatchMemory {image : ProgramImage} {s : State}
    (h : image.fileBytesMatchMemory s.mem) : codeIntactB image s = true := by
  simp only [codeIntactB, List.all_eq_true]
  intro address _
  cases hread : image.readFileByte? address with
  | none => simp
  | some byte => simpa using h address byte hread

/-- The 16 addresses `canonicalAllocatorState` holds of: the cursor word and the arena-top word. -/
def canonicalAllocatorAddresses : List Nat :=
  (List.range 8).map (fun i => Elfling.canonicalHeapPosAddr + i) ++
    (List.range 8).map (fun i => Elfling.canonicalHeapTopAddr + i)

theorem canonicalAllocatorAddresses_are_allocator_state :
    ∀ address ∈ canonicalAllocatorAddresses, Elfling.canonicalAllocatorState address := by
  intro address hmem
  simp only [canonicalAllocatorAddresses, List.mem_append, List.mem_map, List.mem_range] at hmem
  rcases hmem with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact Or.inl ⟨Nat.le_add_right _ _, by omega⟩
  · exact Or.inr ⟨Nat.le_add_right _ _, by omega⟩

/-- Bounded mirror of `DecoderEnvironment.NoAllocation` at the canonical environment. -/
def noAllocationB (before after : State) : Bool :=
  canonicalAllocatorAddresses.all fun address => after.mem.get? address == before.mem.get? address

theorem noAllocationB_of_noAllocation {before after : State}
    (h : canonicalEnvironment.NoAllocation before after) : noAllocationB before after = true := by
  simp only [noAllocationB, List.all_eq_true]
  intro address hmem
  have : canonicalEnvironment.allocatorState address :=
    canonicalAllocatorAddresses_are_allocator_state address hmem
  simpa using h address this

/-! ### Exact support enumeration for the universal write-frame clause

`ExtHashMap` is a quotient by extensional equality, so an arbitrary bucket-order traversal cannot
be exposed as a list. A Boolean conjunction over the keys *is* representation-independent:
equivalent representatives have permuted key lists, and `List.all` is invariant under permutation.
The executable definition uses the map's direct fold, avoiding both sorting and materializing a
million-element key list for the canonical stack; its proof relates that fold to `List.all`. -/

private theorem foldl_and_eq_all {α : Type} (p : α → Bool) (xs : List α) (init : Bool) :
    xs.foldl (fun acc x => acc && p x) init = (init && xs.all p) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.all_cons]
    rw [ih]
    exact Bool.and_assoc _ _ _

/-- Apply a Boolean predicate to every key of an extensional hash map, in linear time. -/
def memorySupportAll {β : Type} (m : ExtHashMap Nat β) (p : Nat → Bool) : Bool :=
  m.inner.lift
    (fun raw => raw.fold (fun acc address _ => acc && p address) true)
    (by
      intro a b h
      change a.fold (fun acc address _ => acc && p address) true =
        b.fold (fun acc address _ => acc && p address) true
      rw [Std.DHashMap.fold_eq_foldl_keys, Std.DHashMap.fold_eq_foldl_keys,
        foldl_and_eq_all, foldl_and_eq_all]
      simp only [Bool.true_and]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro ha address hmem
        exact ha address ((Std.DHashMap.Equiv.keys_perm h).mem_iff.mpr hmem)
      · intro hb address hmem
        exact hb address ((Std.DHashMap.Equiv.keys_perm h).mem_iff.mp hmem))

/-- The lifted fold checks exactly the present keys, despite the quotient representation. -/
theorem memorySupportAll_eq_true_iff
    {β : Type} {m : ExtHashMap Nat β} {p : Nat → Bool} :
    memorySupportAll m p = true ↔
      ∀ address, (m.get? address).isSome → p address = true := by
  rcases m with ⟨inner⟩
  induction inner using ExtDHashMap.inductionOn with
  | mk raw =>
    unfold memorySupportAll ExtDHashMap.lift ExtHashMap.get? ExtDHashMap.Const.get? ExtDHashMap.mk
    change raw.fold (fun acc address _ => acc && p address) true = true ↔ ∀ address,
      (Std.DHashMap.Const.get? raw address).isSome → p address = true
    rw [Std.DHashMap.fold_eq_foldl_keys, foldl_and_eq_all]
    simp only [Bool.true_and, List.all_eq_true]
    constructor
    · intro hall address hsome
      apply hall address
      rw [Std.DHashMap.mem_keys]
      exact Std.DHashMap.Const.mem_iff_isSome_get?.mpr hsome
    · intro hall address hmem
      apply hall address
      exact Std.DHashMap.Const.mem_iff_isSome_get?.mp
        (Std.DHashMap.mem_keys.mp hmem)

private def minimumWhereStep (p : Nat → Bool) (acc address : Nat) : Nat :=
  if p address then min acc address else acc

private theorem minimumWhereStep_comm (p : Nat → Bool) (acc first second : Nat) :
    minimumWhereStep p (minimumWhereStep p acc first) second =
      minimumWhereStep p (minimumWhereStep p acc second) first := by
  simp only [minimumWhereStep]
  by_cases hfirst : p first <;> by_cases hsecond : p second <;>
    simp [hfirst, hsecond, Nat.min_comm, Nat.min_left_comm]

/-- The least support key satisfying `p`, or `sentinel` when none does. The minimum makes the result
permutation-invariant, while the executable path still folds the hash buckets directly. -/
def memorySupportMinimumWhere {β : Type} (m : ExtHashMap Nat β) (p : Nat → Bool)
    (sentinel : Nat) : Nat :=
  m.inner.lift
    (fun raw => raw.fold (fun acc address _ => minimumWhereStep p acc address) sentinel)
    (by
      intro a b h
      change a.fold (fun acc address _ => minimumWhereStep p acc address) sentinel =
        b.fold (fun acc address _ => minimumWhereStep p acc address) sentinel
      rw [Std.DHashMap.fold_eq_foldl_keys, Std.DHashMap.fold_eq_foldl_keys]
      exact (Std.DHashMap.Equiv.keys_perm h).foldl_eq'
        (fun x _ y _ z => minimumWhereStep_comm p z x y) sentinel)

/-- The least changed address outside `ownedB` across the two finite supports. Machine addresses are
64-bit, so `2^64` is the distinguished no-violation result for captured Sail states. -/
def firstWriteFrameViolation (ownedB : Nat → Bool) (before after : State) : Nat :=
  let violates := fun address =>
    !ownedB address && decide (after.mem.get? address ≠ before.mem.get? address)
  min (memorySupportMinimumWhere before.mem violates (2 ^ 64))
    (memorySupportMinimumWhere after.mem violates (2 ^ 64))

/-- Finite mirror of `WritesOnlyWithin`, parameterized by an executable owned-region predicate. -/
def writesOnlyWithinB (ownedB : Nat → Bool) (before after : State) : Bool :=
  let check := fun address =>
    ownedB address || decide (after.mem.get? address = before.mem.get? address)
  memorySupportAll before.mem check && memorySupportAll after.mem check

/-- The finite support check is exactly the original universal write-frame predicate.

Both supports are checked. If an address is in neither, both map lookups are `none`, so the required
equality follows without inspecting an infinite complement. -/
theorem writesOnlyWithinB_iff {owned : Region} {ownedB : Nat → Bool}
    (howned : ∀ address, ownedB address = true ↔ owned address) (before after : State) :
    writesOnlyWithinB ownedB before after = true ↔ WritesOnlyWithin owned before after := by
  simp only [writesOnlyWithinB, Bool.and_eq_true, memorySupportAll_eq_true_iff]
  constructor
  · rintro ⟨hbefore, hafter⟩ address hnot
    have resolve (hrow :
        (ownedB address ||
          decide (after.mem.get? address = before.mem.get? address)) = true) :
        after.mem.get? address = before.mem.get? address := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hrow
      exact hrow.resolve_left (fun hb => hnot ((howned address).mp hb))
    by_cases hb : (before.mem.get? address).isSome = true
    · exact resolve (hbefore address hb)
    · by_cases ha : (after.mem.get? address).isSome = true
      · exact resolve (hafter address ha)
      · rw [Option.not_isSome_iff_eq_none.mp ha, Option.not_isSome_iff_eq_none.mp hb]
  · intro h
    constructor
    · intro address _
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      by_cases hown : owned address
      · exact Or.inl ((howned address).mpr hown)
      · exact Or.inr (h address hown)
    · intro address _
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      by_cases hown : owned address
      · exact Or.inl ((howned address).mpr hown)
      · exact Or.inr (h address hown)

/-- The executable region owned by a scalar reader: no result bytes, only the canonical stack. -/
def scalarReaderOwnedB (address : Nat) : Bool :=
  decide (Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackBase ≤ address ∧
    address < Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackBase +
      Entrypoints.ZesuDecodeRaw.canonicalRunnerLayout.stackSize)

theorem scalarReaderOwnedB_iff (address : Nat) :
    scalarReaderOwnedB address = true ↔
      (Region.union (allocatedRegion 0 0 0 0) canonicalEnvironment.stack) address := by
  simp [scalarReaderOwnedB, canonicalEnvironment, canonicalStack, Region.union, allocatedRegion,
    range, interval]

/-- Exact executable form of the scalar reader's ownership conjunct. -/
def scalarWritesOnlyWithinB (before after : State) : Bool :=
  writesOnlyWithinB scalarReaderOwnedB before after

theorem scalarWritesOnlyWithinB_iff (before after : State) :
    scalarWritesOnlyWithinB before after = true ↔
      canonicalEnvironment.WritesOnlyWithinOwnRecord 0 0 before after :=
  writesOnlyWithinB_iff scalarReaderOwnedB_iff before after

/-! ## `preReadAt`, mirrored in full

All five conjuncts. -/

def preReadAtB (env : DecoderEnvironment) (args : ReadAtArgs) (s : State) : Bool :=
  memoryBytesB s args.base args.bytes &&
    codeIntactB env.image s &&
    (s.regs.get? x10 == some (BitVec.ofNat 64 args.base)) &&
    (s.regs.get? x11 == some (BitVec.ofNat 64 args.bytes.size)) &&
    (s.regs.get? x12 == some (BitVec.ofNat 64 args.offset))

/-- **The mirror is implied by the predicate**, so `preReadAtB = false` refutes `preReadAt`. This is
the mechanical tie a Python oracle cannot have: adding a conjunct to `preReadAt` leaves this theorem
provable (the mirror only weakens), while *removing* the `x12` conjunct from the predicate would
leave the mirror asserting something the contract no longer says — which is why the mirror is read
only in the refuting direction. -/
theorem preReadAtB_of_preReadAt {env : DecoderEnvironment} {args : ReadAtArgs} {s : State}
    (h : preReadAt env args s) : preReadAtB env args s = true := by
  obtain ⟨hmem, hcode, h10, h11, h12⟩ := h
  simp only [preReadAtB, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨memoryBytesB_of_memoryBytes hmem,
    codeIntactB_of_fileBytesMatchMemory hcode⟩, h10⟩, h11⟩, h12⟩

/-- The first `preReadAt` conjunct that fails, by name, or `none` when all five hold. Kept beside the
mirror and checked against it by `preReadAt_failing_conjunct_agrees_with_mirror`, so the reported
name and the verdict cannot drift apart. -/
def preReadAtFailure? (env : DecoderEnvironment) (args : ReadAtArgs) (s : State) : Option String :=
  if !memoryBytesB s args.base args.bytes then some "preReadAt.MemoryBytes"
  else if !codeIntactB env.image s then some "preReadAt.CodeIntact"
  else if s.regs.get? x10 != some (BitVec.ofNat 64 args.base) then some "preReadAt.x10=base"
  else if s.regs.get? x11 != some (BitVec.ofNat 64 args.bytes.size) then
    some "preReadAt.x11=bytes.size"
  else if s.regs.get? x12 != some (BitVec.ofNat 64 args.offset) then some "preReadAt.x12=offset"
  else none

theorem preReadAt_failing_conjunct_agrees_with_mirror (env : DecoderEnvironment)
    (args : ReadAtArgs) (s : State) :
    (preReadAtFailure? env args s).isNone = preReadAtB env args s := by
  simp only [preReadAtFailure?, preReadAtB]
  by_cases h1 : memoryBytesB s args.base args.bytes <;>
    by_cases h2 : codeIntactB env.image s <;>
    by_cases h3 : s.regs.get? x10 = some (BitVec.ofNat 64 args.base) <;>
    by_cases h4 : s.regs.get? x11 = some (BitVec.ofNat 64 args.bytes.size) <;>
    by_cases h5 : s.regs.get? x12 = some (BitVec.ofNat 64 args.offset) <;>
    simp_all

/-! ## `LeafFrame`, mirrored, with the record split off

`LeafFrame env base bytes recordBase recordSize` expands to `MemoryBytes after ∧ CodeIntact after ∧
NoAllocation ∧ WritesOnlyWithinOwnRecord recordBase recordSize`. **Only the last conjunct mentions
the record.** Splitting the first three out is what lets a row whose record is not pinned still be
decided: `leafFrameSharedB` is implied by `LeafFrame` at *every* record, so its refutation refutes
the postcondition whatever `resultBase` the caller really passed.

Every read-family postcondition — `postScalarRead`, `postBytesAt`, `postReadU256`, `postReadArray` —
opens with this same `LeafFrame`. The two whose record is `0 0` (`postScalarRead` and `postBytesAt`)
additionally get the exact ownership clause via `scalarWritesOnlyWithinB`. -/

/-- The three `LeafFrame` conjuncts that do not mention the result record. -/
def leafFrameSharedB (env : DecoderEnvironment) (base : Nat) (bytes : ByteArray)
    (before after : State) : Bool :=
  memoryBytesB after base bytes && codeIntactB env.image after && noAllocationB before after

/-- **Implied by `LeafFrame` at every record.** `recordBase`/`recordSize` are universally quantified
here, which is exactly what makes this mirror sound to run on a `readU256`/`readArray` row whose
`resultBase` Row A does not pin: whatever the real record was, a `false` here refutes the
postcondition. -/
theorem leafFrameSharedB_of_leafFrame {base : Nat} {bytes : ByteArray}
    {recordBase recordSize : Nat} {before after : State}
    (h : LeafFrame canonicalEnvironment base bytes recordBase recordSize before after) :
    leafFrameSharedB canonicalEnvironment base bytes before after = true := by
  obtain ⟨hmem, hcode, hnoalloc, _⟩ := h
  simp only [leafFrameSharedB, Bool.and_eq_true]
  exact ⟨⟨memoryBytesB_of_memoryBytes hmem, codeIntactB_of_fileBytesMatchMemory hcode⟩,
    noAllocationB_of_noAllocation hnoalloc⟩

/-- The first record-independent `LeafFrame` conjunct that fails, by name. -/
def leafFrameSharedFailure? (env : DecoderEnvironment) (base : Nat) (bytes : ByteArray)
    (before after : State) : Option String :=
  if !memoryBytesB after base bytes then some "LeafFrame.MemoryBytes(after)"
  else if !codeIntactB env.image after then some "LeafFrame.CodeIntact(after)"
  else if !noAllocationB before after then some "LeafFrame.NoAllocation"
  else none

theorem leafFrameShared_failing_conjunct_agrees_with_mirror (env : DecoderEnvironment)
    (base : Nat) (bytes : ByteArray) (before after : State) :
    (leafFrameSharedFailure? env base bytes before after).isNone =
      leafFrameSharedB env base bytes before after := by
  simp only [leafFrameSharedFailure?, leafFrameSharedB]
  by_cases h1 : memoryBytesB after base bytes <;>
    by_cases h2 : codeIntactB env.image after <;>
    by_cases h3 : noAllocationB before after <;> simp_all

/-- The full `LeafFrame` mirror at the record a leaf with no caller slot uses, `0 0`. -/
def leafFrameZeroRecordB (env : DecoderEnvironment) (base : Nat) (bytes : ByteArray)
    (before after : State) : Bool :=
  leafFrameSharedB env base bytes before after && scalarWritesOnlyWithinB before after

theorem leafFrameZeroRecordB_of_leafFrame {base : Nat} {bytes : ByteArray} {before after : State}
    (h : LeafFrame canonicalEnvironment base bytes 0 0 before after) :
    leafFrameZeroRecordB canonicalEnvironment base bytes before after = true := by
  simp only [leafFrameZeroRecordB, Bool.and_eq_true]
  exact ⟨leafFrameSharedB_of_leafFrame h,
    (scalarWritesOnlyWithinB_iff before after).mpr h.2.2.2⟩

/-- The first `LeafFrame … 0 0` conjunct that fails, by name. -/
def leafFrameZeroRecordFailure? (env : DecoderEnvironment) (base : Nat) (bytes : ByteArray)
    (before after : State) : Option String :=
  match leafFrameSharedFailure? env base bytes before after with
  | some clause => some clause
  | none =>
      if !scalarWritesOnlyWithinB before after then some "LeafFrame.WritesOnlyWithinOwnRecord"
      else none

theorem leafFrameZeroRecord_failing_conjunct_agrees_with_mirror (env : DecoderEnvironment)
    (base : Nat) (bytes : ByteArray) (before after : State) :
    (leafFrameZeroRecordFailure? env base bytes before after).isNone =
      leafFrameZeroRecordB env base bytes before after := by
  simp only [leafFrameZeroRecordFailure?, leafFrameZeroRecordB,
    ← leafFrameShared_failing_conjunct_agrees_with_mirror]
  cases leafFrameSharedFailure? env base bytes before after <;>
    by_cases h : scalarWritesOnlyWithinB before after <;> simp_all

/-! ## `postScalarRead`, mirrored in full

`scalarWritesOnlyWithinB` decides the ownership conjunct exactly, so the mirror below covers the full
scalar postcondition rather than a one-way projection. -/

def postScalarReadCheckedB (env : DecoderEnvironment) (args : ReadAtArgs) (width : Nat)
    (result : Except SszDecodeError Nat) (before after : State) : Bool :=
  leafFrameZeroRecordB env args.base args.bytes before after &&
    (match result with
     | .ok value => decide (value < 2 ^ width) &&
         (after.regs.get? x10 == some (BitVec.ofNat 64 value))
     | .error error => error == SszDecodeError.invalidSsz)

/-- **The executable mirror is implied by the real postcondition**, at the canonical environment.
Together with `scalarWritesOnlyWithinB_iff`, every expanded conjunct is evaluated. -/
theorem postScalarReadCheckedB_of_postScalarRead {args : ReadAtArgs} {width : Nat}
    {result : Except SszDecodeError Nat} {before after : State}
    (h : postScalarRead canonicalEnvironment args width result before after) :
    postScalarReadCheckedB canonicalEnvironment args width result before after = true := by
  obtain ⟨hframe, harm⟩ := h
  simp only [postScalarReadCheckedB, Bool.and_eq_true]
  refine ⟨leafFrameZeroRecordB_of_leafFrame hframe, ?_⟩
  cases result with
  | ok value =>
      obtain ⟨hlt, hx10⟩ := harm
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨hlt, hx10⟩
  | error error => simpa using harm

/-- The first checked `postScalarRead` conjunct that fails, by name. -/
def postScalarReadFailure? (env : DecoderEnvironment) (args : ReadAtArgs) (width : Nat)
    (result : Except SszDecodeError Nat) (before after : State) : Option String :=
  match leafFrameZeroRecordFailure? env args.base args.bytes before after with
  | some clause => some clause
  | none =>
      match result with
      | .ok value =>
          if !decide (value < 2 ^ width) then some "postScalarRead.value<2^width"
          else if after.regs.get? x10 != some (BitVec.ofNat 64 value) then
            some "postScalarRead.x10=value"
          else none
      | .error error => if error != SszDecodeError.invalidSsz then
          some "postScalarRead.error=invalidSsz" else none

/-- **The scalar failure-namer agrees with its Boolean mirror**, so the conjunct name printed in the
report cannot drift from the verdict. (This tie was missing before task 6a-v: `postScalarReadFailure?`
was maintained by hand alongside `postScalarReadCheckedB` with nothing forcing them to agree.) -/
theorem postScalarRead_failing_conjunct_agrees_with_mirror (env : DecoderEnvironment)
    (args : ReadAtArgs) (width : Nat) (result : Except SszDecodeError Nat) (before after : State) :
    (postScalarReadFailure? env args width result before after).isNone =
      postScalarReadCheckedB env args width result before after := by
  simp only [postScalarReadFailure?, postScalarReadCheckedB,
    ← leafFrameZeroRecord_failing_conjunct_agrees_with_mirror]
  cases leafFrameZeroRecordFailure? env args.base args.bytes before after with
  | some clause => simp
  | none =>
      cases result with
      | ok value =>
          by_cases h1 : value < 2 ^ width <;>
            by_cases h2 : after.regs.get? x10 = some (BitVec.ofNat 64 value) <;> simp_all
      | error error => by_cases h : error = SszDecodeError.invalidSsz <;> simp_all

/-! ## `postBytesAt`, mirrored in full

`postBytesAt`'s frame is `LeafFrame … 0 0` — **the same record `postScalarRead` uses**. `bytesAt`
returns a borrowed sub-slice, so it has no result slot and therefore no `resultBase`; the only
argument it needs beyond `ReadAtArgs` is the runtime `len`, and Row A *does* bind that
(`lenBindingRow?`). The pre-6a-v harness reported these rows as needing "a resultBase Row A does not
pin", which was simply the wrong reason. -/

def postBytesAtCheckedB (env : DecoderEnvironment) (args : BytesAtArgs)
    (result : Except SszDecodeError ByteArray) (before after : State) : Bool :=
  leafFrameZeroRecordB env args.base args.bytes before after &&
    (match result with
     | .ok _ => (after.regs.get? x10 == some (BitVec.ofNat 64 (args.base + args.offset))) &&
         (after.regs.get? x11 == some (BitVec.ofNat 64 args.length))
     | .error error => error == SszDecodeError.invalidSsz)

/-- **The executable mirror is implied by the real postcondition**, at the canonical environment.
Every expanded `postBytesAt` conjunct is evaluated: the four `LeafFrame … 0 0` clauses and both
result-register clauses. -/
theorem postBytesAtCheckedB_of_postBytesAt {args : BytesAtArgs}
    {result : Except SszDecodeError ByteArray} {before after : State}
    (h : postBytesAt canonicalEnvironment args result before after) :
    postBytesAtCheckedB canonicalEnvironment args result before after = true := by
  obtain ⟨hframe, harm⟩ := h
  simp only [postBytesAtCheckedB, Bool.and_eq_true]
  refine ⟨leafFrameZeroRecordB_of_leafFrame hframe, ?_⟩
  cases result with
  | ok slice =>
      obtain ⟨hx10, hx11⟩ := harm
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hx10, hx11⟩
  | error error => simpa using harm

/-- The first checked `postBytesAt` conjunct that fails, by name. -/
def postBytesAtFailure? (env : DecoderEnvironment) (args : BytesAtArgs)
    (result : Except SszDecodeError ByteArray) (before after : State) : Option String :=
  match leafFrameZeroRecordFailure? env args.base args.bytes before after with
  | some clause => some clause
  | none =>
      match result with
      | .ok _ =>
          if after.regs.get? x10 != some (BitVec.ofNat 64 (args.base + args.offset)) then
            some "postBytesAt.x10=base+offset"
          else if after.regs.get? x11 != some (BitVec.ofNat 64 args.length) then
            some "postBytesAt.x11=length"
          else none
      | .error error => if error != SszDecodeError.invalidSsz then
          some "postBytesAt.error=invalidSsz" else none

theorem postBytesAt_failing_conjunct_agrees_with_mirror (env : DecoderEnvironment)
    (args : BytesAtArgs) (result : Except SszDecodeError ByteArray) (before after : State) :
    (postBytesAtFailure? env args result before after).isNone =
      postBytesAtCheckedB env args result before after := by
  simp only [postBytesAtFailure?, postBytesAtCheckedB,
    ← leafFrameZeroRecord_failing_conjunct_agrees_with_mirror]
  cases leafFrameZeroRecordFailure? env args.base args.bytes before after with
  | some clause => simp
  | none =>
      cases result with
      | ok slice =>
          by_cases h1 :
              after.regs.get? x10 = some (BitVec.ofNat 64 (args.base + args.offset)) <;>
            by_cases h2 : after.regs.get? x11 = some (BitVec.ofNat 64 args.length) <;> simp_all
      | error error => by_cases h : error = SszDecodeError.invalidSsz <;> simp_all

/-! ## Reading a register and a Row A binding out of a captured state -/

/-- The value of integer register `number` as a `Nat`, executably. Mirrors `RegisterValueRep`'s
dispatch on the same numbering. -/
def registerValue? (s : State) (number : Nat) : Option (BitVec 64) :=
  match number with
  | 1 => s.regs.get? x1 | 2 => s.regs.get? x2 | 3 => s.regs.get? x3 | 4 => s.regs.get? x4
  | 5 => s.regs.get? x5 | 6 => s.regs.get? x6 | 7 => s.regs.get? x7 | 8 => s.regs.get? x8
  | 9 => s.regs.get? x9 | 10 => s.regs.get? x10 | 11 => s.regs.get? x11 | 12 => s.regs.get? x12
  | 13 => s.regs.get? x13 | 14 => s.regs.get? x14 | 15 => s.regs.get? x15 | 16 => s.regs.get? x16
  | 17 => s.regs.get? x17 | 18 => s.regs.get? x18 | 19 => s.regs.get? x19 | 20 => s.regs.get? x20
  | 21 => s.regs.get? x21 | 22 => s.regs.get? x22 | 23 => s.regs.get? x23 | 24 => s.regs.get? x24
  | 25 => s.regs.get? x25 | 26 => s.regs.get? x26 | 27 => s.regs.get? x27 | 28 => s.regs.get? x28
  | 29 => s.regs.get? x29 | 30 => s.regs.get? x30 | 31 => s.regs.get? x31
  | _ => some (0 : BitVec 64)

/-- The value a Row A binding row denotes at a state, or `none` when the kind resolves to no value
here. Follows `BindingInventory.bindingRowHolds` case for case; kinds it cannot evaluate return
`none` and become an explicit gap rather than a guess. -/
def bindingValue? (row : Nat × String × String × Int × Int) (s : State) : Option Nat :=
  let (_, _, kind, registerOrAddress, offsetOrValue) := row
  if kind = "const" then some offsetOrValue.toNat
  else if kind = "reg" then (registerValue? s registerOrAddress.toNat).map BitVec.toNat
  else if kind = "bregValue" then
    (registerValue? s registerOrAddress.toNat).map fun base =>
      Elfling.addSignedOffset base.toNat offsetOrValue
  else if kind = "addrValue" then some registerOrAddress.toNat
  else if kind = "addr" then observeWord64? s registerOrAddress.toNat
  else if kind = "breg" ∨ kind = "fbreg" then
    match registerValue? s registerOrAddress.toNat with
    | some base => observeWord64? s (Elfling.addSignedOffset base.toNat offsetOrValue)
    | none => none
  else if kind = "derived" then
    (registerValue? s registerOrAddress.toNat).map fun base => base.toNat + offsetOrValue.toNat
  else none

/-- Row A's `offset` binding row for instance `index`, if it declares one. -/
def offsetBindingRow? (index : Nat) :
    Option (Nat × String × String × Int × Int) :=
  Elfling.GeneratedBindings.bindings.find? fun r => r.1 == index && r.2.1 == "offset"

/-- Row A's `len` binding row for instance `index` (`bytesAt` only). -/
def lenBindingRow? (index : Nat) : Option (Nat × String × String × Int × Int) :=
  Elfling.GeneratedBindings.bindings.find? fun r => r.1 == index && r.2.1 == "len"

/-- **Row A declares no `base` and no `bytes.size` binding anywhere in the read family.** This is why
those two arguments are witness-constructed rather than independently supplied, and it is a
contract-interface gap rather than a harness gap: nothing in the artifact pins them. -/
theorem read_family_declares_no_base_or_size_binding :
    (Elfling.GeneratedBindings.bindings.filter fun r =>
      r.2.1 == "data" || r.2.1 == "base" || r.2.1 == "bytes" && r.2.2.1 != "reg").length = 0 := by
  native_decide

/-! ## The instrumented run

The same Sail machine `RunnerExecution` drives, with one addition: before each retirement the pc is
looked up in a boundary index, and the state is snapshotted when it is a declared entry or exit.
Only the FIRST entry of each instance and the first declared exit strictly after it are kept, which
is what makes the capture bounded. -/

/-- What the run recorded for one instance. Every field is `Option`: absent means the run never got
there, which is a gap. -/
structure InstanceCapture where
  entryStep : Option Nat
  entryState : Option State
  exitStep : Option Nat
  exitState : Option State
  exitPc : Option Nat

instance : Inhabited InstanceCapture := ⟨⟨none, none, none, none, none⟩⟩

/-- pc → the instances declaring it their entry. -/
def entryIndex : Std.HashMap Nat (Array Nat) :=
  generatedProgram.functionInstances.zipIdx.foldl (fun m (o, i) =>
    m.insert o.entryPc ((m.getD o.entryPc #[]).push i)) ∅

/-- pc → the instances declaring it an exit. -/
def exitIndex : Std.HashMap Nat (Array Nat) :=
  generatedProgram.functionInstances.zipIdx.foldl (fun m (o, i) =>
    o.exitPcs.foldl (fun m pc => m.insert pc ((m.getD pc #[]).push i)) m) ∅

def emptyCaptures : Array InstanceCapture :=
  Array.replicate generatedProgram.functionInstances.size default

/-- One instrumented step loop. Identical to `runToOutcome` except for the snapshot. -/
def stepCapturing (sentinel : BitVec 64) :
    Nat → Nat → Array InstanceCapture → SailM (SentinelOutcome × Array InstanceCapture)
  | 0, _, caps => pure (.exhausted, caps)
  | fuel + 1, steps, caps => do
    let pc ← readReg PC
    if pc == sentinel then pure (.reached steps, caps)
    else
      let address := pc.toNat
      let entries := entryIndex.getD address #[]
      let exits := exitIndex.getD address #[]
      let caps ←
        if entries.isEmpty && exits.isEmpty then pure caps
        else do
          let s ← EStateM.get
          let caps := entries.foldl (fun (caps : Array InstanceCapture) i =>
            let c := caps[i]!
            if c.entryStep.isNone then
              caps.set! i { c with entryStep := some steps, entryState := some s }
            else caps) caps
          let caps := exits.foldl (fun (caps : Array InstanceCapture) i =>
            let c := caps[i]!
            match c.entryStep, c.exitStep with
            | some entered, none =>
                if entered < steps then
                  caps.set! i { c with exitStep := some steps, exitState := some s,
                                       exitPc := some address }
                else caps
            | _, _ => caps) caps
          pure caps
      let waiting ← try_step steps false
      if waiting then pure (.trapped, caps)
      else stepCapturing sentinel fuel (steps + 1) caps

def captureRun (input : ByteArray) : SailM (SentinelOutcome × Array InstanceCapture) := do
  buildZesuEntryState input
  stepCapturing sentinelWord (zesuFuel input.size) 0 emptyCaptures

/-- The corpus case the capture runs on: the rich accepted fixture, the analogue of the trace
tooling's `present` arm. -/
def captureCaseId : String := "valid-v4-rich-raw"

def captureInput : ByteArray :=
  match GeneratedCorpus.corpus.find? fun c => c.1 == captureCaseId with
  | some c => BinaryFv.SSZ.Zesu.Validation.hexToBytes c.2.2
  | none => ByteArray.empty

/-- The capture, as a value. A Sail fault yields `.trapped` with whatever was captured before it,
which the report shows as gaps rather than as passes. -/
def capture : SentinelOutcome × Array InstanceCapture :=
  match (captureRun captureInput).run initialState with
  | .ok result _ => result
  | .error _ _ => (.trapped, emptyCaptures)

def captureOutcome : SentinelOutcome := capture.1
def captures : Array InstanceCapture := capture.2

/-! ## Reconstructing the read-family arguments -/

/-- The read-family tags, as the manifest spells them. An unrecognised tag is a gap, never a pass, so
a catalog rename makes instances drop out of the checked set rather than silently pass. -/
inductive ReadFamily where
  | readU32 | readU64 | readOffset | readU256 | bytesAt | readArray
deriving DecidableEq, Repr, Inhabited

def readFamily? (tagName : String) : Option ReadFamily :=
  if tagName = "readU32" then some .readU32
  else if tagName = "readU64" then some .readU64
  else if tagName = "readOffset" then some .readOffset
  else if tagName = "readU256" then some .readU256
  else if tagName = "bytesAt" then some .bytesAt
  else if tagName = "readArray" then some .readArray
  else none

/-- The largest borrowed slice the harness will materialise out of memory. A larger `x11` is reported
as a gap: reading an arbitrary register-sized window would be a denial of service, not a check. -/
def maximumSliceBytes : Nat := 8192

/-- Read `size` bytes of machine memory at `base`, or `none` if any byte is unmapped or the window is
oversized. -/
def readSlice? (s : State) (base size : Nat) : Option ByteArray :=
  if size > maximumSliceBytes then none
  else
    (List.range size).foldl (fun acc index =>
      match acc, s.mem.get? (base + index) with
      | some bytes, some byte => some (bytes.push (UInt8.ofNat byte.toNat))
      | _, _ => none) (some ByteArray.empty)

/-- The reconstructed `ReadAtArgs` for an instance at its captured entry state: `offset` from Row A,
`base`/`bytes` witness-constructed from `x10`/`x11` (see the module docstring). -/
def readAtArgs? (index : Nat) (s : State) : Option ReadAtArgs := do
  let row ← offsetBindingRow? index
  let offset ← bindingValue? row s
  let base ← (registerValue? s 10).map BitVec.toNat
  let size ← (registerValue? s 11).map BitVec.toNat
  let bytes ← readSlice? s base size
  pure { base := base, bytes := bytes, offset := offset }

/-- The reconstructed `BytesAtArgs`: the read-at args plus Row A's `len` binding, evaluated at the
same captured entry state. Unlike `readU256`/`readArray`'s `resultBase`, this argument **is** pinned
by the generated binding artifact, which is why `bytesAt`'s `post` needs no witness beyond the ones
`preReadAt` already needed. -/
def bytesAtArgs? (index : Nat) (s : State) : Option BytesAtArgs := do
  let readArgs ← readAtArgs? index s
  let row ← lenBindingRow? index
  let length ← bindingValue? row s
  pure { toReadAtArgs := readArgs, length := length }

/-- The `readArray` width this instance instantiates, from the contract's own dispatch on the
function identity — not a copy of the width table. -/
def readArrayWidth (o : FunctionInstance) : Nat := readArrayWidthOf o.id.function

/-- An arbitrary `ReadAtArgs`, used only where the quantity being computed is proved not to depend on
it. -/
def dummyArgs : ReadAtArgs := { base := 0, bytes := ByteArray.empty, offset := 0 }

/-- The contract's own `stepBound` for the read family, read off the real `FunctionContract` records
rather than restated. Evaluated at `dummyArgs`, which is sound **because the bound does not depend on
the arguments** — proved immediately below rather than assumed, since that is exactly what makes
column 5 answerable for the instances whose arguments could not be reconstructed. -/
def readFamilyStepBound (family : ReadFamily) (o : FunctionInstance) : Nat :=
  match family with
  | .readU32 => (contractReadU32 canonicalEnvironment).stepBound dummyArgs
  | .readU64 => (contractReadU64 canonicalEnvironment).stepBound dummyArgs
  | .readOffset => (contractReadOffset canonicalEnvironment).stepBound dummyArgs
  | .readU256 => (contractReadU256 canonicalEnvironment).stepBound
      { toReadAtArgs := dummyArgs, resultBase := 0 }
  | .bytesAt => (contractBytesAt canonicalEnvironment).stepBound
      { toReadAtArgs := dummyArgs, length := 0 }
  | .readArray => (contractReadArray canonicalEnvironment (readArrayWidth o)).stepBound
      { toReadAtArgs := dummyArgs, resultBase := 0 }

/-- **Every read-family `stepBound` is a constant function of its arguments**, so evaluating it at
`dummyArgs` computes the same number the real obligation would use, whatever the caller passed. -/
theorem read_family_stepBound_ignores_args (env : DecoderEnvironment) (length : Nat)
    (a b : ReadAtArgs) (u v : ReadU256Args) (p q : ReadArrayArgs) (m n : BytesAtArgs) :
    (contractReadU32 env).stepBound a = (contractReadU32 env).stepBound b ∧
      (contractReadU64 env).stepBound a = (contractReadU64 env).stepBound b ∧
      (contractReadOffset env).stepBound a = (contractReadOffset env).stepBound b ∧
      (contractReadU256 env).stepBound u = (contractReadU256 env).stepBound v ∧
      (contractBytesAt env).stepBound m = (contractBytesAt env).stepBound n ∧
      (contractReadArray env length).stepBound p = (contractReadArray env length).stepBound q :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The three scalar readers, whose `post` is `postScalarRead` at a known width.

The other three members have different post shapes, and they are **not** alike. `postBytesAt` needs
only the runtime `len`, which Row A binds, so it is fully checked (`postBytesAtFailure?`).
`postReadU256` and `postReadArray` write to a caller slot whose `resultBase` Row A does not pin, so
for those two only the record-independent `LeafFrame` conjuncts are decidable and the rest is an
explicitly named gap. -/
def scalarWidth? (family : ReadFamily) : Option Nat :=
  match family with
  | .readU32 => some 32
  | .readU64 => some 64
  | .readOffset => some 32
  | _ => none

/-- The scalar reader's meaning at the reconstructed args, taken from the real contract. -/
def scalarMeaning (family : ReadFamily) (args : ReadAtArgs) :
    Option (Except SszDecodeError Nat) :=
  match family with
  | .readU32 => some ((contractReadU32 canonicalEnvironment).meaning args)
  | .readU64 => some ((contractReadU64 canonicalEnvironment).meaning args)
  | .readOffset => some ((contractReadOffset canonicalEnvironment).meaning args)
  | _ => none

/-! ## Per-instance rows -/

structure GroundTruthRow where
  index : Nat
  routineTag : String
  entryPc : Nat
  /-- Q1: the machine entered at the declared entry pc. -/
  entered : Verdict
  /-- Q2: `preReadAt` at the reconstructed args. -/
  pre : Verdict
  /-- Q3: the run left at a declared exit, and the entry is not itself an exit. -/
  exited : Verdict
  /-- Q4: the full `postScalarRead` at the captured exit state. -/
  post : Verdict
  /-- Q5: retired steps within the contract's `stepBound`. -/
  steps : Verdict
  realSteps : Option Nat
  stepBound : Option Nat
  exitPc : Option Nat
  /-- `x10`, `x11`, `x12` at the captured entry state — the three registers `preReadAt` constrains,
  printed so the verdict can be read rather than taken on trust. -/
  entryX10 : Option Nat
  entryX11 : Option Nat
  entryX12 : Option Nat
  /-- The `offset` argument as ROW A places it, evaluated at the same state. `preReadAt` says this
  must equal `x12`. -/
  rowAOffset : Option Nat
deriving Repr, Inhabited

private def tagOf (index : Nat) : String :=
  (generatedManifest[index]?).elim "?" (·.routineTag)

def groundTruthRow (index : Nat) (o : FunctionInstance) : GroundTruthRow :=
  let tag := tagOf index
  let capture := captures[index]!
  let family? := readFamily? tag
  let entered : Verdict :=
    match capture.entryState with
    | some _ => .ok
    | none => .gap "never entered on this arm"
  let exited : Verdict :=
    if o.exitPcs.contains o.entryPc then .violated "entryPc is itself a declared exit"
    else match capture.entryState, capture.exitPc with
      | none, _ => .gap "never entered on this arm"
      | some _, none => .gap "entered but no declared exit reached before the sentinel"
      | some _, some _ => .ok
  let args? := capture.entryState.bind (readAtArgs? index)
  let rowAOffset : Option Nat := do
    let s ← capture.entryState
    let row ← offsetBindingRow? index
    bindingValue? row s
  let pre : Verdict :=
    match family?, capture.entryState with
    | none, _ => .gap ("tag " ++ tag ++ " is outside the checked read family")
    | some _, none => .gap "never entered on this arm"
    | some _, some s =>
      match offsetBindingRow? index with
      | none => .gap "Row A declares no offset binding for this instance"
      | some row =>
        match bindingValue? row s with
        | none => .gap ("Row A offset binding kind " ++ row.2.2.1 ++ " is not evaluable here")
        | some offset =>
          -- The `x12` conjunct is decided FIRST and on its own. `offset` is fixed by Row A, so this
          -- clause is refuted independently of `base`/`bytes`: no choice of the two unpinned
          -- arguments can rescue it. Only when it holds does the harness fall through to the
          -- remaining conjuncts, which need a slice it may not be able to materialise.
          if s.regs.get? x12 != some (BitVec.ofNat 64 offset) then
            .violated "preReadAt.x12=offset"
          else
            match args? with
            | none => .gap ("x12 agrees with Row A; the other conjuncts need the borrowed slice, and"
                ++ " x11 is not a materialisable length here")
            | some args =>
              match preReadAtFailure? canonicalEnvironment args s with
              | some clause => .violated clause
              | none => .ok
  let realSteps : Option Nat := do
    let entryStep ← capture.entryStep
    let exitStep ← capture.exitStep
    pure (exitStep - entryStep)
  let stepBound : Option Nat := family?.map fun family => readFamilyStepBound family o
  let post : Verdict :=
    match family?, capture.entryState, capture.exitState, args? with
    | none, _, _, _ => .gap ("tag " ++ tag ++ " is outside the checked read family")
    | some _, none, _, _ => .gap "never entered on this arm"
    | some _, _, none, _ => .gap "no declared exit state captured"
    | some _, _, _, none => .gap "arguments not reconstructible"
    | some family, some before, some after, some args =>
      match scalarWidth? family, scalarMeaning family args with
      | some width, some result =>
        match postScalarReadFailure? canonicalEnvironment args width result before after with
        | some clause => .violated clause
        | none =>
          -- A passing `.error` arm is NOT a pass. `postScalarRead`'s failure branch asks only that
          -- the error be `invalidSsz`, which every scalar reader's meaning satisfies by
          -- construction, so it carries no information about the machine at all.
          match result with
          | .error _ => .gap "meaning errors at the witness args; postScalarRead's error arm is then               trivially satisfied and says nothing about the run"
          | .ok _ => .ok
      | _, _ =>
        -- Not a scalar reader. The shared `LeafFrame` conjuncts are the SAME three conjuncts in
        -- every read-family post shape and depend on no unpinned argument, so they are decided
        -- BEFORE any shape-specific dispatch. Before task 6a-v this whole branch was a gap.
        match family with
        | .bytesAt =>
          -- `postBytesAt`'s record is `0 0`, so its first four conjuncts are exactly the scalar
          -- reader's. The only extra argument is `len`, which Row A binds.
          match capture.entryState.bind (bytesAtArgs? index) with
          | none =>
            match leafFrameSharedFailure? canonicalEnvironment args.base args.bytes before after with
            | some clause => .violated clause
            | none => .gap ("LeafFrame.MemoryBytes/CodeIntact/NoAllocation hold; Row A binds no"
                ++ " evaluable len, leaving LeafFrame.WritesOnlyWithinOwnRecord and"
                ++ " postBytesAt.x10=base+offset / postBytesAt.x11=length unevaluated")
          | some bytesArgs =>
            let result := (contractBytesAt canonicalEnvironment).meaning bytesArgs
            match postBytesAtFailure? canonicalEnvironment bytesArgs result before after with
            | some clause => .violated clause
            | none =>
              match result with
              | .error _ => .gap "meaning errors at the witness args; postBytesAt's error arm is then               trivially satisfied and says nothing about the run"
              | .ok _ => .ok
        | _ =>
          -- `readU256` / `readArray`: the result slot's `resultBase` is unpinned, so the ownership
          -- clause and the result clause are both unevaluated. Named, not hidden.
          match leafFrameSharedFailure? canonicalEnvironment args.base args.bytes before after with
          | some clause => .violated clause
          | none => .gap ("LeafFrame.MemoryBytes/CodeIntact/NoAllocation hold for " ++ tag
              ++ "; LeafFrame.WritesOnlyWithinOwnRecord(resultBase,width) and the result-slot"
              ++ " clause need a resultBase Row A does not pin")
  let steps : Verdict :=
    match realSteps, stepBound with
    | some real, some bound => if real ≤ bound then .ok else .violated "used > stepBound args"
    | none, _ => .gap "no entry/exit pair captured"
    | _, none => .gap "no stepBound (tag outside the checked read family)"
  { index := index, routineTag := tag, entryPc := o.entryPc
    entered := entered, pre := pre, exited := exited, post := post, steps := steps
    realSteps := realSteps, stepBound := stepBound, exitPc := capture.exitPc
    entryX10 := capture.entryState.bind (fun s => (registerValue? s 10).map BitVec.toNat)
    entryX11 := capture.entryState.bind (fun s => (registerValue? s 11).map BitVec.toNat)
    entryX12 := capture.entryState.bind (fun s => (registerValue? s 12).map BitVec.toNat)
    rowAOffset := rowAOffset }

def groundTruthRows : Array GroundTruthRow :=
  generatedProgram.functionInstances.zipIdx.map fun (o, i) => groundTruthRow i o

/-! ## Rendering -/

private def pad (n : Nat) (s : String) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- `pre`'s pass is rendered distinctly, because the arguments it passes at are witness-constructed
on three of five conjuncts. It is not a statement that `pre` holds at the caller's arguments. -/
private def renderPre : Verdict → String
  | .ok => "ok@witness-args"
  | v => v.render

/-- The scalar `post` mirror evaluates every expanded conjunct. -/
private def renderPost : Verdict → String
  | v => v.render

def GroundTruthRow.render (r : GroundTruthRow) : String :=
  String.intercalate " | "
    [ pad 3 (toString r.index)
    , pad 22 r.routineTag
    , pad 6 (toString r.entryPc)
    , pad 34 r.entered.render
    , pad 46 (renderPre r.pre)
    , pad 44 r.exited.render
    , pad 50 (renderPost r.post)
    , pad 30 r.steps.render
    , pad 6 (r.realSteps.elim "-" toString)
    , pad 6 (r.stepBound.elim "-" toString)
    , pad 21 (r.entryX10.elim "-" toString)
    , pad 21 (r.entryX11.elim "-" toString)
    , pad 21 (r.entryX12.elim "-" toString)
    , pad 12 (r.rowAOffset.elim "-" toString) ]

def header : String :=
  String.intercalate " | "
    [ pad 3 "idx", pad 22 "routineTag", pad 6 "entry", pad 34 "1 entered"
    , pad 46 "2 pre", pad 44 "3 exited", pad 50 "4 post", pad 30 "5 steps"
    , pad 6 "real", pad 6 "bound"
    , pad 21 "x10@entry", pad 21 "x11@entry", pad 21 "x12@entry", pad 12 "RowA offset" ]

private def tally (f : GroundTruthRow → Verdict) : String :=
  toString (groundTruthRows.filter fun r => (f r).isOk).size ++ " / " ++
    toString (groundTruthRows.filter fun r => (f r).isViolated).size ++ " / " ++
    toString (groundTruthRows.filter fun r =>
      !(f r).isOk && !(f r).isViolated).size

def report : String :=
  String.intercalate "\n"
    ([ "## 2. Contract ground truth — real states from the Sail model"
     , ""
     , "Run: corpus case `" ++ captureCaseId ++ "`, " ++ toString captureInput.size
         ++ " input bytes, outcome " ++ (match captureOutcome with
            | .reached n => "reached the sentinel after " ++ toString n ++ " retired steps"
            | .trapped => "TRAPPED"
            | .exhausted => "fuel EXHAUSTED")
     , ""
     , "Legend. `ok@witness-args` — `preReadAt` evaluated true, but `base`/`bytes` were taken from"
     , "the state (`x10`, memory at `[x10, x10+x11)`), so three of its five conjuncts are true by"
     , "construction. Only a FAIL is conclusive. A post `ok` covers all six expanded"
     , "`postScalarRead` / `postBytesAt` conjuncts, including the exact finite-support ownership"
     , "check. A post FAIL naming a `LeafFrame.*` clause holds at every result record, so it does"
     , "not depend on a `resultBase` the artifact leaves unpinned. A `gap` is never a pass, and"
     , "each post gap now names the specific conjuncts left unevaluated."
     , ""
     , "```"
     , header
     , String.ofList (List.replicate 340 '-') ] ++
     (groundTruthRows.map GroundTruthRow.render).toList ++
     [ "```"
     , ""
     , "totals (ok / violated / gap):"
     , "```"
     , "  1 entered : " ++ tally (·.entered)
     , "  2 pre     : " ++ tally (·.pre)
     , "  3 exited  : " ++ tally (·.exited)
     , "  4 post    : " ++ tally (·.post)
     , "  5 steps   : " ++ tally (·.steps)
     , "```"
     , "" ])

/-! ## Kernel-checked findings

Exact values again, not `= true` goals. -/

/-- The capture actually happened: the instrumented run reached the sentinel. If this were `trapped`
or `exhausted`, every row below would be a gap and the module would be reporting nothing. -/
theorem capture_reached_the_sentinel : (match captureOutcome with
    | .reached _ => true | _ => false) = true := by native_decide

/-- The five columns as (ok, violated) pairs over the 141 instances; the gap count is the remainder.

Read them with the legend in force. `pre`'s 2 passes are `ok@witness-args`, `post` has **no** pass at
all, and every column's gap count is instances the harness declined to decide. -/
theorem ground_truth_column_totals :
    [(groundTruthRows.filter fun r => r.entered.isOk).size,
     (groundTruthRows.filter fun r => r.entered.isViolated).size,
     (groundTruthRows.filter fun r => r.pre.isOk).size,
     (groundTruthRows.filter fun r => r.pre.isViolated).size,
     (groundTruthRows.filter fun r => r.exited.isOk).size,
     (groundTruthRows.filter fun r => r.exited.isViolated).size,
     (groundTruthRows.filter fun r => r.post.isOk).size,
     (groundTruthRows.filter fun r => r.post.isViolated).size,
     (groundTruthRows.filter fun r => r.steps.isOk).size,
     (groundTruthRows.filter fun r => r.steps.isViolated).size] =
      [135, 0, 2, 100, 103, 33, 0, 10, 104, 1] := by native_decide

/-- **Q1.** Six instances are never entered on this arm. Five are the statically dead allocator and
error paths; `hasExactErePrefix` is live only on the ERE-prefixed envelope, which this fixture is
not. Their every other column is a gap, never a pass. -/
theorem instances_never_entered :
    (groundTruthRows.filterMap fun r => if r.entered.isOk then none else some r.entryPc) =
      #[66448, 66624, 77872, 79712, 79744, 79756] := by native_decide

/-- **Q2 — the headline.** `preReadAt` demands the `offset` argument in `x12`. Evaluated at every
captured entry state against Row A's own binding for that parameter, it is **refuted at 100 of the
141 instances**, all on the same conjunct. This clause is decided *before* the two unpinned
arguments are witness-constructed, so the refutation does not depend on them: `offset` is fixed by
Row A, so no choice of `base`/`bytes` rescues it.

Only **two** instances pass — the `readOffset`/`readU32` pair at `0x12b78` — and even those pass
only `@witness-args`. -/
theorem pre_refutations_are_all_the_x12_clause :
    ((groundTruthRows.filter fun r => r.pre == Verdict.violated "preReadAt.x12=offset").size,
     (groundTruthRows.filterMap fun r => if r.pre.isOk then some r.entryPc else none)) =
      (100, #[76600, 76600]) := by native_decide

/-- **Q4.** Ten posts are refuted, none passes.

Five are the scalar readers: four `x10 = value` disagreements and index 49's exact frame violation.

Five are `bytesAt`, freed by task 6a-v with no new captured data at all — `postBytesAt`'s frame is
`LeafFrame … 0 0`, the same record the scalar readers use, and its only extra argument is the runtime
`len`, which Row A binds. They split two ways:

* **48, 50, 77** fail `LeafFrame.WritesOnlyWithinOwnRecord`, which needs no argument beyond the
  captured state pair. Index 48 shares `entryPc 0x11a28` with index 49, and
  `indices_48_and_49_are_one_piece_of_frame_evidence` pins that the capture hands them the same
  entry/exit steps and that both refute at the *same address* — so as **evidence** index 48's
  refutation is not a second observation, it is index 49's byte again. As **obligations** the two are
  distinct (different routine, different contract, different post shape), so the column count of 10
  is right even though the underlying machine evidence is 9 distinct observations. Indices 50 and 77
  are independent state pairs.
* **59, 89** fail `postBytesAt.x11=length`, the borrowed slice's returned length. Both reach that
  clause only because the four `LeafFrame` conjuncts *and* `postBytesAt.x10=base+offset` hold at
  them — so this refutation is a genuine single-clause disagreement, not a frame failure in disguise.

`readU256` and `readArray` are still undecided, but for a named reason and after a real evaluation:
`readU256_and_readArray_leave_only_the_record_clauses_open` shows the three record-independent
`LeafFrame` conjuncts hold on all five of their capturable rows. -/
theorem post_refutations_include_exact_frame_violation :
    (groundTruthRows.filterMap fun r =>
      if r.post.isViolated then some (r.index, r.routineTag, r.entryPc, r.post) else none) =
      #[(48, "bytesAt", 72232, .violated "LeafFrame.WritesOnlyWithinOwnRecord"),
        (49, "readU64", 72232, .violated "LeafFrame.WritesOnlyWithinOwnRecord"),
        (50, "bytesAt", 72332, .violated "LeafFrame.WritesOnlyWithinOwnRecord"),
        (59, "bytesAt", 73620, .violated "postBytesAt.x11=length"),
        (66, "readOffset", 73904, .violated "postScalarRead.x10=value"),
        (67, "readU32", 73904, .violated "postScalarRead.x10=value"),
        (68, "readOffset", 73952, .violated "postScalarRead.x10=value"),
        (69, "readU32", 73952, .violated "postScalarRead.x10=value"),
        (77, "bytesAt", 74472, .violated "LeafFrame.WritesOnlyWithinOwnRecord"),
        (89, "bytesAt", 75336, .violated "postBytesAt.x11=length")] := by
  native_decide

/-- **The restructure is not hiding a `readU256`/`readArray` refutation.** All five of their rows with
a capturable argument set are now *run* through the three record-independent `LeafFrame` conjuncts,
and all three hold at every one of them. So what keeps those rows undecided is exactly the missing
`resultBase` — `WritesOnlyWithinOwnRecord(resultBase, width)` and the result-slot clause — and
nothing else. A negative result, recorded as one. -/
theorem readU256_and_readArray_leave_only_the_record_clauses_open :
    ([44, 51, 60, 78, 90].map fun index =>
      (do
        let before ← captures[index]!.entryState
        let after ← captures[index]!.exitState
        let args ← readAtArgs? index before
        pure (leafFrameSharedFailure? canonicalEnvironment args.base args.bytes before after))) =
      [some none, some none, some none, some none, some none] := by native_decide

/-- Concrete address-level evidence for the newly visible frame failure. The two-step captured span
for index 49 starts with heap address `0x15040` absent and ends with byte `11` stored there. This is
the canonical heap's second allocation base, not the scalar reader's owned stack. Because index 49's
entry is itself a declared exit, this is evidence that the current generated stop boundary includes
a parent heap store—not yet evidence that the source `readU64` body itself performed the write. -/
def index49FrameViolation? :
    Option (Nat × Option (BitVec 8) × Option (BitVec 8) × Bool × Bool) := do
  let before ← captures[49]!.entryState
  let after ← captures[49]!.exitState
  let address := firstWriteFrameViolation scalarReaderOwnedB before after
  pure (address, before.mem.get? address, after.mem.get? address,
    scalarReaderOwnedB address,
    decide (BinaryFv.SSZ.Zesu.Elfling.canonicalHeapBase ≤ address ∧
      address < BinaryFv.SSZ.Zesu.Elfling.canonicalHeapLimit))

/-- Whether the capture handed indices 48 and 49 the same entry step, exit step and exit pc, plus the
least out-of-frame changed address each one refutes at. -/
def indices48And49FrameEvidence? : Option (Bool × Nat × Nat) := do
  let before48 ← captures[48]!.entryState
  let after48 ← captures[48]!.exitState
  let before49 ← captures[49]!.entryState
  let after49 ← captures[49]!.exitState
  pure (decide ((captures[48]!.entryStep, captures[48]!.exitStep, captures[48]!.exitPc) =
          (captures[49]!.entryStep, captures[49]!.exitStep, captures[49]!.exitPc)),
        firstWriteFrameViolation scalarReaderOwnedB before48 after48,
        firstWriteFrameViolation scalarReaderOwnedB before49 after49)

/-- **Indices 48 and 49 are two obligations but one observation.** The instrumented run gives them the
same entry step, the same exit step and the same exit pc, and their `WritesOnlyWithinOwnRecord`
refutations bottom out at the *same* address `86080` — the heap byte
`index49_frame_violation_is_heap_byte` already identifies. Reported so the pair is not read as two
independent confirmations of the frame violation. -/
theorem indices_48_and_49_are_one_piece_of_frame_evidence :
    indices48And49FrameEvidence? = some (true, 86080, 86080) := by native_decide

theorem index49_frame_violation_is_heap_byte :
    index49FrameViolation? = some (86080, none, some (BitVec.ofNat 8 11), false, true) := by
  native_decide

/-- **Q5.** One step bound is refuted by the real run: the `readArray` instance entered at `0x11fd8`
retires 233 steps between its entry and its first declared exit, against a `stepBound` of 160.

Two things are deliberately NOT claimed. The measured count is `exitStep - entryStep` on the machine,
so it includes every step retired inside anything called along the way — the callee-inclusive
quantity the contract's `used` means, unlike Row C's in-region count. And a `readArray` whose exit is
a TAIL CALL stops at the call instruction, so the callee's steps fall outside `used` by the trace
semantics, not by an omission here; that is why the byte-at-a-time `memcpy` (1794 retired steps, row
139) does not appear inside any `readArray`'s count. -/
theorem step_bound_refutation :
    (groundTruthRows.filterMap fun r =>
      if r.steps.isViolated then some (r.entryPc, r.realSteps, r.stepBound) else none) =
      #[(73688, some 233, some 160)] := by native_decide

/-! ### Anti-vacuity: both checks are shown flipping

`pre` is exhibited passing on the real artifact (2 rows), so its column is not a constant. `post`
passes nowhere, which is exactly the shape of a check that cannot pass — so it is exhibited flipping
under a mutation instead. -/

/-- Minimal states used to test both directions of the exact ownership evaluator. -/
def frameMutationBefore : State := default

def frameMutationOutside : State :=
  { frameMutationBefore with
    mem := frameMutationBefore.mem.insert 0 (BitVec.ofNat 8 1) }

def frameMutationInside : State :=
  { frameMutationBefore with
    mem := frameMutationBefore.mem.insert canonicalRunnerLayout.stackBase (BitVec.ofNat 8 1) }

/-- **The finite-support ownership check has teeth in both directions.** A new byte at address zero
is outside the scalar reader's owned stack and is rejected; the identical write at the canonical
stack base is accepted. The final two conjuncts transport those executable results through
`scalarWritesOnlyWithinB_iff`, so the mutation test probes the original universal predicate too. -/
theorem scalar_ownership_check_discriminates :
    scalarWritesOnlyWithinB frameMutationBefore frameMutationOutside = false ∧
      scalarWritesOnlyWithinB frameMutationBefore frameMutationInside = true ∧
      ¬ canonicalEnvironment.WritesOnlyWithinOwnRecord 0 0
          frameMutationBefore frameMutationOutside ∧
      canonicalEnvironment.WritesOnlyWithinOwnRecord 0 0
        frameMutationBefore frameMutationInside := by
  have hout :
      scalarWritesOnlyWithinB frameMutationBefore frameMutationOutside = false := by
    native_decide
  have hin :
      scalarWritesOnlyWithinB frameMutationBefore frameMutationInside = true := by
    native_decide
  refine ⟨hout, hin, ?_, (scalarWritesOnlyWithinB_iff _ _).mp hin⟩
  intro houtside
  have := (scalarWritesOnlyWithinB_iff _ _).mpr houtside
  simp_all

/-- The instance the two mutations are run on: the `readU32` at `0x12110` (index 66), whose entry and
exit states were both captured and whose borrowed slice the harness could materialise. -/
def sampleIndex : Nat := 66

/-- **The `x12` conjunct is what decides column 2, and it discriminates.** At the sample's captured
entry state, `preReadAtFailure?` reports `preReadAt.x12=offset` at Row A's offset (`4`) and reports
**no failure at all** once the offset is replaced by the value actually in `x12` (`12`). So the check
is neither constantly failing nor blind to the argument: it is measuring precisely the disagreement
between the contract's register discipline and Row A's binding. -/
theorem pre_check_flips_when_the_offset_is_taken_from_x12 :
    (do
      let entry ← captures[sampleIndex]!.entryState
      let args ← readAtArgs? sampleIndex entry
      pure (preReadAtFailure? canonicalEnvironment args entry,
            preReadAtFailure? canonicalEnvironment { args with offset := 12 } entry)) =
      some (some "preReadAt.x12=offset", none) := by native_decide

/-- The sample's captured exit state with the contract's demanded result written into `x10`. This is
a hand-built counterfactual, not a run: it exists only to show the `post` check can return `none`. -/
def sampleExitWithResultInX10? : Option State := do
  let entry ← captures[sampleIndex]!.entryState
  let exit ← captures[sampleIndex]!.exitState
  let args ← readAtArgs? sampleIndex entry
  match (contractReadU32 canonicalEnvironment).meaning args with
  | .ok value => pure { exit with regs := exit.regs.insert x10 (BitVec.ofNat 64 value) }
  | .error _ => none

set_option maxHeartbeats 1000000 in
/-- **The `post` check can return `none`; the machine is what makes it fail.** On the real exit state
the sample fails `postScalarRead.x10=value`; on the same state with the read value placed in `x10`
the same function reports no failure. The exact ownership mutation above separately tests the newly
visible fifth refutation, so both failure mechanisms have a positive and negative control. -/
theorem post_check_flips_when_the_result_is_placed_in_x10 :
    (do
      let entry ← captures[sampleIndex]!.entryState
      let exit ← captures[sampleIndex]!.exitState
      let patched ← sampleExitWithResultInX10?
      let args ← readAtArgs? sampleIndex entry
      let result := (contractReadU32 canonicalEnvironment).meaning args
      pure (postScalarReadFailure? canonicalEnvironment args 32 result entry exit,
            postScalarReadFailure? canonicalEnvironment args 32 result entry patched)) =
      some (some "postScalarRead.x10=value", none) := by native_decide

/-! ### Anti-vacuity for the clauses task 6a-v newly fires

Two new failure mechanisms reach a verdict for the first time, and each is exercised in both
directions here. -/

/-- The `bytesAt` instance the `postBytesAt` mutations run on: index 59 at `0x11f94`, whose result
arm is reached (its meaning is `.ok`) and which fails exactly one clause. -/
def bytesAtSampleIndex : Nat := 59

/-- What `postBytesAt` demands of the two result registers at the sample, beside what the machine
actually left in them. Printed as values so the refutation can be read rather than trusted:
`x10` is the clause that **holds**, `x11` the one that fails. -/
def bytesAtSampleResultRegisters? : Option (Nat × Nat × Nat × Nat) := do
  let entry ← captures[bytesAtSampleIndex]!.entryState
  let exit ← captures[bytesAtSampleIndex]!.exitState
  let args ← bytesAtArgs? bytesAtSampleIndex entry
  let realX10 ← (registerValue? exit 10).map BitVec.toNat
  let realX11 ← (registerValue? exit 11).map BitVec.toNat
  pure (args.base + args.offset, realX10, args.length, realX11)

/-- **Address-level evidence for the `postBytesAt` refutation, in both directions at once.** At index
59 the contract demands `x10 = base + offset = 0x2000000002e4` and the machine leaves exactly that —
so `postBytesAt.x10=base+offset` *holds*. It demands `x11 = len = 32`, Row A's `const` binding for
this call's `len`, and the machine leaves `724`: the length of the whole borrowed input slice, not of
the 32-byte sub-slice `bytesAt` was asked for. One clause of six disagrees, and the printed pair
shows which. -/
theorem bytesAt_sample_registers :
    bytesAtSampleResultRegisters? = some (35184372089572, 35184372089572, 32, 724) := by
  native_decide

/-- `postBytesAtFailure?` at the sample on three exit states: the real captured one; the same state
with the contract's demanded length written into `x11`; and that one with `x10` additionally moved
off the demanded pointer. The last two are hand-built counterfactuals, not runs. -/
def bytesAtSampleResultMutations? :
    Option (Option String × Option String × Option String) := do
  let entry ← captures[bytesAtSampleIndex]!.entryState
  let exit ← captures[bytesAtSampleIndex]!.exitState
  let args ← bytesAtArgs? bytesAtSampleIndex entry
  let result := (contractBytesAt canonicalEnvironment).meaning args
  let lengthFixed : State :=
    { exit with regs := exit.regs.insert x11 (BitVec.ofNat 64 args.length) }
  let pointerBroken : State :=
    { lengthFixed with regs := lengthFixed.regs.insert x10 (BitVec.ofNat 64 0) }
  pure (postBytesAtFailure? canonicalEnvironment args result entry exit,
        postBytesAtFailure? canonicalEnvironment args result entry lengthFixed,
        postBytesAtFailure? canonicalEnvironment args result entry pointerBroken)

set_option maxHeartbeats 1000000 in
/-- **`postBytesAt` can return `none`; the machine is what makes it fail — and its other result
clause is not dead either.** On the real captured exit state the sample fails
`postBytesAt.x11=length`. Writing Row A's `len` into `x11` and changing nothing else makes the *same*
function report no failure at all, which also witnesses that the other five conjuncts (the four
`LeafFrame` clauses and `postBytesAt.x10=base+offset`) already held. Zeroing `x10` on top of that
brings back `postBytesAt.x10=base+offset` — the clause that holds on every row the harness reaches,
and which would otherwise be a clause never observed failing. -/
theorem bytesAt_post_check_flips_on_each_result_clause :
    bytesAtSampleResultMutations? =
      some (some "postBytesAt.x11=length", none, some "postBytesAt.x10=base+offset") := by
  native_decide

/-- Flip one byte of a captured state, by adding one to whatever is there. `255 + 1` wraps to `0`, so
the mutated byte is never accidentally equal to the original and an absent byte becomes present. -/
def bumpByte (s : State) (address : Nat) : State :=
  let bumped : BitVec 8 := BitVec.ofNat 8 (((s.mem.get? address).getD 0).toNat + 1)
  { s with mem := s.mem.insert address bumped }

/-- The three record-independent `LeafFrame` conjuncts at the `bytesAt` sample: unmutated, and under
one targeted byte flip per conjunct. The addresses are disjoint — the borrowed slice's first byte,
the instance's own entry pc (in the file-backed text image), and the allocator cursor word — so each
mutation reaches its own clause instead of tripping an earlier one. -/
def leafFrameSharedMutations? : Option (Option String × Option String × Option String ×
    Option String) := do
  let entry ← captures[bytesAtSampleIndex]!.entryState
  let exit ← captures[bytesAtSampleIndex]!.exitState
  let args ← readAtArgs? bytesAtSampleIndex entry
  let check := fun (after : State) =>
    leafFrameSharedFailure? canonicalEnvironment args.base args.bytes entry after
  pure (check exit,
        check (bumpByte exit args.base),
        check (bumpByte exit 73620),
        check (bumpByte exit BinaryFv.SSZ.Zesu.Elfling.canonicalHeapPosAddr))

/-- **The record-independent `LeafFrame` gate has teeth, and this is the only place that is visible.**
It fires on none of the 141 captured rows — `readU256_and_readArray_leave_only_the_record_clauses_open`
pins that it genuinely ran and genuinely passed — so a check that is never seen to fail would
otherwise be indistinguishable from one that cannot. Each of its three conjuncts is therefore
exhibited firing under a one-byte mutation of a real captured exit state, with the unmutated state
reporting no failure. That is what licenses reading a `none` from this gate as information. -/
theorem leaf_frame_shared_gate_discriminates :
    leafFrameSharedMutations? = some (none,
      some "LeafFrame.MemoryBytes(after)",
      some "LeafFrame.CodeIntact(after)",
      some "LeafFrame.NoAllocation") := by native_decide

end BinaryFv.SSZ.Zesu.Validation.GroundTruth
