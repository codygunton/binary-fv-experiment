import BinaryFv.Zesu.Contracts.Containers

/-!
# The frame gap, exhibited

D4's open item asks whether *composed local summaries preserve code, input, stack/heap ownership and
required globals through the sentinel*. This module settles the memory half of that question for
sibling composition, and settles it in the negative — by construction rather than by argument.

**The question.** A parent container decodes its children in sequence and must then establish its own
`representation … after …` at the final state. Child A's postcondition establishes A's representation
at the state where A *finished*. Child B then runs. Can the parent conclude that A's representation
still holds at the state where B finished?

**The answer is no, and `sibling_clobber_permitted` below is the witness.** Two children's
postconditions are simultaneously satisfiable in a run where the second overwrites the first's result
byte, so `repA … afterB …` does not follow from `repA … afterA …` and B's contract. No amount of
reasoning about the *real* decoder closes this, because the gap is in what the contracts *say*.

## Why this is not an artifact of a degenerate witness

The obvious objection to a countermodel is that it exploits a degenerate instantiation. Stated
plainly, so it can be checked rather than trusted:

* The clobber does **not** depend on the environment. `env` is universally quantified, and the only
  hypotheses on it are that the clobbered addresses are not file-backed and not in `allocatorState`.
  Both are *forced*: a result buffer in the code image or in the allocator's own state would be a
  different bug, and the canonical environment satisfies both for arena addresses.
* The clobber does **not** depend on the representations being trivial. Both children carry a
  representation that genuinely pins a byte, and child B's representation *holds* at the final state.
  B is a well-behaved child that does its job; it simply also writes somewhere it was never forbidden
  to write.
* The clobber does **not** depend on the two result buffers colliding. `rA ≠ rB` is a hypothesis:
  B writes its own result to its own address *and* clobbers A's. Aliasing would be a stronger and
  less interesting statement — the contracts do not forbid that either, but this exhibit does not
  need it.
* `bytes := ByteArray.empty` is the one convenience, and it is bookkeeping only: `MemoryBytes` is a
  claim about the input region, the clobbered address lies outside it, and carrying a nonempty input
  through the construction changes nothing but the arithmetic.

What the exhibit *does* rely on is the one real fact: `postFixedContainer` constrained the input
region, the code image, `allocatorState`, and its own `resultBase`, and said nothing whatever about
any other address.

## The gap is CLOSED, and this module is now the record of it rather than the report of it

`sibling_clobber_permitted` was the settling fact for D4's composition item, and it settled it in the
negative, so `DECISIONS.md` (Row D) ruled the ownership clause into the `post*` predicates.
`postFixedContainer` now carries `env.WritesOnlyWithinOwnRecord args.resultBase recordSize`, and
against that predicate **the exhibit below no longer proves** — which is the regression signal the
plan named, fired as designed.

The exhibit is therefore restated, not weakened. `postFixedContainerHistorical` is the predicate as it
stood *before* the strengthening, spelled out here so the countermodel keeps its evidentiary value: it
records that the gap was real, and it is the thing a reader compares against to see what the clause
bought. Nothing in the tree uses the historical predicate for anything else — it is deliberately local
to this module and is not a contract.

`strengthened_post_is_satisfiable` below and `Ownership.fixed_container_cannot_clobber_sibling` are
the positive halves: the same situation is now impossible, and the strengthened postcondition is still
satisfiable by a sibling that genuinely writes, so the impossibility is not an artefact of a contract
nothing can satisfy.

**`gapEnv.stack` is empty, and every statement in this module depends on that.** The clause now
permits a callee its stack frame, so at an environment with a real stack `postFixedContainer` would be
weaker than the predicate these theorems were written against — the two bracketing checks would still
pass, for a reason having nothing to do with what they check. The empty region keeps them meaning what
they meant. `OwnershipComposition.stack_writing_routine_satisfies_the_clause` is where a nonempty
stack is exercised, and `Ownership.notStack_hypothesis_is_necessary` is where widening the region is
shown to cost something real.
-/

namespace BinaryFv.Zesu.Contracts.FrameGap

open BinaryFv.RiscV
open BinaryFv.Binary
open BinaryFv.Zesu.MemoryRepresentation

/-- A representation that pins one byte at the result base.

Deliberately the *simplest* representation that can be broken, so that a failure of the exhibit is a
failure of the framing claim rather than of some incidental complexity in a real layout. Every real
container representation is a conjunction that includes constraints of this shape, so a counterexample
here is a counterexample there. -/
def bytePinned (value : BitVec 8) : ContainerRepresentation Unit :=
  fun _ _ _ state resultBase => state.mem.get? resultBase = some value

/-- Writing at an address that is neither file-backed nor allocator state preserves both of the
frame conjuncts a container postcondition actually carries. This is the whole mechanism: the two
conjuncts are insensitive to exactly the writes that break a sibling's representation. -/
theorem frame_conjuncts_survive_write {env : DecoderEnvironment} {state : State}
    {address : Nat} {value : BitVec 8}
    (notFile : env.image.readFileByte? address = none)
    (notAlloc : ¬ env.allocatorState address)
    (code : env.CodeIntact state) :
    env.CodeIntact { state with mem := state.mem.insert address value } ∧
      env.NoAllocation state { state with mem := state.mem.insert address value } := by
  refine ⟨ProgramImage.fileBytesMatchMemory_insert_non_file notFile code, ?_⟩
  intro a ha
  have hne : a ≠ address := by rintro rfl; exact notAlloc ha
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp [hne.symm]

/-- **`postFixedContainer` as it stood before the ownership clause was added.**

Kept verbatim — input region, code image, allocator state, own result — so that
`sibling_clobber_permitted_historical` remains a countermodel to *the predicate that had the gap*,
rather than being quietly re-pointed at a different claim. The live `postFixedContainer` differs from
this in exactly one conjunct, `env.WritesOnlyWithinOwnRecord args.resultBase recordSize`, and that
one conjunct is what makes the exhibit stop proving.

Deliberately **not** a contract and deliberately local: nothing outside this module may state an
obligation in terms of it. -/
def postFixedContainerHistorical {α : Type} (env : DecoderEnvironment) (args : ContainerArgs)
    (representation : ContainerRepresentation α)
    (result : Except DecodeError α) (before after : State) : Prop :=
  MemoryBytes after args.base args.bytes ∧
  env.CodeIntact after ∧
  env.NoAllocation before after ∧
  match result with
  | .ok value => representation args.base args.bytes value after args.resultBase
  | .error error =>
      error = DecodeError.invalidSsz ∨ error = DecodeError.unknownFork

/-- **Two children's *historical* postconditions were simultaneously satisfiable in a run where the
second destroyed the first's representation.**

This was the settling fact for D4's composition question. `repA` holds at `s1`, child B's contract is
satisfied from `s1` to `s2` *with its own representation intact at `s2`*, and `repA` is false at `s2`.

Therefore a parent could not conclude its own `representation … after …` from its children's
postconditions: the information it needed about child A had been discarded by the time child B was
done, and nothing in the contract layer preserved it.

**Read the tense.** Every statement here is about `postFixedContainerHistorical`. Against the live
`postFixedContainer` the same construction fails, and it fails for the right reason: child B writes at
`rA`, `rA` is outside `[rB, rB + recordSize)` whenever `rA < rB`, and the ownership clause forbids it.
`Ownership.fixed_container_cannot_clobber_sibling` proves that in general. -/
theorem sibling_clobber_permitted_historical
    (env : DecoderEnvironment) (s0 : State) (inputBase allocBase rA rB : Nat)
    (hne : rA ≠ rB)
    (code : env.CodeIntact s0)
    (hAfile : env.image.readFileByte? rA = none)
    (hBfile : env.image.readFileByte? rB = none)
    (hAalloc : ¬ env.allocatorState rA)
    (hBalloc : ¬ env.allocatorState rB) :
    ∃ (s1 s2 : State) (argsA argsB : ContainerArgs),
      argsA.resultBase = rA ∧ argsB.resultBase = rB ∧
      -- child A succeeds, establishing its representation at `s1`
      postFixedContainerHistorical env argsA (bytePinned 7) (.ok ()) s0 s1 ∧
      -- child B succeeds from `s1`, establishing its OWN representation at `s2`
      postFixedContainerHistorical env argsB (bytePinned 3) (.ok ()) s1 s2 ∧
      -- and A's representation is destroyed at `s2`
      ¬ bytePinned 7 argsA.base argsA.bytes () s2 argsA.resultBase := by
  classical
  refine ⟨{ s0 with mem := s0.mem.insert rA 7 },
          { s0 with mem := ((s0.mem.insert rA 7).insert rB 3).insert rA 0 },
          ⟨inputBase, ByteArray.empty, allocBase, rA⟩,
          ⟨inputBase, ByteArray.empty, allocBase, rB⟩, rfl, rfl, ?_, ?_, ?_⟩
  · -- child A: input region vacuous, frame conjuncts survive, representation established
    obtain ⟨hcode, halloc⟩ := frame_conjuncts_survive_write (value := (7 : BitVec 8)) hAfile hAalloc code
    refine ⟨?_, hcode, halloc, ?_⟩
    · intro index h; exact absurd h (by simp)
    · show (s0.mem.insert rA 7).get? rA = some 7
      simp [Std.ExtHashMap.get?_eq_getElem?]
  · -- child B: same, and B's own representation holds at `s2`
    have hcodeA := ProgramImage.fileBytesMatchMemory_insert_non_file (value := (7 : BitVec 8)) hAfile code
    have hcodeB := ProgramImage.fileBytesMatchMemory_insert_non_file (value := (3 : BitVec 8)) hBfile hcodeA
    have hcode2 := ProgramImage.fileBytesMatchMemory_insert_non_file (value := (0 : BitVec 8)) hAfile hcodeB
    refine ⟨?_, hcode2, ?_, ?_⟩
    · intro index h; exact absurd h (by simp)
    · intro a ha
      have hneA : a ≠ rA := by rintro rfl; exact hAalloc ha
      have hneB : a ≠ rB := by rintro rfl; exact hBalloc ha
      show (((s0.mem.insert rA 7).insert rB 3).insert rA 0).get? a = (s0.mem.insert rA 7).get? a
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      simp [hneA.symm, hneB.symm]
    · show (((s0.mem.insert rA 7).insert rB 3).insert rA 0).get? rB = some 3
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      simp [hne]
  · -- A's byte now reads 0, not 7
    show ¬ (((s0.mem.insert rA 7).insert rB 3).insert rA 0).get? rA = some 7
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp

/-! ## What the missing clause would buy, and what it would not

`sibling_clobber_permitted` on its own shows a clobber is *possible*. That is only half a
demonstration: a proof that succeeds for an incidental reason would look identical. The companion
below closes it by showing the conclusion **flips** exactly when a total frame is supplied — so the
absent clause is what is load-bearing, not some artifact of the witnesses.

Together the two say: without the frame the representation can die, with it the representation
survives. That is the precise statement of what strengthening the contracts would buy. -/

/-- **With a total memory frame on the second child, the first child's representation survives.**
The exact converse of `sibling_clobber_permitted`, and the reason that exhibit is not an artifact. -/
theorem bytePinned_survives_total_frame {value : BitVec 8} {s1 s2 : State}
    {base resultBase : Nat} {bytes : ByteArray}
    (established : bytePinned value base bytes () s1 resultBase)
    (frame : ∀ address, s2.mem.get? address = s1.mem.get? address) :
    bytePinned value base bytes () s2 resultBase := by
  unfold bytePinned at established ⊢
  rw [frame]; exact established

/-- **A memory-only frame is not enough in general**, and this is a fact about the *shape* of
`ContainerRepresentation` rather than about any particular container.

A representation receives the whole `State`, so it may constrain registers, the PC, or any other
component. `bytePinned` happens to read only `mem`, which is why the lemma above goes through for it;
an arbitrary representation has no such guarantee. Recorded because it bears directly on what a
strengthening would have to say: framing `mem` alone would close the exhibit below without closing
the general obligation. -/
theorem representation_may_read_beyond_memory :
    ∃ (rep : ContainerRepresentation Unit) (s1 s2 : State) (base resultBase : Nat)
      (bytes : ByteArray),
      (∀ address, s2.mem.get? address = s1.mem.get? address) ∧
        rep base bytes () s1 resultBase ∧ ¬ rep base bytes () s2 resultBase := by
  refine ⟨fun _ _ _ state _ => state.cycleCount = (default : State).cycleCount,
          default, { (default : State) with cycleCount := (default : State).cycleCount + 1 },
          0, 0, ByteArray.empty, fun _ => rfl, rfl, ?_⟩
  show ¬ ((default : State).cycleCount + 1 = (default : State).cycleCount)
  omega

/-! ## The exhibit is not vacuous

`sibling_clobber_permitted_historical` is an existential under hypotheses. If those hypotheses were
contradictory it would be vacuously true and would establish nothing — which is precisely the
"check that cannot fail" this row keeps finding in other guises. So they are discharged against a
concrete environment here.

**Read the scope of this witness carefully, because it is narrower than the theorem.** It shows the
hypotheses are *consistent*, which is all that is needed to rule out vacuity. It does NOT show they
hold at the canonical environment. That is a separate and stronger claim, it is not proved here, and
it should not be inferred from this: a proof over `canonicalEnvironment` would have to establish that
the relevant arena addresses are neither file-backed nor in `canonicalAllocatorState`, which is real
work. What made the exhibit bite regardless is that it quantifies over `env` — the clobber was
permitted by the contract *shape*, so the canonical environment would have had to rule it out by some
means the contracts did not then provide. -/

/-- An environment carrying no file bytes and no allocator state. Deliberately minimal: its only job
is to witness that the exhibit's hypotheses can be met at once. -/
def gapEnv : DecoderEnvironment where
  image := ⟨#[]⟩
  allocatorState := fun _ => False
  heapPosAddr := 0
  arenaBase := 0
  optionalBlobSchedule := default
  blobSchedule := ⟨0, 0, 0⟩
  optionalU64 := default
  -- All zero, like the option layouts above. The record sizes this module needs are passed to
  -- `postFixedContainer` explicitly, so a zeroed table here cannot make an exhibit easier: a
  -- record size of 0 is the *strongest* instance of the ownership clause, not the weakest.
  record := default
  -- **Empty, and that is what keeps this module's statements meaning what they meant.** The
  -- ownership clause now permits `env.stack`, so a nonempty stack here would weaken every
  -- `postFixedContainer gapEnv …` in the file — including the two bracketing checks, which would
  -- then be satisfiable for a reason having nothing to do with what they were written to show. The
  -- empty region makes `postFixedContainer gapEnv` definitionally the predicate these theorems were
  -- written against. `OwnershipComposition.frameEnv` is where a real stack is exercised.
  stack := fun _ => False

theorem gapEnv_readFileByte (address : Nat) : gapEnv.image.readFileByte? address = none := rfl

/-- **The hypotheses of `sibling_clobber_permitted_historical` are jointly satisfiable**, so the
exhibit is a genuine countermodel rather than a vacuous implication. -/
theorem sibling_clobber_hypotheses_satisfiable (s0 : State) :
    ∃ (env : DecoderEnvironment) (rA rB : Nat),
      rA ≠ rB ∧ env.CodeIntact s0 ∧
      env.image.readFileByte? rA = none ∧ env.image.readFileByte? rB = none ∧
      ¬ env.allocatorState rA ∧ ¬ env.allocatorState rB :=
  ⟨gapEnv, 0, 1, by decide, by intro a b h; exact absurd h (by rw [gapEnv_readFileByte]; simp),
    gapEnv_readFileByte 0, gapEnv_readFileByte 1, id, id⟩

/-- The two combined: at `gapEnv` the clobber was not merely permitted in the abstract, it was
realised. This is the statement to read if only one is read.

`rA = 0` and `rB = 1`, so `rA < rB` — the case no record size can rescue, which is exactly why the
strengthened `postFixedContainer` refuses it. -/
theorem frame_gap_is_real (s0 : State) :
    ∃ (s1 s2 : State) (argsA argsB : ContainerArgs),
      postFixedContainerHistorical gapEnv argsA (bytePinned 7) (.ok ()) s0 s1 ∧
      postFixedContainerHistorical gapEnv argsB (bytePinned 3) (.ok ()) s1 s2 ∧
      ¬ bytePinned 7 argsA.base argsA.bytes () s2 argsA.resultBase := by
  obtain ⟨s1, s2, argsA, argsB, _, _, hA, hB, hbroken⟩ :=
    sibling_clobber_permitted_historical gapEnv s0 0 0 0 1 (by decide)
      (by intro a b h; exact absurd h (by rw [gapEnv_readFileByte]; simp))
      (gapEnv_readFileByte 0) (gapEnv_readFileByte 1) id id
  exact ⟨s1, s2, argsA, argsB, hA, hB, hbroken⟩

/-! ## The strengthened predicate is satisfiable, by a sibling that really writes

The other half of the regression, and the half that is easy to skip. Showing the clobber is now
impossible is worth nothing if the strengthened postcondition is impossible too: an unsatisfiable
`post` forbids every clobber for the same reason it forbids everything else, making any conditional
root that consumes it vacuous.

So the witness below is **discriminating**: the sibling's memory genuinely changes across the step
(`s1.mem.get? ≠ s2.mem.get?` at its own result byte), and it satisfies the full strengthened
predicate including the ownership clause. A no-op sibling would satisfy the clause for any region and
would prove nothing. -/

/-- **A sibling that writes its own record satisfies the strengthened `postFixedContainer`.**

One byte of record at address `1`, written from absent to `3`. Concrete rather than abstract for the
same reason `OwnershipComposition.sibling_chain_is_real` is: abstract bases let a hidden arithmetic
obstruction survive. -/
theorem strengthened_post_is_satisfiable :
    ∃ (s1 s2 : State) (args : ContainerArgs),
      postFixedContainer gapEnv args (bytePinned 3) 1 (.ok ()) s1 s2 ∧
        s1.mem.get? args.resultBase ≠ s2.mem.get? args.resultBase := by
  refine ⟨{ (default : State) with mem := (default : State).mem.insert 1 0 },
          { (default : State) with mem := ((default : State).mem.insert 1 0).insert 1 3 },
          ⟨0, ByteArray.empty, 0, 1⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro index h; exact absurd h (by simp)
  · intro a b h; exact absurd h (by rw [gapEnv_readFileByte]; simp)
  · intro _ h; exact h.elim
  · intro address houtside
    have hne : address ≠ 1 := by
      intro heq
      refine houtside (Or.inl (Or.inl ?_))
      show (1 : Nat) ≤ address ∧ address < 1 + 1
      omega
    show (((default : State).mem.insert 1 0).insert 1 3).get? address
        = ((default : State).mem.insert 1 0).get? address
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (fun heq => hne heq.symm)]
  · show (((default : State).mem.insert 1 0).insert 1 3).get? 1 = some 3
    simp [Std.ExtHashMap.get?_eq_getElem?]
  · show ((default : State).mem.insert 1 0).get? 1
        ≠ (((default : State).mem.insert 1 0).insert 1 3).get? 1
    simp [Std.ExtHashMap.get?_eq_getElem?]

end BinaryFv.Zesu.Contracts.FrameGap
