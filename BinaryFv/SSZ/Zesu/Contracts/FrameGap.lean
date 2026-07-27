import BinaryFv.SSZ.Zesu.Contracts.Containers

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

What the exhibit *does* rely on is the one real fact: `postFixedContainer` constrains the input
region, the code image, `allocatorState`, and its own `resultBase`, and says nothing whatever about
any other address.
-/

namespace BinaryFv.SSZ.Zesu.Contracts.FrameGap

open BinaryFv.RiscV
open BinaryFv.Binary
open BinaryFv.SSZ.Zesu.MemoryRepresentation

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

/-- **Two children's postconditions are simultaneously satisfiable in a run where the second
destroys the first's representation.**

This is the settling fact for D4's composition question. `repA` holds at `s1`, child B's contract is
satisfied from `s1` to `s2` *with its own representation intact at `s2`*, and `repA` is false at `s2`.

Therefore a parent cannot conclude its own `representation … after …` from its children's
postconditions: the information it needs about child A has been discarded by the time child B is
done, and nothing in the contract layer preserves it. -/
theorem sibling_clobber_permitted
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
      postFixedContainer env argsA (bytePinned 7) (.ok ()) s0 s1 ∧
      -- child B succeeds from `s1`, establishing its OWN representation at `s2`
      postFixedContainer env argsB (bytePinned 3) (.ok ()) s1 s2 ∧
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

`sibling_clobber_permitted` is an existential under hypotheses. If those hypotheses were
contradictory it would be vacuously true and would establish nothing — which is precisely the
"check that cannot fail" this row keeps finding in other guises. So they are discharged against a
concrete environment here.

**Read the scope of this witness carefully, because it is narrower than the theorem.** It shows the
hypotheses are *consistent*, which is all that is needed to rule out vacuity. It does NOT show they
hold at the canonical environment. That is a separate and stronger claim, it is not proved here, and
it should not be inferred from this: a proof over `canonicalEnvironment` would have to establish that
the relevant arena addresses are neither file-backed nor in `canonicalAllocatorState`, which is real
work. What makes the exhibit bite regardless is that `sibling_clobber_permitted` quantifies over
`env` — the clobber is permitted by the contract *shape*, so the canonical environment would have to
rule it out by some means the contracts do not currently provide. -/

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

theorem gapEnv_readFileByte (address : Nat) : gapEnv.image.readFileByte? address = none := rfl

/-- **The hypotheses of `sibling_clobber_permitted` are jointly satisfiable**, so the exhibit is a
genuine countermodel rather than a vacuous implication. -/
theorem sibling_clobber_hypotheses_satisfiable (s0 : State) :
    ∃ (env : DecoderEnvironment) (rA rB : Nat),
      rA ≠ rB ∧ env.CodeIntact s0 ∧
      env.image.readFileByte? rA = none ∧ env.image.readFileByte? rB = none ∧
      ¬ env.allocatorState rA ∧ ¬ env.allocatorState rB :=
  ⟨gapEnv, 0, 1, by decide, by intro a b h; exact absurd h (by rw [gapEnv_readFileByte]; simp),
    gapEnv_readFileByte 0, gapEnv_readFileByte 1, id, id⟩

/-- The two combined: at `gapEnv` the clobber is not merely permitted in the abstract, it is
realised. This is the statement to read if only one is read. -/
theorem frame_gap_is_real (s0 : State) :
    ∃ (s1 s2 : State) (argsA argsB : ContainerArgs),
      postFixedContainer gapEnv argsA (bytePinned 7) (.ok ()) s0 s1 ∧
      postFixedContainer gapEnv argsB (bytePinned 3) (.ok ()) s1 s2 ∧
      ¬ bytePinned 7 argsA.base argsA.bytes () s2 argsA.resultBase := by
  obtain ⟨s1, s2, argsA, argsB, _, _, hA, hB, hbroken⟩ :=
    sibling_clobber_permitted gapEnv s0 0 0 0 1 (by decide)
      (by intro a b h; exact absurd h (by rw [gapEnv_readFileByte]; simp))
      (gapEnv_readFileByte 0) (gapEnv_readFileByte 1) id id
  exact ⟨s1, s2, argsA, argsB, hA, hB, hbroken⟩

end BinaryFv.SSZ.Zesu.Contracts.FrameGap
