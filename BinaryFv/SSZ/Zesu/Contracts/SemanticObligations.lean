import BinaryFv.SSZ.Zesu.Contracts.Catalog
import BinaryFv.SSZ.Zesu.SpecCorrespondence.EncodeDecode

/-!
# Discharging the catalog's semantic obligations

`catalogSemanticObligations` is the conjunction of every claim the catalog makes about the decoder's
*meaning* — as opposed to its machine behaviour. None of them is about a run, so none of them belongs
in a local occurrence proof; they are Row D's to settle.

The obligations split into three kinds, and the split is worth naming because it says where the
difficulty actually lives:

* **Error taxonomy.** Which errors a routine can produce at all. These follow from the shape of the
  meanings, and the machinery below (`FailsOnly` and its bind/ite combinators) is what makes them
  compose instead of being re-derived by hand for each of the twenty-odd meanings.
* **Characterizations.** The exact acceptance condition of one routine, stated over all inputs.
* **Oracle agreement.** That the source-shaped composition and the pinned oracle agree on
  acceptance. This is the hard content: it is stated over `SszBridge.decodeCanonical`, whose
  canonicality test is a global re-serialization equality the binary never performs.

Everything proved here is proved over *all* inputs; nothing is decided on a fixture.
-/

namespace BinaryFv.SSZ.Zesu.Contracts

open SizzLean.Spec

/-! ## Which errors a computation can fail with

The decoder's error set has three constructors, and most of the catalog's semantic obligations are
statements that some routine cannot reach two of them. Proving those one meaning at a time would
mean re-doing the same case analysis through every `do` block, so they are proved once as a
predicate with the combinators the `do` blocks are built from. -/

/-- Every failure of `result` is an error `allowed` admits. -/
def FailsOnly {α : Type} (allowed : SszDecodeError → Prop)
    (result : Except SszDecodeError α) : Prop :=
  ∀ error, result = .error error → allowed error

namespace FailsOnly

theorem of_ok {α : Type} {allowed : SszDecodeError → Prop} (value : α) :
    FailsOnly allowed (.ok value) := by
  intro error h
  exact absurd h (by simp)

theorem of_error {α : Type} {allowed : SszDecodeError → Prop} {error : SszDecodeError}
    (h : allowed error) : FailsOnly (α := α) allowed (.error error) := by
  intro other hother
  have heq : error = other := by simpa using hother
  exact heq ▸ h

/-- The bind rule: a `do` block fails only with what its parts fail with. -/
theorem bind {α β : Type} {allowed : SszDecodeError → Prop} {x : Except SszDecodeError α}
    {f : α → Except SszDecodeError β} (hx : FailsOnly allowed x)
    (hf : ∀ value, FailsOnly allowed (f value)) : FailsOnly allowed (x >>= f) := by
  intro error h
  cases x with
  | error e =>
      -- The propagated error is the same constructor at the *result* type, so it has to be
      -- transported back to the argument type before `hx` will take it.
      have heq : e = error := by
        have hβ : (Except.error e : Except SszDecodeError β) = Except.error error := h
        simpa using hβ
      exact hx error (congrArg Except.error heq)
  | ok value => exact hf value error h

theorem map {α β : Type} {allowed : SszDecodeError → Prop} {f : α → β}
    {x : Except SszDecodeError α} (hx : FailsOnly allowed x) : FailsOnly allowed (x.map f) := by
  intro error h
  cases x with
  | error e =>
      have heq : e = error := by
        have hβ : (Except.error e : Except SszDecodeError β) = Except.error error := h
        simpa using hβ
      exact hx error (congrArg Except.error heq)
  | ok value => exact absurd h (by simp [Except.map])

theorem ite {α : Type} {allowed : SszDecodeError → Prop} {c : Prop} [Decidable c]
    {a b : Except SszDecodeError α} (ha : FailsOnly allowed a) (hb : FailsOnly allowed b) :
    FailsOnly allowed (if c then a else b) := by
  split <;> assumption

/-- Weakening: a computation that fails only with `p` fails only with any `q` above `p`. -/
theorem mono {α : Type} {p q : SszDecodeError → Prop} (h : ∀ error, p error → q error)
    {result : Except SszDecodeError α} (hr : FailsOnly p result) : FailsOnly q result :=
  fun error he => h error (hr error he)

/-- The form the individual obligations are stated in: an error a computation cannot fail with. -/
theorem ne {α : Type} {allowed : SszDecodeError → Prop} {result : Except SszDecodeError α}
    (hr : FailsOnly allowed result) {error : SszDecodeError} (h : ¬ allowed error) :
    result ≠ .error error :=
  fun heq => h (hr error heq)

end FailsOnly

/-- The predicate almost every routine satisfies: `invalidSsz` is its only failure. -/
abbrev OnlyInvalid {α : Type} (result : Except SszDecodeError α) : Prop :=
  FailsOnly (· = .invalidSsz) result

/-- The predicate `decodeForkConfig` and its one caller satisfy. -/
abbrev OnlyInvalidOrFork {α : Type} (result : Except SszDecodeError α) : Prop :=
  FailsOnly (fun error => error = .invalidSsz ∨ error = .unknownFork) result

theorem OnlyInvalid.toFork {α : Type} {result : Except SszDecodeError α} (h : OnlyInvalid result) :
    OnlyInvalidOrFork result :=
  FailsOnly.mono (fun _ he => Or.inl he) h

section Taxonomy

/-! Nothing in this section needs a meaning to *run*, and letting the elaborator try to run one is
the difference between a fast file and a heartbeat timeout: unifying a goal against a meaning built
on `decodeCanonical` otherwise drives the schema deserializer until it gets stuck. Each meaning is
therefore sealed as soon as its own taxonomy lemma is proved, so a caller's proof matches it by name
instead of by unfolding it. The seals are `local`; the characterizations after this section, which
genuinely do evaluate, are unaffected. -/
attribute [local irreducible] SszBridge.decodeCanonical

/-! ### Leaves

Every primitive read funnels through `bytesAt`, whose only failure is `invalidSsz`; the lifted
`Option` readers inherit that. -/

theorem toDecodeResult_onlyInvalid {α : Type} (value : Option α) :
    OnlyInvalid (Option.toDecodeResult value) := by
  cases value with
  | none => exact FailsOnly.of_error rfl
  | some v => exact FailsOnly.of_ok _

theorem meaningBytesAt_onlyInvalid (bytes : ByteArray) (offset length : Nat) :
    OnlyInvalid (meaningBytesAt bytes offset length) := by
  unfold meaningBytesAt
  exact FailsOnly.ite (FailsOnly.of_ok _) (FailsOnly.of_error rfl)

theorem meaningReadU32_onlyInvalid (bytes : ByteArray) (offset : Nat) :
    OnlyInvalid (meaningReadU32 bytes offset) :=
  toDecodeResult_onlyInvalid _

theorem meaningReadU64_onlyInvalid (bytes : ByteArray) (offset : Nat) :
    OnlyInvalid (meaningReadU64 bytes offset) :=
  toDecodeResult_onlyInvalid _

theorem meaningReadOffset_onlyInvalid (bytes : ByteArray) (offset : Nat) :
    OnlyInvalid (meaningReadOffset bytes offset) :=
  FailsOnly.map (meaningReadU32_onlyInvalid bytes offset)

theorem meaningReadU256_onlyInvalid (bytes : ByteArray) (offset : Nat) :
    OnlyInvalid (meaningReadU256 bytes offset) := by
  unfold meaningReadU256
  split
  · exact FailsOnly.of_ok _
  · rename_i error heq
    exact FailsOnly.of_error (meaningBytesAt_onlyInvalid bytes offset 32 error heq)

theorem meaningReadArray_onlyInvalid (length : Nat) (bytes : ByteArray) (offset : Nat) :
    OnlyInvalid (meaningReadArray length bytes offset) :=
  meaningBytesAt_onlyInvalid _ _ _

theorem meaningRequireU32Length_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningRequireU32Length bytes) := by
  unfold meaningRequireU32Length
  exact FailsOnly.ite (FailsOnly.of_ok _) (FailsOnly.of_error rfl)

theorem meaningRequireCanonicalOffsets_onlyInvalid (bytes : ByteArray) (fixedSize : Nat)
    (offsets : List Nat) : OnlyInvalid (meaningRequireCanonicalOffsets bytes fixedSize offsets) := by
  unfold meaningRequireCanonicalOffsets
  refine FailsOnly.ite (FailsOnly.of_error rfl) ?_
  -- The walk either runs off the end (`ok`) or stops at a violating offset (`invalidSsz`).
  suffices h : ∀ (rest : List Nat) (previous : Nat),
      OnlyInvalid (meaningRequireCanonicalOffsets.walk bytes previous rest) from h offsets fixedSize
  intro rest
  induction rest with
  | nil => intro previous; exact FailsOnly.of_ok _
  | cons offset rest ih =>
      intro previous
      unfold meaningRequireCanonicalOffsets.walk
      exact FailsOnly.ite (FailsOnly.of_error rfl) (ih offset)

/-! ### Oracle-shaped meanings

Each of these is `decodeCanonical` at a closed schema followed by a projection, and
`sszToDecodeError` is constant `invalidSsz`, so none of them can reach the other two errors. The
proofs are all the same two-case split; they are written out rather than abstracted because
abstracting over the projection would have to abstract over its type as well, which buys nothing. -/

theorem meaningOptionalBlobSchedule_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningOptionalBlobSchedule bytes) := by
  unfold meaningOptionalBlobSchedule
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningOptionalU64_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningOptionalU64 bytes) := by
  unfold meaningOptionalU64
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningVersionedHashes_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningVersionedHashes bytes) := by
  unfold meaningVersionedHashes
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningWithdrawals_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningWithdrawals bytes) := by
  unfold meaningWithdrawals
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningDepositRequests_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningDepositRequests bytes) := by
  unfold meaningDepositRequests
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningWithdrawalRequests_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningWithdrawalRequests bytes) := by
  unfold meaningWithdrawalRequests
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningConsolidationRequests_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningConsolidationRequests bytes) := by
  unfold meaningConsolidationRequests
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningPublicKeys_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningPublicKeys bytes) := by
  unfold meaningPublicKeys
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningByteListList_onlyInvalid (maxItems maxItemBytes : Nat) (bytes : ByteArray) :
    OnlyInvalid (meaningByteListList maxItems maxItemBytes bytes) := by
  unfold meaningByteListList
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningExecutionWitness_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningExecutionWitness bytes) := by
  unfold meaningExecutionWitness
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningExecutionRequests_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningExecutionRequests bytes) := by
  unfold meaningExecutionRequests
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningExecutionPayload_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningExecutionPayload bytes) := by
  unfold meaningExecutionPayload
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

theorem meaningNewPayloadRequest_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningNewPayloadRequest bytes) := by
  unfold meaningNewPayloadRequest
  split <;> first | exact FailsOnly.of_ok _ | exact FailsOnly.of_error rfl

/-! Each leaf is now a name rather than a body, so a composite's proof matches it directly. -/
attribute [local irreducible] meaningBytesAt meaningReadU32 meaningReadU64 meaningReadOffset
  meaningReadU256 meaningReadArray meaningRequireU32Length meaningRequireCanonicalOffsets
  meaningOptionalBlobSchedule meaningOptionalU64 meaningVersionedHashes meaningWithdrawals
  meaningDepositRequests meaningWithdrawalRequests meaningConsolidationRequests meaningPublicKeys
  meaningByteListList meaningExecutionWitness meaningExecutionRequests meaningExecutionPayload
  meaningNewPayloadRequest

/-! ### The source-shaped containers

`decodeForkActivation` composes only `invalidSsz`-failing parts. `decodeForkConfig` adds the one
`throw .unknownFork` in the whole decoder, and `decodeChainConfig` inherits it by calling it — which
is exactly why `onlyForkConfigRaisesUnknownFork` lists neither of the latter two. -/

/-- Walk a `do` block's desugaring, discharging each step with one of the leaf facts supplied.

`do` in `Except` desugars to nested binds, `if`s, join points, and `pure`s whose exact shape is an
elaboration detail — a hand-written chain of `refine`s is correct only for one particular
desugaring and breaks silently under another. Driving the same list to a fixed point does not depend
on that shape.

The order matters: a supplied leaf is tried before `bind`, because `meaningReadOffset` is itself an
`Except.map` and would otherwise be taken apart into its `readU32` instead of being discharged. -/
syntax "fails_only " "[" term,* "]" : tactic

macro_rules
  | `(tactic| fails_only [$leaves,*]) =>
    `(tactic| repeat' first
        | apply FailsOnly.ite
        $[| exact $leaves]*
        | refine FailsOnly.bind ?_ fun _ => ?_
        | exact FailsOnly.of_error rfl
        | exact FailsOnly.of_error (Or.inl rfl)
        | exact FailsOnly.of_error (Or.inr rfl)
        | exact FailsOnly.of_ok _)

theorem meaningForkActivation_onlyInvalid (bytes : ByteArray) :
    OnlyInvalid (meaningForkActivation bytes) := by
  unfold meaningForkActivation
  fails_only [meaningReadOffset_onlyInvalid _ _, meaningRequireCanonicalOffsets_onlyInvalid _ _ _,
    meaningOptionalU64_onlyInvalid _]

attribute [local irreducible] meaningForkActivation

theorem meaningForkConfig_onlyInvalidOrFork (bytes : ByteArray) :
    OnlyInvalidOrFork (meaningForkConfig bytes) := by
  unfold meaningForkConfig
  fails_only [(meaningReadOffset_onlyInvalid _ _).toFork,
    (meaningRequireCanonicalOffsets_onlyInvalid _ _ _).toFork,
    (meaningReadU64_onlyInvalid _ _).toFork, (meaningForkActivation_onlyInvalid _).toFork,
    (meaningOptionalBlobSchedule_onlyInvalid _).toFork]

attribute [local irreducible] meaningForkConfig

theorem meaningChainConfig_onlyInvalidOrFork (bytes : ByteArray) :
    OnlyInvalidOrFork (meaningChainConfig bytes) := by
  unfold meaningChainConfig
  fails_only [(meaningReadOffset_onlyInvalid _ _).toFork,
    (meaningRequireCanonicalOffsets_onlyInvalid _ _ _).toFork,
    (meaningReadU64_onlyInvalid _ _).toFork, meaningForkConfig_onlyInvalidOrFork _]

attribute [local irreducible] meaningChainConfig

/-! ### The entry points

`decodeRaw` composes the four top-level children; only `decodeChainConfig` among them can raise
`unknownFork`, and none of them has an allocation-failure outcome, because every meaning below is
either a pure read or the pinned oracle. `decode` adds only a retry of `decodeRaw`. -/

theorem meaningDecodeRaw_onlyInvalidOrFork (bytes : ByteArray) :
    OnlyInvalidOrFork (meaningDecodeRaw bytes) := by
  unfold meaningDecodeRaw
  fails_only [(meaningRequireU32Length_onlyInvalid _).toFork,
    (meaningReadOffset_onlyInvalid _ _).toFork,
    (meaningRequireCanonicalOffsets_onlyInvalid _ _ _).toFork,
    (meaningNewPayloadRequest_onlyInvalid _).toFork,
    (meaningExecutionWitness_onlyInvalid _).toFork, meaningChainConfig_onlyInvalidOrFork _,
    (meaningPublicKeys_onlyInvalid _).toFork]

attribute [local irreducible] meaningDecodeRaw

theorem meaningDecode_onlyInvalidOrFork (bytes : ByteArray) :
    OnlyInvalidOrFork (meaningDecode bytes) := by
  unfold meaningDecode
  split
  · exact FailsOnly.of_ok _
  · exact FailsOnly.ite (meaningDecodeRaw_onlyInvalidOrFork _) (FailsOnly.of_error (Or.inl rfl))
  · exact FailsOnly.of_error (meaningDecodeRaw_onlyInvalidOrFork bytes _ (by assumption))

end Taxonomy

/-! ## The error-taxonomy obligations -/

/-- Every leaf reader's only error is `invalidSsz`. -/
theorem leafReadsOnlyFailInvalid_holds : leafReadsOnlyFailInvalid := fun bytes offset =>
  ⟨(meaningReadU32_onlyInvalid bytes offset).ne (by simp),
    (meaningReadU32_onlyInvalid bytes offset).ne (by simp),
    (meaningReadU64_onlyInvalid bytes offset).ne (by simp),
    (meaningReadU64_onlyInvalid bytes offset).ne (by simp),
    (meaningReadOffset_onlyInvalid bytes offset).ne (by simp),
    (meaningReadOffset_onlyInvalid bytes offset).ne (by simp),
    (meaningReadU256_onlyInvalid bytes offset).ne (by simp),
    (meaningReadU256_onlyInvalid bytes offset).ne (by simp),
    (meaningRequireU32Length_onlyInvalid bytes).ne (by simp),
    (meaningRequireU32Length_onlyInvalid bytes).ne (by simp),
    fun length =>
      ⟨(meaningBytesAt_onlyInvalid bytes offset length).ne (by simp),
        (meaningBytesAt_onlyInvalid bytes offset length).ne (by simp),
        (meaningReadArray_onlyInvalid length bytes offset).ne (by simp),
        (meaningReadArray_onlyInvalid length bytes offset).ne (by simp)⟩⟩

/-- No collection decoder reads a fork index. -/
theorem collectionsNeverUnknownFork_holds : collectionsNeverUnknownFork := fun bytes =>
  ⟨(meaningVersionedHashes_onlyInvalid bytes).ne (by simp),
    (meaningWithdrawals_onlyInvalid bytes).ne (by simp),
    (meaningDepositRequests_onlyInvalid bytes).ne (by simp),
    (meaningWithdrawalRequests_onlyInvalid bytes).ne (by simp),
    (meaningConsolidationRequests_onlyInvalid bytes).ne (by simp),
    (meaningPublicKeys_onlyInvalid bytes).ne (by simp)⟩

/-- Unknown-fork and allocation failure are unreachable for the option decoder. -/
theorem meaningNeverForkOrMemory_holds : meaningNeverForkOrMemory := fun bytes =>
  ⟨(meaningOptionalBlobSchedule_onlyInvalid bytes).ne (by simp),
    (meaningOptionalBlobSchedule_onlyInvalid bytes).ne (by simp)⟩

/-- The witness: fork `21`, one past the last known fork, with both offsets equal to the
fixed-section size `16`.

Both facts the fork-ordering divergence needs come from that one choice. The offset table is
canonical, so `meaningForkConfig` gets past `requireCanonicalOffsets` and stops at the fork bound,
which is the whole point — the binary rejects *before* looking at the children. And the offsets being
`16` in a 16-byte buffer leaves the activation slice empty, which is what makes the oracle reject
too, since it decodes the children first and a variable-field container cannot be empty. The oracle
half is at the end of this file; only the binary's half is needed here. -/
def forkOrderingWitness : ByteArray := ⟨#[21, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0]⟩

/-- The binary's side: `unknownFork`, raised before any child is decoded.

This is also the existence half of `onlyForkConfigRaisesUnknownFork` — "only" needs a routine that
actually raises it, not just routines that do not. -/
theorem meaningForkConfig_forkOrderingWitness :
    meaningForkConfig forkOrderingWitness = .error .unknownFork := by
  rfl

/-- `decodeForkConfig` is the decoder's only source of `unknownFork`. -/
theorem onlyForkConfigRaisesUnknownFork_holds : onlyForkConfigRaisesUnknownFork :=
  ⟨fun bytes =>
    ⟨(meaningForkActivation_onlyInvalid bytes).ne (by simp),
      (meaningExecutionWitness_onlyInvalid bytes).ne (by simp),
      (meaningExecutionRequests_onlyInvalid bytes).ne (by simp),
      (meaningExecutionPayload_onlyInvalid bytes).ne (by simp),
      (meaningNewPayloadRequest_onlyInvalid bytes).ne (by simp)⟩,
    forkOrderingWitness, meaningForkConfig_forkOrderingWitness⟩

/-- The three fixed containers never allocate, so out-of-memory is unreachable for them. -/
theorem fixedContainersNeverAllocate_holds : fixedContainersNeverAllocate := fun bytes =>
  ⟨(meaningForkActivation_onlyInvalid bytes).ne (by simp),
    (meaningForkConfig_onlyInvalidOrFork bytes).ne (by simp),
    (meaningChainConfig_onlyInvalidOrFork bytes).ne (by simp)⟩

/-- The three non-`alloc` vtable entries are constant. -/
theorem allocatorVtableEntriesAreConstant_holds : allocatorVtableEntriesAreConstant :=
  ⟨rfl, rfl⟩

/-- **Out-of-memory is unreachable below the root theorem's input bound.**

Stated over the *meaning*, this is the specification-side half: `meaningDecode` is built from pure
reads and the pinned oracle, neither of which has an allocation-failure outcome, so no input — inside
the scope bound or outside it — can make it produce `outOfMemory`. That is what makes the arm
dischargeable rather than normalizable, and it is why the scope hypothesis is not used.

The machine-side half is a different theorem and is not claimed here: the binary really does have an
exhaustion branch, and `Runtime.raw_allocation_bound_fits_arena` is what rules it out below 2 MiB. -/
theorem outOfMemoryUnreachableBelowBound_holds : outOfMemoryUnreachableBelowBound :=
  fun bytes _ => (meaningDecode_onlyInvalidOrFork bytes).ne (by simp)

/-! ## Characterizations that need no oracle reasoning -/

/-- A read succeeds exactly when its window fits. -/
theorem bytesAtSucceedsIffFits_holds : bytesAtSucceedsIffFits := by
  intro bytes offset length
  unfold meaningBytesAt
  constructor
  · rintro ⟨slice, h⟩
    by_cases hfit : offset ≤ bytes.size ∧ length ≤ bytes.size - offset
    · exact hfit
    · rw [if_neg hfit] at h; simp at h
  · intro hfit
    exact ⟨_, if_pos hfit⟩

/-- `readOffset` is exactly `readU32` widened: the Zig `@intCast` is total on this target, so the
meaning adds no failure mode of its own. -/
theorem readOffsetIsWidenedReadU32_holds : readOffsetIsWidenedReadU32 :=
  fun _ _ => rfl

/-! ### The offset table

`requireCanonicalOffsets` is the decoder's whole canonicality discipline, and its recursion carries
one offset of state — the previous entry — that the obligation's `Nondecreasing` does not mention.
Naming that state is what makes the induction go through. -/

/-- The walk's invariant: every entry is at least its predecessor, starting from `previous`.
`Nondecreasing` says the same thing about a list on its own; this is the form the recursion produces
and `nondecreasing_cons_iff` is the bridge. -/
def NondecreasingFrom (previous : Nat) : List Nat → Prop
  | [] => True
  | offset :: rest => previous ≤ offset ∧ NondecreasingFrom offset rest

theorem nondecreasing_cons_iff (offset : Nat) (rest : List Nat) :
    Nondecreasing (offset :: rest) ↔ NondecreasingFrom offset rest := by
  induction rest generalizing offset with
  | nil => simp [Nondecreasing, NondecreasingFrom]
  | cons second rest ih => simp [Nondecreasing, NondecreasingFrom, ih second]

/-- The walk accepts exactly the tables that never step backwards and never leave the slice. -/
theorem walk_ok_iff (bytes : ByteArray) (offsets : List Nat) (previous : Nat) :
    meaningRequireCanonicalOffsets.walk bytes previous offsets = .ok () ↔
      (NondecreasingFrom previous offsets ∧ ∀ offset ∈ offsets, offset ≤ bytes.size) := by
  induction offsets generalizing previous with
  | nil => simp [meaningRequireCanonicalOffsets.walk, NondecreasingFrom]
  | cons offset rest ih =>
      rw [meaningRequireCanonicalOffsets.walk]
      split
      · rename_i hbad
        simp only [NondecreasingFrom, List.mem_cons, forall_eq_or_imp]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨⟨hprev, -⟩, hsize, -⟩; omega
      · rename_i hgood
        rw [ih]
        simp only [NondecreasingFrom, List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨hnd, hall⟩; exact ⟨⟨by omega, hnd⟩, by omega, hall⟩
        · rintro ⟨⟨-, hnd⟩, -, hall⟩; exact ⟨hnd, hall⟩

/-- **`requireCanonicalOffsets` accepts exactly the canonical prefix tables.**

The first entry must *equal* the fixed size, not merely reach it: that equality is what forbids
padding between a container's fixed section and its first variable field, and it is the clause the
oracle's re-serialization check enforces by a completely different route. -/
theorem canonicalOffsetsCharacterization_holds : canonicalOffsetsCharacterization := by
  intro bytes fixedSize offsets
  unfold meaningRequireCanonicalOffsets
  split
  · rename_i hbad
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hfix, hne, hhead, -, -⟩
      rcases hbad with hbad | hbad | hbad
      · omega
      · exact absurd (List.isEmpty_iff.mp hbad) hne
      · exact absurd hhead hbad
  · rename_i hgood
    rw [walk_ok_iff]
    match offsets with
    | [] => simp [List.isEmpty] at hgood
    | first :: rest =>
        have hhead : first = fixedSize :=
          Classical.byContradiction fun hne => hgood (Or.inr (Or.inr hne))
        subst hhead
        constructor
        · rintro ⟨⟨-, hnd⟩, hall⟩
          exact ⟨hall first (by simp), by simp, rfl,
            (nondecreasing_cons_iff first rest).mpr hnd, hall⟩
        · rintro ⟨-, -, -, hnd, hall⟩
          exact ⟨⟨Nat.le_refl _, (nondecreasing_cons_iff first rest).mp hnd⟩, hall⟩

/-! ### The asymmetric ERE retry

The binary retries the four-byte-stripped input on `invalidSsz` while the oracle retries on every
bridge error but `v3Quarantined`. That asymmetry is only safe because the retry can never *succeed*
on an input that reached the top-level offset table, and this is the byte-level reason why. -/

theorem ByteArray.get!_eq_getElem (bytes : ByteArray) (index : Nat) (h : index < bytes.size) :
    bytes.get! index = bytes[index] := by
  show bytes.data[index]! = bytes[index]
  rw [getElem!_pos bytes.data index h]
  rfl

/-- Reading inside a suffix is reading at the shifted index of the original. -/
theorem get!_extract_suffix (bytes : ByteArray) (start index : Nat)
    (h : start + index < bytes.size) :
    (bytes.extract start bytes.size).get! index = bytes.get! (start + index) := by
  have hi : index < (bytes.extract start bytes.size).size := by
    rw [ByteArray.size_extract]; omega
  rw [ByteArray.get!_eq_getElem _ _ hi, ByteArray.getElem_extract hi,
    ByteArray.get!_eq_getElem _ _ h]

/-- **The four-byte-stripped tail of a framed input never carries the schema id.**

An input that reaches the top-level offset table has `hasSchemaId`, so it starts `00 01`, and a first
offset of exactly `16` forces its bytes 2..6 to be `10 00 00 00`. Byte 5 is therefore `00` — and byte
5 is the tail's *second* byte, the one `hasSchemaId` demands be `01`. So the retry cannot succeed on
precisely the inputs where the binary and the oracle disagree about attempting it. -/
theorem retryTailNeverSchemaValid_holds : retryTailNeverSchemaValid := by
  intro bytes _ hfirst
  rw [SszBridge.readU32LE?] at hfirst
  split at hfirst
  · exact absurd hfirst (by simp)
  · rename_i hfits
    rw [ByteArray.size_extract] at hfits
    have hsize : 6 ≤ bytes.size := by omega
    -- The declared value is 16, and every byte is below 256, so the three high bytes are zero.
    have hsum : (bytes.get! 2).toNat + (bytes.get! 3).toNat * 256 +
        (bytes.get! 4).toNat * 256 ^ 2 + (bytes.get! 5).toNat * 256 ^ 3 = 16 := by
      have h0 := get!_extract_suffix bytes 2 0 (by omega)
      have h1 := get!_extract_suffix bytes 2 1 (by omega)
      have h2 := get!_extract_suffix bytes 2 2 (by omega)
      have h3 := get!_extract_suffix bytes 2 3 (by omega)
      simpa [h0, h1, h2, h3] using hfirst
    have hfifth : (bytes.get! 5).toNat = 0 := by
      have hlt := (bytes.get! 5).toNat_lt_size
      omega
    -- Byte 5 of the input is byte 1 of the tail, and `hasSchemaId` needs that byte to be `01`.
    have htail : ((bytes.extract 4 bytes.size).get! 1).toNat = 0 := by
      rw [get!_extract_suffix bytes 4 1 (by omega)]
      exact hfifth
    have hne : (bytes.extract 4 bytes.size).get! 1 ≠ 1 := fun h => by
      rw [h] at htail
      exact absurd htail (by decide)
    simp [SszBridge.hasSchemaId, hne]

/-! ### Evaluating the oracle

The three option-length cases are claims about what `decodeCanonical` *does*, so unlike everything
above they need it to reduce. Two obstacles: the oracle is written in `do` notation, and the
serializer is a mutual structural recursion whose arms do not fire by `rfl` (its `[]` lives in the
dependent `List schema.interp`, so `simp` cannot match the generated equation either). The bridge
below removes the first obstacle once, and the two arms are then supplied at the exact schema. -/

/-- `decodeCanonical` with its `do` notation discharged: deserialize, then demand the decode consumed
the whole body and that re-serializing reproduces it byte for byte.

Stated as a rewrite because the `do` block does not simplify on its own, and every evaluation below
would otherwise get stuck on the same bind. -/
theorem decodeCanonical_eq (schema : SSZType) (body : ByteArray) :
    SszBridge.decodeCanonical schema body =
      match schema.deserialize body with
      | .error error => .error error
      | .ok (value, used) =>
          if used != body.size then .error .trailingBytes
          else if schema.serialize value == body then .ok value else .error .invalidOffset := by
  unfold SszBridge.decodeCanonical
  cases schema.deserialize body <;> rfl

/-- Zero bytes decode to `none`: the element type is fixed-size, so the count is `0 / 24 = 0`, the
empty list re-serializes to the empty buffer, and the projection of an empty array is `none`. -/
theorem meaningEmptyIsNone_holds : meaningEmptyIsNone := by
  have hserialize := SSZType.serializeFixedElems.eq_1
    (SSZType.container [SSZType.uintN 64, SSZType.uintN 64, SSZType.uintN 64])
  have hempty : (ByteArray.empty == ByteArray.empty) = true := by decide
  simp [meaningEmptyIsNone, meaningOptionalBlobSchedule, decodeCanonical_eq,
    optionalBlobScheduleType, SSZType.deserialize, SSZType.isFixedSize, SszBridge.blobScheduleType,
    SszBridge.u64, SSZType.fixedByteSize, SSZType.deserializeFixedElems, SSZType.serialize,
    SSZType.allFixedSize, SSZType.fixedByteSizeFields, SszBridge.maxBlobSchedulesPerFork,
    hserialize, hempty]

/-- **Every length other than 0 and 24 is `invalidSsz`.**

The two rejections are the oracle's own, and which one fires is genuinely input-dependent: more than
one element's worth of bytes is `outOfRange`, and anything that is not a whole number of 24-byte
elements is `trailingBytes`. What rules out the remaining case is arithmetic — a size that survives
both checks has `size / 24 ≤ 1` and `size / 24 * 24 = size`, which for `size ∉ {0, 24}` is
impossible. Both normalize to `invalidSsz` at the Zig boundary. -/
theorem meaningOtherLengthIsInvalid_holds : meaningOtherLengthIsInvalid := by
  intro bytes hzero htwentyFour
  by_cases hbig : bytes.size / 24 > 1
  · simp [meaningOptionalBlobSchedule, decodeCanonical_eq, optionalBlobScheduleType,
      SSZType.deserialize, SSZType.isFixedSize, SszBridge.blobScheduleType, SszBridge.u64,
      SSZType.fixedByteSize, SSZType.allFixedSize, SSZType.fixedByteSizeFields,
      SszBridge.maxBlobSchedulesPerFork, hbig, sszToDecodeError]
  · have htrailing : bytes.size / 24 * 24 ≠ bytes.size := by omega
    simp [meaningOptionalBlobSchedule, decodeCanonical_eq, optionalBlobScheduleType,
      SSZType.deserialize, SSZType.isFixedSize, SszBridge.blobScheduleType, SszBridge.u64,
      SSZType.fixedByteSize, SSZType.allFixedSize, SSZType.fixedByteSizeFields,
      SszBridge.maxBlobSchedulesPerFork, hbig, htrailing, sszToDecodeError]

/-- **A zero-length `byteListList` still allocates.**

The source takes `alloc.alloc([]const u8, 0)` rather than returning a static empty slice, so a
postcondition denying allocation would be false even here. The meaning side of that is this: the
empty input really is *accepted*, with an empty result, for every pair of runtime bounds — the
element type is variable-size, so the decoder takes the explicit empty-list arm before it ever reads
an offset, and the bounds never come into it. -/
theorem emptyByteListListIsEmptyArray_holds : emptyByteListListIsEmptyArray := by
  intro maxItems maxItemBytes
  have hserialize := SSZType.serializeVarElemsAux.eq_1 (SszBridge.u8.list maxItemBytes) 0
  have hempty : (ByteArray.empty == ByteArray.empty) = true := by decide
  simp [meaningByteListList, decodeCanonical_eq, byteListListType, SszBridge.byteList,
    SSZType.deserialize, SSZType.isFixedSize, SSZType.serialize, hserialize, hempty]

/-! ### Toward the zero-first-offset alias

`zeroFirstOffsetAliasRejected` is stated against the bridge's framing reader `readU32LE?`, while the
list decoder consults the spec's own `readUInt32LE`. The two read the same four bytes but are
different functions, so the obligation cannot even reach the decode path without this bridge.

The rest of that obligation is blocked, not unproved: the decoder's offset-table walker
`extractCollOffsets` is `private` in the pinned `Spec/Deserialize.lean`, so its zero-count equation
(`… b 0 off = .ok []`) can neither be named nor unfolded here, and the value the decode produces
stays opaque. Upstream de-privatised its bit-packing definitions for exactly this reason (see
`Spec/Deserialize.lean`'s note that they are "public defs (not `private`) so the Layer 2
bit-packing inverse proof in `Proofs/BitPack.lean` can reach them"), so the precedent for lifting it
is upstream's own. -/

/-- **A zero first offset in the bridge's reader is a zero first offset in the spec's.**

Both read the four leading bytes little-endian; the bridge's returns a `Nat` and the spec's a
`UInt32`, which is the whole of the difference. A sum of four byte values weighted by powers of 256
is zero exactly when every byte is zero, and on all-zero bytes the spec's shift-and-or reader is zero
too. -/
theorem readUInt32LE_zero_of_readU32LE (bytes : ByteArray) (size : bytes.size ≥ 4)
    (zero : SszBridge.readU32LE? bytes 0 = some 0) : readUInt32LE bytes 0 = some 0 := by
  rw [SszBridge.readU32LE?] at zero
  split at zero
  · exact absurd zero (by simp)
  · simp only [Option.some.injEq] at zero
    have h0 := (bytes.get! 0).toNat_lt_size
    have h1 := (bytes.get! (0 + 1)).toNat_lt_size
    have h2 := (bytes.get! (0 + 2)).toNat_lt_size
    have h3 := (bytes.get! (0 + 3)).toNat_lt_size
    have zeroNat : (0 : UInt8).toNat = 0 := rfl
    have z0 : bytes.get! 0 = 0 := UInt8.toNat_inj.mp (by rw [zeroNat]; omega)
    have z1 : bytes.get! (0 + 1) = 0 := UInt8.toNat_inj.mp (by rw [zeroNat]; omega)
    have z2 : bytes.get! (0 + 2) = 0 := UInt8.toNat_inj.mp (by rw [zeroNat]; omega)
    have z3 : bytes.get! (0 + 3) = 0 := UInt8.toNat_inj.mp (by rw [zeroNat]; omega)
    rw [SpecCorrespondence.get!_eq_getElem bytes 0 (by omega)] at z0
    rw [SpecCorrespondence.get!_eq_getElem bytes (0 + 1) (by omega)] at z1
    rw [SpecCorrespondence.get!_eq_getElem bytes (0 + 2) (by omega)] at z2
    rw [SpecCorrespondence.get!_eq_getElem bytes (0 + 3) (by omega)] at z3
    rw [readUInt32LE]
    split
    · simp [z0, z1, z2, z3]
    · omega

/-! ### The general reader bridge

The zero-value bridge above is what `zeroFirstOffsetAliasRejected` needs, but it is not the only
obligation phrased against the wrong reader. `retryTailNeverSchemaValid`'s second hypothesis is
`SszBridge.readU32LE? (bytes.extract 2 bytes.size) 0 = some 16`, while the entry meaning reads that
same offset through `meaningReadOffset` → `meaningReadU32` → `readUInt32LE`. A consumer holding the
meaning's form could not apply the obligation at all. `meaningHasExactErePrefix`'s docstring is
explicit that the bridge's framing reader is the right choice "here and only here", so this is a
mismatch rather than a convention, and the fix is to relate the two readers once and for all.

**Axioms.** `or_shifts_toNat` closes its byte-lane identity with `bv_decide`, so it and
`readU32LE?_eq_map_readUInt32LE` carry `Lean.ofReduceBool`/`Lean.trustCompiler`. The zero-value
bridge above is *not* rewritten as a corollary of them for exactly that reason: its own proof is
axiom-clean, and collapsing the two would spend that for nothing. -/

/-- Four bytes OR-ed into their little-endian lanes have the weighted-sum value.

The lanes are disjoint, so the OR is an addition; `bv_decide` settles that at `UInt32`, and the
remaining step is that the sum of four byte values weighted by powers of 256 cannot overflow. -/
theorem or_shifts_toNat (x0 x1 x2 x3 : UInt8) :
    (x0.toUInt32 ||| x1.toUInt32 <<< 8 ||| x2.toUInt32 <<< 16 ||| x3.toUInt32 <<< 24).toNat
      = x0.toNat + x1.toNat * 256 + x2.toNat * 256 ^ 2 + x3.toNat * 256 ^ 3 := by
  have key : (x0.toUInt32 ||| x1.toUInt32 <<< 8 ||| x2.toUInt32 <<< 16 ||| x3.toUInt32 <<< 24)
      = x0.toUInt32 + x1.toUInt32 * 256 + x2.toUInt32 * 65536 + x3.toUInt32 * 16777216 := by
    bv_decide
  rw [key]
  have hsize : UInt8.size = 256 := rfl
  have h0 := x0.toNat_lt_size
  have h1 := x1.toNat_lt_size
  have h2 := x2.toNat_lt_size
  have h3 := x3.toNat_lt_size
  simp [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32]
  omega

/-- **The bridge's framing reader is the spec's reader, widened.**

At every offset and every value, including out of bounds — both guard on `offset + 4 ≤ size` and
neither has a failure mode the other lacks. This is what lets an obligation stated with
`SszBridge.readU32LE?` be applied to a decode path that reads with `readUInt32LE`. -/
theorem readU32LE?_eq_map_readUInt32LE (bytes : ByteArray) (offset : Nat) :
    SszBridge.readU32LE? bytes offset = (readUInt32LE bytes offset).map UInt32.toNat := by
  rw [SszBridge.readU32LE?, readUInt32LE]
  split
  · rw [dif_neg (by omega)]
    rfl
  · rw [dif_pos (by omega)]
    rw [← SpecCorrespondence.get!_eq_getElem bytes offset (by omega),
      ← SpecCorrespondence.get!_eq_getElem bytes (offset + 1) (by omega),
      ← SpecCorrespondence.get!_eq_getElem bytes (offset + 2) (by omega),
      ← SpecCorrespondence.get!_eq_getElem bytes (offset + 3) (by omega)]
    exact congrArg some (or_shifts_toNat _ _ _ _).symm

/-- The form a consumer of `retryTailNeverSchemaValid` actually holds: the meaning's offset read
determines the bridge reader's value. -/
theorem readU32LE?_of_meaningReadOffset (bytes : ByteArray) (offset value : Nat)
    (read : meaningReadOffset bytes offset = .ok value) :
    SszBridge.readU32LE? bytes offset = some value := by
  rw [readU32LE?_eq_map_readUInt32LE]
  rw [meaningReadOffset, meaningReadU32] at read
  cases h : readUInt32LE bytes offset with
  | none => rw [h] at read; simp [Option.toDecodeResult, Except.map] at read
  | some widened =>
      rw [h] at read
      simp only [Option.toDecodeResult, Except.map, Except.ok.injEq] at read
      simp [read]

/-! ## What the semantic obligations still rest on

The two obligations the navigation calls out as carrying the root theorem —
`sourceShapedDecodeAgreesWithOracle` and `catalogGroundsInSpec` — are not independent, and saying so
is worth a theorem rather than a comment: the second follows from the first, because `SszSpec.decode`
is exactly `decodeStatelessInput` with its value forgotten. So the catalog's remaining semantic
content is one agreement claim about the entry, one about the fixed containers, and three
byte-level facts. -/

/-- **The catalog's meanings are grounded in the pinned oracle** — given that the source-shaped
composition and the oracle agree on acceptance. `SszSpec.decode` accepts exactly when
`decodeStatelessInput` returns a value, so the two statements differ only in how they spell
"accepted". -/
theorem catalogGroundsInSpec_of_agreement (agrees : sourceShapedDecodeAgreesWithOracle) :
    catalogGroundsInSpec := by
  intro bytes
  rw [agrees bytes]
  unfold SszSpec.decode
  cases SszBridge.decodeStatelessInput bytes with
  | ok value => simp [Except.toOption]
  | error error => simp [Except.toOption]

/-- **The catalog's semantic obligations, reduced to the oracle-agreement content.**

Fifteen of the twenty conjuncts are discharged above; the five premises here are what is left, and
they are all of one kind — the binary decides canonicality by per-container offset checks while the
oracle decides it by re-serializing, and these say the two coincide. `catalogGroundsInSpec` is not a
premise because it follows from the first one. -/
theorem catalogSemanticObligations_of_oracleAgreement
    (entryAgrees : sourceShapedDecodeAgreesWithOracle)
    (containersAgree : sourceShapedContainersAgreeWithOracle)
    (v3Excluded : v3ShapeExcludesCanonicalV4) (zeroAlias : zeroFirstOffsetAliasRejected)
    (twentyFourIsSome : meaningTwentyFourIsSome) : catalogSemanticObligations :=
  ⟨entryAgrees, catalogGroundsInSpec_of_agreement entryAgrees, retryTailNeverSchemaValid_holds,
    v3Excluded, containersAgree, canonicalOffsetsCharacterization_holds, zeroAlias,
    bytesAtSucceedsIffFits_holds, readOffsetIsWidenedReadU32_holds, leafReadsOnlyFailInvalid_holds,
    collectionsNeverUnknownFork_holds, emptyByteListListIsEmptyArray_holds,
    onlyForkConfigRaisesUnknownFork_holds, fixedContainersNeverAllocate_holds,
    allocatorVtableEntriesAreConstant_holds, outOfMemoryUnreachableBelowBound_holds,
    meaningEmptyIsNone_holds, twentyFourIsSome, meaningOtherLengthIsInvalid_holds,
    meaningNeverForkOrMemory_holds⟩

/-! ## The fork-ordering divergence

`forkErrorOrderingDiffers` is one half of `knownDivergences`. It is an existential, so it needs a
witness and both of the witness's facts.

**Why the oracle half is not the `decodeCanonical_eq` cascade.** Rewriting with `decodeCanonical_eq`
works and leaves a `match` on `forkConfigType.deserialize`, which is where it stops: reducing that
needs upstream's `extractFieldOffsets`, and that definition is `private` in the pinned
`Spec/Deserialize.lean` — the same obstacle as `extractCollOffsets`, one definition over. `rfl` and
`decide` do not reach it either, since `deserialize` is well-founded rather than structural, so the
kernel gets no unfolding from it.

**Axioms, and why this costs nothing.** `native_decide` puts `Lean.ofReduceBool` and
`Lean.trustCompiler` on this theorem. `BinaryFv.SSZ.binary_is_canonical` — and so `root_compliance` —
already depends on both, from the pinned-artifact facts, so the root's trust class is unchanged.
`catalogSemanticObligations_of_oracleAgreement` is a separate declaration and stays clean. If the
`extractCollOffsets` shim lands and is widened to `extractFieldOffsets`, this becomes provable by
reduction and the axioms can be dropped. -/

/-- The oracle's side: a structural rejection, having never reached the fork bound. -/
theorem decodeCanonical_forkOrderingWitness :
    (SszBridge.decodeCanonical SszBridge.forkConfigType forkOrderingWitness).toOption = none := by
  have h : (SszBridge.decodeCanonical SszBridge.forkConfigType forkOrderingWitness).toOption.isNone
      = true := by native_decide
  simpa using h

/-- **The two reject the same input with different errors.** Both still reject, which is all
`root_compliance` observes — naming this is what stops a container contract from claiming the error
constructors agree. -/
theorem forkErrorOrderingDiffers_holds : forkErrorOrderingDiffers :=
  ⟨forkOrderingWitness, meaningForkConfig_forkOrderingWitness, decodeCanonical_forkOrderingWitness⟩

end BinaryFv.SSZ.Zesu.Contracts
