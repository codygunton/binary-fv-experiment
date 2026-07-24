import BinaryFv.SSZ.Zesu.Contracts.Catalog

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
    (meaningReadU64_onlyInvalid bytes offset).ne (by simp)⟩

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

/-- `decodeForkConfig` is the decoder's only source of `unknownFork`. -/
theorem onlyForkConfigRaisesUnknownFork_holds : onlyForkConfigRaisesUnknownFork := fun bytes =>
  ⟨(meaningForkActivation_onlyInvalid bytes).ne (by simp),
    (meaningExecutionWitness_onlyInvalid bytes).ne (by simp),
    (meaningExecutionRequests_onlyInvalid bytes).ne (by simp),
    (meaningExecutionPayload_onlyInvalid bytes).ne (by simp)⟩

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
discharge­able rather than normalizable, and it is why the scope hypothesis is not used.

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

end BinaryFv.SSZ.Zesu.Contracts
