import ZesuExec.Compliance.RlpUint
import ZesuExec.Compliance.F2
import ZesuExec.Fn.F3.Sail

/-!
# F3 `rlp_decode.nextUint64`: compliance with EVM-Sail's item-then-uint64 decoding

zesislar has no stand-alone Sail statement for `nextUint64`: `NextUint64Meaning.v` notes that
"`rlp_decode_uint64` agrees with this meaning in one direction only … the code also accepts a
leading zero (`82 00 01`) and zero written as `00`, which Sail rejects; that is a registered
known bug" (`RlpUintNonCanonical`, `KnownBugs.v`), and the parent-header meaning
(`ParentHeaderRung2.v`, `ParentHeaderBugTriggers.v`) uses the same class through
`sailShortUintCanonical`. This file states that comparison for `nextUint64` alone.

(a) The candidate is `ZesuExec.Fn.F3.nextUint64` (`nextUint64RootResult`): `f3_spec`'s `Post`
states the result and slice bytes through it.

(b) `sailRun input σ` is what EVM-Sail's parent-header decoder does at an integer field
(`_rec_decode_parent_header_fields`, fields 17 and 18): `rlp_decode_item` on a cursor over the
whole input, then `rlp_decode_uint64` on the field, the cursor advancing by the field's full
length. `f3_candidate_agrees`: Sail's value and advance relate to `nextUint64 input`
(`SailRelates`), or `rlpUintNonCanonical` applies: the binary folds a string of at most 8 bytes
that Sail's `rlp_item_uint_canonical` rejects (`uintCanon … = false`; this is
`sailShortUintCanonical`). The wrap class cannot arise: a non-list item of at most 8 payload
bytes has header length at most 9.

(c) `f3_compliance`: from every machine at the entry satisfying `Pre`, the machine reaches
within `bound` a state satisfying `Post` whose input satisfies
`NextUint64MeaningModuloKnownBugs`; `f3_compliance_sail` transfers it by `sail_reaches`.
-/

namespace ZesuExec.Compliance.F3
open ZesuExec ZesuExec.Fn.F3 ZesuExec.Compliance
open ZesuExec.Compliance.F2 (ofSail item_agrees)
open ZesuExec.Fn.F2 (Item bigEndian decode checkedPayload)

/-! ## EVM-Sail on an input -/

/-- `rlp_decode_item` then `rlp_decode_uint64` on a cursor over the whole input: the value and
the field's full length (the cursor advance). -/
def sailNext (input : List Byte) : Evm.SailM (Nat × Nat) := do
  let ⟨_, ⟨full, field⟩⟩ ←
    Evm.Functions.rlp_decode_item (k_source_off := 0) (k_source_len := input.length) {}
  let v ← Evm.Functions.rlp_decode_uint64 field
  pure (v, full)

abbrev SailNextResult := EStateM.Result (Sail.Error Unit) SailRegs ((Nat × Nat) × Evm.HostState)

/-- `sailNext` with the stateless input holding `input`, from register state `σ`. -/
def sailRun (input : List Byte) (σ : SailRegs) : SailNextResult :=
  ((sailNext input).run (hostOf input)).run σ

/-- A Sail value `v < 2^64` with advance `c` is the candidate's `some (v, c)`; the `fatal_error`
exit is `none`; any other failure relates to nothing. -/
def SailRelates : SailNextResult → Option (Word × Nat) → Prop
  | .ok ((v, c), _) _, r => v < 2 ^ 64 ∧ r = some (BitVec.ofNat 64 v, c)
  | .error .Exit _, r => r = none
  | .error _ _, _ => False

/-! ## Closed form of the Sail run -/

theorem bigEndian_foldl_lt (bs : List Byte) (a : Nat) :
    bs.foldl (fun acc b => 256 * acc + b.toNat) a < (a + 1) * 256 ^ bs.length := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hb := b.isLt
    simp only [List.foldl_cons, List.length_cons]
    have := ih (256 * a + b.toNat)
    have h2 : (256 * a + b.toNat + 1) * 256 ^ bs.length ≤ (a + 1) * 256 ^ (bs.length + 1) := by
      have h3 : 256 * a + b.toNat + 1 ≤ 256 * (a + 1) := by omega
      calc (256 * a + b.toNat + 1) * 256 ^ bs.length ≤ 256 * (a + 1) * 256 ^ bs.length :=
            Nat.mul_le_mul_right _ h3
        _ = (a + 1) * 256 ^ (bs.length + 1) := by
            rw [Nat.pow_succ, Nat.mul_comm 256 (a + 1), Nat.mul_assoc, Nat.mul_comm 256]
    omega

theorem bigEndian_take_lt (bs : List Byte) (w : Nat) (hw : w ≤ 8) :
    bigEndian (bs.take w) < 2 ^ 64 := by
  have h := bigEndian_foldl_lt (bs.take w) 0
  have hl : (bs.take w).length ≤ 8 := by simp; omega
  have : 256 ^ (bs.take w).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hl
  simp only [bigEndian] at *
  omega

theorem sailItem_len_lt (input : List Byte) (l : Bool) (off len : Nat)
    (h : sailItem input = some (l, off, len)) :
    0 < off + len ∧ off + len ≤ input.length ∧ len < 2 ^ 64 := by
  unfold sailItem at h
  split at h
  · cases h
  · rename_i l' off' len' hh
    split at h
    · cases h
      rename_i hc
      refine ⟨hc.1, hc.2, ?_⟩
      unfold sailHeader at hh
      split at hh
      · cases hh
      · rename_i b rest
        have hb := b.isLt
        simp only at hh
        by_cases c1 : b.toNat < 128
        · rw [if_pos c1] at hh; cases hh; omega
        rw [if_neg c1] at hh
        by_cases c2 : b.toNat < 184
        · rw [if_pos c2] at hh; cases hh; omega
        rw [if_neg c2] at hh
        by_cases c3 : b.toNat < 192
        · rw [if_pos c3] at hh
          split at hh
          · simp only [Option.some.injEq, Prod.mk.injEq] at hh
            rw [← hh.2.2]; exact bigEndian_take_lt _ _ (by omega)
          · cases hh
        rw [if_neg c3] at hh
        by_cases c5 : b.toNat < 248
        · rw [if_pos c5] at hh; cases hh; omega
        rw [if_neg c5] at hh
        split at hh
        · simp only [Option.some.injEq, Prod.mk.injEq] at hh
          rw [← hh.2.2]; exact bigEndian_take_lt _ _ (by omega)
        · cases hh
    · cases h

/-- What Sail returns, in closed form. -/
theorem sailRun_eq (input : List Byte) (σ : SailRegs) :
    sailRun input σ =
      match sailItem input with
      | none => .error .Exit σ
      | some (l, off, len) =>
        if l = false ∧ len ≤ 8 ∧ uintCanon input.toArray off len = true then
          .ok ((bigEndian ((input.drop off).take len), off + len), hostOf input) σ
        else .error .Exit σ := by
  unfold sailRun sailNext
  have hi := decode_item_eval input (hostOf input) rfl σ {}
  rcases hs : sailItem input with _ | ⟨l, off, len⟩
  · rw [hs] at hi
    exact run_bind_error _ _ _ _ _ hi
  · rw [hs] at hi
    rw [run_bind_ok _ _ _ _ _ hi]
    obtain ⟨hpos, hfit, hlt⟩ := sailItem_len_lt input l off len hs
    have hu := decode_uint64_eval input (hostOf input) rfl σ l off len hfit hpos
      (Nat.lt_trans hlt (by decide))
    simp only [hostOf] at hu ⊢
    split
    · next hc =>
      rw [if_pos hc] at hu
      rw [run_bind_ok _ _ _ _ _ hu]
      rfl
    · next hc =>
      rw [if_neg hc] at hu
      exact run_bind_error _ _ _ _ _ hu

/-! ## (b) The candidate agrees with Sail modulo known bugs -/

/-- `RlpUintNonCanonical` for `nextUint64`: the candidate folds a non-list item of at most 8
payload bytes whose encoding Sail's `rlp_item_uint_canonical` rejects, and Sail exits. The other
classes belong to other functions. -/
def bugApplies : KnownBug → List Byte → SailRegs → Prop
  | .rlpUintNonCanonical, input, σ =>
    ∃ h p, decode input = .success false h p ∧ p ≤ 8 ∧
      uintCanon input.toArray h p = false ∧ ∃ σ', sailRun input σ = .error .Exit σ'
  | _, _, _ => False

/-- `decode`'s header length is at most 9. -/
theorem decode_header_le (input : List Byte) (l : Bool) (h p : Nat)
    (hd : decode input = .success l h p) : h ≤ 9 := by
  unfold decode at hd
  split at hd
  · cases hd
  · rename_i b rest
    simp only at hd
    have hc : ∀ len h' p' l', checkedPayload len h' p' l' = .success l h p → h = h' := by
      intro len h' p' l' hc
      unfold checkedPayload at hc
      split at hc
      · cases hc; rfl
      · cases hc
    by_cases c1 : b.toNat ≤ 127
    · rw [if_pos c1] at hd; cases hd; omega
    rw [if_neg c1] at hd
    by_cases c0 : b.toNat = 128
    · rw [if_pos c0] at hd; cases hd; omega
    rw [if_neg c0] at hd
    by_cases c2 : b.toNat ≤ 183
    · rw [if_pos c2] at hd; rw [hc _ _ _ _ hd]; omega
    rw [if_neg c2] at hd
    by_cases c3 : b.toNat ≤ 191
    · rw [if_pos c3] at hd
      split at hd
      · rw [hc _ _ _ _ hd]; omega
      · cases hd
    rw [if_neg c3] at hd
    by_cases c5 : b.toNat ≤ 247
    · rw [if_pos c5] at hd; rw [hc _ _ _ _ hd]; omega
    rw [if_neg c5] at hd
    split at hd
    · have := b.isLt; rw [hc _ _ _ _ hd]; omega
    · cases hd

theorem f3_candidate_agrees (input : List Byte) (σ : SailRegs) :
    SailRelates (sailRun input σ) (nextUint64 input) ∨
      ∃ bug ∈ knownBugs, bugApplies bug input σ := by
  rw [sailRun_eq]
  rcases item_agrees input with hd | ⟨l, h, p, hd, hw, hs⟩
  · rcases hs : sailItem input with _ | ⟨l, off, len⟩
    · left
      rw [hs] at hd
      simp only [SailRelates, nextUint64, hd, ofSail]
    · rw [hs] at hd
      simp only [ofSail] at hd
      obtain ⟨-, -, hlt⟩ := sailItem_len_lt input l off len hs
      by_cases hc : l = false ∧ len ≤ 8 ∧ uintCanon input.toArray off len = true
      · left
        dsimp only
        rw [if_pos hc]
        obtain ⟨rfl, h8, -⟩ := hc
        simp only [SailRelates, nextUint64, hd, if_pos h8]
        exact ⟨bigEndian_take_lt _ _ h8, by trivial⟩
      · dsimp only
        rw [if_neg hc]
        by_cases hl : l = false ∧ len ≤ 8
        · right
          obtain ⟨rfl, h8⟩ := hl
          refine ⟨.rlpUintNonCanonical, by simp [knownBugs], off, len, hd, h8, ?_, σ, ?_⟩
          · simpa [h8] using hc
          · rw [sailRun_eq, hs]; dsimp only; rw [if_neg hc]
        · left
          simp only [SailRelates, nextUint64, hd]
          cases l
          · simp only [if_neg (fun h8 => hl ⟨rfl, h8⟩)]
          · rfl
  · left
    rw [hs]
    simp only [SailRelates, nextUint64, hd]
    have := decode_header_le input l h p hd
    cases l
    · dsimp only
      rw [if_neg (by omega)]
    · rfl

/-! ## (c) Compliance of the binary -/

/-- The input's meaning: for every Sail register state, Sail's result relates to the candidate
`nextUint64 input` (in whose terms `Post` states the result and slice bytes), or a listed known
bug applies. -/
def NextUint64MeaningModuloKnownBugs (input : List Byte) : Prop :=
  ∀ σ, SailRelates (sailRun input σ) (nextUint64 input) ∨
    ∃ bug ∈ knownBugs, bugApplies bug input σ

/-- The final-state property of `f3_compliance`: `Post`, and the input slice's bytes satisfy the
meaning. -/
def Compliant (m m' : Machine) : Prop :=
  Post m m' ∧
  ∀ input, BytesAt m (wordAt m (m.reg 11)) input →
    input.length = (wordAt m (m.reg 11 + 8)).toNat → NextUint64MeaningModuloKnownBugs input

theorem f3_compliance (m : Machine) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    Reaches zesuImage bound (Compliant m) m :=
  (f3_spec m hpc hpre).mono (Nat.le_refl _) fun _ hp =>
    ⟨hp, fun input _ _ σ => f3_candidate_agrees input σ⟩

/-- `f3_compliance` on the Sail RISC-V model, by `sail_reaches`. -/
theorem f3_compliance_sail {m : Machine} {s : BinaryFv.RiscV.State}
    (h : SailLink.Rel zesuImage m s) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailLink.SailReaches zesuImage bound
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant m m') s :=
  SailLink.sail_reaches h (f3_compliance m hpc hpre)

/-! ## Witnesses -/

/-- `82 00 01`: a leading zero, folded by the binary, rejected by Sail. -/
example : nextUint64 [0x82, 0x00, 0x01] = some (1, 3) ∧
    ∀ σ, bugApplies .rlpUintNonCanonical [0x82, 0x00, 0x01] σ := by
  have hd : decode [0x82, 0x00, 0x01] = .success false 1 2 := by decide
  have hs : sailItem [0x82, 0x00, 0x01] = some (false, 1, 2) := by decide
  have hc : uintCanon [0x82, 0x00, 0x01].toArray 1 2 = false := by decide
  refine ⟨by decide, fun σ => ⟨1, 2, hd, by decide, hc, σ, ?_⟩⟩
  rw [sailRun_eq, hs]
  dsimp only
  rw [if_neg (by decide)]

/-- `82 01 00`: canonical; Sail and the binary both return 256 and advance 3. -/
example (σ : SailRegs) : SailRelates (sailRun [0x82, 0x01, 0x00] σ) (nextUint64 [0x82, 0x01, 0x00]) := by
  have hs : sailItem [0x82, 0x01, 0x00] = some (false, 1, 2) := by decide
  have hc : uintCanon [0x82, 0x01, 0x00].toArray 1 2 = true := by decide
  rw [sailRun_eq, hs]
  dsimp only
  rw [if_pos ⟨rfl, by decide, hc⟩]
  exact ⟨by decide, by decide⟩

/--
info: 'ZesuExec.Compliance.F3.f3_candidate_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f3_candidate_agrees

/--
info: 'ZesuExec.Compliance.F3.f3_compliance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f3_compliance

/--
info: 'ZesuExec.Compliance.F3.f3_compliance_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f3_compliance_sail

end ZesuExec.Compliance.F3
