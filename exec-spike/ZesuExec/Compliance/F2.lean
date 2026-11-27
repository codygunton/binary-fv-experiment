import ZesuExec.Compliance.RlpItem
import ZesuExec.Compliance.KnownBugs
import ZesuExec.Fn.F2.Sail

/-!
# F2 `rlp.decodeItem`: compliance with EVM-Sail's `rlp_decode_item`

Transcribes zesislar's `DecodeMeaningModuloKnownBugs` (`ZesuSsz/Contracts/RlpDecodeItemContract.v`)
with `relateItem` (`RlpDecodeItemSchema.v`) and `runRlpDecodeItem` (`ZesuSsz/Compliance/SailRun.v`).

(a) The candidate is `ZesuExec.Fn.F2.decode` (`candidateDecodeItem`), and `f2_spec`'s `Post`
states the outcome struct as `result40` of it.

(b) `sailRun input σ` is EVM-Sail's `rlp_decode_item` on a cursor over the whole stateless-input
region, the region holding `input` (`hostOf`), from Sail register state `σ`.
`f2_candidate_agrees`: for every input and `σ`, either Sail's result relates to `decode input`
(`SailRelates`: a returned field gives `.success is_list (full - content) content`, the
`fatal_error RlpDecode` exit gives `.error`), or a listed known bug applies; only
`rlpLongLengthWrap` can apply to this function (the binary's consumed length wraps modulo `2^64`
and Sail rejects).

(c) `f2_compliance`: from every machine at the entry satisfying `Pre`, the machine reaches within
`bound` a state satisfying `Post` whose outcome bytes satisfy `DecodeMeaningModuloKnownBugs`;
`f2_compliance_sail` transfers it to the Sail RISC-V model by `sail_reaches`.
-/

namespace ZesuExec.Compliance.F2
open ZesuExec ZesuExec.Fn.F2 ZesuExec.Compliance

/-! ## EVM-Sail's item decoder on an input -/

/-- The type of `rlp_decode_item`'s run on a source of offset 0. -/
abbrev SailItemResult :=
  EStateM.Result (Sail.Error Unit) SailRegs
    (((c : Nat) × (f : Nat) × Evm.Defs.RlpFieldRef 0 f c) × Evm.HostState)

/-- `runRlpDecodeItem`: EVM-Sail `rlp_decode_item` with the stateless input holding `input`, on
the cursor over all of it, from register state `σ`. -/
def sailRun (input : List Byte) (σ : SailRegs) : SailItemResult :=
  ((Evm.Functions.rlp_decode_item (k_source_off := 0) (k_source_len := input.length) {}).run
    (hostOf input)).run σ

/-- `relateItem` on items: a returned field is a success with header length `full - content`
and payload length `content`; the `fatal_error` exit is the error item; any other failure
relates to nothing. -/
def SailRelates : SailItemResult → Item → Prop
  | .ok (⟨content, full, field⟩, _) _, it => it = .success field.is_list (full - content) content
  | .error .Exit _, it => it = .error
  | .error _ _, _ => False

/-- What Sail returns, in closed form (`decode_item_eval`). -/
theorem sailRun_eq (input : List Byte) (σ : SailRegs) :
    sailRun input σ =
      match sailItem input with
      | some (l, off, len) => .ok (⟨len, ⟨off + len, ⟨{}, l⟩⟩⟩, hostOf input) σ
      | none => .error .Exit σ :=
  decode_item_eval input (hostOf input) rfl σ {}

/-! ## Known bugs -/

/-- `decodeItemBugApplies`: the wrap class needs a candidate success whose header plus payload
length reaches `2^64` (`binaryWrapCase`) while Sail rejects; the other classes belong to other
functions. -/
def bugApplies : KnownBug → List Byte → SailRegs → Prop
  | .rlpLongLengthWrap, input, σ =>
    ∃ isList h p, decode input = .success isList h p ∧ 2 ^ 64 ≤ h + p ∧
      ∃ σ', sailRun input σ = .error .Exit σ'
  | _, _, _ => False

/-! ## (b) The candidate agrees with Sail modulo known bugs -/

/-- A Sail field `(is_list, header, payload)` as a candidate item; a rejection is the error. -/
def ofSail : Option (Bool × Nat × Nat) → Item
  | none => .error
  | some (l, h, p) => .success l h p

theorem checked_fit (len h p : Nat) (l : Bool) (hf : h + p ≤ len) :
    checkedPayload len h p l = .success l h p := by
  have := Nat.mod_le (h + p) (2 ^ 64)
  simp only [checkedPayload, if_pos (Nat.le_trans this hf)]

theorem checked_nofit (len h p : Nat) (l : Bool) (hf : ¬ h + p ≤ len) (hw : h + p < 2 ^ 64) :
    checkedPayload len h p l = .error := by
  simp only [checkedPayload, Nat.mod_eq_of_lt hw, if_neg hf]

/-- A form whose Sail item is `if fits then some (l, h, p) else none`. -/
theorem form_agrees (len h p : Nat) (l : Bool) (hh : 0 < h) :
    checkedPayload len h p l = ofSail (if 0 < h + p ∧ h + p ≤ len then some (l, h, p) else none) ∨
      checkedPayload len h p l = .success l h p ∧ 2 ^ 64 ≤ h + p ∧
        (if 0 < h + p ∧ h + p ≤ len then some (l, h, p) else none) = none := by
  by_cases hf : h + p ≤ len
  · rw [if_pos ⟨by omega, hf⟩]
    exact .inl (checked_fit _ _ _ _ hf)
  · rw [if_neg (fun h => hf h.2)]
    by_cases hw : h + p < 2 ^ 64
    · exact .inl (checked_nofit _ _ _ _ hf hw)
    · unfold checkedPayload
      split
      · exact .inr ⟨rfl, by omega, rfl⟩
      · exact .inl rfl

/-- The pure core of (b): `decode` is `sailItem` read as an item, except on a wrapping success. -/
theorem item_agrees (input : List Byte) :
    decode input = ofSail (sailItem input) ∨
      ∃ l h p, decode input = .success l h p ∧ 2 ^ 64 ≤ h + p ∧ sailItem input = none := by
  cases input with
  | nil => exact .inl rfl
  | cons b rest =>
    have hb : b.toNat < 256 := b.isLt
    simp only [sailItem, sailHeader, decode, List.length_cons]
    by_cases c1 : b.toNat < 128
    · rw [if_pos (show b.toNat ≤ 127 by omega), if_pos c1]
      dsimp only
      rw [if_pos (by omega)]
      exact .inl rfl
    rw [if_neg (show ¬ b.toNat ≤ 127 by omega), if_neg c1]
    by_cases c2 : b.toNat < 184
    · rw [if_pos c2]
      by_cases c0 : b.toNat = 128
      · rw [if_pos c0]
        dsimp only
        rw [if_pos (by omega)]
        simp only [c0]
        exact .inl rfl
      · rw [if_neg c0, if_pos (show b.toNat ≤ 183 by omega)]
        dsimp only
        rcases form_agrees (rest.length + 1) 1 (b.toNat - 128) false (by omega) with h | ⟨h1, h2, h3⟩
        · exact .inl h
        · exact .inr ⟨_, _, _, h1, h2, h3⟩
    rw [if_neg (show ¬ b.toNat = 128 by omega), if_neg (show ¬ b.toNat ≤ 183 by omega), if_neg c2]
    by_cases c3 : b.toNat < 192
    · rw [if_pos (show b.toNat ≤ 191 by omega), if_pos c3]
      by_cases c4 : b.toNat - 183 ≤ rest.length
      · rw [if_pos c4, if_pos (show 1 + (b.toNat - 183) ≤ rest.length + 1 by omega)]
        dsimp only
        rcases form_agrees (rest.length + 1) (1 + (b.toNat - 183))
          (bigEndian (rest.take (b.toNat - 183))) false (by omega) with h | ⟨h1, h2, h3⟩
        · exact .inl h
        · exact .inr ⟨_, _, _, h1, h2, h3⟩
      · rw [if_neg c4, if_neg (show ¬ 1 + (b.toNat - 183) ≤ rest.length + 1 by omega)]
        exact .inl rfl
    rw [if_neg (show ¬ b.toNat ≤ 191 by omega), if_neg c3]
    by_cases c5 : b.toNat < 248
    · rw [if_pos (show b.toNat ≤ 247 by omega), if_pos c5]
      dsimp only
      rcases form_agrees (rest.length + 1) 1 (b.toNat - 192) true (by omega) with h | ⟨h1, h2, h3⟩
      · exact .inl h
      · exact .inr ⟨_, _, _, h1, h2, h3⟩
    rw [if_neg (show ¬ b.toNat ≤ 247 by omega), if_neg c5]
    by_cases c6 : b.toNat - 247 ≤ rest.length
    · rw [if_pos c6, if_pos (show 1 + (b.toNat - 247) ≤ rest.length + 1 by omega)]
      dsimp only
      rcases form_agrees (rest.length + 1) (1 + (b.toNat - 247))
        (bigEndian (rest.take (b.toNat - 247))) true (by omega) with h | ⟨h1, h2, h3⟩
      · exact .inl h
      · exact .inr ⟨_, _, _, h1, h2, h3⟩
    · rw [if_neg c6, if_neg (show ¬ 1 + (b.toNat - 247) ≤ rest.length + 1 by omega)]
      exact .inl rfl

/-- `f2_candidate_agrees`: for every input and Sail register state, EVM-Sail's
`rlp_decode_item` relates to the candidate `decode input`, or a listed known bug applies. -/
theorem f2_candidate_agrees (input : List Byte) (σ : SailRegs) :
    SailRelates (sailRun input σ) (decode input) ∨
      ∃ bug ∈ knownBugs, bugApplies bug input σ := by
  rcases item_agrees input with h | ⟨l, hh, p, hd, hw, hs⟩
  · left
    rw [sailRun_eq, h]
    rcases sailItem input with _ | ⟨l, off, len⟩
    · rfl
    · simp only [SailRelates, ofSail, Nat.add_sub_cancel]
  · right
    refine ⟨.rlpLongLengthWrap, by simp [knownBugs], l, hh, p, hd, hw, σ, ?_⟩
    rw [sailRun_eq, hs]

/-- `decodeItemWrapWitnessInput`: a long string whose 8 length bytes make header plus payload
`2^64`. -/
def wrapWitness : List Byte := [191, 255, 255, 255, 255, 255, 255, 255, 247]

/-- `decodeItemWrapWitness`: the wrap class is inhabited; the binary reports a success that
consumes 0 bytes, Sail rejects. -/
example : decode wrapWitness = .success false 9 (2 ^ 64 - 9) ∧ sailItem wrapWitness = none ∧
    ∀ σ, bugApplies .rlpLongLengthWrap wrapWitness σ := by
  have hd : decode wrapWitness = .success false 9 (2 ^ 64 - 9) := by decide
  have hs : sailItem wrapWitness = none := by decide
  exact ⟨hd, hs, fun σ => ⟨_, _, _, hd, by decide, σ, by rw [sailRun_eq, hs]⟩⟩

/-- Sail and the candidate agree on the one-byte input `0x00`. -/
example (σ : SailRegs) : SailRelates (sailRun [0] σ) (decode [0]) := by
  have hs : sailItem [0] = some (false, 0, 1) := by decide
  rw [sailRun_eq, hs]
  simp only [SailRelates]
  decide

/-! ## (c) Compliance of the binary -/

/-- `candidateResult40` with the item as a parameter: `result40` is it at `decode input`. -/
def encode40 (inPtr : Word) (input before : List Byte) (it : Item) : List Byte :=
  (List.range 40).map fun j =>
    match it with
    | .error => errorByte j
    | .success isList h p =>
      let ptr : Word := if input.head? = some 128 then 1 else inPtr + BitVec.ofNat 64 h
      successByte ptr (BitVec.ofNat 64 p) (BitVec.ofNat 64 (h + p)) isList before j

theorem result40_eq (inPtr : Word) (input before : List Byte) :
    result40 inPtr input before = encode40 inPtr input before (decode input) := by
  unfold result40 encode40 resultByte
  cases decode input <;> rfl

/-- `DecodeMeaningModuloKnownBugs`: the outcome bytes `after` are the candidate's (`C1BResult`),
and for every Sail register state they encode Sail's result (`decodeItemSailResult`) or a listed
known bug applies. -/
def DecodeMeaningModuloKnownBugs (inPtr : Word) (input before after : List Byte) : Prop :=
  after = result40 inPtr input before ∧
  ∀ σ, (∃ it, SailRelates (sailRun input σ) it ∧ after = encode40 inPtr input before it) ∨
    ∃ bug ∈ knownBugs, bugApplies bug input σ

theorem meaning_result40 (inPtr : Word) (input before : List Byte) :
    DecodeMeaningModuloKnownBugs inPtr input before (result40 inPtr input before) := by
  refine ⟨rfl, fun σ => ?_⟩
  rcases f2_candidate_agrees input σ with h | h
  · exact .inl ⟨_, h, result40_eq inPtr input before⟩
  · exact .inr h

/-- The final-state property of `f2_compliance`: `Post`, and the outcome struct at `a0` holds
bytes that mean EVM-Sail's decoding of the input at `a1` modulo known bugs. -/
def Compliant (m m' : Machine) : Prop :=
  Post m m' ∧
  ∀ input before, BytesAt m (m.reg 11) input → input.length = (m.reg 12).toNat →
    BytesAt m (m.reg 10) before → before.length = 40 →
    ∃ after, BytesAt m' (m.reg 10) after ∧
      DecodeMeaningModuloKnownBugs (m.reg 11) input before after

theorem f2_compliance (m : Machine) (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    Reaches zesuImage bound (Compliant m) m :=
  (f2_spec m hpc hpre).mono (Nat.le_refl _) fun _ hp =>
    ⟨hp, fun input before h1 h2 h3 h4 =>
      ⟨_, hp.2.2 input before h1 h2 h3 h4, meaning_result40 _ input before⟩⟩

/-- `f2_compliance` on the Sail RISC-V model, by `sail_reaches`. -/
theorem f2_compliance_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : SailLink.Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailLink.SailReaches zesuImage bound
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant m m') s :=
  SailLink.sail_reaches h (f2_compliance m hpc hpre)

/--
info: 'ZesuExec.Compliance.F2.f2_candidate_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f2_candidate_agrees

/--
info: 'ZesuExec.Compliance.F2.f2_compliance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f2_compliance

/--
info: 'ZesuExec.Compliance.F2.f2_compliance_sail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f2_compliance_sail

end ZesuExec.Compliance.F2
