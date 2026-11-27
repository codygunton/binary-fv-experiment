import ZesuExec.Compliance.RlpItem

/-!
# EVM-Sail `rlp_decode_uint64` on a field of `rlp_decode_item`

For the field `⟨{}, l⟩ : RlpFieldRef 0 (off + len) len` that `decode_item_eval` returns:
`uint_canonical_short` evaluates `rlp_item_uint_canonical` to `uintCanon` (`len ≤ 55`),
`uint_canonical_long` shows it returns a flag without failing (`55 < len < 2^256`), and
`decode_uint64_eval` gives `rlp_decode_uint64`: the big-endian value of the `len` payload bytes
when the field is a canonical non-list integer of at most 8 bytes, else `fatal_error RlpDecode`.
-/

namespace ZesuExec.Compliance
open ZesuExec ZesuExec.Fn.F2 Sail


@[simp] theorem run_map_get {α : Type} (f : Evm.HostState → α) (hs : Evm.HostState) (σ : SailRegs) :
    EStateM.run (StateT.run (f <$> (get : Evm.SailM Evm.HostState)) hs) σ = .ok (f hs, hs) σ := rfl

@[simp] theorem run_map_ok' {α β : Type} (f : α → β) (x : Evm.SailM α) (hs : Evm.HostState) (σ : SailRegs) :
    EStateM.run (StateT.run (f <$> x) hs) σ =
      match EStateM.run (StateT.run x hs) σ with
      | .ok (a, hs') σ' => .ok (f a, hs') σ'
      | .error e σ' => .error e σ' := by
  rw [StateT.run_map]
  simp only [EStateM.run, Functor.map, EStateM.map]
  generalize StateT.run x hs σ = r
  cases r <;> rfl

theorem access7 (b : BitVec 8) : (BitVec.access b 7 = 0#1) ↔ b.toNat < 128 := by
  revert b; decide

/-- `rlp_item_uint_canonical` on a non-list field `(off, len)` with `len ≤ 55` at offset 0 of
input bytes `bs`. -/
def uintCanon (bs : Array Byte) (off len : Nat) : Bool :=
  let B := fun i : Nat => bs[i]?.getD 0#8
  let framing :=
    if len = 0 then off = 1 && B 0 == 128#8
    else if len = 1 ∧ (B off).toNat < 128 then off = 0 && B 0 == B off
    else off = 1 && B 0 == 128#8 + Evm.Functions.rlp_nat_length_byte len
  framing && (len == 0 || B off != 0#8)

/-- `rlp_item_uint_canonical` on a short non-list field. -/
theorem uint_canonical_short (hs : Evm.HostState) (σ : SailRegs)
    (off len : Nat) (hpos : 0 < off + len) (hl : len ≤ 55) :
    ((Evm.Functions.rlp_item_uint_canonical (⟨{}, false⟩ : Evm.Defs.RlpFieldRef 0 (off + len) len)).run hs).run σ =
     .ok (uintCanon hs.inputBytes off len, hs) σ := by
  simp only [Evm.Functions.rlp_item_uint_canonical, Evm.Functions.rlp_ref_bytes_canonical,
    Evm.Functions.rlp_ref_framing_canonical, Evm.Functions.stateless_input_slice_byte,
    Evm.Functions.stateless_input_byte_at, uintCanon]
  rcases Nat.eq_zero_or_pos len with h0 | h0
  · subst h0
    have : off ≠ 0 := by omega
    by_cases hf : off = 1
    · subst hf; simp; split <;> simp_all
    · simp [hf, this]
  · by_cases h1 : len = 1 ∧ (hs.inputBytes[off]?.getD 0#8).toNat < 128
    · obtain ⟨rfl, h1⟩ := h1
      by_cases hf : off = 0
      · subst hf; simp [access7, h1]
      · simp [hf, access7, h1]
    · by_cases hf : off = 1
      · subst hf
        have hne : len ≠ 0 := by omega
        simp [access7, hl, Evm.Functions.RLP_SHORT_LENGTH_LIMIT, hne, h0, Nat.add_comm 1 len]
        have h1' : len = 1 → ¬ (hs.inputBytes[1]?.getD 0#8).toNat < 128 := fun h h' => h1 ⟨h, h'⟩
        by_cases hlen1 : len = 1
        · simp [hlen1, h1' hlen1]; split <;> simp_all
        · simp [hlen1]; split <;> simp_all
      · have hne : len ≠ 0 := by omega
        have hf' : ¬ off + len = len + 1 := by omega
        simp [hf, access7, hl, Evm.Functions.RLP_SHORT_LENGTH_LIMIT, hne, h0, hf']
        have h1' : len = 1 → ¬ (hs.inputBytes[off]?.getD 0#8).toNat < 128 := fun h h' => h1 ⟨h, h'⟩
        by_cases hlen1 : len = 1
        · simp [hlen1, h1' hlen1]
        · simp [hlen1]

/-- `rlp_length_word` below `2^256`. -/
theorem word_ok (n : Nat) (hs : Evm.HostState) (σ : SailRegs) (h : n < 2 ^ 256) :
    ((Evm.Functions.rlp_length_word n).run hs).run σ = .ok (n, hs) σ := by
  simp only [Evm.Functions.rlp_length_word, Evm.Functions.word_of_nat_byte_count]
  rw [if_pos]
  · rfl
  · exact decide_eq_true (Nat.lt_of_lt_of_eq h (by rfl))

/-- `rlp_item_uint_canonical` on a long non-list field returns some flag (its length is below
`2^256`, so `word_of_nat_byte_count` does not assert). -/
theorem uint_canonical_long (hs : Evm.HostState) (σ : SailRegs)
    (off len : Nat) (hpos : 0 < off + len) (hl : 55 < len) (hlt : len < 2 ^ 256) :
    ∃ b, ((Evm.Functions.rlp_item_uint_canonical (⟨{}, false⟩ : Evm.Defs.RlpFieldRef 0 (off + len) len)).run hs).run σ =
     .ok (b, hs) σ := by
  have hne : len ≠ 0 := by omega
  have hn : ¬ len ≤ 55 := by omega
  have hlt' : (len : Int) < 2 ^ 256 := by exact_mod_cast hlt
  simp [word_ok len hs σ hlt, Evm.Functions.rlp_item_uint_canonical, Evm.Functions.rlp_ref_bytes_canonical,
    Evm.Functions.rlp_ref_framing_canonical, Evm.Functions.stateless_input_slice_byte,
    Evm.Functions.stateless_input_byte_at, Evm.Functions.RLP_SHORT_LENGTH_LIMIT, hne, hn, hpos,
    Evm.Functions.stateless_input_slice_load_n, Evm.Functions.stateless_input_load_n_word,
    show 0 < len by omega, access7, show ¬ len = 1 by omega]
  by_cases h1 : off = 1 + Evm.Functions.rlp_minimal_word_len len
  · simp only [h1, if_true]
    by_cases h2 : hs.inputBytes[0]?.getD 0#8 =
        183#8 + Evm.Functions.rlp_nat_length_byte (Evm.Functions.rlp_minimal_word_len len)
    · simp [h2, show 1 < 1 + Evm.Functions.rlp_minimal_word_len len + len by omega]
      split <;> simp [Classical.em]
    · simp [h2]
  · simp [h1]

theorem uint_canonical_list (hs : Evm.HostState) (σ : SailRegs) (full len : Nat) :
    ((Evm.Functions.rlp_item_uint_canonical
      (⟨{}, true⟩ : Evm.Defs.RlpFieldRef 0 full len)).run hs).run σ = .ok (false, hs) σ := by
  simp [Evm.Functions.rlp_item_uint_canonical, Evm.Functions.rlp_ref_bytes_canonical]

/-- `rlp_decode_uint64` on the field `(l, off, len)` over the input `input`. -/
theorem decode_uint64_eval (input : List Byte) (hs : Evm.HostState)
    (hin : hs.inputBytes = input.toArray) (σ : SailRegs) (l : Bool) (off len : Nat)
    (hfit : off + len ≤ input.length) (hpos : 0 < off + len) (hlt : len < 2 ^ 256) :
    ((Evm.Functions.rlp_decode_uint64 (⟨{}, l⟩ : Evm.Defs.RlpFieldRef 0 (off + len) len)).run
      hs).run σ =
      if l = false ∧ len ≤ 8 ∧ uintCanon hs.inputBytes off len = true then
        .ok (bigEndian ((input.drop off).take len), hs) σ
      else .error .Exit σ := by
  simp only [Evm.Functions.rlp_decode_uint64]
  cases l with
  | true =>
    rw [run_bind_ok _ _ _ _ _ (uint_canonical_list hs σ (off + len) len)]
    simp [Evm.Functions.fatal_error]
  | false =>
    by_cases h55 : len ≤ 55
    · rw [run_bind_ok _ _ _ _ _ (uint_canonical_short hs σ off len hpos h55)]
      by_cases h8 : len ≤ 8
      · by_cases hc : uintCanon hs.inputBytes off len = true
        · simp only [hc, h8, Bool.not_true, Bool.false_or, decide_eq_true_eq]
          simp [show ¬ 8 < len by omega, Evm.Functions.rlp_item_content]
          rw [show len.mod 9 = len from Nat.mod_eq_of_lt (by omega)]
          have := uint64_width_eval input hs hin σ (0 + (off + len - len)) len len {}
            (by omega) (Nat.le_refl _)
          rw [this, show 0 + (off + len - len) = off by omega]
        · simp [hc, Evm.Functions.fatal_error]
      · simp [h8, Evm.Functions.fatal_error, show 8 < len by omega]
    · obtain ⟨b, hb⟩ := uint_canonical_long hs σ off len hpos (by omega) hlt
      rw [run_bind_ok _ _ _ _ _ hb]
      simp [Evm.Functions.fatal_error, show 8 < len by omega, show ¬ len ≤ 8 by omega]

end ZesuExec.Compliance
