import ZesuExec.Compliance.SailRun
import ZesuExec.Fn.F2.Spec

/-!
# EVM-Sail `rlp_decode_item` in closed form

`decode_item_eval`: on a host state whose input region holds `xs` from offset `o` (`SliceAt`)
and a cursor over those bytes, `Evm.Functions.rlp_decode_item` returns the field `sailItem xs`
with the host and register state unchanged, or fails with `Sail.Error.Exit` (`fatal_error RlpDecode`) where
`sailItem xs = none`. `sailHeader` is `rlp_ref_hdr` and the length fold `rlp_uint64_width`
is `ZesuExec.Fn.F2.bigEndian` of the length bytes (`uint64_width_eval`).
-/

namespace ZesuExec.Compliance
open ZesuExec ZesuExec.Fn.F2
open Sail

theorem bigEndian_take_succ (rest : List Byte) (k : Nat) (hk : k < rest.length) :
    bigEndian (rest.take (k + 1)) = 256 * bigEndian (rest.take k) + rest[k].toNat := by
  rw [List.take_succ_eq_append_getElem hk]
  simp only [bigEndian, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The host's stateless-input region holds `xs` from offset `o`. -/
def SliceAt (hs : Evm.HostState) (o : Nat) (xs : List Byte) : Prop :=
  ∀ i (h : i < xs.length), hs.inputBytes[o + i]?.getD 0#8 = xs[i]

theorem sliceAt_whole (hs : Evm.HostState) (input : List Byte)
    (hin : hs.inputBytes = input.toArray) : SliceAt hs 0 input := by
  intro i h
  rw [hin, Nat.zero_add]
  simp [List.getElem?_eq_getElem h]

theorem SliceAt.drop {hs : Evm.HostState} {o : Nat} {xs : List Byte} (hx : SliceAt hs o xs)
    (k : Nat) : SliceAt hs (o + k) (xs.drop k) := by
  intro i h
  rw [List.getElem_drop, Nat.add_assoc]
  exact hx (k + i) (by simp at h; omega)

theorem SliceAt.take {hs : Evm.HostState} {o : Nat} {xs : List Byte} (hx : SliceAt hs o xs)
    (k : Nat) : SliceAt hs o (xs.take k) := by
  intro i h
  rw [List.getElem_take]
  exact hx i (by simp at h; omega)

/-- `_rec_rlp_uint64_width` on a slice at offset `o` folds the first `k` bytes of `xs`. -/
theorem width_eval (hs : Evm.HostState) (o : Nat) (xs : List Byte) (hx : SliceAt hs o xs)
    (σ : SailRegs) (w : Nat) (c : Evm.Defs.StatelessInputSliceFields o w) :
    ∀ k r, k ≤ xs.length → k ≤ w → k < r →
    ((Evm.Functions._rec_rlp_uint64_width ⟨o, ⟨w, c⟩⟩ k r).run hs).run σ =
      .ok (bigEndian (xs.take k), hs) σ := by
  intro k
  induction k with
  | zero =>
    intro r _ _ hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Evm.Functions._rec_rlp_uint64_width]
    simp [bigEndian]
  | succ k ih =>
    intro r hk hw hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Evm.Functions._rec_rlp_uint64_width]
    simp [ih r (by omega) (by omega) (by omega), Evm.Functions.stateless_input_slice_byte,
      Evm.Functions.stateless_input_byte_at, Evm.Functions.rlp_uint64_append]
    have hb : hs.inputBytes[o + k]?.getD 0#8 = xs[k] := hx k (by omega)
    have hbe := bigEndian_take_succ xs k (by omega)
    simp [show k < w by omega, hbe, BitVec.toNatInt, StateT.run, get, getThe, MonadStateOf.get,
      StateT.get, EStateM.run, Functor.map, StateT.map]
    simp only [EStateM.map, pure, EStateM.pure, hb, EStateM.Result.ok.injEq, Prod.mk.injEq, and_true]
    omega

/-- `rlp_uint64_width` of `w` bytes on a slice at offset `o` of length `w' ≥ w`. -/
theorem uint64_width_eval (hs : Evm.HostState) (o : Nat) (xs : List Byte) (hx : SliceAt hs o xs)
    (σ : SailRegs) (w' w : Nat) (c : Evm.Defs.StatelessInputSliceFields o w')
    (hw : w ≤ xs.length) (hw' : w ≤ w') :
    ((Evm.Functions.rlp_uint64_width ⟨o, ⟨w', c⟩⟩ w).run hs).run σ =
      .ok (bigEndian (xs.take w), hs) σ := by
  simp only [Evm.Functions.rlp_uint64_width]
  rw [if_neg (by simp)]
  exact width_eval hs o xs hx σ w' c w (w + 1) hw hw' (by omega)

/-- `rlp_ref_hdr` on the whole input `input`: `(is_list, content offset, content length)`, or
`none` where it calls `fatal_error RlpDecode`. -/
def sailHeader : List Byte → Option (Bool × Nat × Nat)
  | [] => none
  | b :: rest =>
    let h := b.toNat
    if h < 128 then some (false, 0, 1)
    else if h < 184 then some (false, 1, h - 128)
    else if h < 192 then
      if h - 183 ≤ rest.length then some (false, 1 + (h - 183), bigEndian (rest.take (h - 183)))
      else none
    else if h < 248 then some (true, 1, h - 192)
    else if h - 247 ≤ rest.length then some (true, 1 + (h - 247), bigEndian (rest.take (h - 247)))
    else none

theorem ref_hdr_eval (hs : Evm.HostState) (o : Nat) (xs : List Byte) (hx : SliceAt hs o xs)
    (σ : SailRegs) (c : Evm.Defs.StatelessInputSliceFields o xs.length) :
    ((Evm.Functions.rlp_ref_hdr ⟨o, ⟨xs.length, c⟩⟩).run hs).run σ =
      match sailHeader xs with
      | some r => .ok (r, hs) σ
      | none => .error .Exit σ := by
  cases xs with
  | nil =>
    simp [Evm.Functions.rlp_ref_hdr, sailHeader, Evm.Functions.fatal_error]
  | cons b rest =>
    have hb : b.toNat < 256 := b.isLt
    have h0 : hs.inputBytes[o]?.getD 0#8 = b := hx 0 (by simp)
    have hr : SliceAt hs (o + 1) rest := hx.drop 1
    simp only [Evm.Functions.rlp_ref_hdr, Evm.Functions.stateless_input_slice_byte,
      Evm.Functions.stateless_input_byte_at]
    simp [h0, sailHeader, Evm.Functions.fatal_error, BitVec.toNatInt]
    by_cases c1 : b.toNat < 128
    · simp (disch := omega) only [if_pos, run_pure]
    by_cases c2 : b.toNat < 184
    · simp (disch := omega) only [if_pos, if_neg, run_pure]
    by_cases c3 : b.toNat < 192
    · by_cases c4 : b.toNat ≤ rest.length + 183
      · simp (disch := omega) only [if_pos, if_neg]
        rw [run_map_ok _ _ _ _ _ (uint64_width_eval hs (o + 1) rest hr σ _ _ _ (by omega)
          (by simp [h0]))]
      · simp (disch := omega) only [if_pos, if_neg, run_throw]
    by_cases c5 : b.toNat < 248
    · simp (disch := omega) only [if_pos, if_neg, run_pure]
    by_cases c6 : b.toNat ≤ rest.length + 247
    · simp (disch := omega) only [if_pos, if_neg]
      rw [run_map_ok _ _ _ _ _ (uint64_width_eval hs (o + 1) rest hr σ _ _ _ (by omega)
        (by simp [h0]))]
    · simp (disch := omega) only [if_pos, if_neg, run_throw]

/-- `rlp_decode_item` on a cursor over the bytes `xs`: `(is_list, header length, payload
length)` of the returned field, or `none` where it calls `fatal_error RlpDecode`. -/
def sailItem (input : List Byte) : Option (Bool × Nat × Nat) :=
  match sailHeader input with
  | none => none
  | some (l, off, len) => if 0 < off + len ∧ off + len ≤ input.length then some (l, off, len) else none

theorem decode_item_eval (hs : Evm.HostState) (o : Nat) (input : List Byte)
    (hx : SliceAt hs o input) (σ : SailRegs)
    (c : Evm.Defs.StatelessInputSliceFields o input.length) :
    ((Evm.Functions.rlp_decode_item c).run hs).run σ =
      match sailItem input with
      | some (l, off, len) => .ok (⟨len, ⟨off + len, ⟨{}, l⟩⟩⟩, hs) σ
      | none => .error .Exit σ := by
  cases input with
  | nil => simp [Evm.Functions.rlp_decode_item, sailItem, sailHeader, Evm.Functions.fatal_error]
  | cons b rest =>
    have hh := ref_hdr_eval hs o (b :: rest) hx σ c
    simp only [Evm.Functions.rlp_decode_item]
    simp only [List.length_cons, Nat.add_one_ne_zero, beq_iff_eq, if_false, pure_bind]
    simp only [List.length_cons] at hh
    rcases hsh : sailHeader (b :: rest) with _ | ⟨l, off, len⟩
    · rw [hsh] at hh
      rw [run_bind_error _ _ _ _ _ hh]
      simp [sailItem, hsh]
    · rw [hsh] at hh
      rw [run_bind_ok _ _ _ _ _ hh]
      simp only [sailItem, hsh]
      by_cases h1 : 0 < off + len ∧ off + len ≤ rest.length + 1
      · have h2 : ¬ rest.length + 1 < off := by omega
        simp [h1, h2, Evm.Functions.fatal_error]
        rw [if_neg (by omega)]
        rfl
      · simp [h1, Evm.Functions.fatal_error]
        split <;> (try split) <;> rfl

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

end ZesuExec.Compliance
