import ZesuExec.Compliance.SailRun
import ZesuExec.Fn.F2.Spec

/-!
# EVM-Sail `rlp_decode_item` in closed form

`decode_item_eval`: on a host state whose input region is `input` and a cursor over the whole
region, `Evm.Functions.rlp_decode_item` returns the field `sailItem input` with the host and
register state unchanged, or fails with `Sail.Error.Exit` (`fatal_error RlpDecode`) where
`sailItem input = none`. `sailHeader` is `rlp_ref_hdr` and the length fold `rlp_uint64_width`
is `ZesuExec.Fn.F2.bigEndian` of the length bytes (`uint64_width_eval`).
-/

namespace ZesuExec.Compliance
open ZesuExec ZesuExec.Fn.F2
open Sail

theorem bigEndian_take_succ (rest : List Byte) (k : Nat) (hk : k < rest.length) :
    bigEndian (rest.take (k + 1)) = 256 * bigEndian (rest.take k) + rest[k].toNat := by
  rw [List.take_succ_eq_append_getElem hk]
  simp only [bigEndian, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `_rec_rlp_uint64_width` on a slice at offset `o` folds the `k` bytes from `o`. -/
theorem width_eval (input : List Byte) (hs : Evm.HostState)
    (hin : hs.inputBytes = input.toArray) (σ : SailRegs) (o w : Nat)
    (c : Evm.Defs.StatelessInputSliceFields o w) :
    ∀ k r, o + k ≤ input.length → k ≤ w → k < r →
    ((Evm.Functions._rec_rlp_uint64_width ⟨o, ⟨w, c⟩⟩ k r).run hs).run σ =
      .ok (bigEndian ((input.drop o).take k), hs) σ := by
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
    have hlt : k < (input.drop o).length := by simp; omega
    have hb : hs.inputBytes[o + k]?.getD 0#8 = (input.drop o)[k] := by
      rw [hin]
      simp only [List.getElem?_toArray]
      rw [show input[o + k]? = (input.drop o)[k]? by simp [List.getElem?_drop]]
      simp [List.getElem?_eq_getElem hlt]
    have hbe := bigEndian_take_succ (input.drop o) k hlt
    simp only [List.getElem_drop] at hbe hb
    simp [show k < w by omega, hbe, BitVec.toNatInt, StateT.run, get, getThe, MonadStateOf.get,
      StateT.get, EStateM.run, Functor.map, StateT.map]
    simp only [EStateM.map, pure, EStateM.pure, hb, EStateM.Result.ok.injEq, Prod.mk.injEq, and_true]
    omega

/-- `rlp_uint64_width` of `w` bytes on a slice at offset `o` of length `w' ≥ w`. -/
theorem uint64_width_eval (input : List Byte) (hs : Evm.HostState)
    (hin : hs.inputBytes = input.toArray) (σ : SailRegs) (o w' w : Nat)
    (c : Evm.Defs.StatelessInputSliceFields o w') (hw : o + w ≤ input.length) (hw' : w ≤ w') :
    ((Evm.Functions.rlp_uint64_width ⟨o, ⟨w', c⟩⟩ w).run hs).run σ =
      .ok (bigEndian ((input.drop o).take w), hs) σ := by
  simp only [Evm.Functions.rlp_uint64_width]
  rw [if_neg (by simp)]
  exact width_eval input hs hin σ o w' c w (w + 1) hw hw' (by omega)

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

theorem ref_hdr_eval (input : List Byte) (hs : Evm.HostState)
    (hin : hs.inputBytes = input.toArray) (σ : SailRegs)
    (c : Evm.Defs.StatelessInputSliceFields 0 input.length) :
    ((Evm.Functions.rlp_ref_hdr ⟨0, ⟨input.length, c⟩⟩).run hs).run σ =
      match sailHeader input with
      | some r => .ok (r, hs) σ
      | none => .error .Exit σ := by
  cases input with
  | nil =>
    simp [Evm.Functions.rlp_ref_hdr, sailHeader, Evm.Functions.fatal_error]
  | cons b rest =>
    have hb : b.toNat < 256 := b.isLt
    have h0 : hs.inputBytes[0]?.getD 0#8 = b := by rw [hin]; rfl
    simp only [Evm.Functions.rlp_ref_hdr, Evm.Functions.stateless_input_slice_byte,
      Evm.Functions.stateless_input_byte_at]
    simp [h0, sailHeader, Evm.Functions.fatal_error, BitVec.toNatInt]
    have h0' : (hs.inputBytes[0]?.getD 0#8).toNat = b.toNat := by rw [h0]
    have hin' : hs.inputBytes = (b :: rest).toArray := hin
    by_cases c1 : b.toNat < 128
    · simp (disch := omega) only [if_pos, run_pure]
    by_cases c2 : b.toNat < 184
    · simp (disch := omega) only [if_pos, if_neg, run_pure]
    by_cases c3 : b.toNat < 192
    · by_cases c4 : b.toNat ≤ rest.length + 183
      · simp (disch := omega) only [if_pos, if_neg]
        rw [run_map_ok _ _ _ _ _ (uint64_width_eval (b :: rest) hs hin' σ 1 _ _ _ (by simp; omega) (by omega))]
        rfl
      · simp (disch := omega) only [if_pos, if_neg, run_throw]
    by_cases c5 : b.toNat < 248
    · simp (disch := omega) only [if_pos, if_neg, run_pure]
    by_cases c6 : b.toNat ≤ rest.length + 247
    · simp (disch := omega) only [if_pos, if_neg]
      rw [run_map_ok _ _ _ _ _ (uint64_width_eval (b :: rest) hs hin' σ 1 _ _ _ (by simp; omega) (by omega))]
      rfl
    · simp (disch := omega) only [if_pos, if_neg, run_throw]

/-- `rlp_decode_item` on a cursor over the whole input: `(is_list, header length, payload
length)` of the returned field, or `none` where it calls `fatal_error RlpDecode`. -/
def sailItem (input : List Byte) : Option (Bool × Nat × Nat) :=
  match sailHeader input with
  | none => none
  | some (l, off, len) => if 0 < off + len ∧ off + len ≤ input.length then some (l, off, len) else none

theorem decode_item_eval (input : List Byte) (hs : Evm.HostState)
    (hin : hs.inputBytes = input.toArray) (σ : SailRegs)
    (c : Evm.Defs.StatelessInputSliceFields 0 input.length) :
    ((Evm.Functions.rlp_decode_item c).run hs).run σ =
      match sailItem input with
      | some (l, off, len) => .ok (⟨len, ⟨off + len, ⟨{}, l⟩⟩⟩, hs) σ
      | none => .error .Exit σ := by
  cases input with
  | nil => simp [Evm.Functions.rlp_decode_item, sailItem, sailHeader, Evm.Functions.fatal_error]
  | cons b rest =>
    have hh := ref_hdr_eval (b :: rest) hs hin σ c
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

end ZesuExec.Compliance
