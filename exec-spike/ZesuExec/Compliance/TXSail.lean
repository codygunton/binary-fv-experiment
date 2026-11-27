import ZesuExec.Compliance.ParentHeaderSail
import Evm.Lib.Rlp.Codecs.Transactions

/-!
# EVM-Sail access-list decoding in closed form

EVM-Sail decodes an EIP-2930 access list (`decode_access_list`,
`Evm/Lib/Rlp/Codecs/Transactions.lean`) from the RLP field of the list: `rlp_decode_list`, then
`_rec_decode_access_list_entries` over the payload. For each entry it decodes the entry item as a
list, the address item and the keys item, checks that nothing follows the keys item
(`rlp_cursor_expect_end`), decodes the address as a word (`rlp_decode_word`: a string of at most
32 bytes), decodes the rest of the list, then the keys list (`decode_access_list_keys`: each key a
word). Its result counts the entries and the keys.

This file states that as pure functions of the bytes (`sailKeys`, `sailEntry`, `sailEntries`,
`sailAccess`) and proves the Sail runs equal to them (`keys_eval`, `entries_eval`,
`access_eval`). Every failure is the `fatal_error RlpDecode` exit with the register state
unchanged; the order of the checks does not change the result.
-/

namespace ZesuExec.Compliance
open ZesuExec ZesuExec.Fn.F2 Sail

/-! ## The pure functions -/

/-- `_rec_decode_access_list_keys` with fuel `r`: the number of keys, or `none` where Sail exits.
Each key is an item decoded as a word (a string of at most 32 bytes). -/
def sailKeys : Nat → List Byte → Option Nat
  | _, [] => some 0
  | 0, _ :: _ => none
  | r + 1, xs@(_ :: _) =>
    match sailItem xs with
    | none => none
    | some (l, off, len) =>
      if l = true ∨ 32 < len then none else (sailKeys r (xs.drop (off + len))).map (· + 1)

/-- One entry, from its payload `e`: the number of its keys, or `none` where Sail exits. -/
def sailEntry (e : List Byte) : Option Nat :=
  match sailItem e with
  | none => none
  | some (al, aoff, alen) =>
    let a := e.drop (aoff + alen)
    match sailItem a with
    | none => none
    | some (kl, koff, klen) =>
      if a.drop (koff + klen) ≠ [] ∨ al = true ∨ 32 < alen ∨ kl = false then none
      else sailKeys (klen + 1) ((a.drop koff).take klen)

/-- `_rec_decode_access_list_entries` with fuel `r`: `(address count, slot count)`, or `none`. -/
def sailEntries : Nat → List Byte → Option (Nat × Nat)
  | _, [] => some (0, 0)
  | 0, _ :: _ => none
  | r + 1, xs@(_ :: _) =>
    match sailItem xs with
    | none => none
    | some (l, off, len) =>
      if l = false then none
      else match sailEntry ((xs.drop off).take len) with
        | none => none
        | some k => (sailEntries r (xs.drop (off + len))).map fun (a, s) => (a + 1, s + k)

/-- `rlp_decode_item` on the whole input, then `decode_access_list` on its field: the counts, or
`none`. -/
def sailAccess (input : List Byte) : Option (Nat × Nat) :=
  match sailItem input with
  | none => none
  | some (l, off, len) =>
    if l = false ∨ 2 ^ 30 < off + len then none
    else sailEntries (len + 1) ((input.drop off).take len)

/-! ## Sail runs -/

theorem slice_eq {o n : Nat} (c : Evm.Defs.StatelessInputSliceFields o n) : c = {} := rfl

/-- `decode_item_eval` for a cursor whose length index is `n = input.length`. -/
theorem decode_item_eval' (hs : Evm.HostState) (o n : Nat) (input : List Byte)
    (hx : SliceAt hs o input) (hn : input.length = n) (σ : SailRegs)
    (c : Evm.Defs.StatelessInputSliceFields o n) :
    ((Evm.Functions.rlp_decode_item c).run hs).run σ =
      match sailItem input with
      | some (l, off, len) => .ok (⟨len, ⟨off + len, ⟨{}, l⟩⟩⟩, hs) σ
      | none => .error .Exit σ := by
  subst hn; exact decode_item_eval hs o input hx σ c

theorem keys_eval (hs : Evm.HostState) (σ : SailRegs) (addr : Vector (BitVec 8) 20)
    {ab sb : Nat} (tail : Evm.Defs.AccessListDecode ab sb) :
    ∀ r n o (xs : List Byte) (hx : SliceAt hs o xs) (hl : xs.length = n)
      (c : Evm.Defs.StatelessInputSliceFields o n), n < r →
      ((Evm.Functions._rec_decode_access_list_keys c addr tail r).run hs).run σ =
        match sailKeys r xs with
        | some k => .ok (⟨tail.address_count, tail.slot_count + k⟩, hs) σ
        | none => .error .Exit σ := by
  intro r
  induction r with
  | zero => intro n _ _ _ _ _ h; omega
  | succ r ih =>
    intro n o xs hx hl c hr
    subst hl
    rw [Evm.Functions._rec_decode_access_list_keys]
    cases xs with
    | nil => simp [sailKeys]
    | cons b rest =>
      have hd := decode_item_eval hs o (b :: rest) hx σ c
      simp only [sailKeys]
      rw [if_neg (by simp)]
      rcases hsi : sailItem (b :: rest) with _ | ⟨l, off, len⟩
      · rw [hsi] at hd; exact run_bind_error _ _ _ _ _ hd
      · rw [hsi] at hd
        obtain ⟨hpos, hfit, -⟩ := sailItem_len_lt _ l off len hsi
        have hw := decode_word_eval hs σ o (b :: rest) hx l off len hfit
        rw [run_bind_ok _ _ _ _ _ hd]
        dsimp only
        by_cases hc : l = true ∨ 32 < len
        · rw [if_pos hc] at hw
          simp only [if_pos hc]
          exact run_bind_error _ _ _ _ _ (run_bind_error _ _ _ _ _ hw)
        · rw [if_neg hc] at hw
          simp only [if_neg hc]
          rw [run_bind_ok _ _ _ _ _ (by rw [run_bind_ok _ _ _ _ _ hw]; rfl)]
          have hih := ih ((b :: rest).length - (off + len)) (o + (off + len))
            ((b :: rest).drop (off + len)) (hx.drop _) (by simp)
            (Evm.Functions.rlp_cursor_advance c (off + len)) (by simp at hr ⊢; omega)
          simp only [Evm.Defs.StatelessInputSliceFields.len]
          rcases hk : sailKeys r ((b :: rest).drop (off + len)) with _ | k
          · rw [hk] at hih
            exact run_bind_error _ _ _ _ _ hih
          · rw [hk] at hih
            rw [run_bind_ok _ _ _ _ _ hih]
            simp [Nat.add_assoc]

/-- `rlp_decode_list` on a field: its payload cursor when it is a list. -/
theorem decode_list_eval (hs : Evm.HostState) (σ : SailRegs) (o full len : Nat) (l : Bool) :
    ((Evm.Functions.rlp_decode_list (⟨{}, l⟩ : Evm.Defs.RlpFieldRef o full len)).run hs).run σ =
      if l = true then .ok ({}, hs) σ else .error .Exit σ := by
  cases l <;> rfl

theorem dkeys_eval (hs : Evm.HostState) (σ : SailRegs) (addr : Vector (BitVec 8) 20)
    {ab sb : Nat} (tail : Evm.Defs.AccessListDecode ab sb) (n o : Nat) (xs : List Byte)
    (hx : SliceAt hs o xs) (hl : xs.length = n) (c : Evm.Defs.StatelessInputSliceFields o n) :
    ((Evm.Functions.decode_access_list_keys c addr tail).run hs).run σ =
      match sailKeys (n + 1) xs with
      | some k => .ok (⟨tail.address_count, tail.slot_count + k⟩, hs) σ
      | none => .error .Exit σ := by
  simp only [Evm.Functions.decode_access_list_keys]
  rw [dif_neg (by simp)]
  have hk := keys_eval hs σ addr tail (n + 1) n o xs hx hl c (by omega)
  simp only [Int.toNat_natCast]
  rcases hs' : sailKeys (n + 1) xs with _ | k
  · rw [hs'] at hk; exact run_bind_error _ _ _ _ _ hk
  · rw [hs'] at hk; rw [run_bind_ok _ _ _ _ _ hk]; rfl

theorem expect_end_eval (hs : Evm.HostState) (σ : SailRegs) (o n : Nat)
    (c : Evm.Defs.StatelessInputSliceFields o n) (h : n = 0) :
    ((Evm.Functions.rlp_cursor_expect_end c).run hs).run σ = .ok ((), hs) σ := by
  subst h; rfl

theorem expect_end_eval' (hs : Evm.HostState) (σ : SailRegs) (o n : Nat)
    (c : Evm.Defs.StatelessInputSliceFields o n) (h : ¬ n = 0) :
    ((Evm.Functions.rlp_cursor_expect_end c).run hs).run σ = .error .Exit σ := by
  simp only [Evm.Functions.rlp_cursor_expect_end]
  rw [if_neg (by simpa using h)]; rfl

theorem entries_eval (hs : Evm.HostState) (σ : SailRegs) :
    ∀ r n o (xs : List Byte) (hx : SliceAt hs o xs) (hl : xs.length = n)
      (c : Evm.Defs.StatelessInputSliceFields o n), n < r →
      ((Evm.Functions._rec_decode_access_list_entries c r).run hs).run σ =
        match sailEntries r xs with
        | some (a, s) => .ok (⟨a, s⟩, hs) σ
        | none => .error .Exit σ := by
  intro r
  induction r with
  | zero => intro n _ _ _ _ _ h; omega
  | succ r ih =>
    intro n o xs hx hl c hr
    subst hl
    rw [Evm.Functions._rec_decode_access_list_entries]
    cases xs with
    | nil => simp [sailEntries]; rfl
    | cons b rest =>
      have hd := decode_item_eval hs o (b :: rest) hx σ c
      simp only [sailEntries]
      rw [dif_neg (by simp)]
      rcases hsi : sailItem (b :: rest) with _ | ⟨l, off, len⟩
      · rw [hsi] at hd; exact run_bind_error _ _ _ _ _ hd
      rw [hsi] at hd
      obtain ⟨hpos, hfit, -⟩ := sailItem_len_lt _ l off len hsi
      rw [run_bind_ok _ _ _ _ _ hd]
      dsimp only
      have hdl := decode_list_eval hs σ o (off + len) len l
      cases l with
      | false =>
        rw [if_neg (by simp)] at hdl
        rw [run_bind_error _ _ _ _ _ hdl]
        simp
      | true =>
      rw [if_pos rfl] at hdl
      rw [run_bind_ok _ _ _ _ _ hdl]
      simp only [Evm.Defs.StatelessInputSliceFields.len, Bool.true_eq_false, if_false]
      generalize hp : List.take len (List.drop off (b :: rest)) = p
      have hpl : p.length = len := by subst hp; simp at hfit ⊢; omega
      have hxp : SliceAt hs (o + (off + len - len)) p := by
        rw [show off + len - len = off by omega, ← hp]; exact (hx.drop off).take len
      have ha := decode_item_eval' hs _ len p hxp hpl σ {}
      rcases hsa : sailItem p with _ | ⟨al, aoff, alen⟩
      · rw [hsa] at ha; rw [run_bind_error _ _ _ _ _ ha]; simp [sailEntry, hsa]
      rw [hsa] at ha
      obtain ⟨hapos, hafit, -⟩ := sailItem_len_lt _ al aoff alen hsa
      rw [run_bind_ok _ _ _ _ _ ha]
      dsimp only
      try simp only [Evm.Defs.StatelessInputSliceFields.len]
      generalize hq : p.drop (aoff + alen) = q
      have hql : q.length = len - (aoff + alen) := by subst hq; simp; omega
      have hxq : SliceAt hs (o + (off + len - len) + (aoff + alen)) q := by
        rw [← hq]; exact hxp.drop _
      have hk := decode_item_eval' hs _ _ q hxq hql σ
        (Evm.Functions.rlp_cursor_advance ({} : Evm.Defs.StatelessInputSliceFields _ len) (aoff + alen))
      rcases hsk : sailItem q with _ | ⟨kl, koff, klen⟩
      · rw [hsk] at hk; rw [run_bind_error _ _ _ _ _ hk]; simp [sailEntry, hsa, hq, hsk]
      rw [hsk] at hk
      obtain ⟨hkpos, hkfit, -⟩ := sailItem_len_lt _ kl koff klen hsk
      rw [run_bind_ok _ _ _ _ _ hk]
      dsimp only
      try simp only [Evm.Defs.StatelessInputSliceFields.len]
      have hE : sailEntry p = if q.drop (koff + klen) ≠ [] ∨ al = true ∨ 32 < alen ∨ kl = false
          then none else sailKeys (klen + 1) ((q.drop koff).take klen) := by
        simp only [sailEntry, hsa, hq, hsk]
      rw [hE]
      by_cases ht : len - (aoff + alen) - (koff + klen) = 0
      · have hdrop : q.drop (koff + klen) = [] := List.drop_eq_nil_of_le (by omega)
        rw [run_bind_ok _ _ _ _ _ (expect_end_eval hs σ _ _ _ ht)]
        have hw := decode_word_eval hs σ _ p hxp al aoff alen hafit
        by_cases hc : al = true ∨ 32 < alen
        · rw [if_pos hc] at hw
          rw [run_bind_error _ _ _ _ _ hw]
          rw [if_pos (by rcases hc with h | h <;> simp [h])]
        rw [if_neg hc] at hw
        rw [run_bind_ok _ _ _ _ _ hw]
        have hih := ih ((b :: rest).length - (off + len)) (o + (off + len))
          ((b :: rest).drop (off + len)) (hx.drop _) (by simp)
          (Evm.Functions.rlp_cursor_advance c (off + len)) (by simp at hr ⊢; omega)
        rcases hte : sailEntries r ((b :: rest).drop (off + len)) with _ | ⟨ta, ts⟩
        · rw [hte] at hih
          rw [run_bind_error _ _ _ _ _ hih]
          rw [← hE]; cases sailEntry p <;> rfl
        rw [hte] at hih
        rw [run_bind_ok _ _ _ _ _ hih]
        have hkl := decode_list_eval hs σ (o + (off + len - len) + (aoff + alen)) (koff + klen)
          klen kl
        cases kl with
        | false =>
          rw [if_neg (by simp)] at hkl
          rw [run_bind_error _ _ _ _ _ hkl]
          simp
        | true =>
        rw [if_pos rfl] at hkl
        rw [run_bind_ok _ _ _ _ _ hkl]
        have hxk : SliceAt hs (o + (off + len - len) + (aoff + alen) + (koff + klen - klen))
            ((q.drop koff).take klen) := by
          rw [show koff + klen - klen = koff by omega]; exact (hxq.drop koff).take klen
        have hks := dkeys_eval hs σ (Evm.Functions.word_to_address
          (bigEndian ((p.drop aoff).take alen))) (⟨ta, ts⟩ : Evm.Defs.AccessListDecode
            ((b :: rest).length - (off + len)) ((b :: rest).length - (off + len)))
          klen _ _ hxk (by simp; omega) {}
        have hc' : ¬ (q.drop (koff + klen) ≠ [] ∨ al = true ∨ 32 < alen ∨ true = false) := by
          simp only [hdrop, ne_eq, not_true_eq_false, false_or, Bool.true_eq_false, or_false]
          exact hc
        rw [if_neg hc']
        rcases hks' : sailKeys (klen + 1) ((q.drop koff).take klen) with _ | k
        · rw [hks'] at hks
          rw [run_bind_error _ _ _ _ _ hks]
        · rw [hks'] at hks
          rw [run_bind_ok _ _ _ _ _ hks]
          rfl
      · rw [run_bind_error _ _ _ _ _ (expect_end_eval' hs σ _ _ _ ht)]
        have hne : q.drop (koff + klen) ≠ [] := by
          intro h; have := congrArg List.length h; simp at this; omega
        rw [if_pos (.inl hne)]

/-- `rlp_decode_item` on a cursor over the whole stateless input, then `decode_access_list` on
the field it returns. -/
def accessRun (input : List Byte) : Evm.SailM Evm.Defs.AccessListRef := do
  let ⟨_, ⟨_, f⟩⟩ ← Evm.Functions.rlp_decode_item (k_source_off := 0)
    (k_source_len := input.length) {}
  Evm.Functions.decode_access_list f

/-- What `accessRun` returns, in closed form: a reference with the counts of `sailAccess`, or the
`fatal_error RlpDecode` exit. -/
theorem access_eval (input : List Byte) (σ : SailRegs) :
    match sailAccess input with
    | some (a, s) => ∃ e, ((accessRun input).run (hostOf input)).run σ =
        .ok (⟨e, a, s⟩, hostOf input) σ
    | none => ((accessRun input).run (hostOf input)).run σ = .error .Exit σ := by
  have hx := sliceAt_whole (hostOf input) input rfl
  have hd := decode_item_eval (hostOf input) 0 input hx σ {}
  simp only [accessRun, sailAccess]
  rcases hsi : sailItem input with _ | ⟨l, off, len⟩
  · rw [hsi] at hd; exact run_bind_error _ _ _ _ _ hd
  rw [hsi] at hd
  obtain ⟨hpos, hfit, -⟩ := sailItem_len_lt _ l off len hsi
  rw [run_bind_ok _ _ _ _ _ hd]
  dsimp only
  simp only [Evm.Functions.decode_access_list]
  have hdl := decode_list_eval (hostOf input) σ 0 (off + len) len l
  by_cases hb : l = false ∨ 2 ^ 30 < off + len
  · rw [if_pos hb]
    dsimp only
    by_cases hc : off + len ≤ 2 ^ 30
    · rw [if_pos (by simpa using hc)]
      rcases hb with rfl | hb
      · rw [if_neg (by simp)] at hdl
        exact run_bind_error _ _ _ _ _ hdl
      · omega
    · rw [if_neg (by simpa using hc)]; rfl
  · rw [if_neg hb]
    have hl : l = true := by cases l <;> simp_all
    subst hl
    rw [if_pos (by simp; omega)]
    rw [if_pos rfl] at hdl
    rw [run_bind_ok _ _ _ _ _ hdl]
    simp only [Evm.Functions.decode_access_list_entries]
    rw [if_neg (by simp)]
    have hp : (List.take len (List.drop off input)).length = len := by simp; omega
    have hxp : SliceAt (hostOf input) (0 + (off + len - len)) (List.take len (List.drop off input)) := by
      rw [show off + len - len = off by omega]; exact (hx.drop off).take len
    have he := entries_eval (hostOf input) σ (len + 1) len _ _ hxp hp {} (by omega)
    simp only [Int.toNat_natCast]
    rcases hse : sailEntries (len + 1) (List.take len (List.drop off input)) with _ | ⟨a, s⟩
    · rw [hse] at he
      exact run_bind_error _ _ _ _ _ he
    · rw [hse] at he
      exact ⟨_, (run_bind_ok _ _ _ _ _ he).trans rfl⟩

end ZesuExec.Compliance
