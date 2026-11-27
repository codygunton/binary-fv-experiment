import ZesuExec.Compliance.RlpUint
import Evm.Lib.Ssz.StatelessInput

/-!
# EVM-Sail parent-header decoding in closed form

EVM-Sail decodes a parent header (`_rec_index_witness_header_cursor`,
`Evm/Lib/Ssz/StatelessInput.lean`) by `rlp_node_cursor` on the header bytes, then
`decode_parent_header_fields cursor 0 EMPTY_PARENT_HEADER_FIELDS`. This file states both as pure
functions of the header bytes (`sailParent`, `fieldsSpec`, `stepSpec`) and proves the Sail runs
equal to them (`node_cursor_eval`, `fields_eval`). Only the fields the binary also returns are
tracked (`Shared`: base fee, blob gas used, excess blob gas, each with its `have_` flag); parent
hash and state root are decoded (`rlp_decode_word`) but their values are not compared.
-/

namespace ZesuExec.Compliance
open ZesuExec ZesuExec.Fn.F2 Sail

theorem run_readReg
 (r : Evm.Defs.Register) (v : Evm.Defs.RegisterType r) (hs : Evm.HostState) (σ : SailRegs)
    (h : σ.regs.get? r = some v) :
    EStateM.run (StateT.run (Evm.readReg r) hs) σ = .ok (v, hs) σ := by
  rw [show Evm.readReg r = StateT.lift (PreSail.readReg r) from rfl]
  simp [PreSail.readReg, h]

/-- `stateless_input_slice_load_n`: the big-endian value of `len` bytes from `off`. -/
theorem load_n_eval (hs : Evm.HostState) (σ : SailRegs) (o : Nat) (xs : List Byte)
    (hx : SliceAt hs o xs) (off len : Nat) (hfit : off + len ≤ xs.length) :
    ((Evm.Functions.stateless_input_slice_load_n ⟨o, ⟨off + len, {}⟩⟩ off len).run hs).run σ =
      .ok (bigEndian ((xs.drop off).take len), hs) σ := by
  simp only [Evm.Functions.stateless_input_slice_load_n]
  rcases Nat.eq_zero_or_pos len with h0 | h0
  · subst h0
    simp [bigEndian, Evm.Functions.ZERO_WORD]
    rfl
  · rw [if_pos (by simp; omega)]
    show EStateM.Result.ok ((((List.range len).map fun i =>
      ((List.range (off + len)).map fun j => hs.inputBytes.getD (o + j) 0).getD (off + i) 0).foldl
        (fun r v => r * 256 + v.toNat) 0), hs) σ = _
    have hl : ((List.range len).map fun i =>
      ((List.range (off + len)).map fun j => hs.inputBytes.getD (o + j) 0).getD (off + i) 0) =
        (xs.drop off).take len := by
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp at h1
        have := hx (off + i) (by omega)
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show off + i < off + len by omega),
          Array.getD_eq_getD_getElem?]
        simpa [Nat.add_assoc] using this
    rw [hl]
    simp only [bigEndian]
    have hf : (fun r (v : Byte) => r * 256 + v.toNat) = (fun acc b => 256 * acc + b.toNat) := by
      funext a b; rw [Nat.mul_comm]
    rw [hf]


/-- `rlp_decode_word` on a field `(l, off, len)` of the item bytes `xs` at `o`. -/
theorem decode_word_eval (hs : Evm.HostState) (σ : SailRegs) (o : Nat) (xs : List Byte)
    (hx : SliceAt hs o xs) (l : Bool) (off len : Nat) (hfit : off + len ≤ xs.length) :
    ((Evm.Functions.rlp_decode_word (⟨{}, l⟩ : Evm.Defs.RlpFieldRef o (off + len) len)).run hs).run σ =
      if l = true ∨ 32 < len then .error .Exit σ
      else .ok (bigEndian ((xs.drop off).take len), hs) σ := by
  simp only [Evm.Functions.rlp_decode_word]
  split
  · rename_i h
    have : l = true ∨ 32 < len := by simpa using h
    rw [if_pos this]; rfl
  · rename_i h
    have : ¬ (l = true ∨ 32 < len) := by simpa using h
    rw [if_neg this, show off + len - len = off by omega]
    exact load_n_eval hs σ o xs hx off len hfit

/-- `rlp_decode_u256` on a field `(l, off, len)` of the item bytes `xs` at `o`. -/
theorem decode_u256_eval (hs : Evm.HostState) (σ : SailRegs) (o : Nat) (xs : List Byte)
    (hx : SliceAt hs o xs) (l : Bool) (off len : Nat) (hfit : off + len ≤ xs.length)
    (hpos : 0 < off + len) (hlt : len < 2 ^ 256) :
    ((Evm.Functions.rlp_decode_u256 (⟨{}, l⟩ : Evm.Defs.RlpFieldRef o (off + len) len)).run hs).run σ =
      if l = true ∨ 32 < len ∨ uintCanon xs off len = false then .error .Exit σ
      else .ok (bigEndian ((xs.drop off).take len), hs) σ := by
  simp only [Evm.Functions.rlp_decode_u256]
  cases l with
  | true =>
    rw [run_bind_ok _ _ _ _ _ (uint_canonical_list hs σ o (off + len) len)]
    simp [Evm.Functions.fatal_error]
  | false =>
    by_cases h55 : len ≤ 55
    · rw [run_bind_ok _ _ _ _ _ (uint_canonical_short hs σ o xs hx off len hpos hfit h55)]
      cases hc : uintCanon xs off len
      · simp [Evm.Functions.fatal_error]
      · simp only [if_true]
        rw [decode_word_eval hs σ o xs hx false off len hfit]
        simp
    · obtain ⟨b, hb⟩ := uint_canonical_long hs σ o off len hpos (by omega) hlt
      rw [run_bind_ok _ _ _ _ _ hb]
      have h32 : 32 < len := by omega
      cases b
      · simp [Evm.Functions.fatal_error, h32]
      · simp only [if_true]
        rw [decode_word_eval hs σ o xs hx false off len hfit]
        simp [h32]

/-- The fields both Sail and the binary return. -/
structure Shared where
  base : Option Nat
  blob : Option Nat
  excess : Option Nat
  deriving DecidableEq, Repr

/-- The shared fields of Sail's record (absent where the `have_` flag is clear). -/
def sharedOf (f : Evm.Defs.ParentHeaderFields) : Shared :=
  ⟨if f.have_base_fee then some f.base_fee else none,
   if f.have_blob_gas then some f.blob_gas_used else none,
   if f.have_excess_blob_gas then some f.excess_blob_gas else none⟩

/-- One field of `_rec_decode_parent_header_fields` (`rlp_decode_word` at 0 and 3, `rlp_decode_u256`
at 15, `rlp_decode_uint64` with the blob checks at 17 and the limit at 18, nothing else), on the
shared fields; `none` where Sail calls `fatal_error RlpDecode`. -/
def stepSpec (maxB limit : Nat) (xs : List Byte) (i : Nat) (l : Bool) (off len : Nat) (s : Shared) :
    Option Shared :=
  let v := bigEndian ((xs.drop off).take len)
  if i = 0 ∨ i = 3 then (if l = true ∨ 32 < len then none else some s)
  else if i = 15 then
    (if l = true ∨ 32 < len ∨ uintCanon xs off len = false then none else some { s with base := some v })
  else if i = 17 then
    (if l = true ∨ 8 < len ∨ uintCanon xs off len = false then none
     else if v / 2 ^ 17 ≤ maxB ∧ v = 2 ^ 17 * (v / 2 ^ 17) then some { s with blob := some v } else none)
  else if i = 18 then
    (if l = true ∨ 8 < len ∨ uintCanon xs off len = false then none
     else if v ≤ limit then some { s with excess := some v } else none)
  else some s

/-- `next_parent_header_field`. -/
def nextIdx (i : Nat) : Nat := if i < 19 then i + 1 else 19

/-- `_rec_decode_parent_header_fields` on the bytes `xs` from field `i`, on the shared fields. -/
def fieldsSpec (maxB limit : Nat) (xs : List Byte) (i : Nat) (s : Shared) : Option Shared :=
  if _hxs : xs = [] then some s else
  match hh : sailItem xs with
  | none => none
  | some (l, off, len) =>
    match stepSpec maxB limit xs i l off len s with
    | none => none
    | some s' => fieldsSpec maxB limit (xs.drop (off + len)) (nextIdx i) s'
termination_by xs.length
decreasing_by
  have := sailItem_len_lt xs l off len hh
  simp; omega

theorem fieldsSpec_nil (maxB limit i : Nat) (s : Shared) : fieldsSpec maxB limit [] i s = some s := by
  rw [fieldsSpec]; simp

theorem fieldsSpec_none (maxB limit i : Nat) (s : Shared) (xs : List Byte) (hne : xs ≠ [])
    (h : sailItem xs = none) : fieldsSpec maxB limit xs i s = none := by
  rw [fieldsSpec]; simp only [hne, dite_false]; split <;> simp_all

theorem fieldsSpec_some (maxB limit i : Nat) (s : Shared) (xs : List Byte) (hne : xs ≠ [])
    (l : Bool) (off len : Nat) (h : sailItem xs = some (l, off, len)) :
    fieldsSpec maxB limit xs i s =
      (stepSpec maxB limit xs i l off len s).bind
        (fun s' => fieldsSpec maxB limit (xs.drop (off + len)) (nextIdx i) s') := by
  rw [fieldsSpec]; simp only [hne, dite_false]
  split
  · simp_all
  · rename_i l' off' len' h'
    rw [h] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    cases stepSpec maxB limit xs i l off len s <;> rfl

theorem blobA (v : Nat) : (131072 * ((v : Int) / max 131072 0)).toNat = 131072 * (v / 131072) := by
  rw [show max (131072 : Int) 0 = 131072 by decide]
  omega

theorem next_eq (i : Nat) : Evm.Functions.next_parent_header_field i = nextIdx i := by
  simp [Evm.Functions.next_parent_header_field, nextIdx]

/-- The blob schedule maximum and excess-blob-gas limit of a profile, as Sail reads them. -/
def profMax (p : Evm.Defs.ExecutionProfile) : Nat := p.2.2.1

def profLimit (p : Evm.Defs.ExecutionProfile) : Nat :=
  Int.toNat (if p.1 < 11 then 0 else 256 * (p.2.2.2.1 : Int) + ((p.2.2.1 : Int) - p.2.1) * 131072)

/-- How a Sail run relates to the spec's result. -/
def RunRel (hs : Evm.HostState) (σ : SailRegs)
    (res : EStateM.Result (Sail.Error Unit) SailRegs (Evm.Defs.ParentHeaderFields × Evm.HostState))
    (spec : Option Shared) : Prop :=
  match spec with
  | none => res = .error .Exit σ
  | some s' => ∃ f', res = .ok (f', hs) σ ∧ sharedOf f' = s'

theorem fields_eval (hs : Evm.HostState) (σ : SailRegs) (prof : Evm.Defs.ExecutionProfile)
    (hσ : σ.regs.get? .k_execution_profile = some prof) :
    ∀ r n o (xs : List Byte) (hx : SliceAt hs o xs) (hl : xs.length = n)
      (c : Evm.Defs.StatelessInputSliceFields o n) i f, n < r →
      RunRel hs σ ((Evm.Functions._rec_decode_parent_header_fields c i f r).run hs |>.run σ)
        (fieldsSpec (profMax prof) (profLimit prof) xs i (sharedOf f)) := by
  intro r
  induction r with
  | zero => intro n _ _ _ _ _ _ _ h; omega
  | succ r ih =>
    intro n o xs hx hl c i f hr
    subst hl
    rw [Evm.Functions._rec_decode_parent_header_fields]
    by_cases hn : xs.length = 0
    · have : xs = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      rw [fieldsSpec_nil]
      simp [RunRel]
    have hd := decode_item_eval hs o xs hx σ c
    have hne : xs ≠ [] := fun h => hn (by simp [h])
    rcases hsi : sailItem xs with _ | ⟨l, off, len⟩
    · rw [hsi] at hd
      rw [fieldsSpec_none _ _ _ _ _ hne hsi]
      simp [hn, hd, RunRel]
    · rw [hsi] at hd
      rw [fieldsSpec_some _ _ _ _ _ hne _ _ _ hsi]
      obtain ⟨hpos, hfit, hlt⟩ := sailItem_len_lt xs l off len hsi
      have hrec : ∀ i' f' s', sharedOf f' = s' →
          RunRel hs σ ((Evm.Functions._rec_decode_parent_header_fields
            (Evm.Functions.rlp_cursor_advance c (off + len)) i' f' r).run hs |>.run σ)
            (fieldsSpec (profMax prof) (profLimit prof) (xs.drop (off + len)) i' s') := by
        intro i' f' s' hs'
        subst hs'
        exact ih (xs.length - (off + len)) (o + (off + len)) (xs.drop (off + len))
          (hx.drop _) (by simp) (Evm.Functions.rlp_cursor_advance c (off + len)) i' f' (by omega)
      rw [← next_eq]
      have hw := decode_word_eval hs σ o xs hx l off len hfit
      have hu := decode_u256_eval hs σ o xs hx l off len hfit hpos (Nat.lt_trans hlt (by decide))
      have h64 := decode_uint64_eval hs o xs hx σ l off len hfit hpos (Nat.lt_trans hlt (by decide))
      have hreg := run_readReg _ _ hs σ hσ
      by_cases h0 : i = 0 ∨ i = 3
      · have hsp : stepSpec (profMax prof) (profLimit prof) xs i l off len (sharedOf f) =
            if l = true ∨ 32 < len then none else some (sharedOf f) := by
          simp [stepSpec, h0]
        rw [hsp]
        rcases h0 with rfl | rfl
        all_goals
          simp [hn, hd, hw]
          by_cases hc : l = true ∨ 32 < len
          · simp [hc, RunRel]
          · simp only [hc, if_false, Option.bind_some]
            exact hrec _ _ _ (by simp [sharedOf])
      by_cases h15 : i = 15
      · subst h15
        simp [hn, hd, hu, stepSpec]
        by_cases hc : l = true ∨ 32 < len ∨ uintCanon xs off len = false
        · simp [hc, RunRel]
        · simp only [hc, if_false, Option.bind_some]
          exact hrec _ _ _ (by simp [sharedOf])
      by_cases h17 : i = 17
      · subst h17
        have e17 : (2 : Int) ^i 17 = 131072 := by decide
        simp [hn, hd, h64, stepSpec]
        by_cases hc : l = false ∧ len ≤ 8 ∧ uintCanon xs off len = true
        · obtain ⟨rfl, h8, hcn⟩ := hc
          simp [h8, hcn, hreg, e17, blobA, show ¬ 8 < len by omega]
          by_cases ha : bigEndian ((xs.drop off).take len) / 131072 ≤ profMax prof ∧
              bigEndian ((xs.drop off).take len) = 131072 * (bigEndian ((xs.drop off).take len) / 131072)
          · have ha' := ha
            simp only [profMax] at ha'
            rw [if_pos ha', if_pos ha]
            simp only [run_pure, Option.bind_some]
            refine hrec _ _ _ ?_
            simp [sharedOf]
            exact ha.2.symm
          · have ha' := ha
            simp only [profMax] at ha'
            rw [if_neg ha', if_neg ha]
            simp [RunRel, Evm.Functions.fatal_error]
            rfl
        · have hc' : l = true ∨ 8 < len ∨ uintCanon xs off len = false := by
            by_cases a : l = true
            · exact .inl a
            by_cases b : 8 < len
            · exact .inr (.inl b)
            right; right
            cases h : uintCanon xs off len
            · rfl
            · exact absurd ⟨by simpa using a, by omega, h⟩ hc
          simp [hc, hc', RunRel]
      by_cases h18 : i = 18
      · subst h18
        simp [hn, hd, h64, stepSpec]
        by_cases hc : l = false ∧ len ≤ 8 ∧ uintCanon xs off len = true
        · obtain ⟨rfl, h8, hcn⟩ := hc
          simp [h8, hcn, hreg, show ¬ 8 < len by omega]
          by_cases ha : bigEndian ((xs.drop off).take len) ≤ profLimit prof
          · have ha' := ha
            simp only [profLimit] at ha'
            rw [if_pos ha', if_pos ha]
            simp only [run_pure, Option.bind_some]
            exact hrec _ _ _ (by simp [sharedOf])
          · have ha' := ha
            simp only [profLimit] at ha'
            rw [if_neg ha', if_neg ha]
            simp [RunRel, Evm.Functions.fatal_error]
            rfl
        · have hc' : l = true ∨ 8 < len ∨ uintCanon xs off len = false := by
            by_cases a : l = true
            · exact .inl a
            by_cases b : 8 < len
            · exact .inr (.inl b)
            right; right
            cases h : uintCanon xs off len
            · rfl
            · exact absurd ⟨by simpa using a, by omega, h⟩ hc
          simp [hc, hc', RunRel]
      have h0a : i ≠ 0 := fun h => h0 (.inl h)
      have h0b : i ≠ 3 := fun h => h0 (.inr h)
      simp [hn, hd, stepSpec, h0a, h0b, h15, h17, h18]
      exact hrec _ _ _ rfl

/-- `rlp_node_cursor` on the whole input: the payload's offset and length, or `none` where it
calls `fatal_error RlpDecode` (empty input, no header, header plus payload not exactly the input,
or not a list). -/
def sailNode (input : List Byte) : Option (Nat × Nat) :=
  if input = [] then none else
  match sailHeader input with
  | none => none
  | some (l, off, len) => if off + len = input.length ∧ l = true then some (off, len) else none

theorem node_cursor_eval (hs : Evm.HostState) (input : List Byte) (hin : hs.inputBytes = input.toArray)
    (σ : SailRegs) :
    ((Evm.Functions.rlp_node_cursor ⟨0, ⟨input.length, {}⟩⟩).run hs).run σ =
      match sailNode input with
      | none => .error .Exit σ
      | some (_, len) => .ok (⟨0 + (input.length - len), ⟨len, {}⟩⟩, hs) σ := by
  have hh := ref_hdr_eval hs 0 input (sliceAt_whole hs input hin) σ {}
  simp only [Evm.Functions.rlp_node_cursor, Evm.Functions.rlp_single_ref]
  by_cases he : input = []
  · subst he; simp [sailNode, Evm.Functions.fatal_error]
  have hne : input.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
  simp [hne, sailNode, he]
  rcases hsh : sailHeader input with _ | ⟨l, off, len⟩
  · rw [hsh] at hh; simp [hh]
  · rw [hsh] at hh
    simp only [hh]
    by_cases hc : off ≤ input.length ∧ len = input.length - off
    · rw [if_pos hc]
      cases l
      · simp [Evm.Functions.rlp_decode_list, Evm.Functions.fatal_error]
        rfl
      · have : off + len = input.length := by omega
        simp [this, Evm.Functions.rlp_decode_list]
    · rw [if_neg hc]
      have : ¬ (off + len = input.length ∧ l = true) := fun h => hc ⟨by omega, by omega⟩
      simp [this, Evm.Functions.fatal_error]

/-- EVM-Sail's parent-header decoding of `input` (the body of `_rec_index_witness_header_cursor`
for one header): `rlp_node_cursor`, then `decode_parent_header_fields cursor 0 EMPTY`. -/
def parentAction (input : List Byte) : Evm.SailM Evm.Defs.ParentHeaderFields := do
  let ⟨_, ⟨_, c⟩⟩ ← Evm.Functions.rlp_node_cursor ⟨0, ⟨input.length, {}⟩⟩
  Evm.Functions.decode_parent_header_fields c 0 Evm.Functions.EMPTY_PARENT_HEADER_FIELDS

/-- `parentAction` in closed form, on the shared fields. -/
def sailParent (maxB limit : Nat) (input : List Byte) : Option Shared :=
  match sailNode input with
  | none => none
  | some (off, _) => fieldsSpec maxB limit (input.drop off) 0 ⟨none, none, none⟩

theorem parent_eval (input : List Byte) (σ : SailRegs) (prof : Evm.Defs.ExecutionProfile)
    (hσ : σ.regs.get? .k_execution_profile = some prof) :
    RunRel (hostOf input) σ (((parentAction input).run (hostOf input)).run σ)
      (sailParent (profMax prof) (profLimit prof) input) := by
  have hn := node_cursor_eval (hostOf input) input rfl σ
  unfold parentAction sailParent
  rcases hs : sailNode input with _ | ⟨off, len⟩
  · rw [hs] at hn
    rw [run_bind_error _ _ _ _ _ hn]
    simp [RunRel]
  · rw [hs] at hn
    rw [run_bind_ok _ _ _ _ _ hn]
    have hfit : off + len = input.length := by
      unfold sailNode at hs
      split at hs
      · cases hs
      · split at hs
        · cases hs
        · split at hs
          · rename_i hc; simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs; exact hc.1
          · cases hs
    have hoff : input.length - len = off := by omega
    simp only [Evm.Functions.decode_parent_header_fields]
    rw [if_neg (by simp)]
    have := fields_eval (hostOf input) σ prof hσ ((len : Int).toNat + 1) len (0 + (input.length - len))
      (input.drop (input.length - len)) ((sliceAt_whole _ input rfl).drop _) (by simp; omega) {} 0
      Evm.Functions.EMPTY_PARENT_HEADER_FIELDS (by simp)
    have hd : input.drop (input.length - len) = input.drop off := by rw [hoff]
    have he : sharedOf Evm.Functions.EMPTY_PARENT_HEADER_FIELDS = ⟨none, none, none⟩ := rfl
    rw [hd, he] at this
    exact this

end ZesuExec.Compliance
