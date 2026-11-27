import ZesuExec.Compliance.ParentHeaderSail
import ZesuExec.Compliance.F2
import ZesuExec.Fn.F6.Spec

/-!
# The candidate `walk` against Sail's `sailParent`, modulo known-bug triggers

Pure part of F6's compliance. `scan` follows the candidate's field walk (`Fn.F6.fieldWalk`) and
records the fields it reaches; the triggers are conditions on those fields (`stepTrig`) or on the
whole input (`missing`, `trailingBytes`, `trailingItems`), one per class of zesislar's
`ParentHeaderBugTriggers.v`. `parent_agree`: if no trigger holds, Sail's result on the shared
fields relates to the candidate's (`Rel`).
-/

namespace ZesuExec.Compliance
open ZesuExec ZesuExec.Fn.F6
open ZesuExec.Compliance.F2 (ofSail item_agrees)
open ZesuExec.Fn.F2 (Item decode bigEndian checkedPayload)

/-! ## The candidate's reached fields -/

inductive WalkEnd
  | missing
  | stop
  | done (rest : List Byte)
  deriving DecidableEq

/-- The fields the candidate walk reaches (`(index, bytes left)` for each non-empty one), and how
it ends: a missing required field, a stop (rejection or an absent optional field), or the end of
the schedule with the bytes after field 18. -/
def scan : List Kind → Nat → List Byte → List (Nat × List Byte) × WalkEnd
  | [], _, rem => ([], .done rem)
  | k :: later, i, rem =>
    match rem with
    | [] => ([], if k.required then .missing else .stop)
    | _ :: _ =>
      match decode rem with
      | .error => ([(i, rem)], .stop)
      | .success b h p =>
        if k.isInt ∧ (b = true ∨ 8 < p) then ([(i, rem)], .stop)
        else
          let r := scan later (i + 1) (rem.drop ((h + p) % 2 ^ 64))
          ((i, rem) :: r.1, r.2)

/-- The outer item's payload, when the outer item is a list inside the input. -/
def outerPayload (input : List Byte) : Option (List Byte) :=
  match decode input with
  | .success true h p => if h + p ≤ input.length then some ((input.drop h).take p) else none
  | _ => none

/-- `rlp_decode_item` accepts every item of `xs` in turn. -/
inductive ItemsOK : List Byte → Prop
  | nil : ItemsOK []
  | cons {xs : List Byte} {l : Bool} {off len : Nat} :
      sailItem xs = some (l, off, len) → ItemsOK (xs.drop (off + len)) → ItemsOK xs

/-! ## Triggers -/

/-- `RlpLongLengthWrap`: the item's header plus payload length reaches `2^64`. -/
def wrapAt (rem : List Byte) : Prop :=
  ∃ b h p, decode rem = .success b h p ∧ 2 ^ 64 ≤ h + p

/-- `ParentHeaderSkippedFieldShape`: field 0 or 3 is a list or longer than 32 bytes. -/
def shapeAt (i : Nat) (rem : List Byte) : Prop :=
  (i = 0 ∨ i = 3) ∧ ∃ b h p, decode rem = .success b h p ∧ (b = true ∨ 32 < p)

/-- `ParentHeaderUndecodedFieldRejected`: field 9, 10 or 11 decodes without a wrap and is a list
or longer than 8 bytes. -/
def undecodedAt (i : Nat) (rem : List Byte) : Prop :=
  (i = 9 ∨ i = 10 ∨ i = 11) ∧
    ∃ b h p, decode rem = .success b h p ∧ h + p < 2 ^ 64 ∧ (b = true ∨ 8 < p)

/-- `RlpUintNonCanonical`: field 15, 17 or 18 is a string of at most 8 bytes that Sail's
`rlp_item_uint_canonical` rejects. -/
def nonCanonAt (i : Nat) (rem : List Byte) : Prop :=
  (i = 15 ∨ i = 17 ∨ i = 18) ∧
    ∃ h p, decode rem = .success false h p ∧ p ≤ 8 ∧ uintCanon rem h p = false

/-- `ParentHeaderUintOver8`: field 15 is a canonical string of 9 to 32 bytes. -/
def over8At (i : Nat) (rem : List Byte) : Prop :=
  i = 15 ∧ ∃ h p, decode rem = .success false h p ∧ 8 < p ∧ p ≤ 32 ∧ uintCanon rem h p = true

/-- `ParentHeaderBlobGasUnaligned`: field 17 is a canonical integer that is not a whole number
of blobs (`2^17` gas each) or has more blobs than the profile's maximum. -/
def blobAt (maxB i : Nat) (rem : List Byte) : Prop :=
  i = 17 ∧ ∃ h p, decode rem = .success false h p ∧ p ≤ 8 ∧ uintCanon rem h p = true ∧
    ¬ (bigEndian ((rem.drop h).take p) / 2 ^ 17 ≤ maxB ∧
      bigEndian ((rem.drop h).take p) = 2 ^ 17 * (bigEndian ((rem.drop h).take p) / 2 ^ 17))

/-- `ParentHeaderExcessBlobGasAboveLimit`: field 18 is a canonical integer above the profile's
excess-blob-gas limit. -/
def excessAt (limit i : Nat) (rem : List Byte) : Prop :=
  i = 18 ∧ ∃ h p, decode rem = .success false h p ∧ p ≤ 8 ∧ uintCanon rem h p = true ∧
    limit < bigEndian ((rem.drop h).take p)

def stepTrig (maxB limit i : Nat) (rem : List Byte) : Prop :=
  wrapAt rem ∨ shapeAt i rem ∨ undecodedAt i rem ∨ nonCanonAt i rem ∨ over8At i rem ∨
    blobAt maxB i rem ∨ excessAt limit i rem

/-- A reached field of the candidate walk satisfies `P`. -/
def AtField (P : Nat → List Byte → Prop) (input : List Byte) : Prop :=
  ∃ pl, outerPayload input = some pl ∧ ∃ e ∈ (scan schedule 0 pl).1, P e.1 e.2

/-- `ParentHeaderMissingRequiredField`: the outer list ends before field 12. -/
def missing (input : List Byte) : Prop :=
  ∃ pl, outerPayload input = some pl ∧ (scan schedule 0 pl).2 = .missing

/-- `ParentHeaderTrailingBytes`: the outer item ends before the input. -/
def trailingBytes (input : List Byte) : Prop :=
  ∃ b h p, decode input = .success b h p ∧ h + p < input.length

/-- `ParentHeaderTrailingItemMalformed`: after field 18 the outer payload is not a sequence of
items `rlp_decode_item` accepts. -/
def trailingItems (input : List Byte) : Prop :=
  ∃ pl rest, outerPayload input = some pl ∧ (scan schedule 0 pl).2 = .done rest ∧ ¬ ItemsOK rest

/-! ## Agreement -/

/-- Sail's shared fields against the candidate's values: both reject, or both accept with base
fee, blob gas used and excess blob gas the candidate's values 3, 4, 5, all below `2^64`. -/
def Rel : Option Shared → Option (List Nat) → Prop
  | none, none => True
  | some s, some vals => s = ⟨vals[3]?, vals[4]?, vals[5]?⟩ ∧ ∀ v ∈ vals, v < 2 ^ 64
  | _, _ => False

/-- The number of integer fields before field `i`. -/
def cnt (i : Nat) : Nat := ((schedule.take i).filter Kind.isInt).length

def Inv (i : Nat) (vals : List Nat) (s : Shared) : Prop :=
  vals.length = cnt i ∧ s = ⟨vals[3]?, vals[4]?, vals[5]?⟩ ∧ ∀ v ∈ vals, v < 2 ^ 64

theorem sailItem_decode (xs : List Byte) (l : Bool) (off len : Nat)
    (h : sailItem xs = some (l, off, len)) : decode xs = .success l off len := by
  rcases item_agrees xs with hd | ⟨_, _, _, _, _, hs⟩
  · rw [hd, h]; rfl
  · rw [hs] at h; cases h

/-- On a non-wrapping successful decode, Sail's item is the same. -/
theorem decode_sailItem (xs : List Byte) (b : Bool) (h p : Nat)
    (hd : decode xs = .success b h p) (hw : h + p < 2 ^ 64) : sailItem xs = some (b, h, p) := by
  rcases item_agrees xs with hd' | ⟨_, h', p', hd', hw', _⟩
  · rw [hd] at hd'
    revert hd'
    rcases sailItem xs with _ | ⟨l, off, len⟩
    · intro e; cases e
    · intro e; simp only [ofSail, Item.success.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e; rfl
  · rw [hd] at hd'; cases hd'; omega

theorem fields_items (maxB limit : Nat) (s : Shared) :
    ∀ xs, ItemsOK xs → fieldsSpec maxB limit xs 19 s = some s := by
  intro xs hx
  induction hx with
  | nil => exact fieldsSpec_nil _ _ _ _
  | @cons xs l off len hs _ ih =>
    have hne : xs ≠ [] := by intro h; subst h; simp [sailItem, sailHeader] at hs
    rw [fieldsSpec_some _ _ _ _ _ hne _ _ _ hs]
    simp [stepSpec, nextIdx, ih]

theorem fields_not_items (maxB limit : Nat) (s : Shared) :
    ∀ n xs, xs.length < n → ¬ ItemsOK xs → fieldsSpec maxB limit xs 19 s = none := by
  intro n
  induction n with
  | zero => intro xs h; omega
  | succ n ih =>
    intro xs hl hn
    by_cases hne : xs = []
    · subst hne; exact absurd .nil hn
    rcases hs : sailItem xs with _ | ⟨l, off, len⟩
    · exact fieldsSpec_none _ _ _ _ _ hne hs
    · rw [fieldsSpec_some _ _ _ _ _ hne _ _ _ hs]
      have := sailItem_len_lt xs l off len hs
      simp only [stepSpec, nextIdx]
      simp
      exact ih _ (by simp; omega) (fun h => hn (.cons hs h))

theorem cnt_le (i : Nat) (hi : i ≤ 11) : cnt i ≤ 2 := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem drop_schedule (i : Nat) (k : Kind) (later : List Kind) (hk : schedule.drop i = k :: later) :
    i < 19 ∧ later = schedule.drop (i + 1) ∧
      cnt (i + 1) = cnt i + (if k.isInt then 1 else 0) := by
  have hi : i < 19 := by
    by_cases h : i < 19
    · exact h
    · rw [List.drop_eq_nil_of_le (by simp [schedule]; omega)] at hk
      cases hk
  refine ⟨hi, ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [schedule, List.drop, List.cons.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨rfl, by decide⟩

/-- One reached field: the candidate and Sail both stop, or both continue with the invariant. -/
def StepOK (maxB limit i : Nat) (k : Kind) (rem : List Byte) (b : Bool) (h p : Nat)
    (vals : List Nat) (s : Shared) : Prop :=
  ((k.isInt = true ∧ (b = true ∨ 8 < p)) ∧ stepSpec maxB limit rem i b h p s = none) ∨
  (¬ (k.isInt = true ∧ (b = true ∨ 8 < p)) ∧ ∃ s', stepSpec maxB limit rem i b h p s = some s' ∧
    Inv (i + 1) (if k.isInt then vals ++ [bigEndian ((rem.drop h).take p)] else vals) s')

theorem inv_skip (i : Nat) (vals : List Nat) (s : Shared) (hinv : Inv i vals s)
    (hc : cnt (i + 1) = cnt i) : Inv (i + 1) vals s :=
  ⟨by rw [hinv.1, hc], hinv.2.1, hinv.2.2⟩

theorem inv_low (i : Nat) (vals : List Nat) (s : Shared) (v : Nat) (hinv : Inv i vals s)
    (hi : i ≤ 11) (hc : cnt (i + 1) = cnt i + 1) (hv : v < 2 ^ 64) :
    Inv (i + 1) (vals ++ [v]) s := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have := cnt_le i hi
  refine ⟨by simp [h1, hc], ?_, ?_⟩
  · rw [h2]
    simp [List.getElem?_eq_none (show vals.length ≤ 3 by omega),
      List.getElem?_eq_none (show vals.length ≤ 4 by omega),
      List.getElem?_eq_none (show vals.length ≤ 5 by omega),
      List.getElem?_append_right (show vals.length ≤ 3 by omega),
      List.getElem?_append_right (show vals.length ≤ 4 by omega),
      List.getElem?_append_right (show vals.length ≤ 5 by omega)]
    omega
  · intro x hx
    simp at hx
    rcases hx with hx | rfl
    · exact h3 x hx
    · exact hv

theorem inv_hi (i : Nat) (vals : List Nat) (s : Shared) (v : Nat) (hinv : Inv i vals s)
    (hc : cnt (i + 1) = cnt i + 1) (hv : v < 2 ^ 64) :
    Inv (i + 1) (vals ++ [v]) ⟨(vals ++ [v])[3]?, (vals ++ [v])[4]?, (vals ++ [v])[5]?⟩ := by
  obtain ⟨h1, -, h3⟩ := hinv
  refine ⟨by simp [h1, hc], rfl, ?_⟩
  intro x hx
  simp at hx
  rcases hx with hx | rfl
  · exact h3 x hx
  · exact hv

theorem shared_app (vals : List Nat) (s : Shared) (v : Nat) (hs : s = ⟨vals[3]?, vals[4]?, vals[5]?⟩)
    (n : Nat) (hn : vals.length = n) :
    (n = 3 → (⟨(vals ++ [v])[3]?, (vals ++ [v])[4]?, (vals ++ [v])[5]?⟩ : Shared) =
      { s with base := some v }) ∧
    (n = 4 → (⟨(vals ++ [v])[3]?, (vals ++ [v])[4]?, (vals ++ [v])[5]?⟩ : Shared) =
      { s with blob := some v }) ∧
    (n = 5 → (⟨(vals ++ [v])[3]?, (vals ++ [v])[4]?, (vals ++ [v])[5]?⟩ : Shared) =
      { s with excess := some v }) := by
  subst hs
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h <;>
    simp [hn]

theorem stepOK (maxB limit i : Nat) (k : Kind) (later : List Kind) (hk : schedule.drop i = k :: later)
    (rem : List Byte) (b : Bool) (h p : Nat) (hd : decode rem = .success b h p)
    (vals : List Nat) (s : Shared) (hinv : Inv i vals s) (hno : ¬ stepTrig maxB limit i rem) :
    StepOK maxB limit i k rem b h p vals s := by
  obtain ⟨hi, -, hc⟩ := drop_schedule i k later hk
  have hw : h + p < 2 ^ 64 := Nat.lt_of_not_le fun hw => hno (.inl ⟨b, h, p, hd, hw⟩)
  have hv8 : p ≤ 8 → bigEndian ((rem.drop h).take p) < 2 ^ 64 := fun h8 => bigEndian_take_lt _ _ h8
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
    i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [schedule, List.drop, List.cons.injEq] at hk
  all_goals obtain ⟨rfl, -⟩ := hk
  all_goals simp only [StepOK, Kind.isInt, Bool.false_eq_true, false_and, if_false, if_true,
    true_and, not_false_eq_true, Nat.reduceAdd] at hc ⊢
  -- word fields 0 and 3
  case inl | inr.inr.inr.inl =>
    by_cases hb : b = true ∨ 32 < p
    · exact absurd (.inr (.inl ⟨by decide, b, h, p, hd, hb⟩)) hno
    · exact .inr ⟨s, by simp [stepSpec, hb], inv_skip _ _ _ hinv (by simpa using hc)⟩
  all_goals try (first
    | exact .inr ⟨s, by simp [stepSpec], inv_skip _ _ _ hinv (by simpa using hc)⟩
    | (by_cases hb : b = true ∨ 8 < p
       · exact absurd (.inr (.inr (.inl ⟨by decide, b, h, p, hd, hw, hb⟩))) hno
       · exact .inr ⟨hb, s, by simp [stepSpec],
           inv_low _ _ _ _ hinv (by decide) (by simpa using hc) (hv8 (by omega))⟩))
  · -- field 15: base fee
    by_cases hb : b = true ∨ 8 < p
    · left
      refine ⟨hb, ?_⟩
      by_cases hx : b = true ∨ 32 < p ∨ uintCanon rem h p = false
      · simp [stepSpec, hx]
      · exfalso
        have hb' : b = false := by
          cases b
          · rfl
          · exact absurd (.inl rfl) hx
        subst hb'
        have h8 : 8 < p := by
          rcases hb with hb | hb
          · cases hb
          · exact hb
        have h32 : p ≤ 32 := Nat.le_of_not_lt fun h' => hx (.inr (.inl h'))
        have hcn : uintCanon rem h p = true := by
          cases hq : uintCanon rem h p
          · exact absurd (.inr (.inr hq)) hx
          · rfl
        exact hno (.inr (.inr (.inr (.inr (.inl ⟨rfl, h, p, hd, h8, h32, hcn⟩)))))
    · right
      refine ⟨hb, ?_⟩
      have hp8 : p ≤ 8 := Nat.le_of_not_lt fun h' => hb (.inr h')
      have hb' : b = false := by cases b <;> simp_all
      subst hb'
      cases hcn : uintCanon rem h p
      · exact absurd (.inr (.inr (.inr (.inl ⟨by decide, h, p, hd, by omega, hcn⟩)))) hno
      · refine ⟨_, ?_, inv_hi _ _ _ _ hinv (by simpa using hc) (hv8 hp8)⟩
        rw [(shared_app vals s _ hinv.2.1 3 (by rw [hinv.1]; decide)).1 rfl]
        simp [stepSpec, hcn, show ¬ 32 < p by omega]
  · -- field 17: blob gas used
    by_cases hb : b = true ∨ 8 < p
    · have hx : b = true ∨ 8 < p ∨ uintCanon rem h p = false := by
        rcases hb with hb | hb
        · exact .inl hb
        · exact .inr (.inl hb)
      exact .inl ⟨hb, by simp [stepSpec, hx]⟩
    · right
      refine ⟨hb, ?_⟩
      have hp8 : p ≤ 8 := Nat.le_of_not_lt fun h' => hb (.inr h')
      have hb' : b = false := by cases b <;> simp_all
      subst hb'
      cases hcn : uintCanon rem h p
      · exact absurd (.inr (.inr (.inr (.inl ⟨by decide, h, p, hd, by omega, hcn⟩)))) hno
      · by_cases ha : bigEndian ((rem.drop h).take p) / 2 ^ 17 ≤ maxB ∧
            bigEndian ((rem.drop h).take p) = 2 ^ 17 * (bigEndian ((rem.drop h).take p) / 2 ^ 17)
        · refine ⟨_, ?_, inv_hi _ _ _ _ hinv (by simpa using hc) (hv8 hp8)⟩
          rw [(shared_app vals s _ hinv.2.1 4 (by rw [hinv.1]; decide)).2.1 rfl]
          simp only [stepSpec]
          simp [hcn, show ¬ 8 < p by omega]
          exact ha
        · exact absurd (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, h, p, hd, by omega, hcn, ha⟩))))))
            hno
  · -- field 18: excess blob gas
    by_cases hb : b = true ∨ 8 < p
    · have hx : b = true ∨ 8 < p ∨ uintCanon rem h p = false := by
        rcases hb with hb | hb
        · exact .inl hb
        · exact .inr (.inl hb)
      exact .inl ⟨hb, by simp [stepSpec, hx]⟩
    · right
      refine ⟨hb, ?_⟩
      have hp8 : p ≤ 8 := Nat.le_of_not_lt fun h' => hb (.inr h')
      have hb' : b = false := by cases b <;> simp_all
      subst hb'
      cases hcn : uintCanon rem h p
      · exact absurd (.inr (.inr (.inr (.inl ⟨by decide, h, p, hd, by omega, hcn⟩)))) hno
      · by_cases ha : bigEndian ((rem.drop h).take p) ≤ limit
        · refine ⟨_, ?_, inv_hi _ _ _ _ hinv (by simpa using hc) (hv8 hp8)⟩
          rw [(shared_app vals s _ hinv.2.1 5 (by rw [hinv.1]; decide)).2.2 rfl]
          simp [stepSpec, hcn, show ¬ 8 < p by omega, ha]
        · exact absurd (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, h, p, hd, by omega, hcn,
            by omega⟩)))))) hno

theorem walk_agree (maxB limit : Nat) :
    ∀ ks i rem vals s, schedule.drop i = ks → i ≤ 19 → Inv i vals s →
      (∀ e ∈ (scan ks i rem).1, ¬ stepTrig maxB limit e.1 e.2) →
      (scan ks i rem).2 ≠ .missing →
      (∀ rest, (scan ks i rem).2 = .done rest → ItemsOK rest) →
      Rel (fieldsSpec maxB limit rem i s) (fieldWalk ks rem vals) := by
  intro ks
  induction ks with
  | nil =>
    intro i rem vals s hk hi hinv _ _ hrest
    have hi19 : i = 19 := by
      by_cases h : i < 19
      · have : (schedule.drop i).length = 19 - i := by simp [schedule]
        rw [hk] at this; simp at this; omega
      · omega
    subst hi19
    rw [fields_items maxB limit s rem (hrest rem rfl)]
    exact ⟨hinv.2.1, hinv.2.2⟩
  | cons k later ih =>
    intro i rem vals s hk hi hinv htr hmiss hrest
    obtain ⟨hi19, hlater, hc⟩ := drop_schedule i k later hk
    cases rem with
    | nil =>
      cases hreq : k.required
      · simp only [fieldWalk, hreq, fieldsSpec_nil]
        exact ⟨hinv.2.1, hinv.2.2⟩
      · simp [scan, hreq] at hmiss
    | cons x xs =>
      have hne : x :: xs ≠ [] := List.cons_ne_nil x xs
      cases hd : decode (x :: xs) with
      | error =>
        have hsi : sailItem (x :: xs) = none := by
          cases hq : sailItem (x :: xs) with
          | none => rfl
          | some r =>
            obtain ⟨l, off, len⟩ := r
            rw [sailItem_decode _ _ _ _ hq] at hd; cases hd
        simp only [fieldWalk, hd, fieldsSpec_none _ _ _ _ _ hne hsi]
        trivial
      | success b h p =>
        have hscan : (scan (k :: later) i (x :: xs)).1 ≠ [] → (i, x :: xs) ∈ (scan (k :: later) i (x :: xs)).1 := by
          intro _; simp only [scan, hd]; split <;> simp
        have hno : ¬ stepTrig maxB limit i (x :: xs) := htr (i, x :: xs) (hscan (by simp only [scan, hd]; split <;> simp))
        have hw : h + p < 2 ^ 64 := Nat.lt_of_not_le fun hw => hno (.inl ⟨b, h, p, hd, hw⟩)
        have hsi := decode_sailItem _ _ _ _ hd hw
        rw [fieldsSpec_some _ _ _ _ _ hne _ _ _ hsi]
        have hmod : (h + p) % 2 ^ 64 = h + p := Nat.mod_eq_of_lt hw
        rcases stepOK maxB limit i k later hk (x :: xs) b h p hd vals s hinv hno with
          ⟨hstop, hsp⟩ | ⟨hgo, s', hsp, hinv'⟩
        · rw [hsp]
          obtain ⟨hint, hb⟩ := hstop
          have : (b || decide (8 < p)) = true := by
            rcases hb with hb | hb <;> simp [hb]
          simp [fieldWalk, hd, hint, this, Rel]
        · rw [hsp]
          simp only [Option.bind_some, nextIdx, if_pos hi19]
          have hscan' : scan (k :: later) i (x :: xs) =
              ((i, x :: xs) :: (scan later (i + 1) ((x :: xs).drop (h + p))).1,
                (scan later (i + 1) ((x :: xs).drop (h + p))).2) := by
            simp only [scan, hd, hmod, if_neg hgo]
          have hfw : fieldWalk (k :: later) (x :: xs) vals =
              fieldWalk later ((x :: xs).drop (h + p))
                (if k.isInt then vals ++ [bigEndian (((x :: xs).drop h).take p)] else vals) := by
            simp only [fieldWalk, hd, hmod]
            cases hk' : k.isInt
            · simp
            · have : (b || decide (8 < p)) = false := by
                simp only [hk', true_and] at hgo
                cases b <;> simp_all
              simp [this]
          rw [hfw]
          rw [hscan'] at htr hmiss hrest
          exact ih (i + 1) _ _ s' hlater.symm (by omega) hinv'
            (fun e he => htr e (List.mem_cons_of_mem _ he)) hmiss hrest

theorem decode_sailHeader (x : List Byte) (l : Bool) (h p : Nat)
    (hd : decode x = .success l h p) : sailHeader x = some (l, h, p) := by
  cases x with
  | nil => cases hd
  | cons b rest =>
    have hb := b.isLt
    have hc : ∀ len h' p' l', checkedPayload len h' p' l' = .success l h p → l' = l ∧ h' = h ∧ p' = p := by
      intro len h' p' l' hc
      unfold checkedPayload at hc
      split at hc
      · cases hc; exact ⟨rfl, rfl, rfl⟩
      · cases hc
    simp only [decode] at hd
    simp only [sailHeader]
    by_cases c1 : b.toNat ≤ 127
    · rw [if_pos c1] at hd; cases hd; rw [if_pos (by omega)]
    rw [if_neg c1] at hd; rw [if_neg (by omega)]
    by_cases c0 : b.toNat = 128
    · rw [if_pos c0] at hd; cases hd; rw [if_pos (by omega)]; simp [c0]
    rw [if_neg c0] at hd
    by_cases c2 : b.toNat ≤ 183
    · rw [if_pos c2] at hd; rw [if_pos (by omega)]
      obtain ⟨rfl, rfl, rfl⟩ := hc _ _ _ _ hd; rfl
    rw [if_neg c2] at hd; rw [if_neg (by omega)]
    by_cases c3 : b.toNat ≤ 191
    · rw [if_pos c3] at hd; rw [if_pos (by omega)]
      split at hd
      · obtain ⟨rfl, rfl, rfl⟩ := hc _ _ _ _ hd
        rw [if_pos (by simp at *; omega)]
      · cases hd
    rw [if_neg c3] at hd; rw [if_neg (by omega)]
    by_cases c5 : b.toNat ≤ 247
    · rw [if_pos c5] at hd; rw [if_pos (by omega)]
      obtain ⟨rfl, rfl, rfl⟩ := hc _ _ _ _ hd; rfl
    rw [if_neg c5] at hd; rw [if_neg (by omega)]
    split at hd
    · obtain ⟨rfl, rfl, rfl⟩ := hc _ _ _ _ hd
      rw [if_pos (by simp at *; omega)]
    · cases hd

theorem sailNode_item (input : List Byte) (off len : Nat) (h : sailNode input = some (off, len)) :
    decode input = .success true off len ∧ off + len = input.length := by
  unfold sailNode at h
  split at h
  · cases h
  rename_i hne
  split at h
  · cases h
  rename_i l off' len' hh
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hfit, rfl⟩ := hc
    have hpos : 0 < off' + len' := by
      have : input.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
      omega
    have : sailItem input = some (true, off', len') := by
      simp [sailItem, hh, hfit, hne]
    exact ⟨sailItem_decode _ _ _ _ this, hfit⟩
  · cases h

/-- (b), pure: Sail's parent-header result relates to the candidate's, or a trigger holds. -/
theorem parent_agree (maxB limit : Nat) (input : List Byte) :
    Rel (sailParent maxB limit input) (walk input) ∨ AtField (stepTrig maxB limit) input ∨
      missing input ∨ trailingBytes input ∨ trailingItems input := by
  have hnode : ∀ off len, sailNode input = some (off, len) →
      decode input = .success true off len ∧ off + len = input.length := sailNode_item input
  cases hd : decode input with
  | error =>
    left
    have : sailNode input = none := by
      cases hq : sailNode input with
      | none => rfl
      | some r => obtain ⟨off, len⟩ := r; rw [(hnode off len hq).1] at hd; cases hd
    simp [sailParent, this, walk, hd, Rel]
  | success b h p =>
    by_cases ht : h + p < input.length
    · exact .inr (.inr (.inr (.inl ⟨b, h, p, hd, ht⟩)))
    have hnone : (b = false ∨ h + p ≠ input.length) → sailNode input = none := by
      intro hb
      cases hq : sailNode input with
      | none => rfl
      | some r =>
        obtain ⟨off, len⟩ := r
        obtain ⟨h1, h2⟩ := hnode off len hq
        rw [hd] at h1; cases h1
        rcases hb with hb | hb
        · cases hb
        · exact absurd h2 hb
    by_cases hfit : h + p = input.length ∧ b = true
    · obtain ⟨hfit, rfl⟩ := hfit
      have hsh := decode_sailHeader input true h p hd
      have hne : input ≠ [] := by intro e; subst e; cases hd
      have hn : sailNode input = some (h, p) := by
        simp [sailNode, hne, hsh, hfit]
      have hpl : (input.drop h).take p = input.drop h := by
        apply List.take_of_length_le; simp; omega
      have hop : outerPayload input = some (input.drop h) := by
        simp [outerPayload, hd, hfit, hpl]
      by_cases hp : p = 0
      · subst hp
        right; right; left
        refine ⟨input.drop h, hop, ?_⟩
        rw [List.drop_eq_nil_of_le (by omega)]
        rfl
      · by_cases hA : AtField (stepTrig maxB limit) input
        · exact .inr (.inl hA)
        by_cases hM : missing input
        · exact .inr (.inr (.inl hM))
        by_cases hT : trailingItems input
        · exact .inr (.inr (.inr (.inr hT)))
        left
        have hw : walk input = fieldWalk schedule (input.drop h) [] := by
          simp [walk, hd, show 0 < p by omega, show h + p ≤ input.length by omega, hpl]
        rw [hw]
        simp only [sailParent, hn]
        refine walk_agree maxB limit schedule 0 (input.drop h) [] ⟨none, none, none⟩ rfl (by omega)
          ⟨rfl, rfl, by simp⟩ ?_ ?_ ?_
        · exact fun e he hs => hA ⟨_, hop, e, he, hs⟩
        · exact fun hm => hM ⟨_, hop, hm⟩
        · intro rest hr
          by_cases hi : ItemsOK rest
          · exact hi
          · exact absurd ⟨_, rest, hop, hr, hi⟩ hT
    · left
      have hb : b = false ∨ h + p ≠ input.length := by
        cases b
        · exact .inl rfl
        · exact .inr fun e => hfit ⟨e, rfl⟩
      have hw : walk input = none := by
        cases b
        · simp [walk, hd]
        · have : ¬ (0 < p ∧ h + p ≤ input.length) := fun e => hfit ⟨by omega, rfl⟩
          simp only [walk, hd, if_neg this]
      simp [sailParent, hnone hb, hw, Rel]

end ZesuExec.Compliance
