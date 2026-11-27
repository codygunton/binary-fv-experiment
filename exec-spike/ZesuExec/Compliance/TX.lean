import ZesuExec.Compliance.TXSail
import ZesuExec.Compliance.F2
import ZesuExec.Fn.TX.Spec
import ZesuExec.Sail.Run

/-!
# TX `rlp_decode.txAccessList`: compliance with EVM-Sail's `decode_access_list`

Transcribes zesislar's `TxAccessListMeaningModuloKnownBugs` (`ZesuSsz/Contracts/TxAccessListMeaning.v`)
with `txAccessListSailAgrees` (`ZesuSsz/Contracts/TxAccessListSailAgreementTheorem.v`) and the
triggers of `ZesuSsz/Contracts/TxAccessListBugTriggers.v`.

(a) The candidate is `ZesuExec.Fn.TX.candidate` (`candidateAccessList`); `TX.Post` states the
outcome through it (`OutcomeAllowed`).

(b) `sailRun input σ` is EVM-Sail's `rlp_decode_item` on the stateless input holding `input`,
then `decode_access_list` on the returned field (`accessRun`), from register state `σ`.
`tx_candidate_agrees`: on the domain (`TX.Domain`: every reached call's long length does not wrap
`2^64`, the first item fits Sail's `2^30`-byte limit), Sail's result relates to `candidate input`
(`SailRelates`: Sail returns a reference whose address and slot counts are the number of accepted
entries and keys, or both reject), or one of the three access-list triggers holds (`trig`):
an address string of at most 32 bytes but not 20, a key string shorter than 32 bytes, or bytes
after an entry's keys list. Sail's `encoded` span is not compared.

(c) `tx_compliance_of` / `tx_compliance_sail_of`: from `tx_spec` (passed as a hypothesis), the
binary reaches a state satisfying `Post` whose input satisfies the meaning; the `_sail` form
transfers it to the Sail RISC-V model by `sail_reaches`.
-/

namespace ZesuExec.Compliance.TX
open ZesuExec ZesuExec.Fn.F2 ZesuExec.Fn.TX ZesuExec.Compliance ZesuExec.Compliance.F2

/-! ## Known-bug triggers (`TxAccessListBugTriggers.v`) -/

/-- `accessListStringAtb`: a call at `site` whose item decodes as a string with payload length
passing `test`. -/
def stringAt (site : Nat) (test : Nat → Bool) (c : Call) : Bool :=
  c.1 == site && match decode c.2 with
    | .success false _ p => test p
    | _ => false

def addrC : Call → Bool := stringAt addressCall fun p => p != 20 && decide (p ≤ 32)
def keyC : Call → Bool := stringAt keyCall fun p => decide (p < 32)
def trailC (c : Call) : Bool :=
  c.1 == keysCall && match decode c.2 with
    | .success true h p => (itemRest c.2 h p).length != 0
    | _ => false

/-- A call meeting one of the three conditions. -/
def trigC (c : Call) : Bool := addrC c || keyC c || trailC c
def trig (cs : List Call) : Bool := cs.any trigC

/-- `txAccessListBugTrigger`: only the three access-list classes apply. -/
def bugTrigger : KnownBug → List Byte → Bool
  | .accessListAddressLength, input => (calls input).any addrC
  | .accessListKeyLength, input => (calls input).any keyC
  | .accessListEntryTrailingBytes, input => (calls input).any trailC
  | _, _ => false

def bugApplies (bug : KnownBug) (input : List Byte) : Prop := bugTrigger bug input = true

theorem trig_bug (input : List Byte) (h : trig (calls input) = true) :
    ∃ bug ∈ knownBugs, bugApplies bug input := by
  obtain ⟨c, hc, ht⟩ := List.any_eq_true.mp h
  simp only [trigC, Bool.or_eq_true] at ht
  rcases ht with (ht | ht) | ht
  · exact ⟨.accessListAddressLength, by simp [knownBugs], List.any_eq_true.mpr ⟨c, hc, ht⟩⟩
  · exact ⟨.accessListKeyLength, by simp [knownBugs], List.any_eq_true.mpr ⟨c, hc, ht⟩⟩
  · exact ⟨.accessListEntryTrailingBytes, by simp [knownBugs], List.any_eq_true.mpr ⟨c, hc, ht⟩⟩

/-! ## The candidate's items are Sail's on the domain -/

/-- On `HeaderFits` inputs the decoder is Sail's item decoder. -/
theorem fits_eq (xs : List Byte) (hf : HeaderFits xs) : decode xs = ofSail (sailItem xs) := by
  rcases item_agrees xs with h | ⟨l, h, p, hd, hw, -⟩
  · exact h
  exfalso
  cases xs with
  | nil => simp [decode] at hd
  | cons b rest =>
    have hb : b.toNat < 256 := b.isLt
    simp only [HeaderFits, longLengthWidth] at hf
    simp only [decode, checkedPayload] at hd
    repeat' (split at hd)
    all_goals first
      | (simp at hd; done)
      | (simp only [Item.success.injEq] at hd
         obtain ⟨-, rfl, rfl⟩ := hd
         first
           | omega
           | (rename_i h1 h2 h3 h4 h5
              rw [if_pos (by omega)] at hf
              omega)
           | (rw [if_neg (by omega), if_pos (by omega)] at hf
              omega))

theorem itemRest_eq (xs : List Byte) (h p : Nat) (hb : h + p < 2 ^ 64) :
    itemRest xs h p = xs.drop (h + p) := by
  simp only [itemRest, itemConsumed, Nat.mod_eq_of_lt hb]

/-! ## The walks against Sail's -/

theorem keysWalk_head (f : Nat) (b : Byte) (rest : List Byte) :
    (keyCall, b :: rest) ∈ (keysWalk (f + 1) (b :: rest)).1 := by
  simp only [keysWalk]
  split
  · split <;> simp
  · simp

theorem keys_rel : ∀ f1 f2 (xs : List Byte), xs.length ≤ f1 → xs.length < f2 →
    xs.length < 2 ^ 64 → (∀ c ∈ (keysWalk f1 xs).1, HeaderFits c.2) →
    (keysWalk f1 xs).2.map List.length = sailKeys f2 xs ∨ trig (keysWalk f1 xs).1 = true := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 xs h1 _ _ _
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; left; cases f2 <;> rfl
  | succ f ih =>
    intro f2 xs h1 h2 hb hf
    cases xs with
    | nil => left; cases f2 <;> rfl
    | cons b rest =>
    obtain ⟨g, rfl⟩ : ∃ g, f2 = g + 1 := ⟨f2 - 1, by simp at h2; omega⟩
    have he := fits_eq _ (hf _ (keysWalk_head f b rest))
    rcases hsi : sailItem (b :: rest) with _ | ⟨l, off, len⟩
    · rw [hsi] at he; left; simp [keysWalk, sailKeys, he, hsi, ofSail]
    obtain ⟨hpos, hfit, -⟩ := sailItem_len_lt _ _ _ _ hsi
    rw [hsi] at he; simp only [ofSail] at he
    have hrest := itemRest_eq (b :: rest) off len (by omega)
    cases l with
    | true => left; simp [keysWalk, sailKeys, he, hsi]
    | false =>
    by_cases h32 : len = 32
    · subst h32
      have hdl : ((b :: rest).drop (off + 32)).length = (b :: rest).length - (off + 32) :=
        List.length_drop
      have hk := ih g ((b :: rest).drop (off + 32)) (by omega) (by omega) (by omega)
        (fun c hc => hf c (by
          simp only [keysWalk, he, hrest, ↓reduceIte, List.mem_cons]; exact .inr hc))
      simp only [keysWalk, sailKeys, he, hsi, hrest, ↓reduceIte, Bool.false_eq_true, false_or,
        Nat.lt_irrefl]
      rcases hk with hk | hk
      · left; rw [← hk]; cases (keysWalk f (List.drop (off + 32) (b :: rest))).2 <;> rfl
      · right; simp only [trig, List.any_cons] at hk ⊢; rw [hk, Bool.or_true]
    · by_cases hlt : len < 32
      · right; simp [keysWalk, he, h32, trig, trigC, keyC, stringAt, hlt]
      · left; simp [keysWalk, sailKeys, he, hsi, h32]; omega

theorem entryWalk_head (e : List Byte) : (addressCall, e) ∈ (entryWalk e).1 := by
  simp only [entryWalk]
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- `sailEntry` when the address item is no word, or no 20-byte string accepted later. -/
theorem sailEntry_none (e : List Byte) (al : Bool) (aoff alen : Nat)
    (hsa : sailItem e = some (al, aoff, alen)) (h : al = true ∨ 32 < alen) : sailEntry e = none := by
  simp only [sailEntry, hsa]
  split
  · rfl
  · rw [if_pos (by rcases h with h | h <;> simp [h])]

theorem entry_rel (e : List Byte) (hb : e.length < 2 ^ 64)
    (hf : ∀ c ∈ (entryWalk e).1, HeaderFits c.2) :
    (entryWalk e).2.map (fun v => v.keys.length) = sailEntry e ∨ trig (entryWalk e).1 = true := by
  have he := fits_eq _ (hf _ (entryWalk_head e))
  rcases hsa : sailItem e with _ | ⟨al, aoff, alen⟩
  · rw [hsa] at he; left; simp [entryWalk, sailEntry, he, hsa, ofSail]
  obtain ⟨hapos, hafit, -⟩ := sailItem_len_lt _ _ _ _ hsa
  rw [hsa] at he; simp only [ofSail] at he
  cases al with
  | true => left; rw [sailEntry_none e true aoff alen hsa (.inl rfl)]; simp [entryWalk, he]
  | false =>
  by_cases h20 : alen = 20
  · subst h20
    have hrest := itemRest_eq e aoff 20 (by omega)
    have hk0 : (keysCall, e.drop (aoff + 20)) ∈ (entryWalk e).1 := by
      simp only [entryWalk, he, ↓reduceIte, hrest]
      split <;> simp
    have hek := fits_eq _ (hf _ hk0)
    generalize hq : e.drop (aoff + 20) = q at hek hk0
    have hql : q.length = e.length - (aoff + 20) := by rw [← hq]; exact List.length_drop
    rcases hsk : sailItem q with _ | ⟨kl, koff, klen⟩
    · rw [hsk] at hek
      left; simp [entryWalk, sailEntry, he, hsa, hrest, hq, hek, hsk, ofSail]
    obtain ⟨hkpos, hkfit, -⟩ := sailItem_len_lt _ _ _ _ hsk
    rw [hsk] at hek; simp only [ofSail] at hek
    have hE : sailEntry e = if q.drop (koff + klen) ≠ [] ∨ false = true ∨ 32 < 20 ∨ kl = false
        then none else sailKeys (klen + 1) ((q.drop koff).take klen) := by
      simp only [sailEntry, hsa, hq, hsk]
    rw [hE]
    cases kl with
    | false => left; simp [entryWalk, he, hrest, hq, hek]
    | true =>
    have hkp : ((q.drop koff).take klen).length = klen := by simp; omega
    have hW : entryWalk e = ((addressCall, e) :: (keysCall, q) ::
        (keysWalk ((q.drop koff).take klen).length ((q.drop koff).take klen)).1,
        (keysWalk ((q.drop koff).take klen).length ((q.drop koff).take klen)).2.map
          fun ks => ⟨itemPayload e aoff 20, ks⟩) := by
      simp only [entryWalk, he, hrest, hq, hek, ↓reduceIte]; rfl
    rw [hW] at hf ⊢
    have hkr := keys_rel _ (klen + 1) ((q.drop koff).take klen) (Nat.le_refl _) (by omega)
      (by omega) (fun c hc => hf c (by simp only [List.mem_cons]; exact .inr (.inr hc)))
    by_cases ht : q.drop (koff + klen) = []
    · rw [if_neg (by simp [ht])]
      rcases hkr with hkr | hkr
      · left; rw [← hkr]; cases (keysWalk _ ((q.drop koff).take klen)).2 <;> rfl
      · right; simp only [trig, List.any_cons] at hkr ⊢; rw [hkr]; simp
    · rw [if_pos (.inl ht)]
      cases hks : (keysWalk ((q.drop koff).take klen).length ((q.drop koff).take klen)).2 with
      | none => left; rfl
      | some ks =>
        right
        have hr := itemRest_eq q koff klen (by omega)
        simp only [trig, List.any_cons, trigC, trailC, hek, hr]
        have hn : q.length - (koff + klen) ≠ 0 := fun h0 => ht (List.drop_eq_nil_of_le (by omega))
        simp [hn]
  · by_cases h32 : alen ≤ 32
    · right; simp [entryWalk, he, h20, trig, trigC, addrC, stringAt, h32]
    · left; rw [sailEntry_none e false aoff alen hsa (.inr (by omega))]; simp [entryWalk, he, h20]

/-- The number of keys of accepted entries. -/
def keyCount (vs : List EntryValue) : Nat := (vs.map fun v => v.keys.length).sum

/-- The counts Sail returns for accepted entries. -/
def counts (vs : List EntryValue) : Nat × Nat := (vs.length, keyCount vs)

theorem entriesWalk_head (f : Nat) (b : Byte) (rest : List Byte) :
    (entryCall, b :: rest) ∈ (entriesWalk (f + 1) (b :: rest)).1 := by
  simp only [entriesWalk]
  split
  · split <;> simp
  · simp

theorem entries_rel : ∀ f1 f2 (xs : List Byte), xs.length ≤ f1 → xs.length < f2 →
    xs.length < 2 ^ 64 → (∀ c ∈ (entriesWalk f1 xs).1, HeaderFits c.2) →
    (entriesWalk f1 xs).2.map counts = sailEntries f2 xs ∨ trig (entriesWalk f1 xs).1 = true := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 xs h1 _ _ _
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; left; cases f2 <;> rfl
  | succ f ih =>
    intro f2 xs h1 h2 hb hf
    cases xs with
    | nil => left; cases f2 <;> rfl
    | cons b rest =>
    obtain ⟨g, rfl⟩ : ∃ g, f2 = g + 1 := ⟨f2 - 1, by simp at h2; omega⟩
    have he := fits_eq _ (hf _ (entriesWalk_head f b rest))
    rcases hsi : sailItem (b :: rest) with _ | ⟨l, off, len⟩
    · rw [hsi] at he; left; simp [entriesWalk, sailEntries, he, hsi, ofSail]
    obtain ⟨hpos, hfit, -⟩ := sailItem_len_lt _ _ _ _ hsi
    rw [hsi] at he; simp only [ofSail] at he
    have hrest := itemRest_eq (b :: rest) off len (by omega)
    cases l with
    | false => left; simp [entriesWalk, sailEntries, he, hsi]
    | true =>
    have hpl : (itemPayload (b :: rest) off len).length ≤ len := by
      simp only [itemPayload, List.length_take]; exact Nat.min_le_left _ _
    have hdl : ((b :: rest).drop (off + len)).length = (b :: rest).length - (off + len) :=
      List.length_drop
    have hS : sailEntries (g + 1) (b :: rest) =
        match sailEntry (itemPayload (b :: rest) off len) with
        | none => none
        | some k => (sailEntries g ((b :: rest).drop (off + len))).map
            fun (a, s) => (a + 1, s + k) := by
      simp only [sailEntries, hsi, Bool.true_eq_false, ↓reduceIte, itemPayload]
      try rfl
    rw [hS]
    rcases hr : (entryWalk (itemPayload (b :: rest) off len)).2 with _ | v
    · have hW : entriesWalk (f + 1) (b :: rest) =
          ((entryCall, b :: rest) :: (entryWalk (itemPayload (b :: rest) off len)).1, none) := by
        simp only [entriesWalk, he, hr]
      rw [hW] at hf ⊢
      have hen := entry_rel (itemPayload (b :: rest) off len) (by omega)
        (fun c hc => hf c (List.mem_cons_of_mem _ hc))
      rw [hr] at hen
      rcases hen with hen | hen
      · left; rw [← hen]; rfl
      · right; simp only [trig, List.any_cons] at hen ⊢; rw [hen, Bool.or_true]
    · have hW : entriesWalk (f + 1) (b :: rest) =
          ((entryCall, b :: rest) :: (entryWalk (itemPayload (b :: rest) off len)).1 ++
            (entriesWalk f ((b :: rest).drop (off + len))).1,
           (entriesWalk f ((b :: rest).drop (off + len))).2.map (v :: ·)) := by
        simp only [entriesWalk, he, hr, hrest]
      rw [hW] at hf ⊢
      have hen := entry_rel (itemPayload (b :: rest) off len) (by omega)
        (fun c hc => hf c (by simp only [List.cons_append, List.mem_cons, List.mem_append]
                              exact .inr (.inl hc)))
      rw [hr] at hen
      rcases hen with hen | hen
      · rw [← hen]
        have hk := ih g ((b :: rest).drop (off + len)) (by omega) (by omega) (by omega)
          (fun c hc => hf c (by simp only [List.cons_append, List.mem_cons, List.mem_append]
                                exact .inr (.inr hc)))
        rcases hk with hk | hk
        · left; rw [← hk]
          cases (entriesWalk f ((b :: rest).drop (off + len))).2 with
          | none => rfl
          | some vs =>
            simp only [Option.map, counts, keyCount, List.length_cons, List.map_cons,
              List.sum_cons, Option.some.injEq, Prod.mk.injEq, true_and]
            omega
        · right; simp only [trig, List.cons_append, List.any_cons, List.any_append] at hk ⊢
          rw [hk]; simp
      · right; simp only [trig, List.cons_append, List.any_cons, List.any_append] at hen ⊢
        rw [hen]; simp

/-- The counts the candidate's decision reports; a rejection has none. -/
def candCounts : Candidate → Option (Nat × Nat)
  | .accepted vs _ => some (counts vs)
  | .rejected _ => none

/-- The pure core of (b): on the domain, the candidate's counts are Sail's, or a trigger holds. -/
theorem access_rel (input : List Byte) (hd : Domain input) :
    candCounts (candidate input) = sailAccess input ∨ trig (calls input) = true := by
  obtain ⟨hf, hlim⟩ := hd
  have he := fits_eq _ (hf (outerCall, input) (by simp only [calls, walk]; split <;> simp))
  rcases hsi : sailItem input with _ | ⟨l, off, len⟩
  · rw [hsi] at he; left; simp [candidate, walk, sailAccess, he, hsi, ofSail, candCounts]
  obtain ⟨hpos, hfit, -⟩ := sailItem_len_lt _ _ _ _ hsi
  rw [hsi] at he; simp only [ofSail] at he
  rw [he] at hlim
  cases l with
  | false => left; simp [candidate, walk, sailAccess, he, hsi, candCounts]
  | true =>
  have hpl : (itemPayload input off len).length ≤ len := by
    simp only [itemPayload, List.length_take]; exact Nat.min_le_left _ _
  have hS : sailAccess input = sailEntries (len + 1) (itemPayload input off len) := by
    simp only [sailAccess, hsi, itemPayload]
    rw [if_neg (by simp; omega)]
  have hW : walk input = ((outerCall, input) ::
      (entriesWalk (itemPayload input off len).length (itemPayload input off len)).1,
      match (entriesWalk (itemPayload input off len).length (itemPayload input off len)).2 with
      | some vs => .accepted vs (itemConsumed off len)
      | none => .rejected (some (itemConsumed off len))) := by
    simp only [walk, he]
    try rfl
  simp only [candidate, calls, hW] at hf ⊢
  rw [hS]
  have hk := entries_rel _ (len + 1) (itemPayload input off len) (Nat.le_refl _) (by omega)
    (by omega) (fun c hc => hf c (List.mem_cons_of_mem _ hc))
  rcases hk with hk | hk
  · left; rw [← hk]
    cases (entriesWalk (itemPayload input off len).length (itemPayload input off len)).2 <;> rfl
  · right; simp only [trig, List.any_cons] at hk ⊢; rw [hk, Bool.or_true]

/-! ## (b) The candidate agrees with Sail modulo known bugs -/

/-- The result type of `accessRun`. -/
abbrev SailAccessResult :=
  EStateM.Result (Sail.Error Unit) SailRegs (Evm.Defs.AccessListRef × Evm.HostState)

/-- EVM-Sail's access-list decoding with the stateless input holding `input`, from register
state `σ`. -/
def sailRun (input : List Byte) (σ : SailRegs) : SailAccessResult :=
  ((accessRun input).run (hostOf input)).run σ

/-- `txAccessListSailAgrees` on counts: a returned reference counts the candidate's accepted
entries and keys; the `fatal_error` exit is a rejection; any other failure relates to nothing. -/
def SailRelates : SailAccessResult → Candidate → Prop
  | .ok (ref, _) _, c => candCounts c = some (ref.address_count, ref.slot_count)
  | .error .Exit _, c => candCounts c = none
  | .error _ _, _ => False

theorem sailRun_relates (input : List Byte) (σ : SailRegs) (c : Candidate)
    (h : candCounts c = sailAccess input) : SailRelates (sailRun input σ) c := by
  have he := access_eval input σ
  rcases hs : sailAccess input with _ | ⟨a, s⟩
  · rw [hs] at he h
    simp only [sailRun, he, SailRelates, h]
  · rw [hs] at he h
    obtain ⟨e, he⟩ := he
    simp only [sailRun, he, SailRelates, h]

/-- `tx_candidate_agrees`: on the domain, for every Sail register state, EVM-Sail's
`decode_access_list` relates to the candidate, or a listed known bug applies. -/
theorem tx_candidate_agrees (input : List Byte) (hd : Domain input) (σ : SailRegs) :
    SailRelates (sailRun input σ) (candidate input) ∨
      ∃ bug ∈ knownBugs, bugApplies bug input := by
  rcases access_rel input hd with h | h
  · exact .inl (sailRun_relates input σ _ h)
  · exact .inr (trig_bug input h)

/-! ## (c) Compliance of the binary -/

/-- `TxAccessListMeaningModuloKnownBugs`: for every Sail register state, Sail's result relates to
the candidate (in whose terms `Post` states the outcome), or a listed known bug applies. -/
def TxAccessListMeaningModuloKnownBugs (input : List Byte) : Prop :=
  ∀ σ, SailRelates (sailRun input σ) (candidate input) ∨
    ∃ bug ∈ knownBugs, bugApplies bug input

/-- The final-state property of `tx_compliance_of`: `Post`, and the input meets the meaning. -/
def Compliant (A : Fn.AllocAssumptions zesuImage) (g : Params) (m m' : Machine) : Prop :=
  Post A g m m' ∧ TxAccessListMeaningModuloKnownBugs g.input

theorem pre_domain {A : Fn.AllocAssumptions zesuImage} {g : Params} {m : Machine}
    (h : Pre A g m) : Domain g.input := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := h
  exact hd

/-- Compliance from `tx_spec` (a hypothesis until it is proven). -/
theorem tx_compliance_of {bound : Nat} {A : Fn.AllocAssumptions zesuImage} {g : Params}
    (hspec : Spec zesuImage Fn.TX.entry bound (Pre A g) (Post A g))
    (m : Machine) (hpc : m.pc.toNat = Fn.TX.entry) (hpre : Pre A g m) :
    Reaches zesuImage bound (Compliant A g m) m :=
  (hspec m hpc hpre).mono (Nat.le_refl _) fun _ hp =>
    ⟨hp, fun σ => tx_candidate_agrees g.input (pre_domain hpre) σ⟩

/-- `tx_compliance_of` on the Sail RISC-V model, by `sail_reaches`. -/
theorem tx_compliance_sail_of {bound : Nat} {A : Fn.AllocAssumptions zesuImage} {g : Params}
    (hspec : Spec zesuImage Fn.TX.entry bound (Pre A g) (Post A g))
    {m : Machine} {s : BinaryFv.RiscV.State} (h : SailLink.Rel zesuImage m s)
    (hpc : m.pc.toNat = Fn.TX.entry) (hpre : Pre A g m) :
    SailLink.SailReaches zesuImage bound
      (fun s' => ∃ m', SailLink.Rel zesuImage m' s' ∧ Compliant A g m m') s :=
  SailLink.sail_reaches h (tx_compliance_of hspec m hpc hpre)

/-! ## Witnesses -/

/-- One entry: a 20-byte address and one 32-byte key. Both accept one entry with one key; no
trigger holds. -/
def agreeWitness : List Byte :=
  [0xf8, 0x38, 0xf7, 0x94] ++ List.replicate 20 1 ++ [0xe1, 0xa0] ++ List.replicate 32 2

example : candCounts (candidate agreeWitness) = some (1, 1) ∧
    sailAccess agreeWitness = some (1, 1) ∧ trig (calls agreeWitness) = false := by decide

/-- `accessListAddressLength`: a 19-byte address; the binary rejects, Sail accepts. -/
def addressWitness : List Byte := [0xd6, 0xd5, 0x93] ++ List.replicate 19 1 ++ [0xc0]

example : candCounts (candidate addressWitness) = none ∧
    sailAccess addressWitness = some (1, 0) ∧
    bugTrigger .accessListAddressLength addressWitness = true := by decide

/-- `accessListKeyLength`: a 31-byte key; the binary rejects, Sail accepts. -/
def keyWitness : List Byte :=
  [0xf7, 0xf6, 0x94] ++ List.replicate 20 1 ++ [0xe0, 0x9f] ++ List.replicate 31 2

example : candCounts (candidate keyWitness) = none ∧ sailAccess keyWitness = some (1, 1) ∧
    bugTrigger .accessListKeyLength keyWitness = true := by decide

/-- `accessListEntryTrailingBytes`: a byte after an entry's keys list; the binary accepts, Sail
rejects. -/
def trailingWitness : List Byte := [0xd8, 0xd7, 0x94] ++ List.replicate 20 1 ++ [0xc0, 0x01]

example : candCounts (candidate trailingWitness) = some (1, 0) ∧
    sailAccess trailingWitness = none ∧
    bugTrigger .accessListEntryTrailingBytes trailingWitness = true := by decide

/--
info: 'ZesuExec.Compliance.TX.tx_candidate_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tx_candidate_agrees

end ZesuExec.Compliance.TX
