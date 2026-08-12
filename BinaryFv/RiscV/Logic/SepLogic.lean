import BinaryFv.RiscV.Logic.Framing

/-!
# A bespoke, memory-only separation logic over `SailM`

This module builds a minimal separation logic directly on the generated Sail state monad.  It is
deliberately small: a logical heap view of the sparse byte memory, the usual separating
connectives (`emp`, points-to, separating conjunction) with their commutativity/associativity/
identity laws, success-only framed Hoare triples over the existing `Runs` relation, and structural
rules for the generated memory primitives.

Separation is confined to memory.  A triple additionally carries an *ordinary* (non-spatial) state
pre/postcondition — `StateAssertion := State → Prop` — so that instruction contracts can assume and
conclude concrete register/PC/privilege/counter/platform facts without encoding them as heap
ownership.  Memory writes preserve any such assertion that is insensitive to the `mem` field
(`MemInsensitive`).  There are no modalities, ghost state, recursively defined heap predicates,
magic wand, or general proof-mode tactic.
-/

namespace BinaryFv.RiscV.Sep

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## Logical heaps -/

/-- A logical view of the machine's sparse byte memory: a partial map from address to byte. -/
abbrev Heap := Nat → Option (BitVec 8)

/-- Two heaps are disjoint when no address is defined in both. -/
def Disjoint (h₁ h₂ : Heap) : Prop := ∀ a, h₁ a = none ∨ h₂ a = none

/-- Union of heaps, left-biased on overlap (overlap never occurs for disjoint heaps). -/
def union (h₁ h₂ : Heap) : Heap := fun a => match h₁ a with | some v => some v | none => h₂ a

/-- The logical heap view of a machine state's byte memory. -/
def stateHeap (s : State) : Heap := fun a => s.mem.get? a

theorem union_apply_of_left {h₁ h₂ : Heap} {a : Nat} {v : BitVec 8} (h : h₁ a = some v) :
    union h₁ h₂ a = some v := by simp only [union, h]

theorem union_apply_of_none {h₁ h₂ : Heap} {a : Nat} (h : h₁ a = none) :
    union h₁ h₂ a = h₂ a := by simp only [union, h]

theorem union_eq_none_iff {h₁ h₂ : Heap} {a : Nat} :
    union h₁ h₂ a = none ↔ h₁ a = none ∧ h₂ a = none := by
  cases ha : h₁ a with
  | some v => simp [union_apply_of_left ha]
  | none => simp [union_apply_of_none ha]

theorem union_assoc (a b c : Heap) : union (union a b) c = union a (union b c) := by
  funext x; simp only [union]; cases a x <;> cases b x <;> rfl

theorem Disjoint.symm {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) : Disjoint h₂ h₁ :=
  fun a => (h a).symm

/-- On a disjoint pair, an address defined on the left is undefined on the right. -/
theorem Disjoint.none_right {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) {a : Nat} {v : BitVec 8}
    (defined : h₁ a = some v) : h₂ a = none := by
  rcases h a with hl | hr
  · rw [hl] at defined; exact absurd defined (by simp)
  · exact hr

theorem Disjoint.none_left {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) {a : Nat} {v : BitVec 8}
    (defined : h₂ a = some v) : h₁ a = none :=
  h.symm.none_right defined

theorem union_comm {h₁ h₂ : Heap} (h : Disjoint h₁ h₂) : union h₁ h₂ = union h₂ h₁ := by
  funext a; simp only [union]
  rcases h a with hl | hr
  · rw [hl]; cases h₂ a <;> rfl
  · rw [hr]; cases h₁ a <;> rfl

/-- Disjointness distributes over a union on the left. -/
theorem disjoint_union_left_iff {a b c : Heap} :
    Disjoint (union a b) c ↔ Disjoint a c ∧ Disjoint b c := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rcases h x with hl | hr
      · exact Or.inl (union_eq_none_iff.mp hl).1
      · exact Or.inr hr
    · rcases h x with hl | hr
      · exact Or.inl (union_eq_none_iff.mp hl).2
      · exact Or.inr hr
  · rintro ⟨hac, hbc⟩ x
    rcases hac x with hl | hr
    · rcases hbc x with hl' | hr'
      · exact Or.inl (union_eq_none_iff.mpr ⟨hl, hl'⟩)
      · exact Or.inr hr'
    · exact Or.inr hr

/-- Disjointness distributes over a union on the right. -/
theorem disjoint_union_right_iff {a b c : Heap} :
    Disjoint a (union b c) ↔ Disjoint a b ∧ Disjoint a c := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := disjoint_union_left_iff.mp h.symm
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact (disjoint_union_left_iff.mpr ⟨h1.symm, h2.symm⟩).symm

/-! ## Heap assertions and separating connectives -/

/-- A memory assertion is a predicate on logical heaps. -/
abbrev Assertion := Heap → Prop

/-- The empty heap owns nothing. -/
def emp : Assertion := fun h => ∀ a, h a = none

/-- Exclusive ownership of a single byte `v` at address `a`. -/
def pointsTo (a : Nat) (v : BitVec 8) : Assertion :=
  fun h => h a = some v ∧ ∀ b, b ≠ a → h b = none

/-- Separating conjunction: the heap splits into disjoint parts satisfying `P` and `Q`. -/
def sepConj (P Q : Assertion) : Assertion :=
  fun h => ∃ h₁ h₂, Disjoint h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂

@[inherit_doc] scoped infixr:55 " ⋆ " => sepConj
@[inherit_doc] scoped infix:60 " ↦ " => pointsTo

/-! ### Separation laws -/

/-- Separating conjunction is commutative (as a two-directional heap equivalence). -/
theorem sepConj_comm {P Q : Assertion} {h : Heap} : (P ⋆ Q) h ↔ (Q ⋆ P) h := by
  constructor <;> rintro ⟨h₁, h₂, hdisj, rfl, hA, hB⟩ <;>
    exact ⟨h₂, h₁, hdisj.symm, union_comm hdisj, hB, hA⟩

/-- `emp` is a left identity for `⋆`. -/
theorem emp_sepConj {P : Assertion} {h : Heap} : (emp ⋆ P) h ↔ P h := by
  constructor
  · rintro ⟨h₁, h₂, _, rfl, hemp, hP⟩
    have hrw : union h₁ h₂ = h₂ := by funext a; rw [union_apply_of_none (hemp a)]
    rw [hrw]; exact hP
  · intro hP
    exact ⟨fun _ => none, h, fun a => Or.inl rfl, by funext a; rw [union_apply_of_none rfl],
      fun a => rfl, hP⟩

/-- `emp` is a right identity for `⋆` (derived from commutativity and the left identity). -/
theorem sepConj_emp {P : Assertion} {h : Heap} : (P ⋆ emp) h ↔ P h :=
  ⟨fun hh => emp_sepConj.mp (sepConj_comm.mp hh), fun hh => sepConj_comm.mp (emp_sepConj.mpr hh)⟩

/-- Separating conjunction is associative (as a two-directional heap equivalence). -/
theorem sepConj_assoc {P Q R : Assertion} {h : Heap} :
    ((P ⋆ Q) ⋆ R) h ↔ (P ⋆ (Q ⋆ R)) h := by
  constructor
  · rintro ⟨hpq, hr, hdisj, rfl, ⟨hp, hq, hdisjpq, rfl, hP, hQ⟩, hR⟩
    obtain ⟨hdisjPhr, hdisjQhr⟩ := disjoint_union_left_iff.mp hdisj
    exact ⟨hp, union hq hr, disjoint_union_right_iff.mpr ⟨hdisjpq, hdisjPhr⟩,
      union_assoc hp hq hr, hP, hq, hr, hdisjQhr, rfl, hQ, hR⟩
  · rintro ⟨hp, hqr, hdisj, rfl, hP, ⟨hq, hr, hdisjqr, rfl, hQ, hR⟩⟩
    obtain ⟨hdisjPhq, hdisjPhr⟩ := disjoint_union_right_iff.mp hdisj
    exact ⟨union hp hq, hr, disjoint_union_left_iff.mpr ⟨hdisjPhr, hdisjqr⟩,
      (union_assoc hp hq hr).symm, ⟨hp, hq, hdisjPhq, rfl, hP, hQ⟩, hR⟩

/-- Rotate three owned regions, so later code/input/output/stack groupings are interchangeable
    without reopening the underlying heap splits. -/
theorem sepConj_rotate {P Q R : Assertion} {h : Heap} :
    ((P ⋆ Q) ⋆ R) h ↔ ((Q ⋆ R) ⋆ P) h :=
  ⟨fun hh => sepConj_comm.mp (sepConj_assoc.mp hh),
   fun hh => sepConj_assoc.mpr (sepConj_comm.mp hh)⟩

/-! ## Ordinary state assertions -/

/-- An ordinary (non-spatial) assertion on the whole machine state: used for register, PC,
    privilege, counter, and platform facts that live outside the separated memory. -/
abbrev StateAssertion := State → Prop

/-- A state assertion insensitive to the `mem` field: preserved by every memory write. -/
def MemInsensitive (S : StateAssertion) : Prop :=
  ∀ (s : State) (m : Std.ExtHashMap Nat (BitVec 8)), S s → S { s with mem := m }

theorem memInsensitive_true : MemInsensitive (fun _ => True) := fun _ _ _ => trivial

theorem MemInsensitive.and {S T : StateAssertion} (hS : MemInsensitive S) (hT : MemInsensitive T) :
    MemInsensitive (fun s => S s ∧ T s) := fun s m ⟨hs, ht⟩ => ⟨hS s m hs, hT s m ht⟩

/-- Any predicate reading only the register file (registers, PC, privilege) is memory-insensitive. -/
theorem memInsensitive_regs (P : Std.ExtDHashMap Register RegisterType → Prop) :
    MemInsensitive (fun s => P s.regs) := fun _ _ h => h

/-- A concrete single-register fact is memory-insensitive. -/
theorem memInsensitive_reg (r : Register) (v : RegisterType r) :
    MemInsensitive (fun s => s.regs.get? r = some v) := fun _ _ h => h

/-! ## Framed success triples

`Triple S P action T Q` is a small-footprint, success-only Hoare triple.  From every machine state
satisfying the ordinary precondition `S` whose byte memory decomposes as an owned part satisfying
`P` and an arbitrary disjoint frame `hf`, the generated `action` runs to completion; the resulting
state satisfies `T`, the frame `hf` survives untouched, and the new owned part satisfies `Q`. -/
def Triple (S : StateAssertion) (P : Assertion) (action : SailM α)
    (T : α → StateAssertion) (Q : α → Assertion) : Prop :=
  ∀ (s : State) (hp hf : Heap),
    S s → P hp → Disjoint hp hf → stateHeap s = union hp hf →
    ∃ (s' : State) (r : α) (hp' : Heap),
      Runs action s s' r ∧ T r s' ∧ Q r hp' ∧ Disjoint hp' hf ∧ stateHeap s' = union hp' hf

/-- A memory-only triple: no ordinary state pre/postcondition.  Convenient when only memory matters
    (it is `Triple` specialized to the trivial, always-preserved state assertion). -/
abbrev MTriple (P : Assertion) (action : SailM α) (Q : α → Assertion) : Prop :=
  Triple (fun _ => True) P action (fun _ _ => True) Q

theorem triple_pure (S : StateAssertion) (P : Assertion) (a : α) :
    Triple S P (pure a) (fun _ => S) (fun r => fun h => r = a ∧ P h) := by
  intro s hp hf hS hP hdisj hsplit
  exact ⟨s, a, hp, rfl, hS, ⟨rfl, hP⟩, hdisj, hsplit⟩

theorem triple_bind {S : StateAssertion} {P : Assertion} {T₁ : α → StateAssertion}
    {Q₁ : α → Assertion} {T₂ : β → StateAssertion} {Q₂ : β → Assertion}
    {first : SailM α} {next : α → SailM β}
    (hFirst : Triple S P first T₁ Q₁) (hNext : ∀ a, Triple (T₁ a) (Q₁ a) (next a) T₂ Q₂) :
    Triple S P (first >>= next) T₂ Q₂ := by
  intro s hp hf hS hP hdisj hsplit
  obtain ⟨s', r, hp', hRun, hT₁, hQ₁, hdisj', hsplit'⟩ := hFirst s hp hf hS hP hdisj hsplit
  obtain ⟨s'', r', hp'', hRun', hT₂, hQ₂, hdisj'', hsplit''⟩ :=
    hNext r s' hp' hf hT₁ hQ₁ hdisj' hsplit'
  exact ⟨s'', r', hp'', Runs.bind hRun hRun', hT₂, hQ₂, hdisj'', hsplit''⟩

theorem triple_consequence {S S' : StateAssertion} {P P' : Assertion} {T T' : α → StateAssertion}
    {Q Q' : α → Assertion} {action : SailM α}
    (hS : ∀ s, S' s → S s) (hP : ∀ h, P' h → P h)
    (hT : ∀ r s, T r s → T' r s) (hQ : ∀ r h, Q r h → Q' r h)
    (h : Triple S P action T Q) : Triple S' P' action T' Q' := by
  intro s hp hf hS' hP' hdisj hsplit
  obtain ⟨s', r, hp', hRun, hTr, hQr, hdisj', hsplit'⟩ :=
    h s hp hf (hS s hS') (hP hp hP') hdisj hsplit
  exact ⟨s', r, hp', hRun, hT r s' hTr, hQ r hp' hQr, hdisj', hsplit'⟩

/-! ### The frame rule -/

theorem triple_frame {S : StateAssertion} {P : Assertion} {T : α → StateAssertion}
    {Q : α → Assertion} {F : Assertion} {action : SailM α}
    (h : Triple S P action T Q) : Triple S (P ⋆ F) action T (fun r => Q r ⋆ F) := by
  intro s hp hf hS hPF hdisj hsplit
  obtain ⟨hP, hF, hdisjPF, rfl, hPhP, hFhF⟩ := hPF
  obtain ⟨hdisjPhf, hdisjFhf⟩ := disjoint_union_left_iff.mp hdisj
  have hdisjInner : Disjoint hP (union hF hf) := disjoint_union_right_iff.mpr ⟨hdisjPF, hdisjPhf⟩
  have hsplitInner : stateHeap s = union hP (union hF hf) := by rw [hsplit, union_assoc]
  obtain ⟨s', r, hp', hRun, hTr, hQ, hdisj', hsplit'⟩ :=
    h s hP (union hF hf) hS hPhP hdisjInner hsplitInner
  obtain ⟨hdisj'F, hdisj'hf⟩ := disjoint_union_right_iff.mp hdisj'
  refine ⟨s', r, union hp' hF, hRun, hTr, ⟨hp', hF, hdisj'F, rfl, hQ, hFhF⟩,
    disjoint_union_left_iff.mpr ⟨hdisj'hf, hdisjFhf⟩, ?_⟩
  rw [hsplit', union_assoc]

/-- Frame an assertion on the left of a triple's memory pre/postcondition. -/
theorem triple_frame_left {S : StateAssertion} {P : Assertion} {T : α → StateAssertion}
    {Q : α → Assertion} {F : Assertion} {action : SailM α}
    (h : Triple S P action T Q) : Triple S (F ⋆ P) action T (fun r => F ⋆ Q r) :=
  triple_consequence (fun _ h => h) (fun _ => sepConj_comm.mp) (fun _ _ h => h)
    (fun _ _ => sepConj_comm.mp) (triple_frame h)

/-! ## Rules for the generated memory primitives -/

/-- Point-update of a logical heap at a single address. -/
def updateByte (h : Heap) (a : Nat) (v : BitVec 8) : Heap := fun b => if b = a then some v else h b

theorem updateByte_self (h : Heap) (a : Nat) (v : BitVec 8) : updateByte h a v a = some v := by
  simp [updateByte]

theorem updateByte_other (h : Heap) {a b : Nat} (v : BitVec 8) (hb : b ≠ a) :
    updateByte h a v b = h b := by simp [updateByte, hb]

theorem union_updateByte_other {h g : Heap} {a b : Nat} {v : BitVec 8} (hb : b ≠ a) :
    union (updateByte h a v) g b = union h g b := by
  unfold union; rw [updateByte_other h v hb]

theorem mem_insert_get? (s : State) (a b : Nat) (v : BitVec 8) :
    (s.mem.insert a v).get? b = if a = b then some v else s.mem.get? b := by
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]; simp

/-- A read leaves all machine state unchanged and returns the owned byte. -/
theorem triple_readByte (S : StateAssertion) (a : Nat) (v : BitVec 8) :
    Triple S (pointsTo a v) (readByte a) (fun _ => S) (fun r => fun h => r = v ∧ pointsTo a v h) := by
  intro s hp hf hS hP hdisj hsplit
  obtain ⟨hpa, hpother⟩ := hP
  have hmem : s.mem.get? a = some v := by
    have hb := congrFun hsplit a
    simp only [stateHeap] at hb
    rw [union_apply_of_left hpa] at hb
    exact hb
  exact ⟨s, v, hp, readByte_run s a v hmem, hS, ⟨rfl, hpa, hpother⟩, hdisj, hsplit⟩

/-- The pure-preservation reading of `readByte`, discarding the returned value. -/
theorem triple_readByte_frame (S : StateAssertion) (a : Nat) (v : BitVec 8) :
    Triple S (pointsTo a v) (readByte a) (fun _ => S) (fun _ => pointsTo a v) :=
  triple_consequence (fun _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.2)
    (triple_readByte S a v)

/-- A write updates exactly its owned byte and preserves every memory-insensitive state fact. -/
theorem triple_writeByte (S : StateAssertion) (hS : MemInsensitive S) (a : Nat) (v v₀ : BitVec 8) :
    Triple S (pointsTo a v₀) (writeByte a v) (fun _ => S) (fun _ => pointsTo a v) := by
  intro s hp hf hSs hP hdisj hsplit
  obtain ⟨hpa, hpother⟩ := hP
  refine ⟨{s with mem := s.mem.insert a v}, PUnit.unit, updateByte hp a v,
    writeByte_run s a v, hS s (s.mem.insert a v) hSs, ⟨updateByte_self hp a v, fun b hb => ?_⟩, ?_, ?_⟩
  · rw [updateByte_other hp v hb]; exact hpother b hb
  · intro b
    by_cases hb : b = a
    · refine Or.inr ?_; rw [hb]; exact hdisj.none_right hpa
    · rw [updateByte_other hp v hb]; exact hdisj b
  · funext b
    show (s.mem.insert a v).get? b = union (updateByte hp a v) hf b
    rw [mem_insert_get?]
    by_cases hb : b = a
    · rw [if_pos hb.symm, hb, union_apply_of_left (updateByte_self hp a v)]
    · rw [if_neg (Ne.symm hb), union_updateByte_other hb]
      exact congrFun hsplit b

/-! ## Byte ranges -/

/-- Ownership of consecutive bytes `vs` starting at address `a`, in ascending address order. -/
def bytes (a : Nat) : List (BitVec 8) → Assertion
  | [] => emp
  | v :: vs => pointsTo a v ⋆ bytes (a + 1) vs

theorem bytes_nil (a : Nat) : bytes a [] = emp := rfl

theorem bytes_cons (a : Nat) (v : BitVec 8) (vs : List (BitVec 8)) :
    bytes a (v :: vs) = pointsTo a v ⋆ bytes (a + 1) vs := rfl

/-- Ownership pins the exact byte at every in-range address. -/
theorem bytes_get : ∀ (a : Nat) (vs : List (BitVec 8)) (h : Heap),
    bytes a vs h → ∀ (i : Nat) (hi : i < vs.length), h (a + i) = some vs[i] := by
  intro a vs
  induction vs generalizing a with
  | nil => intro h _ i hi; exact absurd hi (by simp)
  | cons v vs ih =>
    intro h hb i hi
    obtain ⟨h₁, h₂, hdisj, rfl, ⟨hpt, _⟩, htail⟩ := hb
    cases i with
    | zero => simpa using union_apply_of_left hpt
    | succ j =>
      simp only [List.length_cons] at hi
      have haddr : a + (j + 1) = (a + 1) + j := by omega
      rw [haddr]
      have hget := ih (a + 1) h₂ htail j (by omega)
      have hleft : h₁ ((a + 1) + j) = none := by
        rcases hdisj ((a + 1) + j) with hl | hr
        · exact hl
        · rw [hr] at hget; exact absurd hget (by simp)
      rw [union_apply_of_none hleft]; simpa using hget

/-- Ownership is empty outside the covered window: every address below `a` or at/above
    `a + vs.length` is undefined in the owning heap. -/
theorem bytes_none_outside : ∀ (a : Nat) (vs : List (BitVec 8)) (h : Heap),
    bytes a vs h → ∀ b, (b < a ∨ a + vs.length ≤ b) → h b = none := by
  intro a vs
  induction vs generalizing a with
  | nil => intro h hb b _; exact hb b
  | cons v vs ih =>
    intro h hb b hout
    obtain ⟨h₁, h₂, _, rfl, ⟨_, hpt_other⟩, htail⟩ := hb
    have hbne : b ≠ a := by rcases hout with h | h <;> simp only [List.length_cons] at * <;> omega
    have h1none : h₁ b = none := hpt_other b hbne
    have h2none : h₂ b = none := by
      refine ih (a + 1) h₂ htail b ?_
      rcases hout with h | h <;> simp only [List.length_cons] at * <;> omega
    rw [union_apply_of_none h1none]; exact h2none

/-! ## Little-endian words

`leBytes` decomposes a `BitVec (8 * n)` into its little-endian bytes (lower addresses hold lower
bits); `leWord` is the inverse recomposition, structured to match the recursion of
`PreSail.readBytes` (whose lowest read address lands in the low bits). -/

/-- Little-endian byte decomposition of a word: byte `i` is bits `[8i, 8i+8)`. -/
def leBytes (n : Nat) (value : BitVec (8 * n)) : List (BitVec 8) :=
  List.ofFn (fun i : Fin n => value.extractLsb' (8 * i.val) 8)

/-- Little-endian recomposition of consecutive bytes, matching `PreSail.readBytes`. -/
def leWord : (vs : List (BitVec 8)) → BitVec (8 * vs.length)
  | [] => 0#(8 * 0)
  | v :: vs => (leWord vs ++ v).cast (by simp [List.length_cons, Nat.mul_succ])

theorem leBytes_length (n : Nat) (value : BitVec (8 * n)) : (leBytes n value).length = n := by
  simp [leBytes]

theorem leWord_single (v : BitVec 8) : leWord [v] = v := by
  have appended := @BitVec.setWidth_append_eq_right 0 8 (0#0) v
  simpa only [leWord, BitVec.setWidth_eq] using appended

private theorem extract_extract (n : Nat) (value : BitVec (8 * (n + 1))) (k : Nat) (hk : k < n) :
    value.extractLsb' (8 * (k + 1)) 8 = (value.extractLsb' 8 (8 * n)).extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  by_cases hb8 : b < 8
  · have : 8 * k + b < 8 * n := by omega
    simp only [hb8, this, decide_true, Bool.true_and]; congr 1; omega
  · simp [hb8]

private theorem leBytes_succ (n : Nat) (value : BitVec (8 * (n + 1))) :
    leBytes (n + 1) value = value.extractLsb' 0 8 :: leBytes n (value.extractLsb' 8 (8 * n)) := by
  rw [leBytes, List.ofFn_succ]
  simp only [Fin.val_zero, Nat.mul_zero, Fin.val_succ]
  rw [leBytes]
  congr 1
  exact congrArg List.ofFn (funext fun i => extract_extract n value i.val i.isLt)

private theorem leWord_leBytes_getLsbD : ∀ (n : Nat) (value : BitVec (8 * n)) (j : Nat),
    (leWord (leBytes n value)).getLsbD j = value.getLsbD j := by
  intro n
  induction n with
  | zero => intro value j; rw [leBytes]; simp [BitVec.getLsbD_of_ge]
  | succ n ih =>
    intro value j
    rw [leBytes_succ]
    simp only [leWord, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases h : j < 8
    · rw [if_pos h, BitVec.getLsbD_extractLsb']; simp [h]
    · rw [if_neg h, ih, BitVec.getLsbD_extractLsb']
      by_cases h2 : j - 8 < 8 * n
      · simp only [h2, decide_true, Bool.true_and]; congr 1; omega
      · simp only [h2, decide_false, Bool.false_and]
        rw [BitVec.getLsbD_of_ge]; omega

/-- Recomposition is inverse to decomposition: reassembling `leBytes n value` returns `value`. -/
theorem leWord_leBytes (n : Nat) (value : BitVec (8 * n)) :
    (leWord (leBytes n value)).cast (by rw [leBytes_length]) = value := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_cast]; exact leWord_leBytes_getLsbD n value j

/-- A little-endian 64-bit word stored at address `a`. -/
def wordLE (a : Nat) (w : BitVec (8 * 8)) : Assertion := bytes a (leBytes 8 w)

/-! ## The fixed-width store -/

theorem writeBytes_eq (a : Nat) {n : Nat} (value : BitVec (8 * n)) :
    (writeBytes a value : SailM Bool) =
      (List.forM (List.ofFn (fun i : Fin n => (a + i.val, value.extractLsb' (8 * i.val) 8)))
        (fun p => writeByte p.1 p.2) >>= fun _ => pure true) := rfl

/-- Framed rule for the generated fixed-width store, expressed over consecutive `writeByte`s. -/
theorem triple_forM_ofFn (S : StateAssertion) (hS : MemInsensitive S) :
    ∀ (n a : Nat) (f : Fin n → BitVec 8) (vs₀ : List (BitVec 8)), vs₀.length = n →
    Triple S (bytes a vs₀)
      (List.forM (List.ofFn (fun i : Fin n => (a + i.val, f i))) (fun p => writeByte p.1 p.2))
      (fun _ => S) (fun _ => bytes a (List.ofFn f)) := by
  intro n
  induction n with
  | zero =>
    intro a f vs₀ hlen
    obtain rfl : vs₀ = [] := by cases vs₀ with | nil => rfl | cons v vs' => simp at hlen
    simp only [List.ofFn_zero]
    exact triple_consequence (fun _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h.2)
      (triple_pure S (bytes a []) PUnit.unit)
  | succ n ih =>
    intro a f vs₀ hlen
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs₀ = v :: vs' := by
      cases vs₀ with | nil => simp at hlen | cons v vs' => exact ⟨v, vs', rfl⟩
    have hlen' : vs'.length = n := by simpa using hlen
    have hfun : (fun j : Fin n => ((a + 1) + j.val, f j.succ)) =
                (fun j : Fin n => (a + (Fin.succ j).val, f j.succ)) := by
      funext j
      rw [show (a + 1) + j.val = a + (Fin.succ j).val by simp only [Fin.val_succ]; omega]
    have hhead : Triple S (bytes a (v :: vs')) (writeByte a (f 0))
        (fun _ => S) (fun _ => pointsTo a (f 0) ⋆ bytes (a + 1) vs') := by
      rw [bytes_cons]; exact triple_frame (triple_writeByte S hS a (f 0) v)
    have htail : Triple S (pointsTo a (f 0) ⋆ bytes (a + 1) vs')
        (List.forM (List.ofFn (fun j : Fin n => (a + (Fin.succ j).val, f j.succ)))
          (fun p => writeByte p.1 p.2))
        (fun _ => S) (fun _ => pointsTo a (f 0) ⋆ bytes (a + 1) (List.ofFn (fun j : Fin n => f j.succ))) := by
      rw [← hfun]; exact triple_frame_left (ih (a + 1) (fun j => f j.succ) vs' hlen')
    simp only [List.ofFn_succ, Fin.val_zero, Nat.add_zero]
    exact triple_bind hhead (fun _ => htail)

/-- Framed rule for the generated fixed-width store: an owned `n`-byte range is overwritten with
    the little-endian bytes of `value`, every memory-insensitive state fact is preserved, and every
    disjoint frame survives. -/
theorem triple_writeBytes (S : StateAssertion) (hS : MemInsensitive S) (a : Nat) {n : Nat}
    (value : BitVec (8 * n)) (vs₀ : List (BitVec 8)) (hlen : vs₀.length = n) :
    Triple S (bytes a vs₀) (writeBytes a value) (fun _ => S)
      (fun r => fun h => r = true ∧ bytes a (leBytes n value) h) := by
  rw [writeBytes_eq]
  refine triple_bind (triple_forM_ofFn S hS n a (fun i => value.extractLsb' (8 * i.val) 8) vs₀ hlen) ?_
  intro _
  exact triple_pure S (bytes a (leBytes n value)) true

/-- Framed rule for storing a little-endian 64-bit word (an `sd`-shaped store). -/
theorem triple_writeWord (S : StateAssertion) (hS : MemInsensitive S) (a : Nat) (w : BitVec (8 * 8))
    (vs₀ : List (BitVec 8)) (hlen : vs₀.length = 8) :
    Triple S (bytes a vs₀) (writeBytes a w) (fun _ => S) (fun r => fun h => r = true ∧ wordLE a w h) :=
  triple_writeBytes S hS a w vs₀ hlen

/-! ## The fixed-width read -/

/-- A read over an owned, in-range window runs to completion, leaves the machine state unchanged,
    and returns exactly the little-endian recomposition of the owned bytes with no fault flag. -/
theorem readBytes_run_exact (s : State) : ∀ (vs : List (BitVec 8)) (a : Nat),
    (∀ (i : Nat) (h : i < vs.length), s.mem.get? (a + i) = some vs[i]) →
    Runs (readBytes vs.length a) s s (leWord vs, none) := by
  intro vs
  induction vs with
  | nil =>
    intro a _
    show Runs (readBytes 0 a) s s (leWord [], none)
    have hz : leWord [] = (default : BitVec (8 * 0)) := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp at hi
    rw [hz]; rfl
  | cons v vs ih =>
    intro a hmem
    cases vs with
    | nil =>
      have hv : s.mem.get? a = some v := by simpa using hmem 0 (by simp)
      show Runs (readBytes 1 a) s s (leWord [v], none)
      rw [leWord_single]; simp only [PreSail.readBytes]
      exact Runs.bind (readByte_run s a v hv) rfl
    | cons w rest =>
      have hv : s.mem.get? a = some v := by simpa using hmem 0 (by simp)
      have hmem' : ∀ (i : Nat) (h : i < (w :: rest).length),
          s.mem.get? ((a + 1) + i) = some (w :: rest)[i] := by
        intro i hi
        rw [show (a + 1) + i = a + (i + 1) by omega]
        exact hmem (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
      show Runs (readBytes (rest.length + 1 + 1) a) s s (leWord (v :: w :: rest), none)
      simp only [PreSail.readBytes]
      exact Runs.bind (readByte_run s a v hv) (Runs.bind (ih (a + 1) hmem') rfl)

/-- Framed rule for the generated read: it leaves the machine state and owned range unchanged,
    preserves every disjoint frame, and returns the exact little-endian word with no fault flag. -/
theorem triple_readBytes (S : StateAssertion) (a : Nat) (vs : List (BitVec 8)) :
    Triple S (bytes a vs) (readBytes vs.length a) (fun _ => S)
      (fun r => fun h => r = (leWord vs, none) ∧ bytes a vs h) := by
  intro s hp hf hSs hb hdisj hsplit
  have hmem : ∀ (i : Nat) (h : i < vs.length), s.mem.get? (a + i) = some vs[i] := by
    intro i hi
    have hget := bytes_get a vs hp hb i hi
    have hstate : stateHeap s (a + i) = some vs[i] := by rw [hsplit]; exact union_apply_of_left hget
    simpa only [stateHeap] using hstate
  exact ⟨s, (leWord vs, none), hp, readBytes_run_exact s vs a hmem, hSs, ⟨rfl, hb⟩, hdisj, hsplit⟩

/-- Framed rule for reading a little-endian 64-bit word: it returns exactly `(w, none)` and
    preserves the word, every memory-insensitive state fact, and every disjoint frame. -/
theorem triple_readWord (S : StateAssertion) (a : Nat) (w : BitVec (8 * 8)) :
    Triple S (wordLE a w) (readBytes 8 a) (fun _ => S) (fun r => fun h => r = (w, none) ∧ wordLE a w h) := by
  have hw8 : leWord (leBytes 8 w) = w := by
    apply BitVec.eq_of_getLsbD_eq; intro j _; exact leWord_leBytes_getLsbD 8 w j
  exact triple_consequence (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    (fun r h => fun hpair =>
      ⟨hpair.1.trans (congrArg (fun value => (value, none)) hw8), hpair.2⟩)
    (triple_readBytes S a (leBytes 8 w))

/-! ## Frame preservation and acceptance theorems -/

/-- In a valid split, a defined frame address reads its frame value from the machine heap. -/
theorem stateHeap_frame {s : State} {hp hf : Heap} (hsplit : stateHeap s = union hp hf)
    (hdisj : Disjoint hp hf) {b : Nat} (hfb : hf b ≠ none) : stateHeap s b = hf b := by
  rw [hsplit]; rcases hdisj b with hl | hr
  · rw [union_apply_of_none hl]
  · exact absurd hr hfb

/-- Any disjoint frame address is left unchanged by a triple's action. -/
theorem Triple.frame_preserved {S : StateAssertion} {P : Assertion} {T : α → StateAssertion}
    {Q : α → Assertion} {action : SailM α}
    (h : Triple S P action T Q) (s : State) (hp hf : Heap)
    (hS : S s) (hP : P hp) (hdisj : Disjoint hp hf) (hsplit : stateHeap s = union hp hf) :
    ∃ (s' : State) (r : α), Runs action s s' r ∧ T r s' ∧
      ∀ b, hf b ≠ none → stateHeap s' b = stateHeap s b := by
  obtain ⟨s', r, hp', hRun, hTr, _, hdisj', hsplit'⟩ := h s hp hf hS hP hdisj hsplit
  exact ⟨s', r, hRun, hTr, fun b hfb =>
    (stateHeap_frame hsplit' hdisj' hfb).trans (stateHeap_frame hsplit hdisj hfb).symm⟩

/-- The read-then-write sequence on an owned byte, preserving a memory-insensitive state fact. -/
theorem triple_readWrite (S : StateAssertion) (hS : MemInsensitive S) (a : Nat) (v new : BitVec 8) :
    Triple S (pointsTo a v) (do let _ ← readByte a; writeByte a new) (fun _ => S)
      (fun _ => pointsTo a new) :=
  triple_bind (triple_readByte_frame S a v) (fun _ => triple_writeByte S hS a new v)

/-- Acceptance: a read-then-write on an owned byte updates only that byte, preserves a supplied
    memory-insensitive state fact, and leaves every disjoint frame address unchanged. -/
theorem readWrite_frame_preserved (S : StateAssertion) (hS : MemInsensitive S) (a : Nat)
    (v new : BitVec 8) (s : State) (hp hf : Heap) (hSs : S s) (hP : pointsTo a v hp)
    (hdisj : Disjoint hp hf) (hsplit : stateHeap s = union hp hf) :
    ∃ s' : State, Runs (do let _ ← readByte a; writeByte a new) s s' PUnit.unit ∧
      S s' ∧ (∀ b, hf b ≠ none → stateHeap s' b = stateHeap s b) ∧ stateHeap s' a = some new := by
  obtain ⟨s', r, hp', hRun, hTr, hQ, hdisj', hsplit'⟩ :=
    triple_readWrite S hS a v new s hp hf hSs hP hdisj hsplit
  obtain rfl : r = PUnit.unit := Subsingleton.elim r PUnit.unit
  refine ⟨s', hRun, hTr, fun b hfb =>
    (stateHeap_frame hsplit' hdisj' hfb).trans (stateHeap_frame hsplit hdisj hfb).symm, ?_⟩
  rw [hsplit']; exact union_apply_of_left hQ.1

/-- Acceptance (state side): with a concrete register precondition and an owned word plus an
    arbitrary disjoint frame, the generated word store preserves the register fact and the frame
    and stores exactly the little-endian bytes — proved only from the exported rules, without
    unfolding `Triple`. -/
theorem regFact_writeWord_demo (r : Register) (rv : RegisterType r) (a : Nat) (new : BitVec (8 * 8))
    (vs₀ : List (BitVec 8)) (hlen : vs₀.length = 8) (F : Assertion) :
    Triple (fun s => s.regs.get? r = some rv) (bytes a vs₀ ⋆ F) (writeBytes a new)
      (fun _ s => s.regs.get? r = some rv)
      (fun res => (fun h => res = true ∧ wordLE a new h) ⋆ F) :=
  triple_frame (triple_writeWord (fun s => s.regs.get? r = some rv) (memInsensitive_reg r rv)
    a new vs₀ hlen)

/-- Acceptance (state side): the generated word read preserves a concrete register fact and an
    arbitrary disjoint frame and returns exactly the owned word. -/
theorem regFact_readWord_demo (r : Register) (rv : RegisterType r) (a : Nat) (w : BitVec (8 * 8))
    (F : Assertion) :
    Triple (fun s => s.regs.get? r = some rv) (wordLE a w ⋆ F) (readBytes 8 a)
      (fun _ s => s.regs.get? r = some rv)
      (fun res => (fun h => res = (w, none) ∧ wordLE a w h) ⋆ F) :=
  triple_frame (triple_readWord (fun s => s.regs.get? r = some rv) a w)

end BinaryFv.RiscV.Sep
