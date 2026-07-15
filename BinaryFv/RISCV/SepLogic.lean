import BinaryFv.RISCV.Framing

/-!
# A bespoke, memory-only separation logic over `SailM`

This module builds a minimal separation logic directly on the generated Sail state monad.  It is
deliberately small: a logical heap view of the sparse byte memory, the usual separating
connectives (`emp`, points-to, separating conjunction), success-only framed Hoare triples over the
existing `Runs` relation, and structural rules for the generated memory primitives.

The logic is memory-only.  Registers and platform state are left to the ordinary pre/postcondition
framing already available in `BinaryFv.RISCV.Framing`; nothing here touches them.  There are no
modalities, no ghost state, no recursively defined heap predicates, no magic wand, and no general
proof-mode tactic — only what later Keccak contracts need to frame concrete memory effects.
-/

namespace BinaryFv.RISCV.Sep

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

theorem sepConj_comm {P Q : Assertion} {h : Heap} : (P ⋆ Q) h → (Q ⋆ P) h := by
  rintro ⟨h₁, h₂, hdisj, rfl, hP, hQ⟩
  exact ⟨h₂, h₁, hdisj.symm, union_comm hdisj, hQ, hP⟩

theorem emp_sepConj {P : Assertion} {h : Heap} : (emp ⋆ P) h ↔ P h := by
  constructor
  · rintro ⟨h₁, h₂, _, rfl, hemp, hP⟩
    have hrw : union h₁ h₂ = h₂ := by funext a; rw [union_apply_of_none (hemp a)]
    rw [hrw]; exact hP
  · intro hP
    exact ⟨fun _ => none, h, fun a => Or.inl rfl, by funext a; rw [union_apply_of_none rfl],
      fun a => rfl, hP⟩

/-! ## Framed success triples

`Triple P action Q` is a small-footprint, success-only Hoare triple: from every machine state whose
byte memory decomposes as an owned part satisfying `P` and an arbitrary disjoint frame `hf`, the
generated `action` runs to completion, the frame `hf` survives untouched, and the new owned part
satisfies `Q` on the returned value. -/
def Triple (P : Assertion) (action : SailM α) (Q : α → Assertion) : Prop :=
  ∀ (s : State) (hp hf : Heap),
    P hp → Disjoint hp hf → stateHeap s = union hp hf →
    ∃ (s' : State) (r : α) (hp' : Heap),
      Runs action s s' r ∧ Q r hp' ∧ Disjoint hp' hf ∧ stateHeap s' = union hp' hf

theorem triple_pure (P : Assertion) (a : α) :
    Triple P (pure a) (fun r => fun h => r = a ∧ P h) := by
  intro s hp hf hP hdisj hsplit
  exact ⟨s, a, hp, rfl, ⟨rfl, hP⟩, hdisj, hsplit⟩

theorem triple_bind {P : Assertion} {Q : α → Assertion} {R : β → Assertion}
    {first : SailM α} {next : α → SailM β}
    (hFirst : Triple P first Q) (hNext : ∀ a, Triple (Q a) (next a) R) :
    Triple P (first >>= next) R := by
  intro s hp hf hP hdisj hsplit
  obtain ⟨s', r, hp', hRun, hQ, hdisj', hsplit'⟩ := hFirst s hp hf hP hdisj hsplit
  obtain ⟨s'', r', hp'', hRun', hR, hdisj'', hsplit''⟩ := hNext r s' hp' hf hQ hdisj' hsplit'
  exact ⟨s'', r', hp'', Runs.bind hRun hRun', hR, hdisj'', hsplit''⟩

theorem triple_consequence {P P' : Assertion} {Q Q' : α → Assertion} {action : SailM α}
    (hpre : ∀ h, P' h → P h) (hpost : ∀ r h, Q r h → Q' r h)
    (h : Triple P action Q) : Triple P' action Q' := by
  intro s hp hf hP' hdisj hsplit
  obtain ⟨s', r, hp', hRun, hQ, hdisj', hsplit'⟩ := h s hp hf (hpre hp hP') hdisj hsplit
  exact ⟨s', r, hp', hRun, hpost r hp' hQ, hdisj', hsplit'⟩

/-! ### The frame rule -/

theorem triple_frame {P : Assertion} {Q : α → Assertion} {F : Assertion} {action : SailM α}
    (h : Triple P action Q) : Triple (P ⋆ F) action (fun r => Q r ⋆ F) := by
  intro s hp hf hPF hdisj hsplit
  obtain ⟨hP, hF, hdisjPF, rfl, hPhP, hFhF⟩ := hPF
  obtain ⟨hdisjPhf, hdisjFhf⟩ := disjoint_union_left_iff.mp hdisj
  have hdisjInner : Disjoint hP (union hF hf) := disjoint_union_right_iff.mpr ⟨hdisjPF, hdisjPhf⟩
  have hsplitInner : stateHeap s = union hP (union hF hf) := by
    rw [hsplit, union_assoc]
  obtain ⟨s', r, hp', hRun, hQ, hdisj', hsplit'⟩ := h s hP (union hF hf) hPhP hdisjInner hsplitInner
  obtain ⟨hdisj'F, hdisj'hf⟩ := disjoint_union_right_iff.mp hdisj'
  refine ⟨s', r, union hp' hF, hRun, ⟨hp', hF, hdisj'F, rfl, hQ, hFhF⟩,
    disjoint_union_left_iff.mpr ⟨hdisj'hf, hdisjFhf⟩, ?_⟩
  rw [hsplit', union_assoc]

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

theorem triple_writeByte (a : Nat) (v v₀ : BitVec 8) :
    Triple (pointsTo a v₀) (writeByte a v) (fun _ => pointsTo a v) := by
  intro s hp hf hP hdisj hsplit
  obtain ⟨hpa, hpother⟩ := hP
  refine ⟨{s with mem := s.mem.insert a v}, PUnit.unit, updateByte hp a v,
    writeByte_run s a v, ⟨updateByte_self hp a v, fun b hb => ?_⟩, ?_, ?_⟩
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

theorem triple_readByte (a : Nat) (v : BitVec 8) :
    Triple (pointsTo a v) (readByte a) (fun r => fun h => r = v ∧ pointsTo a v h) := by
  intro s hp hf hP hdisj hsplit
  obtain ⟨hpa, hpother⟩ := hP
  have hmem : s.mem.get? a = some v := by
    have hb := congrFun hsplit a
    simp only [stateHeap] at hb
    rw [union_apply_of_left hpa] at hb
    exact hb
  exact ⟨s, v, hp, readByte_run s a v hmem, ⟨rfl, hpa, hpother⟩, hdisj, hsplit⟩

/-- The pure-preservation reading of `readByte`, discarding the returned value. -/
theorem triple_readByte_frame (a : Nat) (v : BitVec 8) :
    Triple (pointsTo a v) (readByte a) (fun _ => pointsTo a v) :=
  triple_consequence (fun _ h => h) (fun _ _ h => h.2) (triple_readByte a v)

/-- Frame an assertion on the left of a triple's pre/postcondition. -/
theorem triple_frame_left {P : Assertion} {Q : α → Assertion} {F : Assertion} {action : SailM α}
    (h : Triple P action Q) : Triple (F ⋆ P) action (fun r => F ⋆ Q r) :=
  triple_consequence (fun _ => sepConj_comm) (fun _ _ => sepConj_comm) (triple_frame h)

/-! ## Byte ranges and little-endian words -/

/-- Ownership of consecutive bytes `vs` starting at address `a`, in ascending address order. -/
def bytes (a : Nat) : List (BitVec 8) → Assertion
  | [] => emp
  | v :: vs => pointsTo a v ⋆ bytes (a + 1) vs

theorem bytes_nil (a : Nat) : bytes a [] = emp := rfl

theorem bytes_cons (a : Nat) (v : BitVec 8) (vs : List (BitVec 8)) :
    bytes a (v :: vs) = pointsTo a v ⋆ bytes (a + 1) vs := rfl

/-- Every owned address in a byte range is defined in the owning heap. -/
theorem bytes_defined : ∀ (a : Nat) (vs : List (BitVec 8)) (h : Heap),
    bytes a vs h → ∀ i, i < vs.length → ∃ v, h (a + i) = some v := by
  intro a vs
  induction vs generalizing a with
  | nil => intro h _ i hi; exact absurd hi (by simp)
  | cons v vs ih =>
    intro h hb i hi
    obtain ⟨h₁, h₂, hdisj, rfl, ⟨hpt, _⟩, htail⟩ := hb
    cases i with
    | zero => exact ⟨v, by simpa using union_apply_of_left hpt⟩
    | succ j =>
      simp only [List.length_cons] at hi
      obtain ⟨w, hw⟩ := ih (a + 1) h₂ htail j (by omega)
      refine ⟨w, ?_⟩
      have haddr : a + (j + 1) = (a + 1) + j := by omega
      rw [haddr]
      have hleft : h₁ ((a + 1) + j) = none := by
        rcases hdisj ((a + 1) + j) with hl | hr
        · exact hl
        · rw [hr] at hw; exact absurd hw (by simp)
      rw [union_apply_of_none hleft]; exact hw

/-- Framed rule for the generated fixed-width store, expressed over consecutive `writeByte`s. -/
theorem triple_forM_ofFn : ∀ (n a : Nat) (f : Fin n → BitVec 8) (vs₀ : List (BitVec 8)),
    vs₀.length = n →
    Triple (bytes a vs₀)
      (List.forM (List.ofFn (fun i : Fin n => (a + i.val, f i))) (fun p => writeByte p.1 p.2))
      (fun _ => bytes a (List.ofFn f)) := by
  intro n
  induction n with
  | zero =>
    intro a f vs₀ hlen
    obtain rfl : vs₀ = [] := by cases vs₀ with | nil => rfl | cons v vs' => simp at hlen
    simp only [List.ofFn_zero]
    exact triple_consequence (fun _ h => h) (fun _ _ h => h.2) (triple_pure (bytes a []) PUnit.unit)
  | succ n ih =>
    intro a f vs₀ hlen
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs₀ = v :: vs' := by
      cases vs₀ with
      | nil => simp at hlen
      | cons v vs' => exact ⟨v, vs', rfl⟩
    have hlen' : vs'.length = n := by simpa using hlen
    have hfun : (fun j : Fin n => ((a + 1) + j.val, f j.succ)) =
                (fun j : Fin n => (a + (Fin.succ j).val, f j.succ)) := by
      funext j
      rw [show (a + 1) + j.val = a + (Fin.succ j).val by simp only [Fin.val_succ]; omega]
    have hhead : Triple (bytes a (v :: vs')) (writeByte a (f 0))
        (fun _ => pointsTo a (f 0) ⋆ bytes (a + 1) vs') := by
      rw [bytes_cons]; exact triple_frame (triple_writeByte a (f 0) v)
    have htail : Triple (pointsTo a (f 0) ⋆ bytes (a + 1) vs')
        (List.forM (List.ofFn (fun j : Fin n => (a + (Fin.succ j).val, f j.succ)))
          (fun p => writeByte p.1 p.2))
        (fun _ => pointsTo a (f 0) ⋆ bytes (a + 1) (List.ofFn (fun j : Fin n => f j.succ))) := by
      rw [← hfun]; exact triple_frame_left (ih (a + 1) (fun j => f j.succ) vs' hlen')
    simp only [List.ofFn_succ, Fin.val_zero, Nat.add_zero]
    exact triple_bind hhead (fun _ => htail)

/-- The little-endian byte decomposition of a `BitVec (8 * n)`: byte `i` is bits `[8i, 8i+8)`. -/
def leBytes (n : Nat) (value : BitVec (8 * n)) : List (BitVec 8) :=
  List.ofFn (fun i : Fin n => value.extractLsb' (8 * i.val) 8)

theorem writeBytes_eq (a : Nat) {n : Nat} (value : BitVec (8 * n)) :
    (writeBytes a value : SailM Bool) =
      (List.forM (List.ofFn (fun i : Fin n => (a + i.val, value.extractLsb' (8 * i.val) 8)))
        (fun p => writeByte p.1 p.2) >>= fun _ => pure true) := rfl

/-- Framed rule for the generated fixed-width store: an owned `n`-byte range is overwritten with
    the little-endian bytes of `value`, and every disjoint frame is preserved. -/
theorem triple_writeBytes (a : Nat) {n : Nat} (value : BitVec (8 * n)) (vs₀ : List (BitVec 8))
    (hlen : vs₀.length = n) :
    Triple (bytes a vs₀) (writeBytes a value)
      (fun r => fun h => r = true ∧ bytes a (leBytes n value) h) := by
  rw [writeBytes_eq]
  refine triple_bind (triple_forM_ofFn n a (fun i => value.extractLsb' (8 * i.val) 8) vs₀ hlen) ?_
  intro _
  exact triple_pure (bytes a (leBytes n value)) true

/-- A little-endian 64-bit word stored at address `a`. -/
def wordLE (a : Nat) (w : BitVec (8 * 8)) : Assertion := bytes a (leBytes 8 w)

/-- Framed rule for storing a little-endian 64-bit word (an `sd`-shaped store). -/
theorem triple_writeWord (a : Nat) (w : BitVec (8 * 8)) (vs₀ : List (BitVec 8))
    (hlen : vs₀.length = 8) :
    Triple (bytes a vs₀) (writeBytes a w) (fun r => fun h => r = true ∧ wordLE a w h) :=
  triple_writeBytes a w vs₀ hlen

/-! ## Reading a byte range -/

/-- A byte read over an owned, in-range window runs to completion without disturbing state. -/
theorem readBytes_runs_unchanged (s : State) : ∀ (n a : Nat),
    (∀ i, i < n → ∃ v, s.mem.get? (a + i) = some v) →
    ∃ w, Runs (readBytes n a) s s (w, none) := by
  intro n
  induction n with
  | zero => intro a _; exact ⟨default, rfl⟩
  | succ n ih =>
    intro a hpres
    cases n with
    | zero =>
      obtain ⟨v, hv⟩ := hpres 0 (by omega)
      simp only [PreSail.readBytes]
      exact ⟨_, Runs.bind (readByte_run s a v hv) rfl⟩
    | succ m =>
      obtain ⟨v, hv⟩ := hpres 0 (by omega)
      have hpres' : ∀ i, i < m + 1 → ∃ v, s.mem.get? ((a + 1) + i) = some v := by
        intro i hi
        rw [show (a + 1) + i = a + (i + 1) by omega]
        exact hpres (i + 1) (by omega)
      obtain ⟨w, hw⟩ := ih (a + 1) hpres'
      simp only [PreSail.readBytes]
      exact ⟨_, Runs.bind (readByte_run s a v hv) (Runs.bind hw rfl)⟩

/-- Framed rule for the generated read: it returns some value with no fault flag and leaves the
    owned range and every disjoint frame untouched. -/
theorem triple_readBytes (a : Nat) (vs : List (BitVec 8)) :
    Triple (bytes a vs) (readBytes vs.length a) (fun r => fun h => r.2 = none ∧ bytes a vs h) := by
  intro s hp hf hb hdisj hsplit
  have hpres : ∀ i, i < vs.length → ∃ v, s.mem.get? (a + i) = some v := by
    intro i hi
    obtain ⟨v, hv⟩ := bytes_defined a vs hp hb i hi
    refine ⟨v, ?_⟩
    have hstate : stateHeap s (a + i) = some v := by rw [hsplit]; exact union_apply_of_left hv
    simpa only [stateHeap] using hstate
  obtain ⟨w, hrun⟩ := readBytes_runs_unchanged s vs.length a hpres
  exact ⟨s, (w, none), hp, hrun, ⟨rfl, hb⟩, hdisj, hsplit⟩

/-! ## Frame preservation and the read/write acceptance theorem -/

/-- In a valid split, a defined frame address reads its frame value from the machine heap. -/
theorem stateHeap_frame {s : State} {hp hf : Heap} (hsplit : stateHeap s = union hp hf)
    (hdisj : Disjoint hp hf) {b : Nat} (hfb : hf b ≠ none) : stateHeap s b = hf b := by
  rw [hsplit]; rcases hdisj b with hl | hr
  · rw [union_apply_of_none hl]
  · exact absurd hr hfb

/-- Any disjoint frame address is left unchanged by a triple's action. -/
theorem Triple.frame_preserved {P : Assertion} {Q : α → Assertion} {action : SailM α}
    (h : Triple P action Q) (s : State) (hp hf : Heap)
    (hP : P hp) (hdisj : Disjoint hp hf) (hsplit : stateHeap s = union hp hf) :
    ∃ (s' : State) (r : α), Runs action s s' r ∧
      ∀ b, hf b ≠ none → stateHeap s' b = stateHeap s b := by
  obtain ⟨s', r, hp', hRun, _, hdisj', hsplit'⟩ := h s hp hf hP hdisj hsplit
  exact ⟨s', r, hRun, fun b hfb =>
    (stateHeap_frame hsplit' hdisj' hfb).trans (stateHeap_frame hsplit hdisj hfb).symm⟩

/-- The read-then-write sequence on an owned byte updates only that byte and preserves every
    disjoint frame — the concrete acceptance property for this separation logic. -/
theorem triple_readWrite (a : Nat) (v new : BitVec 8) :
    Triple (pointsTo a v) (do let _ ← readByte a; writeByte a new) (fun _ => pointsTo a new) :=
  triple_bind (triple_readByte_frame a v) (fun _ => triple_writeByte a new v)

theorem readWrite_frame_preserved (a : Nat) (v new : BitVec 8) (s : State) (hp hf : Heap)
    (hP : pointsTo a v hp) (hdisj : Disjoint hp hf) (hsplit : stateHeap s = union hp hf) :
    ∃ s' : State, Runs (do let _ ← readByte a; writeByte a new) s s' PUnit.unit ∧
      (∀ b, hf b ≠ none → stateHeap s' b = stateHeap s b) ∧ stateHeap s' a = some new := by
  obtain ⟨s', r, hp', hRun, hQ, hdisj', hsplit'⟩ :=
    triple_readWrite a v new s hp hf hP hdisj hsplit
  obtain rfl : r = PUnit.unit := Subsingleton.elim r PUnit.unit
  refine ⟨s', hRun, fun b hfb =>
    (stateHeap_frame hsplit' hdisj' hfb).trans (stateHeap_frame hsplit hdisj hfb).symm, ?_⟩
  rw [hsplit']; exact union_apply_of_left hQ.1
