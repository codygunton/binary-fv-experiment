import ZesuExec.Fn.MergeInPlace.C11564.Leaves
import ZesuExec.Sail.Run

/-!
# `sort.block.mergeInPlace__anon_11564`: `m11564_spec` and `m11564_sail`

`R11564.reach` (`zesu_assemble`) at the entry cut, whose assertion is `Pre` of the entry machine
and whose budget is `bound`; `sail_reaches` lifts it to the Sail model. The postcondition is
written out (it is `Post cfg`): a return, memory changed only in the output range and the frame,
and the output range a sorted permutation of the two runs (`MergeOf`) by the strings the elements
point to (`sliceKey`, read in the entry machine).
-/

namespace ZesuExec.Fn.MergeInPlace.C11564
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.SailLink ZesuExec.Machine ZesuExec.Fn.MergeInPlace

theorem m11564_spec : Spec zesuImage entry bound (Pre cfg)
    (fun m m' => Returns m m' ∧ SameOutside (Writes cfg m) m m' ∧
      MergeOf (sliceKey m) (win (items m (ptr m)) (aS m) (aE m))
        (win (items m (ptr m)) (bS m) (bE m)) (win (items m' (ptr m)) (aS m) (bE m))) :=
  fun m hpc hpre => R11564.reach xE (by simp [R11564.plan, vcPlan]) m m ⟨rfl, hpc, hpre⟩

theorem m11564_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre cfg m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧
      (Returns m m' ∧ SameOutside (Writes cfg m) m m' ∧
        MergeOf (sliceKey m) (win (items m (ptr m)) (aS m) (aE m))
          (win (items m (ptr m)) (bS m) (bE m)) (win (items m' (ptr m)) (aS m) (bE m)))) s :=
  sail_reaches h (m11564_spec m hpc hpre)

/-! ## Non-vacuity: a machine satisfying `Pre` -/

/-- The witness RAM's bytes: `A = {0, 1}` at `0xa0003000`, `B = {1, 2}` at `0xa0003010`; the two
items at `0xa0002000` are the empty slice at `0xa0004000` (`ptr` = `0xa0004000`, `len` = 0); zero
elsewhere. -/
def wByte (n : Nat) : Byte :=
  if n = 0xa0003008 ∨ n = 0xa0003010 then 1 else if n = 0xa0003018 then 2
  else if n = 0xa0002001 ∨ n = 0xa0002021 then 0x40
  else if n = 0xa0002003 ∨ n = 0xa0002023 then 0xa0 else 0

/-- `sp = 0xa0001000`, `ra = 0x80000000`, `a0 = 0xa0002000`, `a1 = 0xa0003000`,
`a2 = 0xa0003010`; the image's rodata and the witness RAM present, nothing else. -/
def witness : Machine where
  regs := fun i =>
    if i.val = 2 then w 0xa0001000 else if i.val = 1 then w 0x80000000
    else if i.val = 10 then w 0xa0002000 else if i.val = 11 then w 0xa0003000
    else if i.val = 12 then w 0xa0003010 else 0
  pc := w entry
  mem := fun x =>
    match zesuImage.rodataByte? x.toNat with
    | some b => some (BitVec.ofNat 8 b)
    | none => if Rotate.witnessRam x.toNat then some (wByte x.toNat) else none

theorem witness_ram {x : Word} (h : Rotate.witnessRam x.toNat = true) :
    witness.mem x = some (wByte x.toNat) := by
  have hlo : 0xa0000000 ≤ x.toNat := by simp [Rotate.witnessRam] at h; omega
  have hro : zesuImage.rodataByte? x.toNat = none := by
    cases h' : zesuImage.rodataByte? x.toNat with
    | none => rfl
    | some b => have := zesu_rodata_range h'; unfold Layout.rodataHi at this; omega
  simp only [witness, hro, h, if_true]

theorem witness_at {base j : Nat} (h1 : 0xa0000000 ≤ base) (h2 : base + j < 0xa0010000) :
    witness.mem (w base + w j) = some (wByte (base + j)) := by
  have e : (w base + w j).toNat = base + j := by
    rw [toNat_add_ofNat (by simp; omega)]; simp; omega
  rw [witness_ram (by rw [e]; simp [Rotate.witnessRam]; omega), e]

theorem witness_u64 {base : Nat} (off : Nat) (h1 : 0xa0000000 ≤ base) (h2 : base + 16 < 0xa0010000)
    (hoff : off + 8 ≤ 16) :
    u64 witness (w base) off = (ofBytesLE (byteList (fun j => wByte (base + j)) off 8)).toNat := by
  unfold u64; congr 2
  exact byteList_congr fun t ht => by rw [witness_at h1 (by omega)]; rfl

theorem wit_aS : aS witness = 0 := by
  unfold aS; rw [show witness.reg 11 = w 0xa0003000 from rfl, witness_u64 0 (by omega) (by omega)
    (by omega)]; decide
theorem wit_aE : aE witness = 1 := by
  unfold aE; rw [show witness.reg 11 = w 0xa0003000 from rfl, witness_u64 8 (by omega) (by omega)
    (by omega)]; decide
theorem wit_bS : bS witness = 1 := by
  unfold bS; rw [show witness.reg 12 = w 0xa0003010 from rfl, witness_u64 0 (by omega) (by omega)
    (by omega)]; decide
theorem wit_bE : bE witness = 2 := by
  unfold bE; rw [show witness.reg 12 = w 0xa0003010 from rfl, witness_u64 8 (by omega) (by omega)
    (by omega)]; decide

theorem sorted_one {G : Nat → Nat → Byte} {lo : Nat} (key : List Byte → List Byte) :
    Sorted key (win G lo (lo + 1)) := by
  rw [win_one]; exact List.pairwise_singleton _ _

/-- The two items as byte lists. -/
theorem wit_el {e : Nat} (he : e < 2) :
    el (items witness (ptr witness)) e = (List.range 32).map fun o => wByte (0xa0002000 + (32 * e + o)) := by
  unfold el
  apply List.map_congr_left
  intro o ho
  have ho' := List.mem_range.mp ho
  simp only [items, Rotate.bytesOf, ptr, show witness.reg 10 = w 0xa0002000 from rfl]
  rw [witness_at (by omega) (by omega)]; rfl

theorem wit_str {e : Nat} (he : e < 2) :
    slicePtr (el (items witness (ptr witness)) e) = w 0xa0004000 ∧
      sliceLen (el (items witness (ptr witness)) e) = 0 := by
  rw [wit_el he]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- Contract rule (a): `Pre` holds of a concrete machine (`A = [0, 1)`, `B = [1, 2)`, two equal
elements, both the empty string at `0xa0004000`). -/
theorem pre_nonvacuous : ∃ m, Pre cfg m := by
  refine ⟨witness, ?_⟩
  have r1 : witness.reg 1 = w 0x80000000 := rfl
  have r2 : witness.reg 2 = w 0xa0001000 := rfl
  have r10 : witness.reg 10 = w 0xa0002000 := rfl
  have r11 : witness.reg 11 = w 0xa0003000 := rfl
  have r12 : witness.reg 12 = w 0xa0003010 := rfl
  have hfr : (frame cfg witness).toNat = 0xa0000ef0 := by
    unfold frame; rw [r2]; decide
  have hsome : ∀ base j, 0xa0000000 ≤ base → base + j < 0xa0010000 →
      (witness.mem (w base + w j)).isSome := fun base j h1 h2 => by rw [witness_at h1 h2]; rfl
  refine ⟨fun x b h => ?_, ⟨by rw [r2]; decide, by rw [r2]; decide, by rw [r2]; decide,
    fun j hj => ?_⟩, by unfold RetAligned; rw [r1]; decide, by rw [r11]; decide,
    fun j hj => by rw [r11]; exact hsome _ _ (by omega) (by omega), by rw [r12]; decide,
    fun j hj => by rw [r12]; exact hsome _ _ (by omega) (by omega),
    by rw [wit_aS, wit_aE]; decide, by rw [wit_aE, wit_bS], by rw [wit_bS, wit_bE]; decide,
    ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : x < 2 ^ 64 := by
      have := zesu_rodata_range h; unfold Layout.rodataHi at this; omega
    simp [witness, Nat.mod_eq_of_lt hx, h]
  · rw [r2]
    have : w 0xa0001000 - BitVec.ofNat 64 cfg.fs = w 0xa0000ef0 := by decide
    rw [this]; exact hsome _ _ (by omega) (by simp [cfg] at hj; omega)
  · rw [wit_bE]; simp only [ptr, r10]; decide
  · rw [wit_bE] at hj; simp only [ptr, r10]; exact hsome _ _ (by omega) (by omega)
  · unfold Disjoint; rw [wit_bE, hfr]; simp only [ptr, r10, cfg]; decide
  · unfold Disjoint; rw [r11, r12]; decide
  · unfold Disjoint; rw [r11, hfr]; simp only [cfg]; decide
  · unfold Disjoint; rw [r12, hfr]; simp only [cfg]; decide
  · rw [wit_aS, wit_aE]; exact sorted_one _
  · rw [wit_bS, wit_bE]; exact sorted_one _
  · intro e he1 he2
    rw [wit_bE] at he2
    obtain ⟨hp, hl⟩ := wit_str he2
    refine ⟨by rw [hp, hl]; decide, fun j hj => by rw [hl] at hj; omega, ?_, ?_⟩
    · unfold Disjoint; rw [hp, hl, wit_bE]; simp only [ptr, r10]; decide
    · unfold Disjoint; rw [hp, hl, r2]; decide

end ZesuExec.Fn.MergeInPlace.C11564
