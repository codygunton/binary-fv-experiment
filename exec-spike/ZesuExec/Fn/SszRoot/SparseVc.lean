import ZesuExec.Fn.SszRoot.SparseDefs
import ZesuExec.Fn.SszRoot.Lemmas
import ZesuExec.Vc.SoundRec

/-!
# `sparseRoot`: assertions, plan, cut lemmas

`σ` is the entry machine `g`. `fb g = sp - 0x120` is the frame. `Keep g m`: `Pre g`; memory
changed only in `WrittenN` and every present byte kept; `ra`, `s0`–`s5` saved at
`fb + 0xe8 …`; `sp = fb`, `s1` the result pointer, `s6`–`s11` the entry values. `Fr` adds
`depth ≥ 1`, `s0 = sp₀`, `s3 = len`. Assertions: after the left call (`A70`: the left root at
`fb + 0x28`, `s2` the chunks, `s4 = depth - 1`, `s5 = half`), at `ccK k` (`AC k`: `s4 = k`,
`depth = k + 1`, no chunk in the right half), after the right call (`A94`: both roots, `s2 = fb +
0x68`), after `zkvm_sha256` or the depth-0 paths (`A54`: the root of all chunks at `s2`, which
is `fb + 8`, `fb + 0x88` or the zero chunk). Budgets: `sparseCost` at the entry, then what is
left of it.
-/

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Entry-machine quantities -/

def fb (g : Machine) : Word := g.reg 2 - BitVec.ofNat 64 0x120
abbrev ch (g : Machine) : List (List Byte) := chunksOf g (chunkPtr g) (lenOf g)
abbrev half (g : Machine) : Nat := 2 ^ (depthOf g - 1)
def leftRoot (g : Machine) : List Byte := sparseRoot ((ch g).take (half g)) (depthOf g - 1)
def rightRoot (g : Machine) : List Byte := sparseRoot ((ch g).drop (half g)) (depthOf g - 1)

/-- `s5, s4, s3, s2, s1, s0, ra`: saved at `fb + 0xe8 + 8 q`. -/
def savedReg (q : Nat) : Fin 32 := [21, 20, 19, 18, 9, 8, 1].getD q 0

def Saved (g m : Machine) : Prop :=
  ∀ q < 7, ∀ t < 8,
    m.mem (fb g + BitVec.ofNat 64 (0xe8 + 8 * q + t)) = some (byteOf (g.reg (savedReg q)) t)

def keepRegs : List (Fin 32) := [22, 23, 24, 25, 26, 27]

def Keep (g m : Machine) : Prop :=
  SparsePre g ∧ SameOutside (WrittenN (sparseNeed g) g) g m ∧ Preserved g m ∧ Saved g m ∧
  m.reg 2 = fb g ∧ m.reg 9 = g.reg 10 ∧ ∀ i ∈ keepRegs, m.reg i = g.reg i

def Fr (g m : Machine) : Prop :=
  Keep g m ∧ 1 ≤ depthOf g ∧ m.reg 8 = g.reg 2 ∧ m.reg 19 = g.reg 12

def AE (g m : Machine) : Prop := m = g ∧ m.pc.toNat = sparseEntry ∧ SparsePre m

def A70 (g m : Machine) : Prop :=
  Fr g m ∧ m.pc.toNat = pc70 ∧ m.reg 18 = g.reg 11 ∧ m.reg 20 = g.reg 13 - 1 ∧
  m.reg 21 = (1 : Word) <<< ((g.reg 13 - 1).toNat % 64) ∧
  BytesAt m (fb g + BitVec.ofNat 64 0x28) (leftRoot g)

def AC (k : Nat) (g m : Machine) : Prop :=
  Fr g m ∧ m.pc.toNat = pcC4 ∧ m.reg 20 = BitVec.ofNat 64 k ∧ depthOf g = k + 1 ∧
  lenOf g ≤ half g ∧ BytesAt m (fb g + BitVec.ofNat 64 0x28) (leftRoot g)

def A94 (g m : Machine) : Prop :=
  Fr g m ∧ m.pc.toNat = pc94 ∧ m.reg 18 = fb g + BitVec.ofNat 64 0x68 ∧ half g < lenOf g ∧
  BytesAt m (fb g + BitVec.ofNat 64 0x28) (leftRoot g) ∧
  BytesAt m (fb g + BitVec.ofNat 64 0x68) (rightRoot g)

def A54 (g m : Machine) : Prop :=
  Keep g m ∧ m.pc.toNat = pc54 ∧ BytesAt m (m.reg 18) (sparseRoot (ch g) (depthOf g)) ∧
  (m.reg 18 = fb g + BitVec.ofNat 64 8 ∨ m.reg 18 = fb g + BitVec.ofNat 64 0x88 ∨
    m.reg 18 = BitVec.ofNat 64 0x801154c0)

/-! ## Budgets -/

def rest70 (g : Machine) : Nat :=
  if lenOf g ≤ half g then 1 + 36 + shaCost + 17
  else 9 + sparseCost (depthOf g - 1) (lenOf g - half g) + 23 + shaCost + 17

/-! ## Cuts and plan -/

def cE : Cut Machine :=
  ⟨sparseEntry, SE, AE, fun _ m => entryEnv m (regsE m), fun g _ => sparseCost (depthOf g) (lenOf g)⟩
def c70 : Cut Machine := ⟨pc70, S70, A70, fun _ m => entryEnv m [], fun g _ => rest70 g⟩
def c94 : Cut Machine := ⟨pc94, S94, A94, fun _ m => entryEnv m (regsF m), fun _ _ => 23 + shaCost + 17⟩
def c54 : Cut Machine := ⟨pc54, S54, A54, fun _ m => entryEnv m (regs54 m), fun _ _ => 17⟩
def ccK (k : Nat) : Cut Machine :=
  ⟨pcC4, SC k, AC k, fun _ m => entryEnv m (regsF m), fun _ _ => 36 + shaCost + 17⟩

def cuts : List (Cut Machine) := [cE, c70, c94, c54] ++ (List.range 26).map ccK

def leaves (i : Nat) : List Leaf :=
  if i = 0 then runE_leaves else if i = 1 then run70_leaves else if i = 2 then run94_leaves
  else if i = 3 then run54_leaves else lvC.getD (i - 4) []

/-- `zkvm_sha256` on 64 bytes, its result with `Preserved`. -/
def shaC (hsha : ShaSpec) : Callee Machine zesuImage where
  entry := Sha256.entry
  bound := shaCost
  Pre := fun _ _ m => Sha256.Pre m ∧ (m.reg 11).toNat = 64
  Post := fun _ _ m m' => Sha256.Post m m' ∧ Preserved m m'
  spec := fun _ _ m hpc hpre => Reaches.preserve (hsha m hpc hpre)

def plan (hsha : ShaSpec) : PlanR Machine zesuImage where
  cuts := cuts
  fuel := fuel
  leaves := leaves
  callee := fun r => if r = pc54 then some (shaC hsha) else none
  Post := fun g => SparsePost g

theorem cuts_pcs : cuts.map (·.pc) = pcs := by decide

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Arithmetic on the entry machine -/

theorem need_ge (g : Machine) : 0x120 + 0xe0 ≤ sparseNeed g := by
  unfold sparseNeed sparseStack Sha256.frameSize; omega

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The frame base as a numeral address. -/
theorem fb_toNat {g : Machine} (F : PreFacts (sparseNeed g) g) :
    (fb g).toNat = (g.reg 2).toNat - 0x120 := by
  have := need_ge g; have := F.spLo
  unfold fb; rw [BitVec.toNat_sub]; simp [Layout.ramLo] at *; omega

theorem fb_add {g : Machine} (F : PreFacts (sparseNeed g) g) (c : Nat) :
    fb g + BitVec.ofNat 64 c = BitVec.ofNat 64 ((g.reg 2).toNat - 0x120 + c) := by
  rw [← fb_toNat F, ofNat_toNat_add]

/-- Every stack byte of the entry machine is present. -/
theorem stack_present {g : Machine} (F : PreFacts (sparseNeed g) g) {x : Nat}
    (h1 : (g.reg 2).toNat - sparseNeed g ≤ x) (h2 : x < (g.reg 2).toNat) :
    (g.mem (BitVec.ofNat 64 x)).isSome := by
  have := F.stack (x - ((g.reg 2).toNat - sparseNeed g)) (by omega)
  have hsp := F.spLo; have hhi := F.spHi
  rw [show g.reg 2 - BitVec.ofNat 64 (sparseNeed g) +
      BitVec.ofNat 64 (x - ((g.reg 2).toNat - sparseNeed g)) = BitVec.ofNat 64 x by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp [Layout.ramLo, Layout.ramHi] at hsp hhi
    omega] at this
  exact this

/-- A byte present in `g` is present in `m`. -/
theorem present_of {g m : Machine} (hp : Preserved g m) {a : Word} (h : (g.mem a).isSome) :
    (m.mem a).isSome := hp.1 a h

theorem ro_of {g m : Machine} (F : PreFacts (sparseNeed g) g) (hp : Preserved g m) :
    RodataLoaded zesuImage m := RodataLoaded.preserved F.ro hp rodata_lo

/-- The stack region of `g` is written memory. -/
theorem written_stack {g : Machine} (F : PreFacts (sparseNeed g) g) {a : Word}
    (h1 : (g.reg 2).toNat - sparseNeed g ≤ a.toNat) (h2 : a.toNat < (g.reg 2).toNat) :
    WrittenN (sparseNeed g) g a := by
  have := F.spLo
  refine .inl ⟨?_, ?_⟩ <;> rw [BitVec.toNat_sub] <;> simp [Layout.ramLo] at * <;> omega

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Cut lemmas -/

variable (hsha : ShaSpec)

theorem cut_E : CutOK (plan hsha).toPlan cE := by
  rintro g m ⟨rfl, hpc, hpre⟩
  have F := PreFacts.of hpre.2
  have hN := need_ge m
  have hlo := F.spLo; have hhi := F.spHi
  have hsub : (m.reg 2 - BitVec.ofNat 64 0x120).toNat = (m.reg 2).toNat - 0x120 := by
    rw [BitVec.toNat_sub]; simp [Layout.ramLo] at hlo ⊢; omega
  refine ⟨?_, ?_, F.ro, hpc⟩
  · refine entry_wf (shape := [((m.reg 2 - BitVec.ofNat 64 0x120, 0x120), frR),
      ((m.reg 11, 32 * lenOf m), lvR)]) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · refine ⟨fun s hs => by simp [frR] at hs; omega, by simp [frR, Nat.mod_one], ?_⟩
        simp only [frR, if_true, writable, inRange, hsub, Bool.and_eq_true, decide_eq_true_eq]
        simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
      · exact ⟨fun s hs => by simp [lvR] at hs, by simp [lvR, Nat.mod_one],
          by simpa [lvR] using F.chR⟩
    · have := F.dSC
      simp only [chunkPtr] at this
      simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true, Disjoint, hsub]
      refine ⟨by omega, fun _ h => h.elim⟩
  · refine entry_match ?_ ?_ (by simp)
    · intro i _ s hs
      unfold ovE at hs
      split at hs
      · next h2 =>
        cases hs; have : i = 2 := Fin.ext h2; subst this
        simp [Sym.eval, Env.base, entryEnv, regsE, BitVec.sub_add_cancel]
      · split at hs
        · next h11 =>
          cases hs; have : i = 11 := Fin.ext h11; subst this
          simp [Sym.eval, Env.base, entryEnv, regsE]
        · cases hs
    · intro r j hr hj
      simp only [entryState, List.length_cons, List.length_nil] at hr
      match r, hr with
      | 0, _ =>
        simp only [Env.size, entryEnv, regsE, List.getD_cons_zero] at hj
        simp only [Env.base, entryEnv, regsE, List.getD_cons_zero]
        rw [← ofNat_toNat_add, hsub]
        exact stack_present F (by omega) (by omega)
      | 1, _ =>
        simp only [Env.size, entryEnv, regsE, List.getD_cons_succ, List.getD_cons_zero] at hj
        simp only [Env.base, entryEnv, regsE, List.getD_cons_succ, List.getD_cons_zero]
        rw [← ofNat_toNat_add]
        exact present_get F.chP hj

/-- The cuts after the prologue with the frame as their one region (`c94`, `ccK k`). -/
theorem frame_wf_match {g m : Machine} {ov : Nat → Option Sym} (hk : Fr g m)
    (hov : ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s → s.eval (entryEnv m (regsF m)) = m.reg i) :
    Env.WF (entryEnv m (regsF m)) (entryState ov [frR] []) ∧
      Match (entryEnv m (regsF m)) (entryState ov [frR] []) m := by
  obtain ⟨⟨hpre, -, hp, -, h2, -⟩, -⟩ := hk
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have hfb := fb_toNat F
  refine ⟨entry_wf (shape := [((m.reg 2, 0x120), frR)]) ?_ (by simp), entry_match hov ?_ (by simp)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p rfl
    refine ⟨fun s hs => by simp [frR] at hs; omega, by simp [frR, Nat.mod_one], ?_⟩
    simp only [frR, if_true, writable, inRange, h2, hfb, Bool.and_eq_true, decide_eq_true_eq]
    simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
  · intro r j hr hj
    simp only [entryState, List.length_cons, List.length_nil] at hr
    match r, hr with
    | 0, _ =>
      simp only [Env.size, entryEnv, regsF, List.getD_cons_zero] at hj
      simp only [Env.base, entryEnv, regsF, List.getD_cons_zero, h2]
      rw [← ofNat_toNat_add, hfb]
      exact present_of hp (stack_present F (by omega) (by omega))

theorem cut_70 : CutOK (plan hsha).toPlan c70 := by
  rintro g m ⟨hk, hpc, -⟩
  have F := PreFacts.of hk.1.1.2
  refine ⟨entry_wf (shape := []) (by simp) (by simp),
    entry_match (by intro i _ s hs; cases hs) (by intro r j hr; simp [entryState] at hr) (by simp),
    ro_of F hk.1.2.2.1, hpc⟩

theorem cut_94 : CutOK (plan hsha).toPlan c94 := by
  rintro g m ⟨hk, hpc, h18, -⟩
  have F := PreFacts.of hk.1.1.2
  have h2 := hk.1.2.2.2.2.1
  have h8 := hk.2.2.1
  obtain ⟨hwf, hm⟩ := frame_wf_match (ov := ov94) hk (by
    intro i _ s hs
    unfold ov94 at hs
    split at hs
    · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                simp [Sym.eval, Env.base, entryEnv, regsF]
    · split at hs
      · next h => cases hs; have : i = 8 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, regsF, h8, h2, fb, BitVec.sub_add_cancel]
      · split at hs
        · next h => cases hs; have : i = 18 := Fin.ext h; subst this
                    simp [Sym.eval, Env.base, entryEnv, regsF, h18, h2]
        · cases hs)
  exact ⟨hwf, hm, ro_of F hk.1.2.2.1, hpc⟩

theorem cut_C (k : Nat) : CutOK (plan hsha).toPlan (ccK k) := by
  rintro g m ⟨hk, hpc, h20, -⟩
  have F := PreFacts.of hk.1.1.2
  have h2 := hk.1.2.2.2.2.1
  have h8 := hk.2.2.1
  obtain ⟨hwf, hm⟩ := frame_wf_match (ov := ovC k) hk (by
    intro i _ s hs
    unfold ovC at hs
    split at hs
    · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                simp [Sym.eval, Env.base, entryEnv, regsF]
    · split at hs
      · next h => cases hs; have : i = 8 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, regsF, h8, h2, fb, BitVec.sub_add_cancel]
      · split at hs
        · next h => cases hs; have : i = 20 := Fin.ext h; subst this
                    simp [Sym.eval, h20]
        · cases hs)
  exact ⟨hwf, hm, ro_of F hk.1.2.2.1, hpc⟩

theorem zeroChunk_ro : ∀ j < 32, zesuImage.rodataByte? (0x801154c0 + j) = some 0 := by
  decide +kernel

theorem cut_54 : CutOK (plan hsha).toPlan c54 := by
  rintro g m ⟨⟨hpre, -, hp, -, h2, h9, -⟩, hpc, -, hsrc⟩
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have hfb := fb_toNat F
  have hro := ro_of F hp
  have hsv : (m.reg 2 + BitVec.ofNat 64 0xe8).toNat = (g.reg 2).toNat - 0x120 + 0xe8 := by
    rw [h2, toNat_add_ofNat (by simp [Layout.ramHi] at hhi; omega), hfb]
  have h9' : m.reg 9 = outOf g := h9
  have hs18 : ((m.reg 18).toNat = (g.reg 2).toNat - 0x120 + 8 ∨
      (m.reg 18).toNat = (g.reg 2).toNat - 0x120 + 0x88) ∨ m.reg 18 = 0x801154c0 := by
    rcases hsrc with h | h | h
    · left; left; rw [h, fb_add F, toNat_ofNat_lt (by simp [Layout.ramHi] at hhi; omega)]
    · left; right; rw [h, fb_add F, toNat_ofNat_lt (by simp [Layout.ramHi] at hhi; omega)]
    · right; exact h
  have hO := F.dSO; have hoL := F.outLo; have hoH := F.outHi
  refine ⟨entry_wf (shape := [((m.reg 2 + BitVec.ofNat 64 0xe8, 0x38), svR),
      ((m.reg 18, 32), srcR), ((m.reg 9, 32), outW)]) ?_ ?_, entry_match ?_ ?_ (by simp), hro, hpc⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · refine ⟨fun s hs => by simp [svR] at hs; omega, by simp [svR, Nat.mod_one], ?_⟩
      simp only [svR, Bool.false_eq_true, if_false, readable, inRange, hsv, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq]
      right; simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
    · refine ⟨fun s hs => by simp [srcR] at hs; omega, by simp [srcR, Nat.mod_one], ?_⟩
      simp only [srcR, Bool.false_eq_true, if_false, readable, inRange, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq]
      rcases hs18 with (h | h) | h
      · right; rw [h]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
      · right; rw [h]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
      · left; left; rw [h]; decide
    · refine ⟨fun s hs => by simp [outW] at hs; omega, by simp [outW, Nat.mod_one], ?_⟩
      simp only [outW, if_true, writable, inRange, h9', Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hoL, hoH⟩
  · simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
      Disjoint, hsv, h9']
    rcases hs18 with (h | h) | h
    · rw [h]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi hoL ⊢; omega
    · rw [h]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi hoL ⊢; omega
    · rw [h]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi hoL ⊢; omega
  · intro i _ s hs
    unfold ov54 at hs
    split at hs
    · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                simp only [Sym.eval, Env.base, entryEnv, regs54, List.getD_cons_zero]
                rw [BitVec.add_assoc]; simp
    · split at hs
      · next h => cases hs; have : i = 18 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, regs54]
      · split at hs
        · next h => cases hs; have : i = 9 := Fin.ext h; subst this
                    simp [Sym.eval, Env.base, entryEnv, regs54]
        · cases hs
  · intro r j hr hj
    simp only [entryState, List.length_cons, List.length_nil] at hr
    match r, hr with
    | 0, _ =>
      simp only [Env.size, entryEnv, regs54, List.getD_cons_zero] at hj
      simp only [Env.base, entryEnv, regs54, List.getD_cons_zero]
      rw [← ofNat_toNat_add, hsv]
      exact present_of hp (stack_present F (by omega) (by omega))
    | 1, _ =>
      simp only [Env.size, entryEnv, regs54, List.getD_cons_succ, List.getD_cons_zero] at hj
      simp only [Env.base, entryEnv, regs54, List.getD_cons_succ, List.getD_cons_zero]
      rw [← ofNat_toNat_add]
      rcases hs18 with (h | h) | h
      · rw [h]; exact present_of hp (stack_present F (by omega) (by omega))
      · rw [h]; exact present_of hp (stack_present F (by omega) (by omega))
      · rw [h]
        have := hro _ _ (zeroChunk_ro j hj)
        rw [show (BitVec.toNat (2148619456 : Word)) = 0x801154c0 from rfl, this]; rfl
    | 2, _ =>
      simp only [Env.size, entryEnv, regs54, List.getD_cons_succ, List.getD_cons_zero] at hj
      simp only [Env.base, entryEnv, regs54, List.getD_cons_succ, List.getD_cons_zero, h9']
      rw [← ofNat_toNat_add]
      exact present_of hp (present_get F.outP hj)

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Leaf helpers -/

/-- A saved word read back at `c54` (region 0 at `fb + 0xe8`). -/
theorem saved_init {g m : Machine} (hS : Saved g m) (h2 : m.reg 2 = fb g) {q o : Nat}
    (hq : q < 7) (ho : o = 8 * q) :
    (Sym.init 0 o 8).eval (entryEnv m (regs54 m)) = g.reg (savedReg q) := by
  subst ho
  simp only [Sym.eval]
  rw [show byteList ((entryEnv m (regs54 m)).byte0 0) (8 * q) 8 =
      byteList (byteOf (g.reg (savedReg q))) 0 8 from byteList_congr (fun t ht => ?_)]
  · exact ofBytesLE_bytes8 _
  · simp only [Env.byte0, entryEnv, regs54, List.getD_cons_zero, h2]
    rw [ofNat_add_ofNat, show 0xe8 + (8 * q + t) = 0xe8 + 8 * q + t by omega, hS q hq t ht]
    simp

/-- The writable regions of an entry state: an address in one lies in that region's range. -/
theorem inWritable_of {m : Machine} {regs : List (Word × Nat)} {ov : Nat → Option Sym}
    {rs : List Region} {a : Word} (h : InWritable (entryEnv m regs) (entryState ov rs []) a) :
    ∃ r R j, rs[r]? = some R ∧ R.writable = true ∧ j < (regs.getD r (0, 0)).2 ∧
      a = (regs.getD r (0, 0)).1 + BitVec.ofNat 64 j := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  exact ⟨r, R, j, hR, hw, hj, rfl⟩

theorem notOut_of_written {g : Machine} {a : Word} (F : PreFacts (sparseNeed g) g) {j : Nat}
    (hj : j < 32) (ha : a = outOf g + BitVec.ofNat 64 j) : WrittenN (sparseNeed g) g a := by
  have := F.outHi
  refine .inr (.inl ⟨?_, ?_⟩) <;> rw [ha, toNat_add_ofNat (by simp [Layout.ramHi] at this; omega)] <;>
    omega

theorem not_one_eq : (BitVec.ofNat 64 18446744073709551614 : Word) = ~~~1 := by decide

/-! ## Leaf at `c54`: the return -/

theorem leaf_54 : ∀ l ∈ run54_leaves, LeafGoalR (plan hsha) c54 l := by
  intro l hl
  have hL : run54_leaves = [run54_leaves[0]] := rfl
  rw [hL, List.mem_singleton] at hl; subst hl
  rintro g m ⟨⟨hpre, hso0, hp, hS, h2, h9, hkeep⟩, hpc, hroot, hsrc⟩ -
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have hfb := fb_toNat F
  have rlen : (sparseRoot (ch g) (depthOf g)).length = 32 :=
    sparseRoot_length _ _ chunksOf_mem_length
  have hra : (Sym.init 0 48 8).eval (entryEnv m (regs54 m)) = g.reg 1 :=
    saved_init hS h2 (q := 6) (by omega) rfl
  refine ⟨?_, Nat.le_refl 17, fun m' hm' he hso => ?_⟩
  · intro o ho
    have : run54_leaves[0].obligs =
      [.aligned (.bin .and (.init 0 48 8) (.lit 18446744073709551614)) 4] := rfl
    rw [this, List.mem_singleton] at ho; subst ho
    show (BinOp.eval .and ((Sym.init 0 48 8).eval (entryEnv m (regs54 m)))
      ((Sym.lit 18446744073709551614).eval (entryEnv m (regs54 m)))).toNat % 4 = 0
    rw [hra]; simp only [BinOp.eval, Sym.eval_lit, not_one_eq]; exact F.ra
  have hex : run54_leaves[0].exit = .ret (.bin .and (.init 0 48 8) (.lit 18446744073709551614)) := rfl
  rw [hex] at he ⊢
  left
  show SparsePost g m'
  have hreg : ∀ (i : Fin 32) (s : Sym), run54_leaves[0].S.reg i.val = s →
      m'.reg i = s.eval (entryEnv m (regs54 m)) := fun i s h => by rw [← hm'.regs i, h]; rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [ExitOk] at he
    rw [he]
    show BinOp.eval .and ((Sym.init 0 48 8).eval (entryEnv m (regs54 m)))
      ((Sym.lit 18446744073709551614).eval (entryEnv m (regs54 m))) = _
    rw [hra]; simp only [BinOp.eval, Sym.eval_lit, not_one_eq]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [hreg 2 (.ptr 0 0x38) rfl]
      simp only [Sym.eval, Env.base, entryEnv, regs54, List.getD_cons_zero, h2, fb]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]
      simp [Layout.ramLo, Layout.ramHi] at hlo hhi; omega
    · rw [hreg 8 (.init 0 40 8) rfl]; exact saved_init hS h2 (q := 5) (by omega) rfl
    · rw [hreg 9 (.init 0 32 8) rfl]; exact saved_init hS h2 (q := 4) (by omega) rfl
    · rw [hreg 18 (.init 0 24 8) rfl]; exact saved_init hS h2 (q := 3) (by omega) rfl
    · rw [hreg 19 (.init 0 16 8) rfl]; exact saved_init hS h2 (q := 2) (by omega) rfl
    · rw [hreg 20 (.init 0 8 8) rfl]; exact saved_init hS h2 (q := 1) (by omega) rfl
    · rw [hreg 21 (.init 0 0 8) rfl]; exact saved_init hS h2 (q := 0) (by omega) rfl
    all_goals
      first
      | (rw [hreg _ (.var _) rfl]; simp only [Sym.eval, entryEnv_vars]
         exact hkeep _ (by simp [keepRegs]))
  · have hs : ∀ j < 32, byteSrc run54_leaves[0].S.mem 2 j = some (1, j) := by decide
    intro i hi
    rw [rlen] at hi
    have hs := hs i hi
    have := mem_of_src hm' (r := 2) (by decide) (by simp [Env.size, entryEnv, regs54]; omega) hs
    simp only [regs54, List.getD_cons_succ, List.getD_cons_zero, h9] at this
    rw [this, hroot i (by rw [rlen]; exact hi)]; rfl
  · intro a ha
    rw [hso a fun hw => ?_, hso0 a ha]
    obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := inWritable_of hw
    match r, hR with
    | 0, hR => simp [S54, entryState, svR] at hR; subst hR; simp at hw
    | 1, hR => simp [S54, entryState, srcR] at hR; subst hR; simp at hw
    | 2, _ =>
      simp only [regs54, List.getD_cons_succ, List.getD_cons_zero] at hj
      exact ha (notOut_of_written F hj (by simp [regs54, h9]))
    | r + 3, hR => simp [S54, entryState] at hR

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## The `zkvm_sha256` call (after the right root is in the frame) -/

theorem fb_add_toNat {g : Machine} (F : PreFacts (sparseNeed g) g) {c : Nat} (hc : c ≤ 0x120) :
    (fb g + BitVec.ofNat 64 c).toNat = (g.reg 2).toNat - 0x120 + c := by
  have := F.spHi; have := F.spLo; have := need_ge g
  rw [toNat_add_ofNat (by rw [fb_toNat F]; simp [Layout.ramHi] at *; omega), fb_toNat F]

theorem present_iff {mem : Word → Option Byte} {a n : Nat} :
    present mem a n = true ↔ ∀ t < n, (mem (BitVec.ofNat 64 (a + t))).isSome :=
  ⟨fun h _ ht => present_get h ht, fun h => by simpa [present] using readBytes_isSome_of h⟩

theorem present_keep {m m' : Machine} (hp : Preserved m m') {a n : Nat}
    (h : present m.mem a n = true) : present m'.mem a n = true :=
  present_iff.mpr fun t ht => hp.1 _ (present_iff.mp h t ht)

theorem sha_exit {g m m' : Machine} (hk : Fr g m) {left right : List Byte}
    (hl : left.length = 32) (hr : right.length = 32)
    (hroot : sha2 left right = sparseRoot (ch g) (depthOf g))
    (r1 : m'.reg 1 = BitVec.ofNat 64 pc54) (r2 : m'.reg 2 = fb g) (r9 : m'.reg 9 = g.reg 10)
    (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0xa8) (r11 : m'.reg 11 = 64)
    (r12 : m'.reg 12 = fb g + BitVec.ofNat 64 0x88) (r18 : m'.reg 18 = fb g + BitVec.ofNat 64 0x88)
    (rk : ∀ i ∈ keepRegs, m'.reg i = g.reg i) (hpc : m'.pc.toNat = Sha256.entry)
    (hin : BytesAt m' (fb g + BitVec.ofNat 64 0xa8) (left ++ right)) (hS : Saved g m')
    (hso : SameOutside (InRange (fb g) 0x120) m m') (hp : Preserved m m') :
    ExitGoal (plan hsha).toPlan g m' (shaCost + 17) (.call Sha256.entry pc54) := by
  obtain ⟨⟨hpre, hso0, hp0, -, -, -, -⟩, hd1, -, -⟩ := hk
  have F := PreFacts.of hpre.2
  have hN : 0x120 * 2 + 0xe0 ≤ sparseNeed g := by
    unfold sparseNeed sparseStack Sha256.frameSize; omega
  have hlo := F.spLo; have hhi := F.spHi; have h16 := F.sp16
  have hfb := fb_toNat F
  have hp' : Preserved g m' := hp0.trans hp
  have hlo' : Layout.ramLo = 0xa0000000 := rfl
  have hhi' : Layout.ramHi = 0xc0000000 := rfl
  have hbump : Sha256.bump = 0xa05340b8 := rfl
  have hstage : Layout.extraParams = 0xa0000f00 := rfl
  have dSB := F.dSB; have dSS := F.dSS
  have ha8 := fb_add_toNat F (c := 0xa8) (by omega)
  have h88 := fb_add_toNat F (c := 0x88) (by omega)
  have hfs : Sha256.frameSize = 224 := rfl
  have hfr : (m'.reg 2 - BitVec.ofNat 64 224).toNat = (g.reg 2).toNat - 0x120 - 0xe0 := by
    rw [r2, BitVec.toNat_sub, hfb]; simp; omega
  have hlen : (left ++ right).length = 64 := by simp [hl, hr]
  refine ⟨shaC hsha, (), by simp [plan], hpc, ⟨⟨ro_of F hp', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [r2, hfb]; omega
  · rw [r2, hfb]; rw [hfs]; omega
  · rw [r2, hfb]; omega
  · intro j hj
    rw [r2]
    have : fb g - BitVec.ofNat 64 Sha256.frameSize + BitVec.ofNat 64 j =
        BitVec.ofNat 64 ((g.reg 2).toNat - 0x120 - 0xe0 + j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hfb, hfs]
      rw [hfs] at hj
      omega
    rw [this]
    exact hp'.1 _ (stack_present F (by rw [hfs] at hj; omega) (by rw [hfs] at hj; omega))
  · simp only [RetAligned, r1]; decide
  · right
    simp only [srcOk, Bool.and_eq_true, r10, r11, ha8]
    refine ⟨by simp [readable, inRange]; omega, ?_⟩
    have := readBytes_of_bytesAt hin
    rw [hlen, ha8] at this
    simp [present, this]
  · simp only [dstOk, Bool.and_eq_true, r12, h88]
    refine ⟨by simp [writable, inRange]; omega, present_iff.mpr fun t ht => ?_⟩
    exact hp'.1 _ (stack_present F (by omega) (by omega))
  · simp only [dstOk, Bool.and_eq_true]
    exact ⟨by decide, present_keep hp' F.bumpP⟩
  · simp only [dstOk, Bool.and_eq_true]
    exact ⟨by decide, present_keep hp' F.stageP⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, Disjoint, Sha256.frameR, Sha256.outR, Sha256.bumpR,
      Sha256.stageR, hfs, hfr, r12, h88]
    simp only [show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
      show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl,
      false_implies, implies_true, and_true]
    omega
  · right
    simp only [Disjoint, Sha256.inR, Sha256.frameR, Sha256.bumpR, Sha256.stageR, hfs, hfr, r10,
      r11, ha8, show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
      show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl,
      show (64 : Word).toNat = 64 from rfl]
    omega
  · rw [r11]; rfl
  · rintro m'' ⟨⟨⟨hpc'', hcs⟩, -, hout, -, hso2⟩, hp2⟩
    have hwr : ∀ a, ¬ WrittenN (sparseNeed g) g a → ¬ Sha256.Written m' a := by
      intro a ha hw
      apply ha
      rcases hw with h | h | h | h
      · simp only [InRange, Sha256.frameR, hfs, hfr] at h
        exact written_stack F (by omega) (by omega)
      · simp only [InRange, r12, h88] at h
        exact written_stack F (by omega) (by omega)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    refine ⟨c54, (by show c54 ∈ cuts; simp [cuts]), rfl, ?_,
      ⟨⟨hpre, ?_, hp'.trans hp2, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
      Nat.le_refl _⟩
    · rw [hpc'', r1]; rfl
    · intro a ha
      rw [hso2 a (hwr a ha), hso a fun h => ha (by
        simp only [InRange, hfb] at h; exact written_stack F (by omega) (by omega)), hso0 a ha]
    · intro q hq t ht
      rw [hso2 _ fun hw => ?_]
      · exact hS q hq t ht
      · rw [fb_add F] at hw
        have hx : (BitVec.ofNat 64 ((g.reg 2).toNat - 0x120 + (0xe8 + 8 * q + t))).toNat =
            (g.reg 2).toNat - 0x120 + (0xe8 + 8 * q + t) := toNat_ofNat_lt (by omega)
        rcases hw with h | h | h | h <;>
          simp only [InRange, Sha256.frameR, hfs, hfr, r12, h88, hx,
            show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
            show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl] at h <;>
          omega
    · rw [hcs 2 (by decide), r2]
    · rw [hcs 9 (by decide), r9]
    · intro i hi
      rw [hcs i (by simp [keepRegs, calleeSaved] at hi ⊢; omega), rk i hi]
    · rw [hpc'', r1]; rfl
    · rw [hcs 18 (by decide), r18, ← hroot]
      have hmsg : Sha256.msgOf m' = left ++ right := by
        simp only [Sha256.msgOf, r10, r11, show (64 : Word).toNat = 64 from rfl]
        have := readBytes_of_bytesAt hin
        rw [hlen] at this; rw [this]; rfl
      rw [← r12]; unfold sha2; rw [← hmsg]; exact hout
    · right; left; rw [hcs 18 (by decide), r18]

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Leaves of the frame cuts (`c94`, `ccK k`): the `zkvm_sha256` call -/

/-- What the call leaves of `c94` and `ccK k` look like (checked by `decide`). -/
abbrev CallShape (l : Leaf) : Prop :=
  l.exit = .call Sha256.entry pc54 ∧ l.conds = [] ∧ l.obligs = [] ∧ l.S.reg 1 = .lit pc54 ∧
  l.S.reg 2 = .ptr 0 0 ∧ l.S.reg 9 = .var 9 ∧ l.S.reg 10 = .ptr 0 0xa8 ∧ l.S.reg 11 = .lit 64 ∧
  l.S.reg 12 = .ptr 0 0x88 ∧ l.S.reg 18 = .ptr 0 0x88 ∧
  (∀ i ∈ [22, 23, 24, 25, 26, 27], l.S.reg i = .var i) ∧ l.S.regions.length = 1 ∧
  (∀ j < 32, byteSrc l.S.mem 0 (0xa8 + j) = some (0, 0x28 + j)) ∧
  (∀ j < 56, byteSrc l.S.mem 0 (0xe8 + j) = some (0, 0xe8 + j))

theorem fb_ofInt (g : Machine) (c : Nat) (hc : c < 2 ^ 63) :
    fb g + BitVec.ofInt 64 (c : Int) = fb g + BitVec.ofNat 64 c := by
  simp

/-- A byte of the frame after a leaf of a frame cut, from `byteSrc`. -/
theorem frame_src {g m m' : Machine} {S' : SState} (h2 : m.reg 2 = fb g)
    (hm' : Match (entryEnv m (regsF m)) S' m') (hl : S'.regions.length = 1) {j j' : Nat}
    (hj : j < 0x120) (hs : byteSrc S'.mem 0 j = some (0, j')) :
    m'.mem (fb g + BitVec.ofNat 64 j) = some ((m.mem (fb g + BitVec.ofNat 64 j')).getD 0) := by
  have := mem_of_src hm' (r := 0) (by omega) (by simp [Env.size, entryEnv, regsF]; exact hj) hs
  simpa [regsF, h2] using this

theorem frame_lit {g m m' : Machine} {S' : SState} (h2 : m.reg 2 = fb g)
    (hm' : Match (entryEnv m (regsF m)) S' m') (hl : S'.regions.length = 1) {j : Nat} {b : Byte}
    (hj : j < 0x120) (hs : byteLit S'.mem 0 j = some b) :
    m'.mem (fb g + BitVec.ofNat 64 j) = some b := by
  have := mem_of_lit hm' (r := 0) (by omega) (by simp [Env.size, entryEnv, regsF]; exact hj) hs
  simpa [regsF, h2] using this

theorem bytesAt_add {m : Machine} {a : Word} {c : Nat} {bs : List Byte}
    (h : ∀ i < bs.length, m.mem (a + BitVec.ofNat 64 (c + i)) = some (bs.getD i 0)) :
    BytesAt m (a + BitVec.ofNat 64 c) bs := by
  intro i hi
  rw [ofNat_add_ofNat, h i hi]; simp [List.getD_eq_getElem?_getD, hi]

theorem frame_call_leaf {g m : Machine} {ov : Nat → Option Sym} {l : Leaf} {right : List Byte}
    (hk : Fr g m) (hwf : Env.WF (entryEnv m (regsF m)) (entryState ov [frR] []))
    (hsh : CallShape l) (hrl : right.length = 32)
    (hroot : sha2 (leftRoot g) right = sparseRoot (ch g) (depthOf g))
    (hleft : BytesAt m (fb g + BitVec.ofNat 64 0x28) (leftRoot g))
    (hright : ∀ m', Match (entryEnv m (regsF m)) l.S m' →
      BytesAt m' (fb g + BitVec.ofNat 64 0xc8) right) :
    ∀ m', Match (entryEnv m (regsF m)) l.S m' → ExitOk (entryEnv m (regsF m)) l.exit m' →
      SameOutside (InWritable (entryEnv m (regsF m)) (entryState ov [frR] [])) m m' →
      ExitGoal (plan hsha).toPlan g m' (shaCost + 17) l.exit := by
  intro m' hm' he hso
  obtain ⟨hex, -, -, s1, s2, s9, s10, s11, s12, s18, sk, hreg, ha8, hsv⟩ := hsh
  have h2 := hk.1.2.2.2.2.1
  have hkeep := hk.1.2.2.2.2.2.2
  have hS := hk.1.2.2.2.1
  have F := PreFacts.of hk.1.1.2
  have hll : (leftRoot g).length = 32 := sparseRoot_length _ _ chunksOf_take_mem
  have hr : ∀ (i : Fin 32) (s : Sym), l.S.reg i.val = s → m'.reg i = s.eval (entryEnv m (regsF m)) :=
    fun i s h => by rw [← hm'.regs i, h]
  have hb0 : (entryEnv m (regsF m)).base 0 = fb g := by simp [Env.base, entryEnv, regsF, h2]
  rw [hex] at he ⊢
  refine sha_exit (hsha := hsha) hk hll hrl hroot ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he ?_ ?_ ?_ ?_
  · rw [hr 1 _ s1]; rfl
  · rw [hr 2 _ s2]; simp [Sym.eval, hb0]
  · rw [hr 9 _ s9]; exact hk.1.2.2.2.2.2.1
  · rw [hr 10 _ s10, Sym.eval_ptr, hb0]; exact fb_ofInt g 0xa8 (by omega)
  · rw [hr 11 _ s11]; rfl
  · rw [hr 12 _ s12, Sym.eval_ptr, hb0]; exact fb_ofInt g 0x88 (by omega)
  · rw [hr 18 _ s18, Sym.eval_ptr, hb0]; exact fb_ofInt g 0x88 (by omega)
  · intro i hi
    have hi' : i.val ∈ [22, 23, 24, 25, 26, 27] := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hr i _ (sk i.val hi'), Sym.eval_var, entryEnv_var]; exact hkeep i hi
  · have hrr := hright m' hm'
    apply bytesAt_add
    intro i hi
    simp only [List.length_append, hll, hrl] at hi
    by_cases h32 : i < 32
    · rw [frame_src h2 hm' hreg (by omega) (ha8 i h32), ← ofNat_add_ofNat,
        hleft i (by rw [hll]; exact h32)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega)]
    · have := hrr (i - 32) (by rw [hrl]; omega)
      rw [ofNat_add_ofNat, show 0xc8 + (i - 32) = 0xa8 + i by omega] at this
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hll,
        List.getElem?_eq_getElem (by omega)]
      rfl
  · intro q hq t ht
    rw [frame_src h2 hm' hreg (by omega) (show byteSrc l.S.mem 0 (0xe8 + 8 * q + t) = _ by
      rw [show 0xe8 + 8 * q + t = 0xe8 + (8 * q + t) by omega]; exact hsv _ (by omega)),
      show 0xe8 + (8 * q + t) = 0xe8 + 8 * q + t by omega, hS q hq t ht]
    rfl
  · intro a ha
    apply hso a
    intro hw
    obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := inWritable_of hw
    match r, hR with
    | 0, _ =>
      simp only [regsF, List.getD_cons_zero, h2] at hj ha
      apply ha
      have hfb := fb_toNat F; have := F.spHi; have := F.spLo; have := need_ge g
      refine ⟨?_, ?_⟩ <;> rw [toNat_add_ofNat (by rw [hfb]; simp [Layout.ramHi] at *; omega)] <;> omega
    | r + 1, hR => simp [entryState] at hR
  · exact preserved_of_leaf hwf hm' (by simp [entryState, hreg]) hso

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

theorem root_split {g : Machine} (hd : 1 ≤ depthOf g) :
    sparseRoot (ch g) (depthOf g) =
      sha2 (leftRoot g) (if lenOf g ≤ half g then zeroHash (depthOf g - 1) else rightRoot g) := by
  obtain ⟨d, hd'⟩ : ∃ d, depthOf g = d + 1 := ⟨depthOf g - 1, by omega⟩
  simp only [leftRoot, rightRoot, half, hd', Nat.add_sub_cancel]
  rw [sparseRoot_succ, chunksOf_length]

theorem leaf94_facts : ∀ l ∈ run94_leaves, CallShape l ∧ l.S.steps = 23 ∧
    ∀ j < 32, byteSrc l.S.mem 0 (0xc8 + j) = some (0, 0x68 + j) := by decide

theorem leaf_94 : ∀ l ∈ run94_leaves, LeafGoalR (plan hsha) c94 l := by
  intro l hl
  obtain ⟨hsh, hst, hrt⟩ := leaf94_facts l hl
  intro g m hA _
  have hcut := cut_94 hsha g m hA
  obtain ⟨hk, -, -, hlt, hleft, hright⟩ := hA
  have h2 := hk.1.2.2.2.2.1
  refine ⟨by rw [hsh.2.2.1]; simp, by simp [c94, S94, entryState, hst, shaCost],
    fun m' hm' he hso => ?_⟩
  left
  have hrem : c94.budget g m - (l.S.steps - c94.S.steps) = shaCost + 17 := by
    simp [c94, S94, entryState, hst, shaCost]
  rw [hrem]
  refine frame_call_leaf (hsha := hsha) (right := rightRoot g) hk hcut.1 hsh
    (sparseRoot_length _ _ chunksOf_drop_mem) ?_ hleft ?_ m' hm' he hso
  · rw [root_split hk.2.1, if_neg (by omega)]
  · intro m₁ hm₁
    have hrl : (rightRoot g).length = 32 := sparseRoot_length _ _ chunksOf_drop_mem
    apply bytesAt_add
    intro i hi
    rw [hrl] at hi
    rw [frame_src h2 hm₁ hsh.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (hrt i hi), ← ofNat_add_ofNat,
      hright i (by rw [hrl]; exact hi)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hrl]; exact hi)]

theorem leafC_facts : ∀ k ∈ List.range 26, ∀ l ∈ lvC.getD k [], CallShape l ∧ l.S.steps = 36 ∧
    ∀ j < 32, byteLit l.S.mem 0 (0xc8 + j) = some ((tableEntry k).getD j 0) := by
  decide +kernel

theorem leaf_C (k : Nat) (hk26 : k < 26) : ∀ l ∈ lvC.getD k [], LeafGoalR (plan hsha) (ccK k) l := by
  intro l hl
  obtain ⟨hsh, hst, hrt⟩ := leafC_facts k (List.mem_range.mpr hk26) l hl
  intro g m hA _
  have hcut := cut_C hsha k g m hA
  obtain ⟨hk, -, -, hdk, hle, hleft⟩ := hA
  have h2 := hk.1.2.2.2.2.1
  have hzl : (tableEntry k).length = 32 := by simp [tableEntry]
  refine ⟨by rw [hsh.2.2.1]; simp, by simp [ccK, SC, entryState, hst, shaCost],
    fun m' hm' he hso => ?_⟩
  left
  have hrem : (ccK k).budget g m - (l.S.steps - (ccK k).S.steps) = shaCost + 17 := by
    simp [ccK, SC, entryState, hst, shaCost]
  rw [hrem]
  refine frame_call_leaf (hsha := hsha) (right := tableEntry k) hk hcut.1 hsh hzl ?_ hleft ?_
    m' hm' he hso
  · rw [root_split hk.2.1, if_pos hle, hdk, Nat.add_sub_cancel, zeroHash_eq_table k hk26]
  · intro m₁ hm₁
    apply bytesAt_add
    intro i hi
    rw [hzl] at hi
    exact frame_lit h2 hm₁ hsh.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (hrt i hi)

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Word facts for the entry leaves -/

theorem and255_toNat (x : Word) : (x &&& BitVec.ofNat 64 255).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and]
  have : (BitVec.ofNat 64 255).toNat = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem dec_toNat {x : Word} (h : 1 ≤ x.toNat) : (x + BitVec.ofNat 64 18446744073709551615).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_add]; simp; omega

theorem dec_eq (x : Word) : x + BitVec.ofNat 64 18446744073709551615 = x - 1 := by
  bv_omega

theorem shl_toNat {k : Nat} (hk : k < 64) : ((1 : Word) <<< k).toNat = 2 ^ k := by
  rw [BitVec.toNat_shiftLeft]
  simp only [show (1 : Word).toNat = 1 from rfl, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)

/-- The depth from the entry conditions: `a3 & 0xff` is zero exactly at depth 0 (depth ≤ 26). -/
theorem depth_zero_iff {g : Machine} (h : depthOf g ≤ 26) :
    (g.reg 13 &&& BitVec.ofNat 64 255 == BitVec.ofNat 64 0) = true ↔ depthOf g = 0 := by
  constructor
  · intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [and255_toNat] at this; simp at this; simp only [depthOf] at h ⊢; omega
  · intro hd
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [and255_toNat]; simp only [depthOf] at hd; simp [hd]

/-! ## Entry leaves: what they keep -/

/-- `s5, s4, s3, s2, s1, s0, ra` stored at `0xe8 + 8 q` of the frame region. -/
abbrev ESaved (l : Leaf) : Prop :=
  ∀ q < 7, ∀ t < 8, byteVal l.S.mem 0 (0xe8 + 8 * q + t) = some (.var (savedReg q).val, t)

abbrev EShape (l : Leaf) : Prop :=
  l.S.reg 2 = .ptr 0 0 ∧ l.S.reg 8 = .ptr 0 0x120 ∧ l.S.reg 9 = .var 10 ∧
  l.S.reg 19 = .var 12 ∧ (∀ i ∈ [22, 23, 24, 25, 26, 27], l.S.reg i = .var i) ∧
  l.S.regions.length = 2 ∧ ESaved l

theorem entry_keep {g m' : Machine} {l : Leaf} (hpre : SparsePre g)
    (hwf : Env.WF (entryEnv g (regsE g)) SE) (hm' : Match (entryEnv g (regsE g)) l.S m')
    (hso : SameOutside (InWritable (entryEnv g (regsE g)) SE) g m') (hsh : EShape l) :
    Keep g m' ∧ m'.reg 8 = g.reg 2 ∧ m'.reg 19 = g.reg 12 := by
  obtain ⟨s2, s8, s9, s19, sk, hreg, hsv⟩ := hsh
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have hb0 : (entryEnv g (regsE g)).base 0 = fb g := by simp [Env.base, entryEnv, regsE, fb]
  have hr : ∀ (i : Fin 32) (s : Sym), l.S.reg i.val = s → m'.reg i = s.eval (entryEnv g (regsE g)) :=
    fun i s h => by rw [← hm'.regs i, h]
  refine ⟨⟨hpre, ?_, preserved_of_leaf hwf hm' (by simp [SE, entryState, hreg]) hso, ?_, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · intro a ha
    apply hso a
    intro hw
    obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := inWritable_of hw
    rcases r with _ | _ | r
    · simp only [regsE, List.getD_cons_zero] at hj ha
      have hfbd : g.reg 2 - BitVec.ofNat 64 0x120 = fb g := rfl
      rw [hfbd] at ha
      apply ha
      have e := fb_add_toNat F (c := j) (by omega)
      exact written_stack F (by rw [e]; omega) (by rw [e]; omega)
    · simp [entryState, lvR] at hR; subst hR; simp at hw
    · simp [entryState] at hR
  · intro q hq t ht
    have := mem_of_val hm' (r := 0) (by omega) (by simp [Env.size, entryEnv, regsE]; omega)
      (hsv q hq t ht)
    simp only [regsE, List.getD_cons_zero] at this
    rw [show fb g = g.reg 2 - BitVec.ofNat 64 0x120 from rfl, this]
    simp [Sym.eval, entryEnv_vars]
  · rw [hr 2 _ s2]; simp [Sym.eval, hb0]
  · rw [hr 9 _ s9]; simp [Sym.eval]; rfl
  · intro i hi
    have hi' : i.val ∈ [22, 23, 24, 25, 26, 27] := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hr i _ (sk i.val hi'), Sym.eval_var, entryEnv_var]
  · rw [hr 8 _ s8, Sym.eval_ptr, hb0]
    exact (fb_ofInt g 0x120 (by omega)).trans (by simp [fb, BitVec.sub_add_cancel])
  · rw [hr 19 _ s19]; simp [Sym.eval]; rfl

end ZesuExec.Fn.SszRoot.Sparse

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Recursive calls: the callee's precondition, and what the caller keeps -/

theorem readable_sub {a n a' n' : Nat} (h : readable a n = true) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) :
    readable a' n' = true := by
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

theorem need_pred {g m' : Machine} (hd : 1 ≤ depthOf g) (r13 : depthOf m' = depthOf g - 1) :
    sparseNeed m' + 0x120 = sparseNeed g := by
  unfold sparseNeed sparseStack; rw [r13]
  obtain ⟨k, hk⟩ : ∃ k, depthOf g = k + 1 := ⟨depthOf g - 1, by omega⟩
  rw [hk]; simp; omega

theorem chunk_toNat {g : Machine} (F : PreFacts (sparseNeed g) g) {x : Nat} (hx : x ≤ 32 * lenOf g) :
    (chunkPtr g + BitVec.ofNat 64 x).toNat = (chunkPtr g).toNat + x := by
  have := F.chR
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact toNat_add_ofNat (by simp [Layout.rodataHi, Layout.inputHi, Layout.ramHi] at this; omega)

set_option maxHeartbeats 400000 in
attribute [local irreducible] sparseNeed in
theorem callee_pre {g m' : Machine} (hpre : SparsePre g) (hp : Preserved g m') (hd : 1 ≤ depthOf g)
    {o s n' : Nat} (r2 : m'.reg 2 = fb g) (hra : RetAligned m')
    (r13 : depthOf m' = depthOf g - 1) (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 o)
    (ho : o + 32 ≤ 0x120) (r11 : m'.reg 11 = chunkPtr g + BitVec.ofNat 64 (32 * s))
    (r12 : lenOf m' = n') (hsn : s + n' ≤ lenOf g) : SparsePre m' := by
  have F := PreFacts.of hpre.2
  have hN := need_pred hd r13
  have hlo := F.spLo; have hhi := F.spHi; have h16 := F.sp16
  have hfb := fb_toNat F
  have hlo' : Layout.ramLo = 0xa0000000 := rfl
  have hhi' : Layout.ramHi = 0xc0000000 := rfl
  have hbump : Sha256.bump = 0xa05340b8 := rfl
  have hstage : Layout.extraParams = 0xa0000f00 := rfl
  have hc : (m'.reg 11).toNat = (chunkPtr g).toNat + 32 * s := by
    rw [r11]; exact chunk_toNat F (by omega)
  have hout : (m'.reg 10).toNat = (g.reg 2).toNat - 0x120 + o := by
    rw [r10]; exact fb_add_toNat F (by omega)
  have hst : (m'.reg 2 - BitVec.ofNat 64 (sparseNeed m')).toNat = (g.reg 2).toNat - sparseNeed g := by
    rw [r2, BitVec.toNat_sub, hfb]; simp [Layout.ramLo] at hlo ⊢; omega
  have hlen : 32 * lenOf m' = 32 * n' := by rw [r12]
  refine ⟨by rw [r13]; have := hpre.1; omega, ro_of F hp, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r2, hfb]; omega
  · rw [r2, hfb]; generalize sparseNeed m' = N' at hN ⊢; omega
  · rw [r2, hfb]; omega
  · intro j hj
    have : m'.reg 2 - BitVec.ofNat 64 (sparseNeed m') + BitVec.ofNat 64 j =
        BitVec.ofNat 64 ((g.reg 2).toNat - sparseNeed g + j) := by
      rw [← hst, ofNat_toNat_add]
    rw [this]; exact hp.1 _ (stack_present F (by omega) (by omega))
  · exact hra
  · simp only [srcOk, Bool.and_eq_true, chunkPtr, hc, hlen]
    refine ⟨readable_sub F.chR (by simp only [chunkPtr]; omega) (by simp only [chunkPtr]; omega),
      present_iff.mpr fun t ht => ?_⟩
    rw [show (chunkPtr g).toNat + 32 * s + t = (chunkPtr g).toNat + (32 * s + t) by omega]
    exact hp.1 _ (present_get F.chP (by omega))
  · simp only [dstOk, Bool.and_eq_true, outOf, hout]
    refine ⟨?_, present_iff.mpr fun t ht => ?_⟩
    · simp only [writable, inRange, Bool.and_eq_true, decide_eq_true_eq]
      simp only [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
    exact hp.1 _ (stack_present F (by omega) (by omega))
  · simp only [dstOk, Bool.and_eq_true]; exact ⟨by decide, present_keep hp F.bumpP⟩
  · simp only [dstOk, Bool.and_eq_true]; exact ⟨by decide, present_keep hp F.stageP⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, Disjoint, outR, chunkR, Sha256.bumpR, Sha256.stageR,
      hst, outOf, chunkPtr, hout, hc, hlen,
      show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
      show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl,
      false_implies, implies_true]
    have dSB := F.dSB; have dSS := F.dSS; have dSC := F.dSC; have dBC := F.dBC; have dTC := F.dTC
    simp only [chunkPtr] at dSC dBC dTC
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · omega
    · clear dSS dSC dBC dTC; omega
    · clear dSB dSC dBC dTC; omega
    · clear dSB dSS dBC dTC; omega
    · clear dSS dSC dBC dTC; omega
    · clear dSB dSC dBC dTC; omega
    · clear dSB dSS dBC dTC; omega
    · clear dSB dSS dSC dBC dTC; omega
    · clear dSB dSS dSC dTC; omega
    · clear dSB dSS dSC dBC; omega

/-- After a recursive call whose result goes to `fb + o`: memory outside the caller's written
memory and the frame bytes outside the result are kept. -/
theorem after_self {g m' m'' : Machine} (hpre : SparsePre g) (hd : 1 ≤ depthOf g)
    (hso : SameOutside (WrittenN (sparseNeed g) g) g m') {o : Nat}
    (r2 : m'.reg 2 = fb g) (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 o) (ho : o + 32 ≤ 0x120)
    (r13 : depthOf m' = depthOf g - 1)
    (hso2 : SameOutside (WrittenN (sparseNeed m') m') m' m'') :
    SameOutside (WrittenN (sparseNeed g) g) g m'' ∧
      ∀ a : Word, (g.reg 2).toNat - 0x120 ≤ a.toNat → a.toNat < (g.reg 2).toNat →
        ¬ ((g.reg 2).toNat - 0x120 + o ≤ a.toNat ∧ a.toNat < (g.reg 2).toNat - 0x120 + o + 32) →
        m''.mem a = m'.mem a := by
  have F := PreFacts.of hpre.2
  have hN := need_pred hd r13
  have hlo := F.spLo; have hhi := F.spHi
  have hfb := fb_toNat F
  have hout : (m'.reg 10).toNat = (g.reg 2).toNat - 0x120 + o := by
    rw [r10]; exact fb_add_toNat F (by omega)
  have hst : (m'.reg 2 - BitVec.ofNat 64 (sparseNeed m')).toNat = (g.reg 2).toNat - sparseNeed g := by
    rw [r2, BitVec.toNat_sub, hfb]; simp [Layout.ramLo] at hlo ⊢; omega
  have hw : ∀ a, WrittenN (sparseNeed m') m' a →
      WrittenN (sparseNeed g) g a ∧ ((g.reg 2).toNat - 0x120 ≤ a.toNat → a.toNat < (g.reg 2).toNat →
        (g.reg 2).toNat - 0x120 + o ≤ a.toNat ∧ a.toNat < (g.reg 2).toNat - 0x120 + o + 32) := by
    intro a h
    rcases h with h | h | h | h
    · simp only [InRange, hst] at h
      exact ⟨written_stack F (by omega) (by omega), fun h1 h2 => by omega⟩
    · simp only [InRange, outOf, hout] at h
      exact ⟨written_stack F (by omega) (by omega), fun _ _ => h⟩
    · refine ⟨.inr (.inr (.inl h)), fun h1 h2 => ?_⟩
      have := F.dSB; simp only [InRange, show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl] at h
      omega
    · refine ⟨.inr (.inr (.inr h)), fun h1 h2 => ?_⟩
      have := F.dSS
      simp only [InRange, show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl] at h
      omega
  refine ⟨fun a ha => ?_, fun a h1 h2 h3 => hso2 a fun h => h3 ((hw a h).2 h1 h2)⟩
  rw [hso2 a fun h => ha (hw a h).1, hso a ha]

/-- The chunks a caller hands to a recursive call are unchanged since the entry. -/
theorem chunks_same {g m' : Machine} (hpre : SparsePre g)
    (hso : SameOutside (WrittenN (sparseNeed g) g) g m') {s n' : Nat} (hsn : s + n' ≤ lenOf g) :
    chunksOf m' (chunkPtr g + BitVec.ofNat 64 (32 * s)) n' =
      chunksOf g (chunkPtr g + BitVec.ofNat 64 (32 * s)) n' := by
  have F := PreFacts.of hpre.2
  apply chunksOf_congr
  intro i hi j hj
  apply hso
  rw [ofNat_add_ofNat]
  have e := chunk_toNat F (x := 32 * s + (32 * i + j)) (by omega)
  have dSC := F.dSC; have dOC := F.dOC; have dBC := F.dBC; have dTC := F.dTC
  have hlo := F.spLo
  simp only [chunkPtr, outOf] at e dSC dOC dBC dTC
  rintro (h | h | h | h) <;>
    simp only [InRange, outOf, show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
      show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl, e] at h
  · rw [BitVec.toNat_sub] at h; simp [Layout.ramLo] at hlo h; omega
  · omega
  · omega
  · omega

end ZesuExec.Fn.SszRoot.Sparse
