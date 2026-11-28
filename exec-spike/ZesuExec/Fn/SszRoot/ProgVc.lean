import ZesuExec.Fn.SszRoot.ProgDefs
import ZesuExec.Fn.SszRoot.Lemmas
import ZesuExec.Vc.SoundRec

/-!
# `progressiveRootAt`: assertions, plan, cut lemmas

`σ` is the entry machine `g`. `fb g = sp - 0xa0` is the frame, `pw g = 2 ^ depth`, `sz g = min
pw len` the chunks `sparseRoot` takes. `Keep g m`: `Pre g`, `len ≠ 0`; memory changed only in
`WrittenN` and every present byte kept; `s5, s4, s3, s2, s1, s0, ra` saved at `fb + 0x68 + 8 q`;
`sp = fb`, `s0 = sp₀`, `s1` the result pointer, `s6`–`s11` the entry values. Assertions: after
`sparseRoot` (`AS`: its root at `fb + 0x28`, `s2 = len`, `s3 = sz`, `s4` the chunks, `s5` the
depth), after the recursive call (`AR`: both roots), after `zkvm_sha256` (`AH`: the root at
`fb + 8`). Budgets: `progCost` at the entry, then what is left of it.

`sparseRoot` enters as the hypothesis `SparseSpec` (`SparseProof.lean`: `sparseRoot_spec`), a
`CalleeD` whose budget is `sparseCost depth sz`.
-/

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-- The `sparseRoot` contract (`Sparse.sparseRoot_spec`), per depth and length. -/
def SparseSpec : Prop :=
  ∀ d n, Spec zesuImage sparseEntry (sparseCost d n)
    (fun m => SparsePre m ∧ depthOf m = d ∧ lenOf m = n) SparsePost

/-! ## Entry-machine quantities -/

def fb (g : Machine) : Word := g.reg 2 - BitVec.ofNat 64 0xa0
abbrev ch (g : Machine) : List (List Byte) := chunksOf g (chunkPtr g) (lenOf g)
abbrev pw (g : Machine) : Nat := 2 ^ depthOf g
def sz (g : Machine) : Nat := min (pw g) (lenOf g)
def leftRoot (g : Machine) : List Byte := sparseRoot ((ch g).take (pw g)) (depthOf g)
def restRoot (g : Machine) : List Byte := progressiveRootAt ((ch g).drop (pw g)) (depthOf g + 2)

/-- `s5, s4, s3, s2, s1, s0, ra`: saved at `fb + 0x68 + 8 q`. -/
def savedReg (q : Nat) : Fin 32 := [21, 20, 19, 18, 9, 8, 1].getD q 0

def Saved (g m : Machine) : Prop :=
  ∀ q < 7, ∀ t < 8,
    m.mem (fb g + BitVec.ofNat 64 (0x68 + 8 * q + t)) = some (byteOf (g.reg (savedReg q)) t)

def keepRegs : List (Fin 32) := [22, 23, 24, 25, 26, 27]

def Keep (g m : Machine) : Prop :=
  ProgPre g ∧ lenOf g ≠ 0 ∧ SameOutside (WrittenN (progNeed g) g) g m ∧ Preserved g m ∧
  Saved g m ∧ m.reg 2 = fb g ∧ m.reg 8 = g.reg 2 ∧ m.reg 9 = g.reg 10 ∧
  ∀ i ∈ keepRegs, m.reg i = g.reg i

def AE (g m : Machine) : Prop := m = g ∧ m.pc.toNat = progEntry ∧ ProgPre m

def AS (g m : Machine) : Prop :=
  Keep g m ∧ m.pc.toNat = pcS ∧ m.reg 18 = g.reg 12 ∧ m.reg 19 = BitVec.ofNat 64 (sz g) ∧
  m.reg 20 = g.reg 11 ∧ m.reg 21 = g.reg 13 ∧ BytesAt m (fb g + BitVec.ofNat 64 0x28) (leftRoot g)

def AR (g m : Machine) : Prop :=
  Keep g m ∧ m.pc.toNat = pcR ∧ BytesAt m (fb g + BitVec.ofNat 64 0x28) (leftRoot g) ∧
  BytesAt m (fb g + BitVec.ofNat 64 0x48) (restRoot g)

def AH (g m : Machine) : Prop :=
  Keep g m ∧ m.pc.toNat = pcH ∧
  BytesAt m (fb g + BitVec.ofNat 64 8) (progressiveRootAt (ch g) (depthOf g))

/-! ## Budgets, cuts, plan -/

def restS (g : Machine) : Nat := 7 + progCost (lenOf g - pw g) (depthOf g + 2) + 5 + shaCost + 18

def cE : Cut Machine :=
  ⟨progEntry, SE, AE, fun _ m => entryEnv m (regsE m), fun g _ => progCost (lenOf g) (depthOf g)⟩
def cS : Cut Machine := ⟨pcS, S0, AS, fun _ m => entryEnv m [], fun g _ => restS g⟩
def cR : Cut Machine := ⟨pcR, S0, AR, fun _ m => entryEnv m [], fun _ _ => 5 + shaCost + 18⟩
def cH : Cut Machine := ⟨pcH, SH, AH, fun _ m => entryEnv m (regsH m), fun _ _ => 18⟩

def cuts : List (Cut Machine) := [cE, cS, cR, cH]

def leaves (i : Nat) : List Leaf :=
  if i = 0 then runE_leaves else if i = 1 then runS_leaves else if i = 2 then runR_leaves
  else if i = 3 then runH_leaves else []

/-- `zkvm_sha256` on 64 bytes, its result with `Preserved`. -/
def shaC (hsha : ShaSpec) : Callee Machine zesuImage where
  entry := Sha256.entry
  bound := shaCost
  Pre := fun _ _ m => Sha256.Pre m ∧ (m.reg 11).toNat = 64
  Post := fun _ _ m m' => Sha256.Post m m' ∧ Preserved m m'
  spec := fun _ _ m hpc hpre => Reaches.preserve (hsha m hpc hpre)

/-- `sparseRoot` on the first `sz g` chunks at the caller's depth. -/
def sparseD (hsp : SparseSpec) : CalleeD Machine zesuImage where
  entry := sparseEntry
  bound := fun g _ => sparseCost (depthOf g) (sz g)
  Pre := fun g _ m => SparsePre m ∧ depthOf m = depthOf g ∧ lenOf m = sz g
  Post := fun _ _ m m' => SparsePost m m'
  spec := fun g _ => hsp (depthOf g) (sz g)

def plan (hsha : ShaSpec) (hsp : SparseSpec) : PlanR Machine zesuImage where
  cuts := cuts
  fuel := fuel
  leaves := leaves
  callee := fun r => if r = pcH then some (shaC hsha) else none
  dcallee := fun r => if r = pcS then some (sparseD hsp) else none
  Post := fun g => ProgPost g

theorem cuts_pcs : cuts.map (·.pc) = pcs := by decide

end ZesuExec.Fn.SszRoot.Prog

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## The model and the budgets on a nonempty list -/

theorem progStack_ge (n d : Nat) : 0xa0 ≤ progStack n d := by
  rw [progStack]; split <;> omega

theorem progStack_ne {n d : Nat} (h : n ≠ 0) :
    progStack n d = 0xa0 + max (sparseStack d) (progStack (n - 2 ^ d) (d + 2)) := by
  rw [progStack, if_neg h]

theorem progCost_ne {n d : Nat} (h : n ≠ 0) :
    progCost n d = 22 + sparseCost d (min n (2 ^ d)) + 7 + progCost (n - 2 ^ d) (d + 2) + 5 +
      shaCost + 18 := by
  rw [progCost, if_neg h]

theorem progFits_ne {n d : Nat} (h : n ≠ 0) (hf : progFits n d = true) :
    d ≤ 26 ∧ progFits (n - 2 ^ d) (d + 2) = true := by
  rw [progFits, if_neg h] at hf
  split at hf
  · exact ⟨by omega, hf⟩
  · cases hf

theorem prog_ne {ls : List (List Byte)} (h : ls ≠ []) (d : Nat) :
    progressiveRootAt ls d =
      sha2 (sparseRoot (ls.take (2 ^ d)) d) (progressiveRootAt (ls.drop (2 ^ d)) (d + 2)) := by
  rw [progressiveRootAt, if_neg h]

theorem root_split {g : Machine} (hn : lenOf g ≠ 0) :
    progressiveRootAt (ch g) (depthOf g) = sha2 (leftRoot g) (restRoot g) := by
  apply prog_ne
  intro h
  have := congrArg List.length h
  rw [chunksOf_length] at this; exact hn (by simpa using this)

/-! ## Arithmetic on the entry machine -/

theorem need_ge (g : Machine) : 0xa0 ≤ progNeed g := progStack_ge _ _

theorem need_ne {g : Machine} (hn : lenOf g ≠ 0) :
    progNeed g = 0xa0 + max (sparseStack (depthOf g)) (progStack (lenOf g - pw g) (depthOf g + 2)) :=
  progStack_ne hn

theorem need_ge' {g : Machine} (hn : lenOf g ≠ 0) : 0xa0 + 0x120 + 0xe0 ≤ progNeed g := by
  rw [need_ne hn]; unfold sparseStack Sha256.frameSize; omega

theorem toNat_ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem fb_toNat {g : Machine} (F : PreFacts (progNeed g) g) :
    (fb g).toNat = (g.reg 2).toNat - 0xa0 := by
  have := need_ge g; have := F.spLo
  unfold fb; rw [BitVec.toNat_sub]; simp [Layout.ramLo] at *; omega

theorem fb_add {g : Machine} (F : PreFacts (progNeed g) g) (c : Nat) :
    fb g + BitVec.ofNat 64 c = BitVec.ofNat 64 ((g.reg 2).toNat - 0xa0 + c) := by
  rw [← fb_toNat F, ofNat_toNat_add]

theorem fb_add_toNat {g : Machine} (F : PreFacts (progNeed g) g) {c : Nat} (hc : c ≤ 0xa0) :
    (fb g + BitVec.ofNat 64 c).toNat = (g.reg 2).toNat - 0xa0 + c := by
  have := F.spHi; have := F.spLo; have := need_ge g
  rw [toNat_add_ofNat (by rw [fb_toNat F]; simp [Layout.ramHi] at *; omega), fb_toNat F]

theorem fb_ofInt (g : Machine) (c : Nat) (hc : c < 2 ^ 63) :
    fb g + BitVec.ofInt 64 (c : Int) = fb g + BitVec.ofNat 64 c := by
  simp

theorem stack_present {g : Machine} (F : PreFacts (progNeed g) g) {x : Nat}
    (h1 : (g.reg 2).toNat - progNeed g ≤ x) (h2 : x < (g.reg 2).toNat) :
    (g.mem (BitVec.ofNat 64 x)).isSome := by
  have := F.stack (x - ((g.reg 2).toNat - progNeed g)) (by omega)
  have hsp := F.spLo; have hhi := F.spHi
  rw [show g.reg 2 - BitVec.ofNat 64 (progNeed g) +
      BitVec.ofNat 64 (x - ((g.reg 2).toNat - progNeed g)) = BitVec.ofNat 64 x by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp [Layout.ramLo, Layout.ramHi] at hsp hhi
    omega] at this
  exact this

theorem present_of {g m : Machine} (hp : Preserved g m) {a : Word} (h : (g.mem a).isSome) :
    (m.mem a).isSome := hp.1 a h

theorem ro_of {g m : Machine} (F : PreFacts (progNeed g) g) (hp : Preserved g m) :
    RodataLoaded zesuImage m := RodataLoaded.preserved F.ro hp rodata_lo

theorem written_stack {g : Machine} (F : PreFacts (progNeed g) g) {a : Word}
    (h1 : (g.reg 2).toNat - progNeed g ≤ a.toNat) (h2 : a.toNat < (g.reg 2).toNat) :
    WrittenN (progNeed g) g a := by
  have := F.spLo
  refine .inl ⟨?_, ?_⟩ <;> rw [BitVec.toNat_sub] <;> simp [Layout.ramLo] at * <;> omega

theorem written_out {g : Machine} (F : PreFacts (progNeed g) g) {a : Word} {j : Nat}
    (hj : j < 32) (ha : a = outOf g + BitVec.ofNat 64 j) : WrittenN (progNeed g) g a := by
  have := F.outHi
  refine .inr (.inl ⟨?_, ?_⟩) <;> rw [ha, toNat_add_ofNat (by simp [Layout.ramHi] at this; omega)] <;>
    omega

theorem present_iff {mem : Word → Option Byte} {a n : Nat} :
    present mem a n = true ↔ ∀ t < n, (mem (BitVec.ofNat 64 (a + t))).isSome :=
  ⟨fun h _ ht => present_get h ht, fun h => by simpa [present] using readBytes_isSome_of h⟩

theorem present_keep {m m' : Machine} (hp : Preserved m m') {a n : Nat}
    (h : present m.mem a n = true) : present m'.mem a n = true :=
  present_iff.mpr fun t ht => hp.1 _ (present_iff.mp h t ht)

theorem readable_sub {a n a' n' : Nat} (h : readable a n = true) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) :
    readable a' n' = true := by
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  omega

theorem chunk_toNat {g : Machine} (F : PreFacts (progNeed g) g) {x : Nat} (hx : x ≤ 32 * lenOf g) :
    (chunkPtr g + BitVec.ofNat 64 x).toNat = (chunkPtr g).toNat + x := by
  have := F.chR
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact toNat_add_ofNat (by simp [Layout.rodataHi, Layout.inputHi, Layout.ramHi] at this; omega)

theorem inWritable_of {m : Machine} {regs : List (Word × Nat)} {ov : Nat → Option Sym}
    {rs : List Region} {a : Word} (h : InWritable (entryEnv m regs) (entryState ov rs []) a) :
    ∃ r R j, rs[r]? = some R ∧ R.writable = true ∧ j < (regs.getD r (0, 0)).2 ∧
      a = (regs.getD r (0, 0)).1 + BitVec.ofNat 64 j := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := h
  exact ⟨r, R, j, hR, hw, hj, rfl⟩

theorem bytesAt_add {m : Machine} {a : Word} {c : Nat} {bs : List Byte}
    (h : ∀ i < bs.length, m.mem (a + BitVec.ofNat 64 (c + i)) = some (bs.getD i 0)) :
    BytesAt m (a + BitVec.ofNat 64 c) bs := by
  intro i hi
  rw [ofNat_add_ofNat, h i hi]; simp [List.getD_eq_getElem?_getD, hi]

theorem reg_eq_of {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (i : Fin 32)
    {s : Sym} (h : S.reg i.val = s) : m.reg i = s.eval env := by rw [← hm.regs i, h]

theorem not_one_eq : (BitVec.ofNat 64 18446744073709551614 : Word) = ~~~1 := by decide

theorem shl_toNat {k : Nat} (hk : k < 64) : ((1 : Word) <<< k).toNat = 2 ^ k := by
  rw [BitVec.toNat_shiftLeft]
  simp only [show (1 : Word).toNat = 1 from rfl, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)

end ZesuExec.Fn.SszRoot.Prog

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Cut lemmas -/

variable (hsha : ShaSpec) (hsp : SparseSpec)

theorem cut_E : CutOK (plan hsha hsp).toPlan cE := by
  rintro g m ⟨rfl, hpc, hpre⟩
  have F := PreFacts.of hpre.2
  have hN := need_ge m
  have hlo := F.spLo; have hhi := F.spHi
  have hoL := F.outLo; have hoH := F.outHi; have hO := F.dSO
  have hsub : (m.reg 2 - BitVec.ofNat 64 0xa0).toNat = (m.reg 2).toNat - 0xa0 := by
    rw [BitVec.toNat_sub]; simp [Layout.ramLo] at hlo ⊢; omega
  refine ⟨?_, ?_, F.ro, hpc⟩
  · refine entry_wf (shape := [((m.reg 2 - BitVec.ofNat 64 0xa0, 0xa0), frR),
      ((m.reg 10, 32), outW)]) ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · refine ⟨fun s hs => by simp [frR] at hs; omega, by simp [frR, Nat.mod_one], ?_⟩
        simp only [frR, if_true, writable, inRange, hsub, Bool.and_eq_true, decide_eq_true_eq]
        simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
      · refine ⟨fun s hs => by simp [outW] at hs; omega, by simp [outW, Nat.mod_one], ?_⟩
        simp only [outW, if_true, writable, inRange, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hoL, hoH⟩
    · simp only [outOf] at hO
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
        · next h10 =>
          cases hs; have : i = 10 := Fin.ext h10; subst this
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
        exact present_get F.outP hj

theorem cut_S : CutOK (plan hsha hsp).toPlan cS := by
  rintro g m ⟨hk, hpc, -⟩
  have F := PreFacts.of hk.1.2
  refine ⟨entry_wf (shape := []) (by simp) (by simp),
    entry_match (by intro i _ s hs; cases hs) (by intro r j hr; simp [entryState] at hr) (by simp),
    ro_of F hk.2.2.2.1, hpc⟩

theorem cut_R : CutOK (plan hsha hsp).toPlan cR := by
  rintro g m ⟨hk, hpc, -⟩
  have F := PreFacts.of hk.1.2
  refine ⟨entry_wf (shape := []) (by simp) (by simp),
    entry_match (by intro i _ s hs; cases hs) (by intro r j hr; simp [entryState] at hr) (by simp),
    ro_of F hk.2.2.2.1, hpc⟩

theorem cut_H : CutOK (plan hsha hsp).toPlan cH := by
  rintro g m ⟨⟨hpre, hn, -, hp, -, h2, h8, h9, -⟩, hpc, -⟩
  have F := PreFacts.of hpre.2
  have hN := need_ge' hn
  have hlo := F.spLo; have hhi := F.spHi
  have hfb := fb_toNat F
  have hoL := F.outLo; have hoH := F.outHi; have hO := F.dSO
  have h9' : m.reg 9 = outOf g := h9
  have h2' : (m.reg 2).toNat = (g.reg 2).toNat - 0xa0 := by rw [h2, hfb]
  refine ⟨entry_wf (shape := [((m.reg 2, 0xa0), frRo), ((m.reg 9, 32), outW)]) ?_ ?_,
    entry_match ?_ ?_ (by simp), ro_of F hp, hpc⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · refine ⟨fun s hs => by simp [frRo] at hs; omega, by simp [frRo, Nat.mod_one], ?_⟩
      simp only [frRo, Bool.false_eq_true, if_false, readable, inRange, h2', Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq]
      right; simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
    · refine ⟨fun s hs => by simp [outW] at hs; omega, by simp [outW, Nat.mod_one], ?_⟩
      simp only [outW, if_true, writable, inRange, h9', Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hoL, hoH⟩
  · simp only [outOf] at hO
    simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil, and_true, Disjoint, h2', h9']
    refine ⟨by simp only [outOf]; omega, fun _ h => h.elim⟩
  · intro i _ s hs
    unfold ovH at hs
    split at hs
    · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                simp [Sym.eval, Env.base, entryEnv, regsH]
    · split at hs
      · next h => cases hs; have : i = 8 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, regsH, h8, h2, fb, BitVec.sub_add_cancel]
      · split at hs
        · next h => cases hs; have : i = 9 := Fin.ext h; subst this
                    simp [Sym.eval, Env.base, entryEnv, regsH]
        · cases hs
  · intro r j hr hj
    simp only [entryState, List.length_cons, List.length_nil] at hr
    match r, hr with
    | 0, _ =>
      simp only [Env.size, entryEnv, regsH, List.getD_cons_zero] at hj
      simp only [Env.base, entryEnv, regsH, List.getD_cons_zero]
      rw [← ofNat_toNat_add, h2']
      exact present_of hp (stack_present F (by omega) (by omega))
    | 1, _ =>
      simp only [Env.size, entryEnv, regsH, List.getD_cons_succ, List.getD_cons_zero] at hj
      simp only [Env.base, entryEnv, regsH, List.getD_cons_succ, List.getD_cons_zero, h9']
      rw [← ofNat_toNat_add]
      exact present_of hp (present_get F.outP hj)

end ZesuExec.Fn.SszRoot.Prog
