import ZesuExec.Fn.DTF.HashF1

/-!
# DTF: the `txHashList` loop after `ensureTotalCapacity` (programme plan S7 step 4)

At `0x8000211c` F1 has returned: the header has room for one more element (kept, or a grown
buffer that replaced the old one in DTF's blocks), or F1 failed with `OutOfMemory` (`a0 = 2`).
Leaf 1 (no error) loads the slot `p + 32 n` and goes to the store cut `0x80002138`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## List headers in F1's terms -/

theorem fr_add8 (σ : Sig) (o : Nat) : σ.fr + w o + 8 = σ.fr + w (o + 8) := by
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl]; simp only [w]; rw [F1.add_add_ofNat]

theorem fr_add16 (σ : Sig) (o : Nat) : σ.fr + w o + 16 = σ.fr + w (o + 16) := by
  rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl]; simp only [w]; rw [F1.add_add_ofNat]

theorem hdr_words {σ : Sig} {m : Machine} {o : Nat} {p n cap : Word}
    (l0 : m.load (σ.fr + w o) 8 = some p) (l8 : m.load (σ.fr + w (o + 8)) 8 = some n)
    (l16 : m.load (σ.fr + w (o + 16)) 8 = some cap) :
    F1.wordAt m (σ.fr + w o) = p ∧ F1.wordAt m (σ.fr + w o + 8) = n ∧
      F1.wordAt m (σ.fr + w o + 16) = cap :=
  ⟨by simp [F1.wordAt, l0], by rw [fr_add8]; simp [F1.wordAt, l8],
    by rw [fr_add16]; simp [F1.wordAt, l16]⟩

/-- A header F1 reports, with `n` elements and room for one more. -/
theorem hdr_of_is {σ : Sig} {m : Machine} {o n : Nat} {p cap : Word}
    (hH : F1.HeaderIs m (σ.fr + w o) p (w n) cap) (hn : n + 1 ≤ cap.toNat) (hp : 0 < p.toNat)
    {L X : List (Word × Nat)} (hlive : Live σ m L X) (hb : BufOwn X p cap) :
    ListHdr σ m o n 1 := by
  obtain ⟨l0, l8, l16⟩ := hH
  exact ⟨p, cap, l0, by rw [← fr_add8]; exact l8, by rw [← fr_add16]; exact l16, hn, hp, L, X,
    hlive, hb⟩

/-- The slot after the `n` elements of a header with room for one more: RAM, present, carved
from the allocator's private memory. -/
theorem hdr_slot {σ : Sig} {m : Machine} {o n : Nat} (hh : ListHdr σ m o n 1) {a : Word}
    (ha : ∀ p, m.load (σ.fr + w o) 8 = some p → a = p + w (32 * n)) :
    RamRange a 32 ∧ Present m a 32 ∧ ∀ b, InRange a 32 b → σ.A.Priv σ.g.L b := by
  obtain ⟨p, cap, l0, -, -, hnr, -, L, X, hlive, hb⟩ := hh
  rw [ha p l0]
  have hmem := hb (by omega)
  obtain ⟨-, hram, hpriv⟩ := hlive.2.2 _ hmem
  have hmemL : (p, cap.toNat * 32) ∈ L := hlive.2.1.symm.subset (List.mem_append_right _ hmem)
  have hpres := ((σ.A.live_ok L m hlive.1).2 _ hmemL).2
  simp only at hram
  unfold RamRange Layout.ramHi at hram
  have hpa : (p + w (32 * n)).toNat = p.toNat + 32 * n := toNat_add_ofNat (by omega)
  refine ⟨⟨by unfold Layout.ramLo at *; omega, by unfold Layout.ramHi; omega⟩, fun j hj => ?_,
    fun b hb' => hpriv b ?_⟩
  · rw [show p + w (32 * n) + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (32 * n + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
    exact hpres _ (by simp only; omega)
  · simp only [InRange] at hb' ⊢; rw [hpa] at hb'; omega

/-! ## The return from `ensureTotalCapacity` -/

/-- At `0x8000211c`: F1 failed with `OutOfMemory`, or the loop state with room for the item. -/
theorem hash_f1 {σ : Sig} {m : Machine} (hA : (mkCut (table[109]!)).A σ m) :
    m.reg 10 = 2 ∨ HashItem σ m 1 := by
  have hpc : (table[109]!).pc ≠ entry := by decide
  simp only [mkCut, if_neg hpc, ACut] at hA
  rcases hA with ⟨h, -⟩ | ⟨s, hs, mc, x, hsite, hpost⟩
  · exact absurd h (by decide)
  have hs' : s = siteAt 109 := by
    show s = ((table[109]!).site).getD default; rw [hs]; rfl
  subst hs'
  have hkind : (siteAt 109).kind = .f1 := by decide
  have hSF : (siteAt 109).kind.SiteFine (siteAt 109) = true := by decide
  obtain ⟨hret, -, -⟩ := ret_common hSF hsite hpost
  have hc := hsite.2.1
  have hpre := hc.2.1
  have h3 : σ.t = 3 := arm3 hsite.2.2.2.1 (by decide)
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[109]!).pc = 0x8000211c by decide] at hsx
  simp only [SiteX, show (0x8000211c : Nat) ≠ 0x800020c0 by decide, if_false, if_true] at hsx
  obtain ⟨⟨c, h, p, n, j, k, hl, hsk, hsk1, hnk, hk32, r23, r22, r25, r20, hdr⟩, a12⟩ := hsx
  have hix := hsite.2.2.2.2.2.1
  rw [hkind] at hix
  obtain ⟨-, X, hlive, hbuf⟩ := hix
  obtain ⟨hq, -⟩ := hpost
  replace hq : F1.PostKeep σ.A x.1 x.2.1 mc m := by rw [hkind] at hq; exact hq
  obtain ⟨⟨-, -, hbr⟩, -⟩ := hq
  have hhdr : mc.reg 10 = σ.fr + w 0x258 := hsite.2.2.1.1 (10, .fr 0x258) (by decide) _ rfl
  obtain ⟨p0, cap, l0, l8, l16, -, hp0, -, -, -, -⟩ := hdr
  obtain ⟨ep, en, ec⟩ := hdr_words l0 l8 l16
  have hle := hashList_le hpre h3 hl
  have hjk : j + k ≤ p := by
    have := skip_le hsk1
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  have hn32 : n + 1 < 2 ^ 32 := by have := len_lt32 hpre; omega
  have hreq : (mc.reg 12).toNat = n + 1 := by
    rw [a12, r25]
    show (BitVec.ofNat 64 n + BitVec.ofNat 64 1).toNat = n + 1
    rw [← BitVec.ofNat_add]; simp only [BitVec.toNat_ofNat]; omega
  rw [hhdr, ep, en, ec, hreq] at hbr
  rw [hhdr, ep, ec] at hbuf
  have e23 : m.reg 23 = mc.reg 23 := hret.2 23 (by decide)
  have e22 : m.reg 22 = mc.reg 22 := hret.2 22 (by decide)
  have e25 : m.reg 25 = mc.reg 25 := hret.2 25 (by decide)
  have e20 : m.reg 20 = mc.reg 20 := hret.2 20 (by decide)
  split at hbr
  · next hle' =>
    obtain ⟨-, hH, hheap, -⟩ := hbr
    exact .inr ⟨c, h, p, n, j, k, hl, hsk, hsk1, hnk, hk32, e23.trans r23, e22.trans r22,
      e25.trans r25, e20.trans r20,
      hdr_of_is hH (by omega) hp0 ⟨hheap, hlive.2.1, hlive.2.2⟩ hbuf⟩
  · rcases hbr with ⟨-, p', hH, hp', hR', -, hheap', -⟩ | ⟨h2, -⟩
    · have hpos : 0 < F1.grown (n + 1) * F1.elemBytes := by unfold F1.grown F1.elemBytes; omega
      have hg : (BitVec.ofNat 64 (F1.grown (n + 1))).toNat = F1.grown (n + 1) := by
        simp only [BitVec.toNat_ofNat]; unfold F1.grown; omega
      have hlive' : ∃ L' X', Live σ m L' X' ∧ (p', F1.grown (n + 1) * F1.elemBytes) ∈ X' := by
        split at hheap'
        · next h0 => exact ⟨_, _, live_swap hpre hlive (hbuf h0) hpos hR' hheap',
            List.mem_append_right _ (List.mem_singleton_self _)⟩
        · exact ⟨_, _, live_ext hpre hlive (B := [(p', _)])
            (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact ⟨hpos, hR'⟩)
            (List.Perm.refl _) hheap', List.mem_append_right _ (List.mem_singleton_self _)⟩
      obtain ⟨L', X', hl', hmem⟩ := hlive'
      exact .inr ⟨c, h, p, n, j, k, hl, hsk, hsk1, hnk, hk32, e23.trans r23, e22.trans r22,
        e25.trans r25, e20.trans r20,
        hdr_of_is hH (by rw [hg]; unfold F1.grown; omega) hp' hl' (fun _ => by rw [hg]; exact hmem)⟩
    · exact .inl h2

/-- No error from F1 (`0x8000211c`, leaf 1): the slot `p + 32 n`, then the store cut. -/
theorem DTF.leaf_8000211c_1 :
    LeafGoal DTF.plan DTF.plan.cuts[109]! ((DTF.plan.leaves 0x8000211c)[1]!) := by
  refine leaf_at_x (table[109]!) (table[110]!) ((leavesAt 0x8000211c)[1]!) (by decide)
    DTF.cut_8000211c (by decide) (by decide) (by decide) rfl (by decide) ?_
  intro σ m m' hA hc C
  have hcond := hc _ (show SBool.eq (.bin .srl (.bin .sll (.var 10) (.lit 48)) (.lit 48)) (.lit 0)
    ∈ _ by decide)
  rcases hash_f1 hA with h2 | hit
  · exfalso
    simp only [SBool.eval, Sym.eval, BinOp.eval, envOf, show (10 : Nat) < 32 by decide, if_true,
      show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, h2, beq_iff_eq] at hcond
    exact absurd hcond (by decide)
  obtain ⟨c, h, p, n, j, k, hl, hsk, hsk1, hnk, hk32, r23, r22, r25, r20, hdr⟩ := hit
  have hdr' := hdr_keep C (o := 0x258) (by decide) (by decide) (by decide) (by decide) hdr
  obtain ⟨p0, -, l0, l8, -⟩ := hdr
  have hpre := C.F.common.2.1
  have hle := hashList_le hpre (arm3 C.F.arms (by decide)) hl
  have hjk : j + k ≤ p := by
    have := skip_le hsk1
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  have hn32 : n < 2 ^ 32 := by have := len_lt32 hpre; omega
  have e10 : m'.reg 10 = p0 + w (32 * n) := by
    rw [show (10 : Fin 32) = Fin.ofNat 32 10 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x8000211c)[1]!).S.reg 10 =
        .bin .add (.init 0 600 8) (.bin .sll (.init 0 608 8) (.lit 5)) by decide]
    simp only [Sym.eval_bin, BinOp.eval]
    rw [frame_init l0, frame_init (o := 608) l8]
    refine congrArg (p0 + ·) ?_
    apply BitVec.eq_of_toNat_eq
    have hn : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
    simp only [w, Sym.eval_lit, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, hn,
      show 5 % 2 ^ 64 % 64 = 5 from rfl]
    omega
  have e25 : m'.reg 25 = w n := by
    rw [show (25 : Fin 32) = Fin.ofNat 32 25 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x8000211c)[1]!).S.reg 25 = .init 0 608 8 by decide,
      frame_init (o := 608) l8]
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e20 := ctx_reg C (i := 20) (i' := 20) (by decide) (by decide) (by decide)
  have hslot := hdr_slot hdr' (a := m'.reg 10) fun p' hl0 => by
    rw [ctx_load C (by decide) (by decide), l0, Option.some.injEq] at hl0
    rw [e10, hl0]
  have hitem : HashItem σ m' 1 := ⟨c, h, p, n, j, k, hl, hsk, hsk1, hnk, hk32, e23.trans r23,
    e22.trans r22, e25, e20.trans r20, hdr'⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [show (table[110]!).pc = 0x80002138 by decide]
    simp only [Extra]
    refine ⟨hslot, hitem, p0, by rw [ctx_load C (by decide) (by decide)]; exact l0, ?_⟩
    rw [e10, e25]
    refine congrArg (p0 + ·) ?_
    apply BitVec.eq_of_toNat_eq
    have hn : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
    simp only [w, BitVec.toNat_mul, BitVec.toNat_ofNat, hn, show (32 : Word).toNat = 32 from rfl]
  · rw [show budgetAt (table[110]!).pc = (2564, .list (.reg 22)) from rfl]; trivial
  unfold budgetOf restLen
  rw [show budgetAt (table[110]!).pc = (2564, .list (.reg 22)) from rfl,
    show budgetAt (table[109]!).pc = (2571, .list (.reg 22)) from rfl,
    show (table[110]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide,
    show (table[109]!).rest.find? (·.len) = some ⟨.slot 0x158, true, 11⟩ by decide,
    show ((leavesAt 0x8000211c)[1]!).S.steps - (table[109]!).shape.S.steps = 7 by decide]
  simp only [innerOf, Loc.word]
  rw [ctx_slot C (o := 0x158) (by decide) (by decide), e22]
  omega

end ZesuExec.Fn.DTF
