import ZesuExec.Fn.SszRoot.ProgLeaf

/-!
# `progressiveRootAt`: the leaves after the calls, assembly

After `sparseRoot` (`leaf_S`): the recursive call on the rest of the chunks at depth `+ 2`, a
`SelfGoal` back to `cE`. After it (`leaf_R`): `zkvm_sha256` on both roots (`sha_exit`). After it
(`leaf_H`): the root copied to the result, the registers restored, return. `vc_sound_rec`
assembles the plan (`prog_spec`, with `sparseRoot`'s contract as the hypothesis `SparseSpec`).
-/

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

variable (hsha : ShaSpec) (hsp : SparseSpec)

/-! ## Leaves without memory (`cS`, `cR`) -/

theorem mem_eq_of_S0 {env : Env} {m m' : Machine} (hso : SameOutside (InWritable env S0) m m') :
    ∀ a, m'.mem a = m.mem a :=
  fun a => hso a fun h => by obtain ⟨r, R, j, hR, -⟩ := h; simp [S0, entryState] at hR

theorem mid_regs {m m' : Machine} {l : Leaf} (hm' : Match (entryEnv m []) l.S m')
    (h : ∀ i ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], l.S.reg i = .var i) :
    ∀ i ∈ calleeSaved, m'.reg i = m.reg i := by
  intro i hi
  have hi' : i.val ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  rw [reg_eq_of hm' i (h _ hi'), Sym.eval_var, entryEnv_var]

theorem keep_same {g m m' : Machine} (hk : Keep g m) (hmem : ∀ a, m'.mem a = m.mem a)
    (hcs : ∀ i ∈ calleeSaved, m'.reg i = m.reg i) : Keep g m' :=
  (keep_after (W := fun _ => False) (o := 0) hk (by omega) (fun _ h => h.elim) (fun a _ => hmem a)
    hcs (Preserved.of_mem_eq (funext hmem))).1

theorem bytes_keep {g m m'' : Machine} (F : PreFacts (progNeed g) g) {c o : Nat} {bs : List Byte}
    (hb : BytesAt m (fb g + BitVec.ofNat 64 c) bs) (hlen : bs.length = 32) (hc : c + 32 ≤ 0xa0)
    (hdis : c + 32 ≤ o ∨ o + 32 ≤ c)
    (hfr : ∀ a : Word, InFrame g a → ¬ InSlot g o a → m''.mem a = m.mem a) :
    BytesAt m'' (fb g + BitVec.ofNat 64 c) bs := by
  have hN := need_ge g; have hhi := F.spHi; have hlo := F.spLo
  intro i hi
  rw [hfr _ ?_ ?_, hb i hi]
  all_goals simp only [InFrame, InSlot]
  all_goals rw [ofNat_add_ofNat, fb_add F, toNat_ofNat_lt (by simp [Layout.ramHi] at hhi; omega)]
  · constructor <;> omega
  · omega

theorem len32 {g : Machine} (F : PreFacts (progNeed g) g) : 32 * lenOf g < 2 ^ 64 := by
  have := F.chR
  simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  simp [Layout.rodataHi, Layout.inputHi, Layout.ramHi] at this; omega

theorem leaf_S : ∀ l ∈ runS_leaves, LeafGoalR (plan hsha hsp) cS l := by
  intro l hl
  rw [lS, List.mem_singleton] at hl; subst hl
  obtain ⟨⟨hex, -, hob, hst, s1, sk⟩, s10, s11, s12, s13⟩ := fS
  rintro g m hA -
  obtain ⟨hk, hpc, r18, r19, r20, r21, hleft⟩ := hA
  have hk0 := hk
  obtain ⟨hpre, hn, -, -, -, -, h8, -⟩ := hk
  have F := PreFacts.of hpre.2
  have hfit := progFits_ne hn hpre.1
  have hL := len32 F
  have hszl := sz_le g
  have hb : cS.budget g m = restS g := rfl
  have h0 : cS.S.steps = 0 := rfl
  refine ⟨by rw [hob]; simp, by rw [hb, h0, hst]; unfold restS; omega, fun m' hm' he hso => ?_⟩
  rw [hex] at he ⊢
  apply ExitGoalR.self
  have hmem := mem_eq_of_S0 hso
  have hcs := mid_regs hm' sk
  have hk' := keep_same hk0 hmem hcs
  have r1 : m'.reg 1 = BitVec.ofNat 64 pcR := by rw [reg_eq_of hm' 1 s1]; rfl
  have r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0x48 := by
    rw [reg_eq_of hm' 10 s10]
    show m.reg 8 + BitVec.ofNat 64 18446744073709551528 = _
    rw [h8]; unfold fb; bv_omega
  have r11 : m'.reg 11 = chunkPtr g + BitVec.ofNat 64 (32 * sz g) := by
    rw [reg_eq_of hm' 11 s11]
    show m.reg 20 + m.reg 19 <<< ((BitVec.ofNat 64 5).toNat % 64) = _
    rw [r20, r19]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt (x := 32 * sz g) (by omega),
      toNat_ofNat_lt (x := sz g) (by omega)]
    simp only [Nat.shiftLeft_eq, show (BitVec.ofNat 64 5).toNat % 64 = 5 from rfl]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have r12 : lenOf m' = lenOf g - sz g := by
    simp only [lenOf]; rw [reg_eq_of hm' 12 s12]
    show (m.reg 18 - m.reg 19).toNat = _
    rw [r18, r19, BitVec.toNat_sub, toNat_ofNat_lt (by omega)]
    simp only [lenOf] at hszl ⊢
    omega
  have r13 : depthOf m' = depthOf g + 2 := by
    simp only [depthOf]; rw [reg_eq_of hm' 13 s13]
    show (m.reg 21 + BitVec.ofNat 64 2).toNat = _
    rw [r21, BitVec.toNat_add]
    have := hfit.1
    simp only [depthOf] at this ⊢
    simp; omega
  have hnp := need_prog hn r12 r13
  have hpre' : ProgPre m' := ⟨by rw [r12, r13, sub_sz]; exact hfit.2,
    callee_pre hk' (by simp only [RetAligned, r1]; decide) hnp r10 (by omega) r11 r12 (by omega)⟩
  refine ⟨cE, by simp [plan, cuts], m', ⟨rfl, he, hpre'⟩, ?_, fun k m'' hrun _ hpost => ?_⟩
  · show progCost (lenOf m') (depthOf m') ≤ restS g - (runS_leaves[0].S.steps - 0)
    rw [hst, r12, r13, sub_sz]; unfold restS; omega
  obtain ⟨hk'', hfr⟩ := keep_after hk' (o := 0x48) (by omega) (written_callee hk' hnp r10 (by omega))
    hpost.2.2 hpost.1.2 hrun.preserved
  refine ⟨cR, by simp [plan, cuts], by rw [hpost.1.1, r1]; rfl,
    ⟨hk'', by rw [hpost.1.1, r1]; rfl, ?_, ?_⟩, ?_⟩
  · exact bytes_keep F hleft (sparseRoot_length _ _ chunksOf_take_mem) (by omega) (by omega)
      fun a h1 h2 => (hfr a h1 h2).trans (hmem a)
  · have hb := hpost.2.1
    simp only [outOf, r10] at hb
    rw [show chunkPtr m' = chunkPtr g + BitVec.ofNat 64 (32 * sz g) from r11, r12, r13,
      chunks_same hpre hk'.2.2.1 (by omega)] at hb
    rw [restRoot, drop_eq]; exact hb
  · show progCost (lenOf m') (depthOf m') + (5 + shaCost + 18) ≤
      restS g - (runS_leaves[0].S.steps - 0)
    rw [hst, r12, r13, sub_sz]; unfold restS; omega

/-! ## `zkvm_sha256` on both roots -/

theorem sha_exit {g m' : Machine} (hk : Keep g m') (r1 : m'.reg 1 = BitVec.ofNat 64 pcH)
    (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0x28) (r11 : m'.reg 11 = 64)
    (r12 : m'.reg 12 = fb g + BitVec.ofNat 64 8) (hpc : m'.pc.toNat = Sha256.entry)
    (hin : BytesAt m' (fb g + BitVec.ofNat 64 0x28) (leftRoot g ++ restRoot g)) :
    ExitGoal (plan hsha hsp).toPlan g m' (shaCost + 18) (.call Sha256.entry pcH) := by
  have hk0 := hk
  obtain ⟨hpre, hn, -, hp', -, r2, -⟩ := hk
  have F := PreFacts.of hpre.2
  have hN := need_ge' hn
  have hlo := F.spLo; have hhi := F.spHi; have h16 := F.sp16
  have hfb := fb_toNat F
  have hlo' : Layout.ramLo = 0xa0000000 := rfl
  have hhi' : Layout.ramHi = 0xc0000000 := rfl
  have hbump : Sha256.bump = 0xa05340b8 := rfl
  have hstage : Layout.extraParams = 0xa0000f00 := rfl
  have dSB := F.dSB; have dSS := F.dSS
  have h28 := fb_add_toNat F (c := 0x28) (by omega)
  have h8 := fb_add_toNat F (c := 8) (by omega)
  have hfs : Sha256.frameSize = 224 := rfl
  have hfr : (m'.reg 2 - BitVec.ofNat 64 224).toNat = (g.reg 2).toNat - 0xa0 - 0xe0 := by
    rw [r2, BitVec.toNat_sub, hfb]; simp; omega
  have hll : (leftRoot g).length = 32 := sparseRoot_length _ _ chunksOf_take_mem
  have hrl : (restRoot g).length = 32 := progressiveRootAt_length _ _
  have hlen : (leftRoot g ++ restRoot g).length = 64 := by simp [hll, hrl]
  refine ⟨shaC hsha, (), by simp [plan], hpc,
    ⟨⟨ro_of F hp', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [r2, hfb]; omega
  · rw [r2, hfb]; rw [hfs]; omega
  · rw [r2, hfb]; omega
  · intro j hj
    rw [r2]
    have : fb g - BitVec.ofNat 64 Sha256.frameSize + BitVec.ofNat 64 j =
        BitVec.ofNat 64 ((g.reg 2).toNat - 0xa0 - 0xe0 + j) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hfb, hfs]
      rw [hfs] at hj
      omega
    rw [this]
    exact hp'.1 _ (stack_present F (by rw [hfs] at hj; omega) (by rw [hfs] at hj; omega))
  · simp only [RetAligned, r1]; decide
  · right
    simp only [srcOk, Bool.and_eq_true, r10, r11, h28]
    refine ⟨by simp [readable, inRange]; omega, ?_⟩
    have := readBytes_of_bytesAt hin
    rw [hlen, h28] at this
    simp [present, this]
  · simp only [dstOk, Bool.and_eq_true, r12, h8]
    refine ⟨by simp [writable, inRange]; omega, present_iff.mpr fun t ht => ?_⟩
    exact hp'.1 _ (stack_present F (by omega) (by omega))
  · simp only [dstOk, Bool.and_eq_true]
    exact ⟨by decide, present_keep hp' F.bumpP⟩
  · simp only [dstOk, Bool.and_eq_true]
    exact ⟨by decide, present_keep hp' F.stageP⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, Disjoint, Sha256.frameR, Sha256.outR, Sha256.bumpR,
      Sha256.stageR, hfs, hfr, r12, h8]
    simp only [show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
      show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl,
      false_implies, implies_true, and_true]
    omega
  · right
    simp only [Disjoint, Sha256.inR, Sha256.frameR, Sha256.bumpR, Sha256.stageR, hfs, hfr, r10,
      r11, h28, show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl,
      show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl,
      show (64 : Word).toNat = 64 from rfl]
    omega
  · rw [r11]; rfl
  · rintro m'' ⟨⟨⟨hpc'', hcs⟩, -, hout, -, hso2⟩, hp2⟩
    have hW : ∀ a, Sha256.Written m' a →
        WrittenN (progNeed g) g a ∧ (InFrame g a → InSlot g 8 a) := by
      intro a hw
      rcases hw with h | h | h | h
      · simp only [InRange, Sha256.frameR, hfs, hfr] at h
        exact ⟨written_stack F (by omega) (by omega), fun h1 => by simp only [InFrame] at h1; omega⟩
      · simp only [InRange, r12, h8] at h
        exact ⟨written_stack F (by omega) (by omega), fun _ => by simp only [InSlot]; omega⟩
      · refine ⟨.inr (.inr (.inl h)), fun h1 => ?_⟩
        simp only [InRange, show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl] at h
        simp only [InFrame] at h1; omega
      · refine ⟨.inr (.inr (.inr h)), fun h1 => ?_⟩
        simp only [InRange,
          show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl] at h
        simp only [InFrame] at h1; omega
    obtain ⟨hk'', -⟩ := keep_after hk0 (o := 8) (by omega) hW hso2 hcs hp2
    refine ⟨cH, by simp [plan, cuts], rfl, by rw [hpc'', r1]; rfl,
      ⟨hk'', by rw [hpc'', r1]; rfl, ?_⟩, Nat.le_refl _⟩
    rw [root_split hn, ← r12]
    have hmsg : Sha256.msgOf m' = leftRoot g ++ restRoot g := by
      simp only [Sha256.msgOf, r10, r11, show (64 : Word).toNat = 64 from rfl]
      have := readBytes_of_bytesAt hin
      rw [hlen] at this; rw [this]; rfl
    unfold sha2; rw [← hmsg]; exact hout

theorem bytesAt_append {m : Machine} {a : Word} {xs ys : List Byte} (hx : BytesAt m a xs)
    (hy : BytesAt m (a + BitVec.ofNat 64 xs.length) ys) : BytesAt m a (xs ++ ys) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [hx i h, List.getElem_append_left h]
  · have := hy (i - xs.length) (by simp at hi; omega)
    rw [ofNat_add_ofNat, show xs.length + (i - xs.length) = i by omega] at this
    rw [this, List.getElem_append_right (by omega)]

theorem leaf_R : ∀ l ∈ runR_leaves, LeafGoalR (plan hsha hsp) cR l := by
  intro l hl
  rw [lR, List.mem_singleton] at hl; subst hl
  obtain ⟨⟨hex, -, hob, hst, s1, sk⟩, s10, s11, s12⟩ := fR
  rintro g m ⟨hk, hpc, hleft, hrest⟩ -
  have h8 := hk.2.2.2.2.2.2.1
  have hb : cR.budget g m = 5 + shaCost + 18 := rfl
  have h0 : cR.S.steps = 0 := rfl
  refine ⟨by rw [hob]; simp, by rw [hb, h0, hst]; omega, fun m' hm' he hso => ?_⟩
  rw [hex] at he ⊢
  left
  have hmem := mem_eq_of_S0 hso
  have hk' := keep_same hk hmem (mid_regs hm' sk)
  have r1 : m'.reg 1 = BitVec.ofNat 64 pcH := by rw [reg_eq_of hm' 1 s1]; rfl
  have r10 : m'.reg 10 = fb g + BitVec.ofNat 64 0x28 := by
    rw [reg_eq_of hm' 10 s10]
    show m.reg 8 + BitVec.ofNat 64 18446744073709551496 = _
    rw [h8]; unfold fb; bv_omega
  have r11 : m'.reg 11 = 64 := by rw [reg_eq_of hm' 11 s11]; rfl
  have r12 : m'.reg 12 = fb g + BitVec.ofNat 64 8 := by
    rw [reg_eq_of hm' 12 s12]
    show m.reg 8 + BitVec.ofNat 64 18446744073709551464 = _
    rw [h8]; unfold fb; bv_omega
  have hll : (leftRoot g).length = 32 := sparseRoot_length _ _ chunksOf_take_mem
  have hin : BytesAt m' (fb g + BitVec.ofNat 64 0x28) (leftRoot g ++ restRoot g) := by
    refine bytesAt_append (fun i hi => ?_) (fun i hi => ?_)
    · rw [hmem]; exact hleft i hi
    · rw [hmem, hll, ofNat_add_ofNat, ofNat_add_ofNat, show 40 + (32 + i) = 0x48 + i by omega,
        ← ofNat_add_ofNat]
      exact hrest i hi
  rw [hb, h0, hst]
  exact sha_exit hsha hsp hk' r1 r10 r11 r12 he hin

/-! ## The return -/

theorem saved_init {g m : Machine} (hS : Saved g m) (h2 : m.reg 2 = fb g) {q o : Nat}
    (hq : q < 7) (ho : o = 0x68 + 8 * q) :
    (Sym.init 0 o 8).eval (entryEnv m (regsH m)) = g.reg (savedReg q) := by
  subst ho
  simp only [Sym.eval]
  rw [show byteList ((entryEnv m (regsH m)).byte0 0) (0x68 + 8 * q) 8 =
      byteList (byteOf (g.reg (savedReg q))) 0 8 from byteList_congr (fun t ht => ?_)]
  · exact ofBytesLE_bytes8 _
  · simp only [Env.byte0, entryEnv, regsH, List.getD_cons_zero, h2]
    rw [hS q hq t ht]
    simp

theorem leaf_H : ∀ l ∈ runH_leaves, LeafGoalR (plan hsha hsp) cH l := by
  intro l hl
  rw [lH, List.mem_singleton] at hl; subst hl
  obtain ⟨-, hob, hex, hst, s2, s8, s9, s18, s19, s20, s21, sk, hreg, hsrc⟩ := fH
  rintro g m ⟨⟨hpre, hn, hso0, hp, hS, h2, h8, h9, hkeep⟩, hpc, hroot⟩ -
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have rlen : (progressiveRootAt (ch g) (depthOf g)).length = 32 := progressiveRootAt_length _ _
  have hra : (Sym.init 0 152 8).eval (entryEnv m (regsH m)) = g.reg 1 :=
    saved_init hS h2 (q := 6) (by omega) rfl
  have hand : (Sym.bin .and (.init 0 152 8) (.lit M2)).eval (entryEnv m (regsH m)) =
      g.reg 1 &&& ~~~1 := by
    rw [Sym.eval_bin, hra]; simp only [Sym.eval_lit, BinOp.eval, M2, not_one_eq]
  have hb : cH.budget g m = 18 := rfl
  have h0 : cH.S.steps = 0 := rfl
  have henv : cH.env g m = entryEnv m (regsH m) := rfl
  rw [henv]
  refine ⟨?_, by rw [hb, h0, hst]; omega, fun m' hm' he hso => ?_⟩
  · rw [hob]; intro o ho; rw [List.mem_singleton] at ho; subst ho
    show ((Sym.bin .and (.init 0 152 8) (.lit M2)).eval (entryEnv m (regsH m))).toNat % 4 = 0
    rw [hand]; exact F.ra
  rw [hex] at he ⊢
  left
  show ProgPost g m'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [ExitOk] at he; rw [he, hand]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [reg_eq_of hm' 2 s2, Sym.eval_ptr]
      show m.reg 2 + _ = _
      rw [h2]; exact (fb_ofInt g 0xa0 (by omega)).trans (by simp [fb, BitVec.sub_add_cancel])
    · rw [reg_eq_of hm' 8 s8]; exact saved_init hS h2 (q := 5) (by omega) rfl
    · rw [reg_eq_of hm' 9 s9]; exact saved_init hS h2 (q := 4) (by omega) rfl
    · rw [reg_eq_of hm' 18 s18]; exact saved_init hS h2 (q := 3) (by omega) rfl
    · rw [reg_eq_of hm' 19 s19]; exact saved_init hS h2 (q := 2) (by omega) rfl
    · rw [reg_eq_of hm' 20 s20]; exact saved_init hS h2 (q := 1) (by omega) rfl
    · rw [reg_eq_of hm' 21 s21]; exact saved_init hS h2 (q := 0) (by omega) rfl
    all_goals
      rw [reg_eq_of hm' _ (sk _ (by decide)), Sym.eval_var, entryEnv_var]
      exact hkeep _ (by simp [keepRegs])
  · intro i hi
    rw [rlen] at hi
    have := mem_of_src hm' (r := 1) (by rw [hreg]; omega)
      (by simp [Env.size, entryEnv, regsH]; omega) (hsrc i hi)
    simp only [regsH, List.getD_cons_succ, List.getD_cons_zero, h9, h2] at this
    rw [this, ← ofNat_add_ofNat, hroot i (by rw [rlen]; exact hi)]; rfl
  · intro a ha
    rw [hso a fun hw => ?_, hso0 a ha]
    obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := inWritable_of hw
    match r, hR with
    | 0, hR => simp [SH, entryState, frRo] at hR; subst hR; simp at hw
    | 1, _ =>
      simp only [regsH, List.getD_cons_succ, List.getD_cons_zero] at hj
      exact ha (written_out F hj (by simp [regsH, h9]))
    | r + 2, hR => simp [SH, entryState] at hR

end ZesuExec.Fn.SszRoot.Prog

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-! ## Assembly -/

variable (hsha : ShaSpec) (hsp : SparseSpec)

theorem hruns : ∀ i (h : i < (plan hsha hsp).cuts.length),
    run zesuImage ((plan hsha hsp).cuts.map (·.pc)) (plan hsha hsp).fuel (plan hsha hsp).cuts[i].pc
      (plan hsha hsp).cuts[i].S = some ((plan hsha hsp).leaves i) := by
  intro i h
  show run zesuImage (cuts.map (·.pc)) fuel cuts[i].pc cuts[i].S = some (leaves i)
  rw [cuts_pcs]
  match i, h with
  | 0, _ => exact runE
  | 1, _ => exact runS
  | 2, _ => exact runR
  | 3, _ => exact runH

theorem posE : ∀ l ∈ runE_leaves, 0 < l.S.steps := by decide
theorem posS : ∀ l ∈ runS_leaves, 0 < l.S.steps := by decide
theorem posR : ∀ l ∈ runR_leaves, 0 < l.S.steps := by decide
theorem posH : ∀ l ∈ runH_leaves, 0 < l.S.steps := by decide

theorem hpos : ∀ i (h : i < (plan hsha hsp).cuts.length), ∀ l ∈ (plan hsha hsp).leaves i,
    (plan hsha hsp).cuts[i].S.steps < l.S.steps := by
  intro i h
  match i, h with
  | 0, _ => exact posE
  | 1, _ => exact posS
  | 2, _ => exact posR
  | 3, _ => exact posH

theorem hcut : ∀ c ∈ (plan hsha hsp).cuts, CutOK (plan hsha hsp).toPlan c := by
  intro c hc
  simp only [plan, cuts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact cut_E hsha hsp
  · exact cut_S hsha hsp
  · exact cut_R hsha hsp
  · exact cut_H hsha hsp

theorem hleaf : ∀ i (h : i < (plan hsha hsp).cuts.length), ∀ l ∈ (plan hsha hsp).leaves i,
    LeafGoalR (plan hsha hsp) (plan hsha hsp).cuts[i] l := by
  intro i h
  match i, h with
  | 0, _ => exact leaf_E hsha hsp
  | 1, _ => exact leaf_S hsha hsp
  | 2, _ => exact leaf_R hsha hsp
  | 3, _ => exact leaf_H hsha hsp

/-- The `progressiveRootAt` contract, per depth and length. -/
def ProgSpec : Prop :=
  ∀ d n, Spec zesuImage progEntry (progCost n d)
    (fun m => ProgPre m ∧ depthOf m = d ∧ lenOf m = n) ProgPost

include hsha hsp in
/-- `progressiveRootAt` against `ProgPre`/`ProgPost`, given the contracts of `zkvm_sha256` and
`sparseRoot`. -/
theorem prog_spec : ProgSpec := by
  rintro d n m hpc ⟨hpre, rfl, rfl⟩
  exact vc_sound_rec (plan hsha hsp) (hruns hsha hsp) (hpos hsha hsp) (hcut hsha hsp)
    (hleaf hsha hsp) cE (by simp [plan, cuts]) m m ⟨rfl, hpc, hpre⟩

end ZesuExec.Fn.SszRoot.Prog
