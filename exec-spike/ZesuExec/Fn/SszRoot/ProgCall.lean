import ZesuExec.Fn.SszRoot.ProgVc

/-!
# `progressiveRootAt`: calls

What a callee needs (`callee_pre`: `PreN` for a callee whose stack lies below the frame and whose
result goes into the frame) and what the caller keeps across a call (`keep_after`, with
`written_callee` for the callees `sparseRoot` and `progressiveRootAt` and `written_sha` for
`zkvm_sha256`); the chunks a callee reads are unchanged since the entry (`chunks_same`).
-/

namespace ZesuExec.Fn.SszRoot.Prog
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym ZesuExec.Vc

/-- In the frame `[sp₀ - 0xa0, sp₀)`. -/
abbrev InFrame (g : Machine) (a : Word) : Prop :=
  (g.reg 2).toNat - 0xa0 ≤ a.toNat ∧ a.toNat < (g.reg 2).toNat

/-- In the frame slot `[fb + o, fb + o + 32)`. -/
abbrev InSlot (g : Machine) (o : Nat) (a : Word) : Prop :=
  (g.reg 2).toNat - 0xa0 + o ≤ a.toNat ∧ a.toNat < (g.reg 2).toNat - 0xa0 + o + 32

theorem keep_after {g m' m'' : Machine} {W : Word → Prop} {o : Nat} (hk : Keep g m')
    (ho : o + 32 ≤ 0x68)
    (hW : ∀ a, W a → WrittenN (progNeed g) g a ∧ (InFrame g a → InSlot g o a))
    (hso2 : SameOutside W m' m'') (hcs : ∀ i ∈ calleeSaved, m''.reg i = m'.reg i)
    (hrun : Preserved m' m'') :
    Keep g m'' ∧ ∀ a : Word, InFrame g a → ¬ InSlot g o a → m''.mem a = m'.mem a := by
  obtain ⟨hpre, hn, hso, hp, hS, h2, h8, h9, hkeep⟩ := hk
  have F := PreFacts.of hpre.2
  have hN := need_ge g
  have hlo := F.spLo; have hhi := F.spHi
  have hfr : ∀ a : Word, InFrame g a → ¬ InSlot g o a → m''.mem a = m'.mem a :=
    fun a h1 h3 => hso2 a fun h => h3 ((hW a h).2 h1)
  refine ⟨⟨hpre, hn, fun a ha => ?_, hp.trans hrun, ?_, ?_, ?_, ?_, ?_⟩, hfr⟩
  · rw [hso2 a fun h => ha (hW a h).1, hso a ha]
  · intro q hq t ht
    rw [hfr _ ?_ ?_, hS q hq t ht]
    all_goals simp only [InFrame, InSlot]
    all_goals rw [fb_add F, toNat_ofNat_lt (by simp [Layout.ramHi] at hhi; omega)]
    · constructor <;> omega
    · omega
  · rw [hcs 2 (by decide), h2]
  · rw [hcs 8 (by decide), h8]
  · rw [hcs 9 (by decide), h9]
  · intro i hi
    rw [hcs i (by simp [keepRegs, calleeSaved] at hi ⊢; omega), hkeep i hi]

/-- The memory a callee of `PreN need'` writes, with its stack below the frame and its result at
`fb + o`. -/
theorem written_callee {g m' : Machine} (hk : Keep g m') {need' o : Nat}
    (hneed : need' + 0xa0 ≤ progNeed g) (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 o)
    (ho : o + 32 ≤ 0xa0) :
    ∀ a, WrittenN need' m' a → WrittenN (progNeed g) g a ∧ (InFrame g a → InSlot g o a) := by
  obtain ⟨hpre, -, -, -, -, h2, -⟩ := hk
  have F := PreFacts.of hpre.2
  have hlo := F.spLo; have hhi := F.spHi
  have hfb := fb_toNat F
  have hout : (m'.reg 10).toNat = (g.reg 2).toNat - 0xa0 + o := by
    rw [r10]; exact fb_add_toNat F (by omega)
  have hst : (m'.reg 2 - BitVec.ofNat 64 need').toNat = (g.reg 2).toNat - 0xa0 - need' := by
    rw [h2, BitVec.toNat_sub, hfb]; simp [Layout.ramLo] at hlo ⊢; omega
  intro a h
  rcases h with h | h | h | h
  · simp only [InRange, hst] at h
    exact ⟨written_stack F (by omega) (by omega), fun h1 => by omega⟩
  · simp only [InRange, outOf, hout] at h
    exact ⟨written_stack F (by omega) (by omega), fun _ => h⟩
  · refine ⟨.inr (.inr (.inl h)), fun h1 => ?_⟩
    have := F.dSB
    simp only [InRange, show (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump from rfl] at h
    omega
  · refine ⟨.inr (.inr (.inr h)), fun h1 => ?_⟩
    have := F.dSS
    simp only [InRange, show (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams from rfl] at h
    omega

/-- The chunks a callee reads are unchanged since the entry. -/
theorem chunks_same {g m' : Machine} (hpre : ProgPre g)
    (hso : SameOutside (WrittenN (progNeed g) g) g m') {s n' : Nat} (hsn : s + n' ≤ lenOf g) :
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

set_option maxHeartbeats 400000 in
/-- `PreN need'` for a callee with its stack below the frame, its result at `fb + o`, and the
chunks `[s, s + n')` of the caller's. -/
theorem callee_pre {g m' : Machine} (hk : Keep g m') (hra : RetAligned m') {need' o s n' : Nat}
    (hneed : need' + 0xa0 ≤ progNeed g) (r10 : m'.reg 10 = fb g + BitVec.ofNat 64 o)
    (ho : o + 32 ≤ 0xa0) (r11 : m'.reg 11 = chunkPtr g + BitVec.ofNat 64 (32 * s))
    (r12 : lenOf m' = n') (hsn : s + n' ≤ lenOf g) : PreN need' m' := by
  obtain ⟨hpre, -, -, hp, -, r2, -⟩ := hk
  have F := PreFacts.of hpre.2
  have hlo := F.spLo; have hhi := F.spHi; have h16 := F.sp16
  have hfb := fb_toNat F
  have hlo' : Layout.ramLo = 0xa0000000 := rfl
  have hhi' : Layout.ramHi = 0xc0000000 := rfl
  have hbump : Sha256.bump = 0xa05340b8 := rfl
  have hstage : Layout.extraParams = 0xa0000f00 := rfl
  have hc : (m'.reg 11).toNat = (chunkPtr g).toNat + 32 * s := by
    rw [r11]; exact chunk_toNat F (by omega)
  have hout : (m'.reg 10).toNat = (g.reg 2).toNat - 0xa0 + o := by
    rw [r10]; exact fb_add_toNat F (by omega)
  have hst : (m'.reg 2 - BitVec.ofNat 64 need').toNat = (g.reg 2).toNat - 0xa0 - need' := by
    rw [r2, BitVec.toNat_sub, hfb]; simp [Layout.ramLo] at hlo ⊢; omega
  have hlen : 32 * lenOf m' = 32 * n' := by rw [r12]
  refine ⟨ro_of F hp, ⟨?_, ?_, ?_, ?_⟩, hra, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r2, hfb]; omega
  · rw [r2, hfb]; omega
  · rw [r2, hfb]; omega
  · intro j hj
    have : m'.reg 2 - BitVec.ofNat 64 need' + BitVec.ofNat 64 j =
        BitVec.ofNat 64 ((g.reg 2).toNat - 0xa0 - need' + j) := by
      rw [← hst, ofNat_toNat_add]
    rw [this]; exact hp.1 _ (stack_present F (by omega) (by omega))
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

/-! ## The callees' stacks -/

theorem sub_sz (g : Machine) : lenOf g - sz g = lenOf g - pw g := by
  unfold sz; omega

theorem sz_le (g : Machine) : sz g ≤ lenOf g := by unfold sz; omega

/-- `sparseRoot` at the caller's depth fits below the frame. -/
theorem need_sparse {g : Machine} (hn : lenOf g ≠ 0) {m' : Machine} (r13 : depthOf m' = depthOf g) :
    sparseNeed m' + 0xa0 ≤ progNeed g := by
  rw [need_ne hn]; unfold sparseNeed; rw [r13]; omega

/-- The recursive call fits below the frame. -/
theorem need_prog {g : Machine} (hn : lenOf g ≠ 0) {m' : Machine}
    (r12 : lenOf m' = lenOf g - sz g) (r13 : depthOf m' = depthOf g + 2) :
    progNeed m' + 0xa0 ≤ progNeed g := by
  rw [need_ne hn]; unfold progNeed; rw [r12, r13, sub_sz]; omega

/-- The rest of the chunks, as the recursive call reads them. -/
theorem drop_eq (g : Machine) :
    (ch g).drop (pw g) = chunksOf g (chunkPtr g + BitVec.ofNat 64 (32 * sz g)) (lenOf g - sz g) := by
  by_cases h : pw g ≤ lenOf g
  · rw [chunksOf_drop, show sz g = pw g by unfold sz; omega]
  · rw [show lenOf g - sz g = 0 by unfold sz; omega, List.drop_eq_nil_of_le (by
      rw [chunksOf_length]; omega)]
    rfl

end ZesuExec.Fn.SszRoot.Prog
