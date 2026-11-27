import ZesuExec.Fn.TX.Finish

/-!
# TX: room for the next key (`0x800001f8`, leaf 1)

`ensureTotalCapacity(K, ao, n + 1)` (F1) returned 0: the keys list `K` holds the keys so far
(F1's `f1_spec_keep` on the no-growth branch, its grown buffer otherwise) and has room for one
more. The leaf stores the new length `n + 1` into `K` and loads the key's slot and words for the
key store `0x80000230`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- `InEntry` carries over to a machine that keeps its bytes and registers, with the live list
the new machine has and a possibly moved keys buffer `{q, c}`. -/
theorem ie_same {σ : Sig} {mc m : Machine} {o : Obs} {k k0 : Kobs} {L L' : List (Word × Nat)}
    {kp' q c : Word} (h : InEntry σ mc o k L) (hcm : Common σ m)
    (hl : Live σ m L' (EX o ++ KX { k with kq := q, kc := c }))
    (hr : ∀ i ∈ ([20, 21, 26, 27] : List (Fin 32)), m.reg i = mc.reg i)
    (hs : EDSame σ o k0 kp' mc m) : InEntry σ m o { k with kq := q, kc := c } L' := by
  obtain ⟨-, hok, ⟨r20, r21, hi, hmag⟩, hEL, -, ⟨hd, hle, r26⟩, ⟨had, hal, hA⟩, hkl, r27⟩ := h
  have l0 := hs.slot (0x1f0, 8) (by simp)
  have l1 := hs.slot (0x1c0, 24) (by simp)
  have l2 := hs.slot (0x158, 20) (by simp)
  obtain ⟨hH, hle', hp0, hc0, hc32, hram', hil, hbytes, hz⟩ := hEL
  refine ⟨hcm, ⟨hok.1, hok.2.1, ?_, ?_, hok.2.2.2.2⟩,
    ⟨(hr 20 (by decide)).trans r20, (hr 21 (by decide)).trans r21, hi,
      (load_congr fun t ht => l0 t ht).trans hmag⟩,
    ⟨hdr_congr hH l1, hle', hp0, hc0, hc32, hram', hil, ?_, fun x hx => ?_⟩,
    hl, ⟨hd, hle, (hr 26 (by decide)).trans r26⟩,
    ⟨had, hal, bytes_congr hA fun t ht => l2 t (by
      simp only [itemPayload, List.length_take] at ht; omega)⟩, hkl,
    (hr 27 (by decide)).trans r27⟩
  · rw [load_congr fun t ht => hs.rest t (by omega)]; exact hok.2.2.1
  · rw [load_congr (m := mc) fun t ht => by
      rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact hs.rest _ (by omega)]
    exact hok.2.2.2.1
  · rcases Nat.eq_zero_or_pos o.ec.toNat with he | he
    · have : o.done = [] := List.eq_nil_of_length_eq_zero (by omega)
      have : o.is = [] := List.eq_nil_of_length_eq_zero (by rw [hil, this]; rfl)
      intro i hi; simp [entriesBytes, *] at hi
    · have hlen := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
      refine bytes_congr hbytes fun t ht => hs.blk (o.ep, entrySize * o.ec.toNat)
        (List.mem_append_left _ (by simp [EX, he])) t ?_
      rw [hlen] at ht
      exact Nat.lt_of_lt_of_le ht (Nat.mul_le_mul_left _ hle')
  · obtain ⟨hpad, haddr, hkl', hkram, hkb'⟩ := hz x hx
    refine ⟨hpad, haddr, hkl', hkram, ?_⟩
    by_cases hk : x.1.keys = []
    · rw [hk]; intro i hi; simp at hi
    · exact bytes_congr hkb' fun t ht => hs.blk _ (List.mem_append_left _ (by
          simp only [EX, List.mem_append]; exact .inr (mem_keysBlocks hx hk))) t
        (by rw [flatten_length _ hkl'] at ht; exact ht)

/-- After `ensureTotalCapacity` returned 0: the keys loop's state with the keys buffer
`{kq, kc}` (moved if it grew) holding the keys so far and room for one more. -/
theorem after1f8 {σ : Sig} {m : Machine} (h : ARet f1C Site1f4 σ m)
    (hz : (m.reg 10 <<< ((48#64).toNat % 64)) >>> ((48#64).toNat % 64) = 0) :
    ∃ o k L kh', InEntry σ m o k L ∧ KeysOk σ m o k ∧ KList σ m k k.keys.length ∧ k.j < k.kl ∧
      KeyOk σ m o k kh' ∧ k.keys.length + 1 ≤ k.kc.toNat := by
  have hm := (ret_1f8 h).1
  obtain ⟨mc, ⟨L, items⟩, ⟨o, k, kh', hIE, hx2, hKO, hKL, hj, hKY, ha⟩,
    ⟨⟨hret, hso, hbr⟩, hkeep⟩, hp⟩ := h
  dsimp only at hIE hx2 hso hbr hkeep
  subst hx2
  have hc := hIE.1
  have hpre := hc.2.1
  have hlive := hIE.2.2.2.2.1
  have hhdr : mc.reg 10 = σ.sl 0x118 := ha.arg 0 (by simp)
  have hreq : mc.reg 12 = w (k.keys.length + 1) := ha.arg 2 (by simp)
  obtain ⟨hH, hn, hq0, hc1, hc32, hram, hyl, hkb⟩ := hKL
  have hn32 : k.keys.length < 2 ^ 32 := by omega
  have hreqN : (mc.reg 12).toNat = k.keys.length + 1 := by
    rw [hreq]; simp only [w, BitVec.toNat_ofNat]; omega
  have hnN : (w k.keys.length).toNat = k.keys.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have e0 : F1.wordAt mc (mc.reg 10) = k.kq := by rw [hhdr]; exact f1w hH.1
  have e8 : F1.wordAt mc (mc.reg 10 + 8) = w k.keys.length := by rw [hhdr]; exact f1w hH.2.1
  have e16 : F1.wordAt mc (mc.reg 10 + 16) = k.kc := by rw [hhdr]; exact f1w hH.2.2
  have hsp : mc.reg 2 - 128 = σ.sl 704 := sp_sub hc 128
  rw [e0, e8, e16, hreqN, hhdr] at hbr
  rw [e0, e16, hreqN] at hkeep
  rw [e0, e16, hhdr, hsp] at hso
  -- what F1 may write
  have hKX : 0 < k.kc.toNat → (k.kq, keySize * k.kc.toNat) ∈ KX k := fun h0 => by simp [KX, h0]
  have hR4 : ∀ a, (InRange (σ.sl 0x118) 24 a ∨ InRange (σ.sl 704) 128 a ∨
      InRange (BitVec.ofNat 64 Layout.extraParams) 8 a ∨ σ.A.Priv L a ∨
      (0 < k.kc.toNat ∧ InRange k.kq (k.kc.toNat * F1.elemBytes) a)) →
      (InRange (σ.sl stackBytes) stackBytes a ∧
        ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20), (0xd8, 32)] :
          List (Nat × Nat)), ¬ InRange (σ.sl kn.1) kn.2 a) ∨
      InRange scratch 8 a ∨ σ.A.Priv L a ∨ ∃ c ∈ KX k, InRange c.1 c.2 a := by
    intro a ha
    rcases ha with h | h | h | h | ⟨hc0, h⟩
    · refine .inl ⟨sl_in_stack hpre (by decide) (by decide) h, fun kn hkn hin => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
      rcases hkn with rfl | rfl | rfl | rfl | rfl <;>
        exact sl_apart hpre (by decide) (by decide) (by decide) h hin
    · refine .inl ⟨sl_in_stack hpre (by decide) (by decide) h, fun kn hkn hin => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
      rcases hkn with rfl | rfl | rfl | rfl | rfl <;>
        exact sl_apart hpre (by decide) (by decide) (by decide) h hin
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨_, hKX hc0, by
        simpa [Nat.mul_comm, keySize, F1.elemBytes] using h⟩))
  have hR5 : ∀ a, (InRange (σ.sl 0x118) 24 a ∨ InRange (σ.sl 704) 128 a ∨
      InRange (BitVec.ofNat 64 Layout.extraParams) 8 a ∨ σ.A.Priv L a ∨
      (0 < k.kc.toNat ∧ InRange k.kq (k.kc.toNat * F1.elemBytes) a)) →
      (InRange (σ.sl stackBytes) stackBytes a ∧
        ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20)] : List (Nat × Nat)),
          ¬ InRange (σ.sl kn.1) kn.2 a) ∨
      InRange scratch 8 a ∨ σ.A.Priv L a ∨ ∃ c ∈ KX k, InRange c.1 c.2 a := fun a ha =>
    (hR4 a ha).imp_left fun h => ⟨h.1, fun kn hkn => h.2 kn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn ⊢
      rcases hkn with h | h | h | h <;> simp [h])⟩
  have hlive0 : Live σ mc L (EX o ++ KD { k with keys := [] } 0 ++ KX k) := by
    have : KD { k with keys := [] } 0 = [] := by simp [KD]
    rw [this, List.append_nil]; exact hlive
  have hS := edsame_of hpre hlive0 hso hR5
  -- the key's copy at `S-0xd8`
  have hkey : BytesAt m (σ.sl 0xd8) (itemPayload (kwin σ o k) kh' keySize) := by
    have h3 := sl_toNat hpre (k := 0xd8) (by decide)
    have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
    refine bytes_congr hKY.2.2.1 fun t ht => hso _ fun hr => ?_
    have ht' : t < 32 := by simp only [itemPayload, List.length_take] at ht; unfold keySize at ht; omega
    have hin : InRange (σ.sl 0xd8) 32 (σ.sl 0xd8 + BitVec.ofNat 64 t) :=
      in_self (by rw [h3]; omega) ht'
    have hst := sl_in_stack hpre (by decide) (by decide) hin
    rcases hR4 _ hr with ⟨-, hs⟩ | h | h | ⟨c, hc', h⟩
    · exact hs (0xd8, 32) (by simp) hin
    · exact scratch_not_stack hpre h hst
    · exact stack_not_priv hpre hst (priv_sub hpre hlive h)
    · exact stack_not_priv hpre hst ((hlive.2.2 c (List.mem_append_right _ hc')).2.2 _ h)
  have hreg : ∀ i ∈ ([20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)), m.reg i = mc.reg i :=
    fun i hi => hret.2 i (by revert hi; revert i; decide)
  have hKO' : KeysOk σ m o k := ⟨hKO.1, (hreg 23 (by decide)).trans hKO.2.1,
    (hreg 22 (by decide)).trans hKO.2.2.1, (hreg 24 (by decide)).trans hKO.2.2.2⟩
  have hKY' : KeyOk σ m o k kh' := ⟨hKY.1, hKY.2.1, hkey, (hreg 25 (by decide)).trans hKY.2.2.2⟩
  have hr4 : ∀ i ∈ ([20, 21, 26, 27] : List (Fin 32)), m.reg i = mc.reg i :=
    fun i hi => hreg i (by revert hi; revert i; decide)
  split at hbr
  · -- no growth: the same buffer
    rename_i hle
    obtain ⟨-, hH', hheap, -⟩ := hbr
    have hl : Live σ m L (EX o ++ KX { k with kq := k.kq, kc := k.kc }) :=
      ⟨hheap, hlive.2.1, hlive.2.2⟩
    exact ⟨o, k, L, kh', ie_same hIE hm hl hr4 hS, hKO', ⟨hH', hn, hq0, hc1, hc32,
      hram, hyl, hkeep hle⟩, hj, hKY', hle⟩
  · rename_i hlt
    rcases hbr with ⟨-, p', hH', hp', hR', hB', hheap', -⟩ | ⟨h2, -⟩
    rotate_left
    · rw [h2] at hz; exact absurd hz (by decide)
    -- growth: the new buffer `p'` of `G` keys
    have hRam := hR'; unfold RamRange Layout.ramHi at hRam
    have hG32 : F1.grown (k.keys.length + 1) < 2 ^ 32 := by
      simp only [F1.elemBytes] at hRam; omega
    have hGn : (w (F1.grown (k.keys.length + 1))).toNat = F1.grown (k.keys.length + 1) := by
      simp only [w, BitVec.toNat_ofNat]; omega
    have hGpos : 0 < F1.grown (k.keys.length + 1) := by unfold F1.grown; omega
    let k' : Kobs := { k with kq := p', kc := w (F1.grown (k.keys.length + 1)) }
    have hKX' : KX k' = [(p', keySize * F1.grown (k.keys.length + 1))] := by
      simp only [KX, k', hGn, hGpos, if_true]
    have hperm : ((if 0 < k.kc.toNat then L.erase (k.kq, k.kc.toNat * F1.elemBytes) else L) ++
        [(p', F1.grown (k.keys.length + 1) * F1.elemBytes)]).Perm (σ.g.L ++ (EX o ++ KX k')) := by
      rw [hKX', show F1.grown (k.keys.length + 1) * F1.elemBytes =
        keySize * F1.grown (k.keys.length + 1) by simp [Nat.mul_comm, keySize, F1.elemBytes],
        ← List.append_assoc]
      refine List.Perm.append_right _ ?_
      split
      · rename_i h0
        have hl1 : Live σ mc L (EX o ++ [(k.kq, keySize * k.kc.toNat)]) := by
          have : KX k = [(k.kq, keySize * k.kc.toNat)] := by simp [KX, h0]
          rw [← this]; exact hlive
        have := erase_perm hl1 (by show 0 < keySize * k.kc.toNat; unfold keySize; omega)
        rwa [show keySize * k.kc.toNat = k.kc.toNat * F1.elemBytes by
          simp [Nat.mul_comm, keySize, F1.elemBytes]] at this
      · rename_i h0
        have : KX k = [] := by simp [KX, h0]
        have hP := hlive.2.1; rwa [this, List.append_nil] at hP
    have hl : Live σ m _ (EX o ++ KX k') := live_of_heap hpre hheap' hperm fun b hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact (hlive.2.2 b (List.mem_append_left _ hb)).1
      · rw [hKX'] at hb; simp only [List.mem_singleton] at hb; subst hb
        show 0 < keySize * _; unfold keySize; omega
    have hGle : k.keys.length + 1 ≤ F1.grown (k.keys.length + 1) := by unfold F1.grown; omega
    refine ⟨o, k', _, kh', ie_same hIE hm hl hr4 hS, hKO', ⟨hH', ?_, ?_,
      fun h => absurd h (by rw [hGn]; omega), by rw [hGn]; exact hG32, fun _ => ?_, hyl, hB'⟩,
      hj, hKY', ?_⟩
    · show k.keys.length ≤ (w (F1.grown (k.keys.length + 1))).toNat; rw [hGn]; omega
    · exact hp'
    · show RamRange p' (keySize * (w (F1.grown (k.keys.length + 1))).toNat)
      rw [hGn, show keySize * F1.grown (k.keys.length + 1) =
        F1.grown (k.keys.length + 1) * F1.elemBytes by simp [Nat.mul_comm, keySize, F1.elemBytes]]
      exact hR'
    · show k.keys.length + 1 ≤ (w (F1.grown (k.keys.length + 1))).toNat; rw [hGn]; exact hGle

theorem TX.leaf_800001f8_1 :
    LeafGoal TX.plan TX.plan.cuts[8]! ((TX.plan.leaves 0x800001f8)[1]!) := by
  show LeafGoal TX.plan cut1f8 (run1f8_leaves[1]!)
  have hcs : (run1f8_leaves[1]!).conds = [SBool.eq (Sym.bin BinOp.srl
      (Sym.bin BinOp.sll (Sym.var 10) (Sym.lit 48)) (Sym.lit 48)) (Sym.lit 0)] := by decide
  have hsteps : (run1f8_leaves[1]!).S.steps - SBody.steps = 14 := by decide
  intro σ m hA hc
  have hcm := (ret_1f8 hA).1
  have hpre := hcm.2.1
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.bin BinOp.srl
      (Sym.bin BinOp.sll (Sym.var 10) (Sym.lit 48)) (Sym.lit 48)) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have hz : (m.reg 10 <<< ((48#64).toNat % 64)) >>> ((48#64).toNat % 64) = 0 := by
    simpa [SBool.eval, Sym.eval, BinOp.eval, envB_var] using h1
  obtain ⟨o, k, L, kh', hie, hko, hkl, hj, hky, hroom⟩ := after1f8 hA hz
  refine ⟨nil_obligs (by decide), ?_, ?_⟩
  · show (run1f8_leaves[1]!).S.steps - SBody.steps ≤ 32 * (afterEntry m + keysLeft m) + 439
    rw [hsteps]; omega
  intro m' hm' hex hfr
  have hx : (run1f8_leaves[1]!).exit = .at 0x80000230 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x80000230 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  obtain ⟨hwf, hm, -⟩ := body_cut hcm
  have hwf' : Env.WF (envB σ m) (run1f8_leaves[1]!).S := hwf.congr (by decide)
  have hS : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 23, 25, 26, 27] : List (Fin 32)),
      (run1f8_leaves[1]!).S.reg i.val = SBody.reg i.val := by decide
  have hr := regs_keep hm hm' _ hS
  have reg : ∀ (i : Fin 32) (s : Sym), (run1f8_leaves[1]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have hlive := hie.2.2.2.2.1
  obtain ⟨hc', hlive', hp⟩ := base_leaf hcm hlive (BaseEnv.ofB σ m) hwf rfl hm' (by decide) hfr
    (by decide) fun i hi => hr i (by simp at hi ⊢; omega)
  have hso := frame_leaf_so hcm rfl hm' (by decide) hfr (by decide)
  have hmem : (run1f8_leaves[1]!).S.mem =
      [⟨0, 304, 8, .bin .add (.init 0 304 8) (.lit 1)⟩] := by decide
  have hW : ∀ a, (∃ wr ∈ (run1f8_leaves[1]!).S.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      InRange (σ.sl 0x110) 8 a := by
    rintro a ⟨wr, hwr, hin⟩
    rw [hmem] at hwr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwr
    subst hwr
    exact fr_in hpre (by decide) (by decide) (by decide) (by decide) hin
  have hap : ∀ {kk nn : Nat}, kk ≤ 704 → (0x110 + nn ≤ kk ∨ kk + 8 ≤ 0x110) →
      ∀ a, (∃ wr ∈ (run1f8_leaves[1]!).S.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
        ¬ InRange (σ.sl kk) nn a :=
    fun hkk hd a h hin => sl_apart hpre (by decide) (by unfold stackBytes; omega) hd (hW a h) hin
  have hst : ∀ a, (∃ wr ∈ (run1f8_leaves[1]!).S.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      InRange (σ.sl stackBytes) stackBytes a :=
    fun a h => sl_in_stack hpre (by decide) (by decide) (hW a h)
  -- `InEntry` with the keys list as it is
  have hlive0 : Live σ m L (EX o ++ KD { k with keys := [] } 0 ++ KX k) := by
    have : KD { k with keys := [] } 0 = [] := by simp [KD]
    rw [this, List.append_nil]; exact hlive
  have hS' := edsame_of hpre hlive0 hso fun a h => .inl ⟨hst a h, fun kn hkn => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
    rcases hkn with rfl | rfl | rfl | rfl <;> exact hap (by decide) (by decide) a h⟩
  have hie' : InEntry σ m' o { k with kq := k.kq, kc := k.kc } L :=
    ie_same hie hc' hlive' (fun i hi => hr i (by revert hi; revert i; decide)) hS'
  -- the keys list header: length `n + 1`
  obtain ⟨hH, hn, hq0, hc1, hc32, hram, hyl, hkb⟩ := hkl
  have hn32 : k.keys.length < 2 ^ 32 := by omega
  have hnN : (w k.keys.length).toNat = k.keys.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have e118 : σ.sl 0x118 + 8 = σ.sl 0x110 := by simp only [Sig.sl, w]; bv_omega
  have e108 : σ.sl 0x118 + 16 = σ.sl 0x108 := by simp only [Sig.sl, w]; bv_omega
  have i296 := frame_init hpre (m := m) (k := 0x118) (by decide) (by decide) hH.1
  have i304 := frame_init hpre (m := m) (k := 0x110) (by decide) (by decide)
    (by rw [← e118]; exact hH.2.1)
  simp only [show 576 - 0x118 = 296 from rfl, show 576 - 0x110 = 304 from rfl] at i296 i304
  have fl := frame_word (BaseEnv.ofB σ m) hwf' hm' (by decide) (k := 0x110) (by decide) (by decide)
  rw [show readConst (run1f8_leaves[1]!).S 0 (576 - 0x110) 8 =
    .bin .add (.init 0 304 8) (.lit 1) by decide] at fl
  simp only [Sym.eval_bin, BinOp.eval, i304, Sym.eval_lit] at fl
  have hH' : F1.HeaderIs m' (σ.sl 0x118) k.kq (w (k.keys.length + 1)) k.kc := by
    refine ⟨frame_keep hpre hso (k := 0x118) (by decide) (by decide)
        (fun a h hin => hap (by decide) (by decide) a h hin) hH.1, ?_, ?_⟩
    · rw [e118, fl]; simp only [w, BitVec.ofNat_add]
    · rw [e108]
      exact frame_keep hpre hso (k := 0x108) (by decide) (by decide)
        (fun a h hin => hap (by decide) (by decide) a h hin) (by rw [← e108]; exact hH.2.2)
  have hk0 : 0 < k.kc.toNat := by omega
  have hkl' : KList σ m' k (k.keys.length + 1) := ⟨by simpa using hH', hn, hq0, hc1, hc32, hram,
    hyl, bytes_keep_priv hpre hso hst hkb (block_priv hlive (p := k.kq)
      (n := keySize * k.kc.toNat) (by simp [EX, KX, hk0]) (hram hk0)
      (by rw [flatten_length _ hyl]; exact Nat.mul_le_mul_left _ hn))⟩
  -- the store's registers
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hkl64 : k.kl ≤ σ.len := by
    have := hie.2.1.2.1; have := hie.2.2.2.2.2.1.2.1; have := hie.2.2.2.2.2.2.2.1.2; omega
  have hkb2 := hky.2.1
  have r10 := reg 10 _ (by decide : (run1f8_leaves[1]!).S.reg 10 =
    .bin .add (.init 0 296 8) (.bin .sll (.init 0 304 8) (.lit 5)))
  simp only [Sym.eval_bin, BinOp.eval, i296, i304, Sym.eval_lit] at r10
  have r22 : m'.reg 22 = m.reg 22 - m.reg 25 := by
    rw [reg 22 _ (by decide : (run1f8_leaves[1]!).S.reg 22 = .bin .sub (.var 22) (.var 25))]
    exact congr (congrArg (· - ·) (envB_var σ m 22)) (envB_var σ m 25)
  have r24 := reg 24 _ (by decide : (run1f8_leaves[1]!).S.reg 24 =
    .bin .add (.init 0 304 8) (.lit 1))
  simp only [Sym.eval_bin, BinOp.eval, i304, Sym.eval_lit] at r24
  have hwd : ∀ t < 4, m'.load (σ.sl 0xd8 + w (8 * t)) 8 =
      some ((Sym.init 0 (360 + 8 * t) 8).eval (envB σ m)) := by
    intro t ht
    have e : σ.sl 0xd8 + w (8 * t) = σ.sl (0xd8 - 8 * t) := by
      obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
      all_goals simp only [Sig.sl, w]; bv_omega
    have hl := frame_load hcm (k := 0xd8 - 8 * t) (by omega) (by unfold frameBytes; omega)
    rw [e, frame_keep hpre hso (k := 0xd8 - 8 * t) (by omega) (by omega)
      (fun a h hin => hap (by omega) (by omega) a h hin) hl,
      show 360 + 8 * t = 576 - (0xd8 - 8 * t) by omega, frame_init hpre (by omega) (by omega) hl]
  have hregs : ∀ t < 4, m'.load (σ.sl 0xd8 + w (8 * t)) 8 = some (m'.reg (Fin.ofNat 32 (11 + t))) := by
    intro t ht
    rw [hwd t ht]
    obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    · rw [reg _ _ (by decide : (run1f8_leaves[1]!).S.reg (Fin.ofNat 32 (11 + 0)).val = .init 0 360 8)]
    · rw [reg _ _ (by decide : (run1f8_leaves[1]!).S.reg (Fin.ofNat 32 (11 + 1)).val = .init 0 368 8)]
    · rw [reg _ _ (by decide : (run1f8_leaves[1]!).S.reg (Fin.ofNat 32 (11 + 2)).val = .init 0 376 8)]
    · rw [reg _ _ (by decide : (run1f8_leaves[1]!).S.reg (Fin.ofNat 32 (11 + 3)).val = .init 0 384 8)]
  have hkey : BytesAt m' (σ.sl 0xd8) (itemPayload (kwin σ o k) kh' keySize) :=
    bytes_congr hky.2.2.1 fun t ht => hso _ fun h => hap (kk := 0xd8) (nn := 32) (by decide)
      (by decide) _ h (in_self (by
        have h3 := sl_toNat hpre (k := 0xd8) (by decide)
        have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo; rw [h3]; omega)
        (by simp only [itemPayload, List.length_take] at ht; unfold keySize at ht; omega))
  have hkr22 := hko.2.2.1
  have hkr25 := hky.2.2.2
  refine ExitGoal.at_cut rfl ⟨cut230, by simp [TX.plan, vcPlan], hex, ⟨hex, o, k, L, _, kh', hie',
    hko.1, hj, hky.1, hkb2, rfl, hkl', hroom, ?_, hkey, hregs, (hr 23 (by decide)).trans hko.2.1,
    ?_, (hr 25 (by decide)).trans hkr25, ?_⟩, ?_⟩
  · rw [r10, shl5 (by rw [hnN]; omega), hnN]; rfl
  · rw [r22, hkr22, hkr25, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by unfold keySize at *; omega)]
  · rw [r24]; simp only [w, BitVec.ofNat_add]
  · show 32 * (afterEntry m' + keysLeft m') + 744 ≤ 32 * (afterEntry m + keysLeft m) + 439 -
      ((run1f8_leaves[1]!).S.steps - SBody.steps)
    rw [hsteps]; unfold afterEntry keysLeft
    rw [hr 21 (by decide), hr 26 (by decide), r22, hkr22, hkr25,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by unfold keySize at *; omega)]
    simp only [w, BitVec.toNat_ofNat]
    unfold keySize at *; omega

end ZesuExec.Fn.TX
