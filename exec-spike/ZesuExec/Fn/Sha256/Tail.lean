import ZesuExec.Fn.Sha256.Loop

/-!
# `zkvm_sha256`: the tail (`0x800ea280` → `0x800ea2b8`)

From `TAt`: the 64 bytes at `sp + 0x28` zeroed (CSR `0x816`), the two slice-bound panics shown
unreachable, the remaining `r = n mod 64` input bytes copied there (CSR `0x813`, register count:
the count is staged at `Layout.extraParams`), the `r = 64` panic shown unreachable, and `0x80`
stored at `sp + 0x28 + r` by hand (the executor does not store at a symbolic offset). The result
is `PAt` at `0x800ea2b8`: the buffer at `sp + 0x28` is `Sha256.tailBuf msg`.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

/-- The input as `Pre` gives it: `n` bytes. -/
theorem msg_len {m0 : Machine} (hpre : Pre m0) : (msgOf m0).length = (m0.reg 11).toNat := by
  by_cases h0 : (m0.reg 11).toNat = 0
  · simp [msgOf, h0, readBytes]
  · exact (inNums hpre h0).len

/-- At `0x800ea2b8`, after the `0x80` marker. -/
structure PAt (m0 m : Machine) : Prop where
  pc : m.pc.toNat = 0x800ea2b8
  mid : Mid m0 m
  a1 : m.reg 11 = m0.reg 11
  st : FrameAt m 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64)))
  buf : FrameAt m 0x28 (Sha256.tailBuf (msgOf m0))
  a4 : m.reg 14 = BitVec.ofNat 64 ((m0.reg 11).toNat % 64)

theorem dst_frame {m0 m : Machine} (hn : Nums m0) (hmid : Mid m0 m) {lo len : Nat}
    (h : lo + len ≤ 0xe0) : dstOk m.mem ((spM m0).toNat + lo) len = true := by
  have := hn.lo; have := hn.hi
  simp only [dstOk, Bool.and_eq_true]
  refine ⟨by simp [writable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
  apply readBytes_isSome_of
  intro t ht
  rw [Nat.add_assoc, frame_ofNat, ← hmid.sp]
  exact hmid.frame _ (by unfold frameSize; omega)

/-- `csrsi 0x816, 2; addi zero, a5, 0x40; addi zero, a5, 0`: zero `sp + 0x28 .. + 0x68`. -/
theorem t_fill {m0 m : Machine} (hpre : Pre m0) (h : TAt m0 m) :
    ∃ m1, next zesuImage m = some (m1, 3) ∧ m1.pc.toNat = 0x800ea28c ∧ Mid m0 m1 ∧
      (∀ r, m1.reg r = m.reg r) ∧
      FrameAt m1 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64))) ∧
      FrameAt m1 0x28 (List.replicate 64 0) := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al
  have hd : (m.reg 15).toNat = (spM m0).toNat + 0x28 := by
    rw [h.a5]; exact frame_addr hn (by decide)
  have hn1 := next_816i (m := m) (w0 := 0x81616073) (w1 := 0x04078013) (w2 := 0x00078013) (b := 0)
    (by rw [h.pc]; decide) (by rw [h.pc]; decide +kernel) (by rw [h.pc]; decide +kernel)
    (by rw [h.pc]; decide +kernel) (by rw [h.pc]; decide +kernel) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show Decode.reg 0x04078013 15 = 15 by decide]; exact hd) (n := 64) (by decide)
    (dst_frame hn h.body.mid (by decide))
  obtain ⟨m1, hm1⟩ : ∃ x : Machine, x = { m with
      mem := fillMem m.mem ((spM m0).toNat + 0x28) 64 0, pc := m.pc + BitVec.ofNat 64 12 } :=
    ⟨_, rfl⟩
  rw [← hm1] at hn1
  have hsp1 : m1.reg 2 = spM m0 := by rw [hm1, mk_reg]; exact h.body.mid.sp
  subst hm1
  refine ⟨_, hn1, by simp only [BitVec.toNat_add, h.pc]; rfl, ?_, fun r => rfl, ?_, ?_⟩
  · refine mid_frame hn h.body.mid (fun r => rfl) (lo := 0x28) (len := 0x40) (by decide)
      (fun x hx => fill_out hx) ?_
    intro j hj
    show (fillMem _ _ _ _ _).isSome = true
    rw [← frame_ofNat, ← Nat.add_assoc, fill_in hj (by omega)]; rfl
  · exact frameAt_out (lo := 0x28) (len := 64) hn h.body.mid.sp hsp1 (fun x hx => fill_out hx) h.st
      (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
      (by left; simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
  · refine frameAt_of hsp1 fun t ht => ?_
    simp only [List.length_replicate] at ht
    show fillMem _ _ _ _ _ = _
    rw [fill_in ht (by omega), List.getElem_replicate]

/-- `Mid` across a step that keeps the registers, writes frame offsets `[lo, lo + len)` below
`0x78` and the staging word, leaving them present. -/
theorem mid_frame_st {m0 m m' : Machine} (hn : Nums m0) (hmid : Mid m0 m)
    (hreg : ∀ i, m'.reg i = m.reg i) {lo len : Nat} (hlo : lo + len ≤ 0x78)
    (hout : ∀ x : Word, ¬ ((spM m0).toNat + lo ≤ x.toNat ∧ x.toNat < (spM m0).toNat + lo + len) →
      ¬ (0xa0000f00 ≤ x.toNat ∧ x.toNat < 0xa0000f08) → m'.mem x = m.mem x)
    (hin : ∀ j < len, (m'.mem (spM m0 + BitVec.ofNat 64 (lo + j))).isSome)
    (hstg : ∀ j < 8, (m'.mem (stageW + BitVec.ofNat 64 j)).isSome) : Mid m0 m' := by
  have hsp : m'.reg 2 = spM m0 := by rw [hreg, hmid.sp]
  have hfa := fun j (hj : j < 0xe0) => frame_addr hn hj
  have := hn.hi; have := hn.fb; have := hn.fs
  refine ⟨hsp, by rw [hreg, hmid.out], fun p hp => by rw [hreg, hmid.saved p hp], ?_, ?_, ?_, ?_,
    hstg⟩
  · intro x hx
    have hx' := hx
    simp only [WrittenMid, InRange, frameSize, stageW, Layout.extraParams, BitVec.toNat_ofNat,
      not_or, not_and, Nat.not_lt] at hx'
    rw [hout x (by omega) (by omega), hmid.same x hx]
  · intro j hj
    rw [hsp]
    unfold frameSize at hj
    by_cases hc : lo ≤ j ∧ j < lo + len
    · have := hin (j - lo) (by omega)
      rwa [show lo + (j - lo) = j by omega] at this
    · rw [hout _ (by rw [hfa j hj]; omega) (by rw [hfa j hj]; omega), ← hmid.sp]
      exact hmid.frame j (by unfold frameSize; omega)
  · intro p hp i hi
    have hoff := savedRegs_off p hp
    have hi8 : i < 8 := by rw [le8_length] at hi; exact hi
    rw [hsp, hout _ (by rw [hfa _ (by omega)]; omega) (by rw [hfa _ (by omega)]; omega), ← hmid.sp]
    exact hmid.savedMem p hp i hi
  · intro i hi
    have hi16 : i < 16 := by simpa [bumpBytes] using hi
    have hx : (bumpW + BitVec.ofNat 64 i).toNat = 0xa05340b8 + i := by
      rw [BitVec.toNat_add]; simp [bumpW, bump]; omega
    rw [hout _ (by rw [hx]; omega) (by rw [hx]; omega)]; exact hmid.bump i hi

/-- `csrs 0x813, a3; add zero, a0, a4`: the remaining `r` input bytes to `sp + 0x28`. -/
theorem t_copy {m0 m : Machine} (hpre : Pre m0) (hmid : Mid m0 m) (hpc : m.pc.toNat = 0x800ea29c)
    (h13 : m.reg 13 = m0.reg 10 + BitVec.ofNat 64 (64 * ((m0.reg 11).toNat / 64)))
    (h10 : m.reg 10 = spM m0 + 0x28) (h14 : m.reg 14 = BitVec.ofNat 64 ((m0.reg 11).toNat % 64))
    {ST : List Byte} (hst : FrameAt m 8 ST) (hSTl : ST.length = 32)
    (hz : FrameAt m 0x28 (List.replicate 64 0)) :
    ∃ m1, next zesuImage m = some (m1, 2) ∧ m1.pc.toNat = 0x800ea2a4 ∧ Mid m0 m1 ∧
      (∀ r, m1.reg r = m.reg r) ∧ FrameAt m1 8 ST ∧
      FrameAt m1 0x28 ((msgOf m0).drop (64 * ((m0.reg 11).toNat / 64)) ++
        List.replicate (64 - (m0.reg 11).toNat % 64) 0) := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al; have := hn.fs
  have hlen := msg_len hpre
  obtain ⟨k, hk⟩ : ∃ k, (m0.reg 11).toNat / 64 = k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, (m0.reg 11).toNat % 64 = r := ⟨_, rfl⟩
  have hdm : 64 * k + r = (m0.reg 11).toNat := by rw [← hk, ← hr]; exact Nat.div_add_mod _ 64
  have hr64 : r < 64 := by rw [← hr]; exact Nat.mod_lt _ (by decide)
  rw [hk] at h13; rw [hr] at h14; rw [hk, hr]
  have hd : (m.reg 10).toNat = (spM m0).toNat + 0x28 := by rw [h10]; exact frame_addr hn (by decide)
  have hc : (m.reg 14).toNat = r := by rw [h14, BitVec.toNat_ofNat]; omega
  have hinb : r ≠ 0 → InNums m0 := fun h => inNums hpre (by omega)
  have hs : r ≠ 0 → (m.reg 13).toNat = (m0.reg 10).toNat + 64 * k := fun h => by
    have hi := hinb h; have := hi.hi
    rw [h13, toNat_add_ofNat (by omega)]
  have hframe : ∀ j < 0xe0, (m.mem (BitVec.ofNat 64 ((spM m0).toNat + j))).isSome := fun j hj => by
    rw [frame_ofNat, ← hmid.sp]; exact hmid.frame j (by unfold frameSize; omega)
  have hdom : dmaMemcpyDomain m.mem (m.reg 10).toNat (m.reg 13).toNat (m.reg 14).toNat = true := by
    simp only [dmaMemcpyDomain, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨by decide, ?_⟩, ?_⟩
    · apply readBytes_isSome_of
      intro t ht
      have := hmid.stage t ht
      rwa [show stageW + BitVec.ofNat 64 t = BitVec.ofNat 64 (Layout.extraParams + t) by
        rw [← ofNat_toNat_add]; rfl] at this
    · rw [hc]
      by_cases h0 : r = 0
      · left; exact h0
      right
      have hi := hinb h0
      have := hi.hi; have := hi.lo
      rw [hs h0, hd]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · have := hi.inR
        simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          Layout.rodataLo, Layout.rodataHi, Layout.inputLo, Layout.inputHi, Layout.ramLo,
          Layout.ramHi] at this ⊢
        omega
      · apply readBytes_isSome_of
        intro t ht
        rw [Nat.add_assoc, input_at hn hi hmid (64 * k + t) (by omega)]; rfl
      · simp [writable, inRange, Layout.ramLo, Layout.ramHi]; omega
      · exact readBytes_isSome_of fun t ht => by rw [Nat.add_assoc]; exact hframe _ (by omega)
  have hn1 := next_813r (m := m) (w0 := 0x8136a073) (w1 := 0x00e50033)
    (by rw [hpc]; decide) (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
    (by rw [hpc]; decide +kernel) (by decide) (by decide)
    (by
      rw [show Decode.reg 0x00e50033 15 = 10 by decide, show Decode.reg 0x8136a073 15 = 13 by decide,
        show Decode.reg 0x00e50033 20 = 14 by decide]
      exact hdom)
  rw [show Decode.reg 0x00e50033 15 = 10 by decide, show Decode.reg 0x8136a073 15 = 13 by decide,
    show Decode.reg 0x00e50033 20 = 14 by decide] at hn1
  obtain ⟨m1, hm1⟩ : ∃ x : Machine, x = { m with
      mem := dmaMemcpyMem m.mem (m.reg 10).toNat (m.reg 13).toNat (m.reg 14), pc := m.pc + 8 } :=
    ⟨_, rfl⟩
  rw [← hm1] at hn1
  have hsp1 : m1.reg 2 = spM m0 := by rw [hm1, mk_reg]; exact hmid.sp
  have hmem1 : ∀ x : Word, m1.mem x = dmaMemcpyMem m.mem (m.reg 10).toNat (m.reg 13).toNat
      (m.reg 14) x := fun x => by rw [hm1]
  -- outside the copy and the staging word, memory is unchanged
  have hout : ∀ x : Word, ¬ ((spM m0).toNat + 0x28 ≤ x.toNat ∧ x.toNat < (spM m0).toNat + 0x28 + r) →
      ¬ (0xa0000f00 ≤ x.toNat ∧ x.toNat < 0xa0000f08) → m1.mem x = m.mem x := by
    intro x hx hxs
    rw [hmem1]
    simp only [dmaMemcpyMem, hc, hd, Layout.extraParams]
    rw [if_neg (by omega), if_neg hxs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hstg : ∀ j < 8, (m1.mem (stageW + BitVec.ofNat 64 j)).isSome := by
    intro j hj
    have hx : (stageW + BitVec.ofNat 64 j).toNat = 0xa0000f00 + j := by
      rw [BitVec.toNat_add]; simp [stageW, Layout.extraParams]; omega
    rw [hmem1]
    simp only [dmaMemcpyMem, hc, hd, Layout.extraParams, hx]
    rw [if_neg (by omega), if_pos (by omega)]; rfl
  -- the copied bytes
  have hin : ∀ t (ht : t < r), m1.mem (BitVec.ofNat 64 ((spM m0).toNat + 0x28 + t)) =
      some ((msgOf m0)[64 * k + t]'(by omega)) := by
    intro t ht
    have hi := hinb (by omega)
    have := hi.hi; have := hi.df; have := hi.ds
    rw [hmem1]
    simp only [dmaMemcpyMem, hc, hd, hs (by omega), Layout.extraParams, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), if_pos (by omega), if_neg (by omega),
      show (m0.reg 10).toNat + 64 * k + ((spM m0).toNat + 0x28 + t) - ((spM m0).toNat + 0x28) =
        (m0.reg 10).toNat + (64 * k + t) by omega]
    exact input_at hn hi hmid _ _
  have hDl : ((msgOf m0).drop (64 * k)).length = r := by simp [hlen]; omega
  refine ⟨m1, hn1, by rw [hm1]; simp only [BitVec.toNat_add, hpc]; rfl, ?_,
    fun r => by rw [hm1, mk_reg], ?_, ?_⟩
  · refine mid_frame_st hn hmid (fun r => by rw [hm1, mk_reg]) (lo := 0x28) (len := r)
      (by omega) hout ?_ hstg
    intro j hj
    rw [← frame_ofNat, ← Nat.add_assoc, hin j hj]; rfl
  · intro t ht
    rw [hSTl] at ht
    rw [hsp1, ← frame_ofNat, hout _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), frame_ofNat, ← hmid.sp]
    exact hst t (by omega)
  · refine frameAt_of hsp1 fun t ht => ?_
    simp only [List.length_append, List.length_replicate, hDl] at ht
    by_cases htr : t < r
    · rw [hin t htr, List.getElem_append_left (by omega)]; simp
    · rw [hout _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        List.getElem_append_right (by omega)]
      have := hz (t) (by simp; omega)
      rw [hmid.sp, ← frame_ofNat, ← Nat.add_assoc] at this
      rw [this, List.getElem_replicate, List.getElem_replicate]

/-- `sb a3, 0(a0)` with `a0 = sp + 0x28 + r`, `a3 = 0x80`, by hand. -/
theorem t_sb {m0 m : Machine} (hn : Nums m0) (hmid : Mid m0 m) (hpc : m.pc.toNat = 0x800ea2b4)
    {r : Nat} (hr : r < 64) (h10 : m.reg 10 = spM m0 + 0x28 + BitVec.ofNat 64 r)
    (h13 : m.reg 13 = 0x80) {L : List Byte} (hL : L.length = 64) (hb : FrameAt m 0x28 L) :
    ∃ m1, next zesuImage m = some (m1, 1) ∧ m1.pc.toNat = 0x800ea2b8 ∧ Mid m0 m1 ∧
      (∀ r, m1.reg r = m.reg r) ∧ FrameAt m1 0x28 (L.set r 0x80) ∧
      (∀ x : Word, ¬ (x.toNat = (spM m0).toNat + 0x28 + r) → m1.mem x = m.mem x) := by
  have := hn.lo; have := hn.hi; have := hn.al
  have ha : (m.reg 10 + Machine.sx (0 : BitVec 12)).toNat = (spM m0).toNat + 0x28 + r := by
    have h0 : Machine.sx (0 : BitVec 12) = 0 := by decide
    simp only [h10, h0, BitVec.add_zero]
    have h40 : (spM m0 + 40).toNat = (spM m0).toNat + 40 := frame_addr hn (j := 40) (by decide)
    rw [BitVec.toNat_add, BitVec.toNat_add, h40, BitVec.toNat_ofNat]; simp
    omega
  obtain ⟨m1, hm1⟩ : ∃ x : Machine, x = { m with
      mem := writeBytes m.mem ((spM m0).toNat + 0x28 + r) (m.reg 13) 1, pc := m.pc + 4 } := ⟨_, rfl⟩
  have hn1 : next zesuImage m = some (m1, 1) := by
    refine next_exec (i := .sb 10 13 0) (by rw [hpc]; decide) (by rw [hpc]; decide +kernel) ?_
    show m.storeFrom 10 13 0 1 = _
    rw [exec_store (by rw [ha]; simp [writable, inRange, Layout.ramLo, Layout.ramHi]; omega) (by
      rw [ha]
      apply readBytes_isSome_of
      intro t ht
      rw [Nat.add_assoc, Nat.add_assoc, frame_ofNat, ← hmid.sp]
      exact hmid.frame _ (by unfold frameSize; omega)), ha, hm1]
  have hout : ∀ x : Word, ¬ (x.toNat = (spM m0).toNat + 0x28 + r) → m1.mem x = m.mem x := by
    intro x hx; rw [hm1]; exact writeBytes_out (by omega) (by omega)
  have hat : m1.mem (BitVec.ofNat 64 ((spM m0).toNat + 0x28 + r)) = some 0x80 := by
    rw [hm1]; show writeBytes _ _ _ _ _ = _
    rw [writeBytes_apply (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      if_pos (by omega), h13, Nat.sub_self]; rfl
  have hsp1 : m1.reg 2 = spM m0 := by rw [hm1, mk_reg]; exact hmid.sp
  refine ⟨m1, hn1, by rw [hm1]; simp only [BitVec.toNat_add, hpc]; rfl, ?_,
    fun r => by rw [hm1, mk_reg], ?_, hout⟩
  · refine mid_frame hn hmid (fun r => by rw [hm1, mk_reg]) (lo := 0x28 + r) (len := 1) (by omega)
      (fun x hx => hout x (by omega)) ?_
    intro j hj
    rw [show j = 0 by omega, ← frame_ofNat, show (spM m0).toNat + (0x28 + r + 0) =
      (spM m0).toNat + 0x28 + r by omega, hat]; rfl
  · refine frameAt_of hsp1 fun t ht => ?_
    rw [List.length_set] at ht
    by_cases htr : t = r
    · subst htr; rw [hat, List.getElem_set_self]
    · rw [hout _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        List.getElem_set_ne (Ne.symm htr)]
      have := hb t (by omega)
      rw [hmid.sp, ← frame_ofNat, ← Nat.add_assoc] at this
      exact this

/-- The buffer after the marker store is `Sha256.tailBuf`. -/
theorem set_tail (D : List Byte) (hD : D.length < 64) :
    (D ++ List.replicate (64 - D.length) 0).set D.length 0x80 =
      D ++ [0x80] ++ List.replicate (63 - D.length) 0 := by
  rw [show 64 - D.length = (63 - D.length) + 1 by omega, List.replicate_succ,
    List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
  simp

sym_run runT1 := run zesuImage [0x800ea29c, 0x800ea514, 0x800ea528] 20 0x800ea28c SM
sym_run runT2 := run zesuImage [0x800ea2b4, 0x800ea538] 20 0x800ea2a4 SM

theorem t1_facts : runT1_leaves = [runT1_leaves[0]!, runT1_leaves[1]!, runT1_leaves[2]!] ∧
    (runT1_leaves[0]!).conds = [.geu (.var 14) (.var 16)] ∧
    (runT1_leaves[1]!).conds = [.ltu (.var 14) (.var 16), .ltu (.var 11) (.var 13)] ∧
    keepsM (runT1_leaves[2]!).S = true ∧ (runT1_leaves[2]!).S.regions.length = 1 ∧
    (runT1_leaves[2]!).S.mem = [] ∧ (runT1_leaves[2]!).obligs = [] ∧
    (runT1_leaves[2]!).S.reg 10 = .ptr 0 40 ∧
    (runT1_leaves[2]!).S.reg 13 = .bin .add (.var 10) (.var 13) ∧
    (∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 10 → i.val ≠ 13 →
      (runT1_leaves[2]!).S.reg i.val = if i.val = 0 then .lit 0 else .var i.val) := by decide

theorem t2_facts : runT2_leaves = [runT2_leaves[0]!, runT2_leaves[1]!] ∧
    (runT2_leaves[0]!).conds = [.eq (.var 14) (.lit 64)] ∧
    keepsM (runT2_leaves[1]!).S = true ∧ (runT2_leaves[1]!).S.regions.length = 1 ∧
    (runT2_leaves[1]!).S.mem = [] ∧ (runT2_leaves[1]!).obligs = [] ∧
    (runT2_leaves[1]!).S.reg 10 = .bin .add (.var 10) (.var 14) ∧
    (runT2_leaves[1]!).S.reg 13 = .lit 128 ∧
    (∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 10 → i.val ≠ 13 →
      (runT2_leaves[1]!).S.reg i.val = if i.val = 0 then .lit 0 else .var i.val) := by decide

/-- `0x800ea280` → `0x800ea2b8`. -/
theorem tail_p {m0 m : Machine} (hpre : Pre m0) (h : TAt m0 m) :
    ∃ m', RunsIn zesuImage 14 m m' ∧ PAt m0 m' := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al
  have hlen := msg_len hpre
  have hr64 : (m0.reg 11).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have hdm := Nat.div_add_mod (m0.reg 11).toNat 64
  have hSTl : (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64))).length = 32 :=
    Sha256.leBytes_length (Sha256.foldBlocks_length _ _)
  obtain ⟨m1, hn1, hpc1, hmid1, hreg1, hst1, hz1⟩ := t_fill hpre h
  have h14 : m1.reg 14 = BitVec.ofNat 64 ((m0.reg 11).toNat % 64) := by rw [hreg1]; exact h.a4
  have h16 : m1.reg 16 = 65 := by rw [hreg1]; exact h.a6
  have h11 : m1.reg 11 = m0.reg 11 := by rw [hreg1]; exact h.body.a1
  have h13 : m1.reg 13 = BitVec.ofNat 64 (64 * ((m0.reg 11).toNat / 64)) := by
    rw [hreg1]; exact h.a3
  have h10 : m1.reg 10 = m0.reg 10 := by rw [hreg1]; exact h.body.a0
  -- `bgeu a4, a6, panic; bltu a1, a3, panic; add a3, a0, a3; addi a0, sp, 0x28`
  obtain ⟨l, hl, hc, hr⟩ := segM runT1 hpre hmid1 (ro_mid hpre hn hmid1) hpc1
  obtain ⟨hls, hc0, hc1, hk2, hlen2, hmem2, hob2, hr10, hr13, hrk⟩ := t1_facts
  rw [hls] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exfalso
    have hcond := hc _ (by rw [hc0]; exact List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_var, envM_vars, Bool.not_eq_true', BitVec.ult,
      decide_eq_false_iff_not, Nat.not_lt] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, show (Fin.ofNat 32 16 : Fin 32) = 16 from rfl,
      h14, h16, BitVec.toNat_ofNat, show (65 : Word).toNat = 65 from rfl] at hcond
    omega
  · exfalso
    have hcond := hc (.ltu (.var 11) (.var 13)) (by rw [hc1]; simp)
    simp only [SBool.eval, Sym.eval_var, envM_vars, BitVec.ult, decide_eq_true_eq] at hcond
    rw [show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl, show (Fin.ofNat 32 13 : Fin 32) = 13 from rfl,
      h11, h13, BitVec.toNat_ofNat] at hcond
    have := BitVec.isLt (m0.reg 11)
    rw [Nat.mod_eq_of_lt (by omega)] at hcond
    omega
  obtain ⟨m2, hrun2, hm2, hex2, hso2⟩ := hr (fun o ho => by rw [hob2] at ho; simp at ho)
  have hmid2 := mid_leaf hn hmid1 hm2 hso2 hk2 hlen2
  have hk : ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 10 → i.val ≠ 13 → m2.reg i = m1.reg i :=
    fun i h2 h10 h13 => reg_kept hm2 (hrk i h2 h10 h13)
  have hsp2 : m2.reg 2 = m1.reg 2 := by rw [hmid2.sp, hmid1.sp]
  have hst2 := frameAt_leaf hm2 hsp2 hlen2 hst1 (by rw [hSTl]; decide)
    (fun t _ => by rw [hmem2]; rfl)
  have hz2 := frameAt_leaf hm2 hsp2 hlen2 hz1 (by simp)
    (fun t _ => by rw [hmem2]; rfl)
  have h2_10 : m2.reg 10 = spM m0 + 0x28 := by
    rw [reg_of_match hm2, show ((10 : Fin 32).val) = 10 from rfl, hr10]
    show m1.reg 2 + BitVec.ofInt 64 40 = _
    rw [hmid1.sp]; rfl
  have h2_13 : m2.reg 13 = m0.reg 10 + BitVec.ofNat 64 (64 * ((m0.reg 11).toNat / 64)) := by
    rw [reg_of_match hm2, show ((13 : Fin 32).val) = 13 from rfl, hr13]
    show m1.reg 10 + m1.reg 13 = _
    rw [h10, h13]
  -- `csrs 0x813, a3; add zero, a0, a4`
  obtain ⟨m3, hn3, hpc3, hmid3, hreg3, hst3, hb3⟩ := t_copy hpre hmid2 hex2 h2_13 h2_10
    (by rw [hk 14 (by decide) (by decide) (by decide), h14]) hst2 hSTl hz2
  -- `addi a3, zero, 0x40; beq a4, a3, panic; add a0, a0, a4; addi a3, zero, 0x80`
  obtain ⟨l, hl, hc, hr⟩ := segM runT2 hpre hmid3 (ro_mid hpre hn hmid3) hpc3
  obtain ⟨hls', hc0', hk1', hlen1', hmem1', hob1', hr10', hr13', hrk'⟩ := t2_facts
  have h3_14 : m3.reg 14 = BitVec.ofNat 64 ((m0.reg 11).toNat % 64) := by
    rw [hreg3, hk 14 (by decide) (by decide) (by decide), h14]
  rw [hls'] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · exfalso
    have hcond := hc _ (by rw [hc0']; exact List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, envM_vars, beq_iff_eq] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, h3_14] at hcond
    have := congrArg BitVec.toNat hcond
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    omega
  obtain ⟨m4, hrun4, hm4, hex4, hso4⟩ := hr (fun o ho => by rw [hob1'] at ho; simp at ho)
  have hmid4 := mid_leaf hn hmid3 hm4 hso4 hk1' hlen1'
  have hk4 : ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 10 → i.val ≠ 13 → m4.reg i = m3.reg i :=
    fun i h2 h10 h13 => reg_kept hm4 (hrk' i h2 h10 h13)
  have hsp4 : m4.reg 2 = m3.reg 2 := by rw [hmid4.sp, hmid3.sp]
  have hDl : ((msgOf m0).drop (64 * ((m0.reg 11).toNat / 64))).length = (m0.reg 11).toNat % 64 := by
    simp [hlen]; omega
  have hb4 := frameAt_leaf hm4 hsp4 hlen1' hb3 (by simp [hDl]; omega)
    (fun t _ => by rw [hmem1']; rfl)
  have hst4 := frameAt_leaf hm4 hsp4 hlen1' hst3 (by rw [hSTl]; decide)
    (fun t _ => by rw [hmem1']; rfl)
  have h4_10 : m4.reg 10 = spM m0 + 0x28 + BitVec.ofNat 64 ((m0.reg 11).toNat % 64) := by
    rw [reg_of_match hm4, show ((10 : Fin 32).val) = 10 from rfl, hr10']
    show m3.reg 10 + m3.reg 14 = _
    rw [hreg3, h2_10, h3_14]
  have h4_13 : m4.reg 13 = 0x80 := by
    rw [reg_of_match hm4, show ((13 : Fin 32).val) = 13 from rfl, hr13']; rfl
  -- `sb a3, 0(a0)`
  obtain ⟨m5, hn5, hpc5, hmid5, hreg5, hb5, hout5⟩ := t_sb hn hmid4 hex4 hr64 h4_10 h4_13
    (by simp [hDl]; omega) hb4
  rw [← hDl, set_tail _ (by rw [hDl]; exact hr64)] at hb5
  refine ⟨m5, RunsIn.step hn1 (hrun2.trans (RunsIn.step hn3 (hrun4.trans (RunsIn.step hn5 .refl)))),
    hpc5, hmid5, ?_, ?_, ?_, ?_⟩
  · rw [hreg5, hk4 11 (by decide) (by decide) (by decide), hreg3,
      hk 11 (by decide) (by decide) (by decide), h11]
  · exact frameAt_out (lo := 0x28 + (m0.reg 11).toNat % 64) (len := 1) hn hmid4.sp hmid5.sp
      (fun x hx => hout5 x (by omega)) hst4 (by rw [hSTl]; decide) (by left; rw [hSTl]; omega)
  · have htb : Sha256.tailBuf (msgOf m0) = (msgOf m0).drop (64 * ((m0.reg 11).toNat / 64)) ++
        [0x80] ++ List.replicate (63 - ((msgOf m0).drop (64 * ((m0.reg 11).toNat / 64))).length) 0 := by
      simp only [Sha256.tailBuf, hlen, hDl]
    rw [htb]; exact hb5
  · rw [hreg5, hk4 14 (by decide) (by decide) (by decide), h3_14]

end ZesuExec.Fn.Sha256
