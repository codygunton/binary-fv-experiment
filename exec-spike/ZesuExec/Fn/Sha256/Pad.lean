import ZesuExec.Fn.Sha256.Tail

/-!
# `zkvm_sha256`: the padding blocks (`0x800ea2b8` → `0x800ea394`)

From `PAt`: `a1 = 8 n` byte-reversed (`rev8`), its eight bytes stored big-endian at
`sp + 0x60 .. + 0x68`, and one compression (`n mod 64 ≤ 55`) or two (the buffer as it is, then
56 zeros and the length). `OAt` at `0x800ea394`: the state is `Sha256.finish msg` of the whole
blocks' state.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

/-- At `0x800ea394`, before the output. -/
structure OAt (m0 m : Machine) : Prop where
  pc : m.pc.toNat = 0x800ea394
  mid : Mid m0 m
  st : FrameAt m 8 (Sha256.leBytes (Sha256.finish (msgOf m0)
    (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64))))

theorem lenBytes_length (n : Nat) : (Sha256.lenBytes n).length = 8 := by simp [Sha256.lenBytes]

/-- Byte `k` of the big-endian bit length is byte `k` of `rev8 (8 n)`. -/
theorem len_byte (x : Word) (hx : x.toNat < 2 ^ 61) (k : Nat) (hk : k < 8) :
    byteOf (rev8 (x <<< 3) >>> (8 * k)) 0 =
      (Sha256.lenBytes x.toNat)[k]'(by rw [lenBytes_length]; exact hk) := by
  rw [byteOf_rev8_shift _ _ hk]
  simp only [Sha256.lenBytes, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range]
  apply BitVec.eq_of_toNat_eq
  simp only [byteOf, BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show x.toNat * 2 ^ 3 < 2 ^ 64 by omega),
    show 8 * (7 - k) = 8 * (8 - 1 - k) by omega, Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from rfl,
    show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_comm (x.toNat)]

/-- Frame bytes from byte stores of a piece. -/
theorem frameAt_stores {m m' : Machine} {S : SState} (hm' : Match (envM m) S m')
    (hsp : m'.reg 2 = m.reg 2) (hlen : S.regions.length = 1) {off : Nat} {L : List Byte}
    (hfit : off + L.length ≤ 0xe0)
    (h : ∀ t (ht : t < L.length), ∃ s, S.mem.find? (·.covers 0 (off + t)) = some ⟨0, off + t, 1, s⟩ ∧
      byteOf (s.eval (envM m)) 0 = L[t]) : FrameAt m' off L := by
  intro t ht
  obtain ⟨s, hf, hv⟩ := h t ht
  have := mem_of_find hm' (r := 0) (j := off + t) (by rw [hlen]; decide) (by show _ < 0xe0; omega) hf
  rw [show (envM m).base 0 = m.reg 2 from rfl] at this
  rw [hsp, this, Nat.sub_self, hv]

theorem frameAt_append {m : Machine} {off : Nat} {L1 L2 : List Byte} (h1 : FrameAt m off L1)
    (h2 : FrameAt m (off + L1.length) L2) : FrameAt m off (L1 ++ L2) := by
  intro t ht
  by_cases h : t < L1.length
  · rw [List.getElem_append_left h]; exact h1 t h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (t - L1.length) (by simp at ht; omega)
    rwa [show off + L1.length + (t - L1.length) = off + t by omega] at this

theorem frameAt_take {m : Machine} {off : Nat} {L : List Byte} (h : FrameAt m off L) (j : Nat) :
    FrameAt m off (L.take j) := fun t ht => by
  rw [List.getElem_take]; exact h t (by simp at ht; omega)

/-- An 8-byte store of a piece at frame offset `off`. -/
theorem frameAt_word {m m' : Machine} {S : SState} (hm' : Match (envM m) S m')
    (hsp : m'.reg 2 = m.reg 2) (hlen : S.regions.length = 1) {off : Nat} {s : Sym} {v : Word}
    (hfd : ∀ t < 8, S.mem.find? (·.covers 0 (off + t)) = some ⟨0, off, 8, s⟩) (hfit : off + 8 ≤ 0xe0)
    (hv : s.eval (envM m) = v) : FrameAt m' off (le8 v) := by
  intro t ht
  have ht8 : t < 8 := by rw [le8_length] at ht; exact ht
  have := mem_of_find hm' (r := 0) (j := off + t) (by rw [hlen]; decide) (by show _ < 0xe0; omega)
    (hfd t ht8)
  rw [show (envM m).base 0 = m.reg 2 from rfl] at this
  rw [hsp, this, le8_get]
  simp only [Nat.add_sub_cancel_left, hv]

sym_run runT3 := run zesuImage [0x800ea2f0, 0x800ea390] 60 0x800ea2b8 SM
sym_run runT4 := run zesuImage [0x800ea2f8] 10 0x800ea2f4 SM
sym_run runT5 := run zesuImage [0x800ea334] 40 0x800ea304 SM
sym_run runT6 := run zesuImage [0x800ea394] 10 0x800ea338 SM

/-- `rev8 (a1 << 3)`. -/
def ySym : Sym := .bin .rev8 (.bin .sll (.var 11) (.lit 3)) (.lit 0)
/-- `rev8 (a1 << 3) >> 8 k`, as the executor writes it. -/
def lenSym (k : Nat) : Sym := if k = 0 then ySym else .bin .srl ySym (.lit (8 * k))
/-- The registers the second padding block's byte stores take, by offset `0x60 + k`. -/
def t5Src : List Sym :=
  [.var 11, .bin .srl (.var 11) (.lit 8), .var 14, .var 6, .var 5, .var 17, .var 16, .var 15]

theorem t3_facts : runT3_leaves = [runT3_leaves[0]!, runT3_leaves[1]!] ∧
    (runT3_leaves[0]!).conds = [.geu (.lit 55) (.var 14)] ∧
    (runT3_leaves[1]!).conds = [.ltu (.lit 55) (.var 14)] ∧
    (runT3_leaves[0]!).S.steps = 24 ∧ (runT3_leaves[1]!).S.steps = 14 := by decide

theorem t3a_facts : keepsM (runT3_leaves[0]!).S = true ∧ (runT3_leaves[0]!).S.regions.length = 1 ∧
    (runT3_leaves[0]!).obligs = [] ∧ (runT3_leaves[0]!).S.reg 10 = .ptr 0 104 ∧
    (∀ t < 32, (runT3_leaves[0]!).S.mem.find? (·.covers 0 (8 + t)) = none) ∧
    (∀ t < 56, (runT3_leaves[0]!).S.mem.find? (·.covers 0 (0x28 + t)) = none) ∧
    (∀ t < 8, (runT3_leaves[0]!).S.mem.find? (·.covers 0 (0x60 + t)) =
      some ⟨0, 0x60 + t, 1, lenSym t⟩) ∧
    (∀ t < 8, (runT3_leaves[0]!).S.mem.find? (·.covers 0 (0x68 + t)) = some ⟨0, 0x68, 8, .ptr 0 8⟩) ∧
    (∀ t < 8, (runT3_leaves[0]!).S.mem.find? (·.covers 0 (0x70 + t)) = some ⟨0, 0x70, 8, .ptr 0 40⟩) := by
  decide

theorem t3b_facts : keepsM (runT3_leaves[1]!).S = true ∧ (runT3_leaves[1]!).S.regions.length = 1 ∧
    (runT3_leaves[1]!).obligs = [] ∧
    (∀ t < 32, (runT3_leaves[1]!).S.mem.find? (·.covers 0 (8 + t)) = none) ∧
    (∀ t < 64, (runT3_leaves[1]!).S.mem.find? (·.covers 0 (0x28 + t)) = none) ∧
    (∀ t < 8, (runT3_leaves[1]!).S.mem.find? (·.covers 0 (0x68 + t)) = some ⟨0, 0x68, 8, .ptr 0 8⟩) ∧
    (∀ t < 8, (runT3_leaves[1]!).S.mem.find? (·.covers 0 (0x70 + t)) = some ⟨0, 0x70, 8, .ptr 0 40⟩) ∧
    (runT3_leaves[1]!).S.reg 14 = .ptr 0 104 ∧ (runT3_leaves[1]!).S.reg 13 = .ptr 0 40 ∧
    (runT3_leaves[1]!).S.reg 10 = .ptr 0 8 ∧ (runT3_leaves[1]!).S.reg 11 = ySym ∧
    (runT3_leaves[1]!).S.reg 5 = lenSym 4 ∧ (runT3_leaves[1]!).S.reg 6 = lenSym 3 ∧
    (runT3_leaves[1]!).S.reg 15 = lenSym 7 ∧ (runT3_leaves[1]!).S.reg 16 = lenSym 6 ∧
    (runT3_leaves[1]!).S.reg 17 = lenSym 5 := by decide

theorem t4_facts : runT4_leaves = [runT4_leaves[0]!] ∧ keepsM (runT4_leaves[0]!).S = true ∧
    (runT4_leaves[0]!).S.regions.length = 1 ∧ (runT4_leaves[0]!).obligs = [] ∧
    (runT4_leaves[0]!).S.mem = [] ∧ (runT4_leaves[0]!).S.steps = 1 ∧
    (runT4_leaves[0]!).S.reg 14 = .bin .srl (.var 11) (.lit 16) ∧
    (∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 14 →
      (runT4_leaves[0]!).S.reg i.val = if i.val = 0 then .lit 0 else .var i.val) := by decide

theorem t5_facts : runT5_leaves = [runT5_leaves[0]!] ∧ keepsM (runT5_leaves[0]!).S = true ∧
    (runT5_leaves[0]!).S.regions.length = 1 ∧ (runT5_leaves[0]!).obligs = [] ∧
    (runT5_leaves[0]!).S.steps = 12 ∧ (runT5_leaves[0]!).S.reg 10 = .ptr 0 104 ∧
    (∀ t < 32, (runT5_leaves[0]!).S.mem.find? (·.covers 0 (8 + t)) = none) ∧
    (∀ t < 56, (runT5_leaves[0]!).S.mem.find? (·.covers 0 (0x28 + t)) = none) ∧
    (∀ t < 8, (runT5_leaves[0]!).S.mem.find? (·.covers 0 (0x60 + t)) =
      some ⟨0, 0x60 + t, 1, t5Src.getD t (.lit 0)⟩) ∧
    (∀ t < 8, (runT5_leaves[0]!).S.mem.find? (·.covers 0 (0x68 + t)) = some ⟨0, 0x68, 8, .var 10⟩) ∧
    (∀ t < 8, (runT5_leaves[0]!).S.mem.find? (·.covers 0 (0x70 + t)) = some ⟨0, 0x70, 8, .var 13⟩) := by
  decide

theorem t6_facts : runT6_leaves = [runT6_leaves[0]!] ∧ keepsM (runT6_leaves[0]!).S = true ∧
    (runT6_leaves[0]!).S.regions.length = 1 ∧ (runT6_leaves[0]!).obligs = [] ∧
    (runT6_leaves[0]!).S.mem = [] ∧ (runT6_leaves[0]!).S.steps = 1 := by decide

/-- `csrsi 0x816, 2; addi zero, a3, 0x38; addi zero, a3, 0`: zero `sp + 0x28 .. + 0x60`. -/
theorem pad_fill {m0 m : Machine} (hn : Nums m0) (hmid : Mid m0 m) (hpc : m.pc.toNat = 0x800ea2f8)
    (h13 : m.reg 13 = spM m0 + 0x28) {ST : List Byte} (hst : FrameAt m 8 ST) (hSTl : ST.length = 32)
    {P1 P2 : List Byte} (hp1 : FrameAt m 0x68 P1) (hp1l : P1.length = 8) (hp2 : FrameAt m 0x70 P2)
    (hp2l : P2.length = 8) :
    ∃ m1, next zesuImage m = some (m1, 3) ∧ m1.pc.toNat = 0x800ea304 ∧ Mid m0 m1 ∧
      (∀ r, m1.reg r = m.reg r) ∧ FrameAt m1 8 ST ∧ FrameAt m1 0x28 (List.replicate 56 0) ∧
      FrameAt m1 0x68 P1 ∧ FrameAt m1 0x70 P2 := by
  have := hn.lo; have := hn.hi; have := hn.al
  have hd : (m.reg 13).toNat = (spM m0).toNat + 0x28 := by
    rw [h13]; exact frame_addr hn (by decide)
  have hn1 := next_816i (m := m) (w0 := 0x81616073) (w1 := 0x03868013) (w2 := 0x00068013) (b := 0)
    (by rw [hpc]; decide) (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show Decode.reg 0x03868013 15 = 13 by decide]; exact hd) (n := 56) (by decide)
    (dst_frame hn hmid (by decide))
  obtain ⟨m1, hm1⟩ : ∃ x : Machine, x = { m with
      mem := fillMem m.mem ((spM m0).toNat + 0x28) 56 0, pc := m.pc + BitVec.ofNat 64 12 } :=
    ⟨_, rfl⟩
  rw [← hm1] at hn1
  have hsp1 : m1.reg 2 = spM m0 := by rw [hm1, mk_reg]; exact hmid.sp
  subst hm1
  have hout := fun (x : Word) (hx : ¬ ((spM m0).toNat + 0x28 ≤ x.toNat ∧
      x.toNat < (spM m0).toNat + 0x28 + 56)) => (fill_out (mem := m.mem) (b := 0) hx)
  refine ⟨_, hn1, by simp only [BitVec.toNat_add, hpc]; rfl, ?_, fun r => rfl, ?_, ?_, ?_, ?_⟩
  · refine mid_frame hn hmid (fun r => rfl) (lo := 0x28) (len := 56) (by decide) hout ?_
    intro j hj
    show (fillMem _ _ _ _ _).isSome = true
    rw [← frame_ofNat, ← Nat.add_assoc, fill_in hj (by omega)]; rfl
  · exact frameAt_out (lo := 0x28) (len := 56) hn hmid.sp hsp1 hout hst (by omega) (by omega)
  · refine frameAt_of hsp1 fun t ht => ?_
    simp only [List.length_replicate] at ht
    show fillMem _ _ _ _ _ = _
    rw [fill_in ht (by omega), List.getElem_replicate]
  · exact frameAt_out (lo := 0x28) (len := 56) hn hmid.sp hsp1 hout hp1 (by omega) (by omega)
  · exact frameAt_out (lo := 0x28) (len := 56) hn hmid.sp hsp1 hout hp2 (by omega) (by omega)

/-- The 64-byte block at frame offset `0x28` as `compress_step` reads it. -/
theorem blk_facts {m0 m : Machine} (hn : Nums m0) (hmid : Mid m0 m) {L : List Byte}
    (hL : L.length = 64) (hb : FrameAt m 0x28 L) :
    (spM m0 + 0x28).toNat % 8 = 0 ∧ srcOk m.mem (spM m0 + 0x28).toNat 64 = true ∧
      readBytes m.mem (spM m0 + 0x28).toNat 64 = some L := by
  have := hn.lo; have := hn.hi; have := hn.al
  have hS28 : (spM m0 + 0x28).toNat = (spM m0).toNat + 0x28 := frame_addr hn (j := 0x28) (by decide)
  have hrd := readBytes_frame hb
  rw [hL, hmid.sp, ← hS28] at hrd
  refine ⟨by rw [hS28]; omega, ?_, hrd⟩
  simp only [srcOk, Bool.and_eq_true, hS28]
  refine ⟨by simp [readable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
  rw [← hS28]; simp only [present, hrd]; rfl

theorem ySym_eval {m : Machine} : ySym.eval (envM m) = rev8 (m.reg 11 <<< 3) := by
  simp only [ySym, Sym.eval, BinOp.eval, envM_vars]; rfl

theorem lenSym_eval {m : Machine} {k : Nat} (hk : k < 8) :
    (lenSym k).eval (envM m) = rev8 (m.reg 11 <<< 3) >>> (8 * k) := by
  unfold lenSym
  split
  · next h => subst h; rw [ySym_eval]; simp
  · simp only [Sym.eval, BinOp.eval]
    rw [ySym_eval]; congr 1; simp; omega

/-- `0x800ea2b8` → `0x800ea394`. -/
theorem pad {m0 m : Machine} (hpre : Pre m0) (h : PAt m0 m) :
    ∃ k m', RunsIn zesuImage k m m' ∧ k ≤ 33 ∧ OAt m0 m' := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al
  have hlen := msg_len hpre
  have hr64 : (m0.reg 11).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  have hn61 : (m0.reg 11).toNat < 2 ^ 61 := by
    by_cases h0 : (m0.reg 11).toNat = 0
    · omega
    · have := (inNums hpre h0).hi; omega
  have hH := Sha256.foldBlocks_length (msgOf m0) ((m0.reg 11).toNat / 64)
  have hSTl := Sha256.leBytes_length hH
  have hTBl : (Sha256.tailBuf (msgOf m0)).length = 64 := by
    simp [Sha256.tailBuf, hlen]; omega
  have hS8 : spM m0 + BitVec.ofNat 64 0x68 = m.reg 2 + BitVec.ofInt 64 104 := by rw [h.mid.sp]; rfl
  have hy : ∀ k < 8, (lenSym k).eval (envM m) = rev8 (m0.reg 11 <<< 3) >>> (8 * k) := by
    intro k hk; rw [lenSym_eval hk, h.a1]
  have hlb : ∀ k (hk : k < 8), byteOf (rev8 (m0.reg 11 <<< 3) >>> (8 * k)) 0 =
      (Sha256.lenBytes (msgOf m0).length)[k]'(by rw [lenBytes_length]; exact hk) := by
    intro k hk; rw [len_byte _ hn61 k hk]; simp only [hlen]
  obtain ⟨l, hl, hc, hr⟩ := segM runT3 hpre h.mid (ro_mid hpre hn h.mid) h.pc
  obtain ⟨hls, hc0, hc1, hs0, hs1⟩ := t3_facts
  rw [hls] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · -- one padding block
    have hcond := hc _ (by rw [hc0]; exact List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, envM_vars, Bool.not_eq_true', BitVec.ult,
      decide_eq_false_iff_not, Nat.not_lt] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, h.a4, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat] at hcond
    have hr55 : (m0.reg 11).toNat % 64 ≤ 55 := by omega
    obtain ⟨hk, hlen1, hob, hr10, hn8, hn28, h60, h68, h70⟩ := t3a_facts
    obtain ⟨m1, hrun1, hm1, hex1, hso1⟩ := hr (fun o ho => by rw [hob] at ho; simp at ho)
    have hmid1 := mid_leaf hn h.mid hm1 hso1 hk hlen1
    have hsp1 : m1.reg 2 = m.reg 2 := by rw [hmid1.sp, h.mid.sp]
    have hst1 := frameAt_leaf hm1 hsp1 hlen1 h.st (by rw [hSTl]; decide) (fun t ht => hn8 t (by omega))
    have hBl : ((Sha256.tailBuf (msgOf m0)).take 56 ++ Sha256.lenBytes (msgOf m0).length).length =
        64 := by simp [hTBl, lenBytes_length]
    have hblk1 : FrameAt m1 0x28
        ((Sha256.tailBuf (msgOf m0)).take 56 ++ Sha256.lenBytes (msgOf m0).length) := by
      apply frameAt_append
      · exact frameAt_leaf hm1 hsp1 hlen1 (frameAt_take h.buf 56) (by simp [hTBl])
          (fun t ht => hn28 t (by simp [hTBl] at ht; omega))
      · rw [show 0x28 + ((Sha256.tailBuf (msgOf m0)).take 56).length = 0x60 by simp [hTBl]]
        refine frameAt_stores hm1 hsp1 hlen1 (by rw [lenBytes_length]; decide) fun t ht => ?_
        rw [lenBytes_length] at ht
        exact ⟨lenSym t, h60 t ht, by rw [hy t ht, hlb t ht]⟩
    have hpb := frameAt_word hm1 hsp1 hlen1 h68 (by decide) (v := spM m0 + 8)
      (by show m.reg 2 + BitVec.ofInt 64 8 = _; rw [h.mid.sp]; rfl)
    have hib := frameAt_word hm1 hsp1 hlen1 h70 (by decide) (v := spM m0 + 0x28)
      (by show m.reg 2 + BitVec.ofInt 64 40 = _; rw [h.mid.sp]; rfl)
    obtain ⟨hb8, hbs, hbr⟩ := blk_facts hn hmid1 hBl hblk1
    have hpc1 : m1.pc.toNat = 0x800ea390 := hex1
    obtain ⟨m2, hn2, hpc2, hmid2, -, hst2, -⟩ := compress_step (w0 := 0x80552073) (P := 0x68)
      (blkA := spM m0 + 0x28) hn hmid1 (by rw [hpc1]; decide) (by rw [hpc1]; decide +kernel)
      (by rw [hpc1]; decide +kernel) (by decide)
      (by
        rw [show Decode.reg 0x80552073 15 = 10 by decide, reg_of_match hm1,
          show ((10 : Fin 32).val) = 10 from rfl, hr10, hS8]; rfl)
      (by decide) (by decide) (by decide) hpb hib hH hst1 hb8 hbs hbr
    have hfin : Sha256.finish (msgOf m0) (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64)) =
        Sha256.sha256Compress (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64))
          ((Sha256.tailBuf (msgOf m0)).take 56 ++ Sha256.lenBytes (msgOf m0).length) := by
      unfold Sha256.finish; rw [if_pos (by rw [hlen]; exact hr55)]
    refine ⟨_, _, hrun1.trans (RunsIn.step hn2 .refl), by rw [hs0]; decide,
      ⟨by rw [hpc2, BitVec.toNat_add, hpc1]; rfl, hmid2, by rw [hfin]; exact hst2⟩⟩
  · -- two padding blocks
    have hcond := hc _ (by rw [hc1]; exact List.mem_singleton_self _)
    simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, envM_vars, BitVec.ult,
      decide_eq_true_eq] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, h.a4, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat] at hcond
    have hr55 : ¬ (m0.reg 11).toNat % 64 ≤ 55 := by omega
    obtain ⟨hk, hlen1, hob, hn8, hn28, h68, h70, hr14, hr13, hr10, hr11, hr5, hr6, hr15, hr16,
      hr17⟩ := t3b_facts
    obtain ⟨m1, hrun1, hm1, hex1, hso1⟩ := hr (fun o ho => by rw [hob] at ho; simp at ho)
    have hmid1 := mid_leaf hn h.mid hm1 hso1 hk hlen1
    have hsp1 : m1.reg 2 = m.reg 2 := by rw [hmid1.sp, h.mid.sp]
    have hst1 := frameAt_leaf hm1 hsp1 hlen1 h.st (by rw [hSTl]; decide) (fun t ht => hn8 t (by omega))
    have hbuf1 := frameAt_leaf hm1 hsp1 hlen1 h.buf (by rw [hTBl]; decide)
      (fun t ht => hn28 t (by omega))
    have hpb := frameAt_word hm1 hsp1 hlen1 h68 (by decide) (v := spM m0 + 8)
      (by show m.reg 2 + BitVec.ofInt 64 8 = _; rw [h.mid.sp]; rfl)
    have hib := frameAt_word hm1 hsp1 hlen1 h70 (by decide) (v := spM m0 + 0x28)
      (by show m.reg 2 + BitVec.ofInt 64 40 = _; rw [h.mid.sp]; rfl)
    have hY : ∀ {i : Fin 32} {k : Nat}, (runT3_leaves[1]!).S.reg i.val = lenSym k → k < 8 →
        m1.reg i = rev8 (m0.reg 11 <<< 3) >>> (8 * k) := fun hi hk => by
      rw [reg_of_match hm1, hi, hy _ hk]
    have r11 : m1.reg 11 = rev8 (m0.reg 11 <<< 3) := by
      rw [reg_of_match hm1, show ((11 : Fin 32).val) = 11 from rfl, hr11, ySym_eval, h.a1]
    obtain ⟨hb8, hbs, hbr⟩ := blk_facts hn hmid1 hTBl hbuf1
    have hpc1 : m1.pc.toNat = 0x800ea2f0 := hex1
    -- `csrs 0x805, a4`: the buffer as it is
    obtain ⟨m2, hn2, hpc2, hmid2, hreg2, hst2, hout2⟩ := compress_step (w0 := 0x80572073)
      (P := 0x68) (blkA := spM m0 + 0x28) hn hmid1 (by rw [hpc1]; decide)
      (by rw [hpc1]; decide +kernel) (by rw [hpc1]; decide +kernel) (by decide)
      (by
        rw [show Decode.reg 0x80572073 15 = 14 by decide, reg_of_match hm1,
          show ((14 : Fin 32).val) = 14 from rfl, hr14, hS8]; rfl)
      (by decide) (by decide) (by decide) hpb hib hH hst1 hb8 hbs hbr
    have hpc2' : m2.pc.toNat = 0x800ea2f4 := by rw [hpc2, BitVec.toNat_add, hpc1]; rfl
    have hpb2 := frameAt_out (lo := 8) (len := 32) hn hmid1.sp hmid2.sp hout2 hpb (by simp [le8_length])
      (by right; decide)
    have hib2 := frameAt_out (lo := 8) (len := 32) hn hmid1.sp hmid2.sp hout2 hib (by simp [le8_length])
      (by right; decide)
    -- `srli a4, a1, 16`
    obtain ⟨l4, hl4, -, hr4⟩ := segM runT4 hpre hmid2 (ro_mid hpre hn hmid2) hpc2'
    obtain ⟨hls4, hk4, hlen4, hob4, hmem4, hs4, hr4_14, hrk4⟩ := t4_facts
    rw [hls4, List.mem_singleton] at hl4; subst hl4
    obtain ⟨m3, hrun3, hm3, hex3, hso3⟩ := hr4 (fun o ho => by rw [hob4] at ho; simp at ho)
    have hmid3 := mid_leaf hn hmid2 hm3 hso3 hk4 hlen4
    have hsp3 : m3.reg 2 = m2.reg 2 := by rw [hmid3.sp, hmid2.sp]
    have hR3 : ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 14 → m3.reg i = m1.reg i := fun i h2 h14 => by
      rw [reg_kept hm3 (hrk4 i h2 h14), hreg2]
    have r3_14 : m3.reg 14 = rev8 (m0.reg 11 <<< 3) >>> (8 * 2) := by
      rw [reg_of_match hm3, show ((14 : Fin 32).val) = 14 from rfl, hr4_14]
      show m2.reg 11 >>> ((BitVec.ofNat 64 16).toNat % 64) = _
      rw [hreg2, r11]; rfl
    have hst3 := frameAt_leaf hm3 hsp3 hlen4 hst2
      (by rw [Sha256.leBytes_length (Sha256.compress_length _ _)]; decide)
      (fun t _ => by rw [hmem4]; rfl)
    have hpb3 := frameAt_leaf hm3 hsp3 hlen4 hpb2 (by rw [le8_length]; decide)
      (fun t _ => by rw [hmem4]; rfl)
    have hib3 := frameAt_leaf hm3 hsp3 hlen4 hib2 (by rw [le8_length]; decide)
      (fun t _ => by rw [hmem4]; rfl)
    -- `csrsi 0x816`: zero `sp + 0x28 .. + 0x60`
    obtain ⟨m4, hn4, hpc4, hmid4, hreg4, hst4, hz4, -, -⟩ := pad_fill hn hmid3 hex3
      (by
        rw [hR3 13 (by decide) (by decide), reg_of_match hm1, show ((13 : Fin 32).val) = 13 from rfl,
          hr13]
        show m.reg 2 + BitVec.ofInt 64 40 = _; rw [h.mid.sp]; rfl)
      hst3 (Sha256.leBytes_length (Sha256.compress_length _ _)) hpb3 (le8_length _) hib3
      (le8_length _)
    -- the length bytes, the parameter block
    obtain ⟨l5, hl5, -, hr5'⟩ := segM runT5 hpre hmid4 (ro_mid hpre hn hmid4) hpc4
    obtain ⟨hls5, hk5, hlen5, hob5, hs5, hr5_10, hn5_8, hn5_28, h5_60, h5_68, h5_70⟩ := t5_facts
    rw [hls5, List.mem_singleton] at hl5; subst hl5
    obtain ⟨m5, hrun5, hm5, hex5, hso5⟩ := hr5' (fun o ho => by rw [hob5] at ho; simp at ho)
    have hmid5 := mid_leaf hn hmid4 hm5 hso5 hk5 hlen5
    have hsp5 : m5.reg 2 = m4.reg 2 := by rw [hmid5.sp, hmid4.sp]
    have hR4 : ∀ i : Fin 32, i.val ≠ 2 → i.val ≠ 14 → m4.reg i = m1.reg i := fun i h2 h14 => by
      rw [hreg4, hR3 i h2 h14]
    have hsrc : ∀ t (ht : t < 8), (t5Src.getD t (.lit 0)).eval (envM m4) =
        rev8 (m0.reg 11 <<< 3) >>> (8 * t) := by
      intro t ht
      have e4 : ∀ {i : Fin 32} {k : Nat}, i.val ≠ 2 → i.val ≠ 14 →
          (runT3_leaves[1]!).S.reg i.val = lenSym k → k < 8 →
          (Sym.var i.val).eval (envM m4) = rev8 (m0.reg 11 <<< 3) >>> (8 * k) :=
        fun h2 h14 hi hk => by
          simp only [Sym.eval, envM_vars, Fin.ofNat_val_eq_self]
          rw [hR4 _ h2 h14, hY hi hk]
      match t, ht with
      | 0, _ =>
        show (Sym.var 11).eval (envM m4) = _
        simp only [Sym.eval, envM_vars]
        rw [show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl, hR4 11 (by decide) (by decide), r11]; simp
      | 1, _ =>
        show m4.reg (Fin.ofNat 32 11) >>> ((BitVec.ofNat 64 8).toNat % 64) = _
        rw [show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl, hR4 11 (by decide) (by decide), r11]; rfl
      | 2, _ =>
        show m4.reg (Fin.ofNat 32 14) = _
        rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, hreg4, r3_14]
      | 3, _ => exact e4 (i := 6) (by decide) (by decide) hr6 (by decide)
      | 4, _ => exact e4 (i := 5) (by decide) (by decide) hr5 (by decide)
      | 5, _ => exact e4 (i := 17) (by decide) (by decide) hr17 (by decide)
      | 6, _ => exact e4 (i := 16) (by decide) (by decide) hr16 (by decide)
      | 7, _ => exact e4 (i := 15) (by decide) (by decide) hr15 (by decide)
    have hBl : (List.replicate 56 (0 : Byte) ++ Sha256.lenBytes (msgOf m0).length).length = 64 := by
      simp [lenBytes_length]
    have hblk5 : FrameAt m5 0x28 (List.replicate 56 0 ++ Sha256.lenBytes (msgOf m0).length) := by
      apply frameAt_append
      · exact frameAt_leaf hm5 hsp5 hlen5 hz4 (by simp) (fun t ht => hn5_28 t (by simpa using ht))
      · rw [show 0x28 + (List.replicate 56 (0 : Byte)).length = 0x60 by simp]
        refine frameAt_stores hm5 hsp5 hlen5 (by rw [lenBytes_length]; decide) fun t ht => ?_
        rw [lenBytes_length] at ht
        exact ⟨_, h5_60 t ht, by rw [hsrc t ht, hlb t ht]⟩
    have hst5 := frameAt_leaf hm5 hsp5 hlen5 hst4
      (by rw [Sha256.leBytes_length (Sha256.compress_length _ _)]; decide)
      (fun t ht => hn5_8 t (by rw [Sha256.leBytes_length (Sha256.compress_length _ _)] at ht; exact ht))
    have hpb5 := frameAt_word hm5 hsp5 hlen5 h5_68 (by decide) (v := spM m0 + 8)
      (by
        show m4.reg (Fin.ofNat 32 10) = _
        rw [show (Fin.ofNat 32 10 : Fin 32) = 10 from rfl, hR4 10 (by decide) (by decide),
          reg_of_match hm1, show ((10 : Fin 32).val) = 10 from rfl, hr10]
        show m.reg 2 + BitVec.ofInt 64 8 = _; rw [h.mid.sp]; rfl)
    have hib5 := frameAt_word hm5 hsp5 hlen5 h5_70 (by decide) (v := spM m0 + 0x28)
      (by
        show m4.reg (Fin.ofNat 32 13) = _
        rw [show (Fin.ofNat 32 13 : Fin 32) = 13 from rfl, hR4 13 (by decide) (by decide),
          reg_of_match hm1, show ((13 : Fin 32).val) = 13 from rfl, hr13]
        show m.reg 2 + BitVec.ofInt 64 40 = _; rw [h.mid.sp]; rfl)
    obtain ⟨hb8', hbs', hbr'⟩ := blk_facts hn hmid5 hBl hblk5
    have hpc5 : m5.pc.toNat = 0x800ea334 := hex5
    -- `csrs 0x805, a0`: 56 zeros and the length
    obtain ⟨m6, hn6, hpc6, hmid6, -, hst6, -⟩ := compress_step (w0 := 0x80552073) (P := 0x68)
      (blkA := spM m0 + 0x28) hn hmid5 (by rw [hpc5]; decide) (by rw [hpc5]; decide +kernel)
      (by rw [hpc5]; decide +kernel) (by decide)
      (by
        rw [show Decode.reg 0x80552073 15 = 10 by decide, reg_of_match hm5,
          show ((10 : Fin 32).val) = 10 from rfl, hr5_10]
        show m4.reg 2 + BitVec.ofInt 64 104 = _; rw [hmid4.sp]; rfl)
      (by decide) (by decide) (by decide) hpb5 hib5 (Sha256.compress_length _ _) hst5 hb8' hbs' hbr'
    have hpc6' : m6.pc.toNat = 0x800ea338 := by rw [hpc6, BitVec.toNat_add, hpc5]; rfl
    -- `j 0x800ea394`
    obtain ⟨l7, hl7, -, hr7⟩ := segM runT6 hpre hmid6 (ro_mid hpre hn hmid6) hpc6'
    obtain ⟨hls7, hk7, hlen7, hob7, hmem7, hs7⟩ := t6_facts
    rw [hls7, List.mem_singleton] at hl7; subst hl7
    obtain ⟨m7, hrun7, hm7, hex7, hso7⟩ := hr7 (fun o ho => by rw [hob7] at ho; simp at ho)
    have hmid7 := mid_leaf hn hmid6 hm7 hso7 hk7 hlen7
    have hst7 := frameAt_leaf hm7 (by rw [hmid7.sp, hmid6.sp]) hlen7 hst6
      (by rw [Sha256.leBytes_length (Sha256.compress_length _ _)]; decide)
      (fun t _ => by rw [hmem7]; rfl)
    have hfin : Sha256.finish (msgOf m0) (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64)) =
        Sha256.sha256Compress (Sha256.sha256Compress
          (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64)) (Sha256.tailBuf (msgOf m0)))
          (List.replicate 56 0 ++ Sha256.lenBytes (msgOf m0).length) := by
      unfold Sha256.finish; rw [if_neg (by rw [hlen]; exact hr55)]
    refine ⟨_, _, hrun1.trans (RunsIn.step hn2 (hrun3.trans (RunsIn.step hn4 (hrun5.trans
      (RunsIn.step hn6 hrun7))))), by rw [hs1, hs4, hs5, hs7]; decide,
      ⟨hex7, hmid7, by rw [hfin]; exact hst7⟩⟩

end ZesuExec.Fn.Sha256
