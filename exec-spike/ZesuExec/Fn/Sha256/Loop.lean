import ZesuExec.Fn.Sha256.Body

/-!
# `zkvm_sha256`: the whole blocks (`0x800ea1ec` → `0x800ea280`)

Two loops, chosen by `a0 & 7`. Unaligned (`UAt`, at the CSR `0x813` site `0x800ea210`): each
block is copied to `sp + 0x28` and compressed from there. Aligned (`AAt`, at the CSR `0x805` site
`0x800ea260`): each block is compressed in place. Both leave `TAt` at the CSR `0x816` site
`0x800ea280`: the state is `foldBlocks msg ⌊n / 64⌋`, `a3 = 64 ⌊n / 64⌋`, `a4 = n mod 64`.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

/-- After the prologue: `Mid`, and `a0`, `a1` are the entry's. -/
structure Body (m0 m : Machine) : Prop where
  mid : Mid m0 m
  a0 : m.reg 10 = m0.reg 10
  a1 : m.reg 11 = m0.reg 11

/-- At `0x800ea210` before block `i` of the unaligned loop. -/
structure UAt (m0 m : Machine) (i : Nat) : Prop where
  pc : m.pc.toNat = 0x800ea210
  body : Body m0 m
  st : FrameAt m 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) i))
  a3 : m.reg 13 = m0.reg 10 + BitVec.ofNat 64 (64 * i)
  a4 : m.reg 14 = BitVec.ofNat 64 (64 * i)
  a5 : m.reg 15 = spM m0 + 0x28
  a6 : m.reg 16 = spM m0 + 8
  a7 : m.reg 17 = spM m0 + 0x68
  lt : 64 * (i + 1) ≤ (m0.reg 11).toNat

/-- At `0x800ea280` after the whole blocks. -/
structure TAt (m0 m : Machine) : Prop where
  pc : m.pc.toNat = 0x800ea280
  body : Body m0 m
  st : FrameAt m 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) ((m0.reg 11).toNat / 64)))
  a3 : m.reg 13 = BitVec.ofNat 64 (64 * ((m0.reg 11).toNat / 64))
  a4 : m.reg 14 = BitVec.ofNat 64 ((m0.reg 11).toNat % 64)
  a5 : m.reg 15 = spM m0 + 0x28
  a6 : m.reg 16 = 65

sym_run runU2 := run zesuImage [0x800ea220] 10 0x800ea218 SM
sym_run runU3 := run zesuImage [0x800ea210, 0x800ea280] 20 0x800ea224 SM

theorem u2_facts : keepsM (runU2_leaves[0]!).S = true ∧ (runU2_leaves[0]!).S.regions.length = 1 ∧
    (∀ t < 32, (runU2_leaves[0]!).S.mem.find? (·.covers 0 (8 + t)) = none) ∧
    (∀ t < 64, (runU2_leaves[0]!).S.mem.find? (·.covers 0 (0x28 + t)) = none) ∧
    (∀ t < 8, (runU2_leaves[0]!).S.mem.find? (·.covers 0 (0x68 + t)) = some ⟨0, 0x68, 8, .var 16⟩) ∧
    (∀ t < 8, (runU2_leaves[0]!).S.mem.find? (·.covers 0 (0x70 + t)) = some ⟨0, 0x70, 8, .var 15⟩) ∧
    (∀ i : Fin 32, (runU2_leaves[0]!).S.reg i.val = if i.val = 0 then .lit 0 else
      if i.val = 2 then .ptr 0 0 else .var i.val) := by
  decide

theorem blk_len {msg : List Byte} {i : Nat} (h : 64 * (i + 1) ≤ msg.length) :
    ((msg.drop (64 * i)).take 64).length = 64 := by simp; omega

theorem blk_get {msg : List Byte} {i t : Nat} (h : 64 * (i + 1) ≤ msg.length) (ht : t < 64) :
    ((msg.drop (64 * i)).take 64)[t]'(by rw [blk_len h]; exact ht) =
      msg[64 * i + t]'(by omega) := by
  simp

/-- The unaligned loop's CSR `0x813` step: block `i` copied to `sp + 0x28`. -/
theorem u_copy {m0 m : Machine} {i : Nat} (hpre : Pre m0) (h : UAt m0 m i) :
    ∃ m1, next zesuImage m = some (m1, 2) ∧ m1.pc.toNat = 0x800ea218 ∧ Mid m0 m1 ∧
      (∀ r, m1.reg r = m.reg r) ∧
      FrameAt m1 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) i)) ∧
      FrameAt m1 0x28 (((msgOf m0).drop (64 * i)).take 64) := by
  have hn := nums hpre
  have hn0 : (m0.reg 11).toNat ≠ 0 := by have := h.lt; omega
  have hi := inNums hpre hn0
  have := hn.lo; have := hn.hi; have := hn.al; have := hi.df; have := hi.hi; have := hi.lo
  have hlt := h.lt
  have hlen := hi.len
  have hs : (m.reg 13).toNat = (m0.reg 10).toNat + 64 * i := by
    rw [h.a3, toNat_add_ofNat (by omega)]
  have hd : (m.reg 15).toNat = (spM m0).toNat + 0x28 := by
    rw [h.a5]; exact frame_addr hn (by decide)
  have hsrc : srcOk m.mem ((m0.reg 10).toNat + 64 * i) 64 = true := by
    simp only [srcOk, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := hi.inR
      simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
      omega
    · apply readBytes_isSome_of
      intro t ht
      rw [Nat.add_assoc, input_at hn hi h.body.mid (64 * i + t) (by omega)]; rfl
  have hdst : dstOk m.mem ((spM m0).toNat + 0x28) 64 = true := by
    simp only [dstOk, Bool.and_eq_true]
    refine ⟨by simp [writable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
    apply readBytes_isSome_of
    intro t ht
    rw [Nat.add_assoc, frame_ofNat, ← h.body.mid.sp]
    exact h.body.mid.frame _ (by unfold frameSize; omega)
  have hn1 := next_813i (m := m) (w0 := 2167840883) (w1 := 67600403) (n := 64)
    (by rw [h.pc]; decide) (by rw [h.pc]; decide +kernel) (by rw [h.pc]; decide +kernel)
    (by rw [h.pc]; decide +kernel) (by decide) (by decide) (by decide)
    (by rw [show Decode.reg 2167840883 15 = 13 by decide]; exact hs)
    (by rw [show Decode.reg 67600403 15 = 15 by decide]; exact hd) (by decide) hsrc hdst
  have hds : (spM m0).toNat + 0x28 ≠ (m0.reg 10).toNat + 64 * i := by omega
  obtain ⟨m1, hm1⟩ : ∃ x : Machine, x = { m with
      mem := copyMem m.mem ((spM m0).toNat + 0x28) ((m0.reg 10).toNat + 64 * i) 64,
      pc := m.pc + 8 } := ⟨_, rfl⟩
  rw [← hm1] at hn1
  have hsp1 : m1.reg 2 = spM m0 := by rw [hm1, mk_reg]; exact h.body.mid.sp
  have hout : ∀ x : Word, ¬ ((spM m0).toNat + 0x28 ≤ x.toNat ∧ x.toNat < (spM m0).toNat + 0x28 + 64) →
      m1.mem x = m.mem x := fun x hx => by rw [hm1]; exact copy_out hx
  have hin : ∀ t (ht : t < 64), m1.mem (BitVec.ofNat 64 ((spM m0).toNat + 0x28 + t)) =
      some ((msgOf m0)[64 * i + t]'(by omega)) := by
    intro t ht
    rw [hm1]
    show copyMem _ _ _ _ _ = _
    rw [copy_in ht hds (by omega), Nat.add_assoc, input_at hn hi h.body.mid (64 * i + t) (by omega)]
  refine ⟨m1, hn1, by rw [hm1]; simp only [BitVec.toNat_add, h.pc]; rfl, ?_,
    fun r => by rw [hm1, mk_reg], ?_, ?_⟩
  · refine mid_frame hn h.body.mid (fun r => by rw [hm1, mk_reg]) (lo := 0x28) (len := 0x40)
      (by decide) hout ?_
    intro j hj
    rw [← frame_ofNat, ← Nat.add_assoc, hin j hj]; rfl
  · exact frameAt_out (lo := 0x28) (len := 64) hn h.body.mid.sp hsp1 hout h.st
      (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
      (by left; simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
  · refine frameAt_of hsp1 fun t ht => ?_
    have ht' : t < 64 := by rw [blk_len (by omega)] at ht; exact ht
    rw [hin t ht', blk_get (by omega) ht']

theorem u3_facts : keepsM (runU3_leaves[0]!).S = true ∧ (runU3_leaves[0]!).S.regions.length = 1 ∧
    (runU3_leaves[0]!).S.mem = [] ∧ keepsM (runU3_leaves[1]!).S = true ∧
    (runU3_leaves[1]!).S.regions.length = 1 ∧ (runU3_leaves[1]!).S.mem = [] := by decide

/-- One block of the unaligned loop. -/
theorem u_iter {m0 m : Machine} {i : Nat} (hpre : Pre m0) (h : UAt m0 m i) :
    ∃ k m', RunsIn zesuImage k m m' ∧
      ((k = 10 ∧ UAt m0 m' (i + 1)) ∨ (k = 13 ∧ TAt m0 m')) := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al
  obtain ⟨m1, hn1, hpc1, hmid1, hreg1, hst1, hblk1⟩ := u_copy hpre h
  -- `sd a6, 0x68(sp); sd a5, 0x70(sp)`
  obtain ⟨l, hl, -, hr⟩ := segM runU2 hpre hmid1 (ro_mid hpre hn hmid1) hpc1
  replace hl : l = runU2_leaves[0]! := by simp only [runU2_leaves, List.mem_singleton] at hl; exact hl
  subst hl
  obtain ⟨m2, hrun2, hm2, hex2, hso2⟩ := hr (fun o ho => by simp [runU2_leaves] at ho)
  obtain ⟨hk2, hlen2, hn2a, hn2b, hf68, hf70, hregs2⟩ := u2_facts
  have hmid2 := mid_leaf hn hmid1 hm2 hso2 hk2 hlen2
  have hreg2 : ∀ r : Fin 32, r.val ≠ 2 → m2.reg r = m1.reg r := fun r hr2 =>
    reg_kept hm2 (by rw [hregs2 r]; split <;> simp_all)
  have hsp2 : m2.reg 2 = m1.reg 2 := by rw [hmid2.sp, hmid1.sp]
  have hst2 := frameAt_leaf hm2 hsp2 hlen2 hst1
    (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
    (fun t ht => hn2a t (by simpa [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)] using ht))
  have hlt := h.lt
  have hlen := (inNums hpre (by omega)).len
  have hblk2 := frameAt_leaf hm2 hsp2 hlen2 hblk1 (by rw [blk_len (by omega)]; decide)
    (fun t ht => hn2b t (by rw [blk_len (by omega)] at ht; exact ht))
  have hpar : ∀ {off : Nat} {r : Fin 32} {v : Word}, (∀ t < 8,
      (runU2_leaves[0]!).S.mem.find? (·.covers 0 (off + t)) = some ⟨0, off, 8, .var r.val⟩) →
      off + 8 ≤ 0xe0 → m1.reg r = v → FrameAt m2 off (le8 v) := by
    intro off r v hfd hfit hv t ht
    have ht8 : t < 8 := by rw [le8_length] at ht; exact ht
    have := mem_of_find hm2 (r := 0) (j := off + t) (by rw [hlen2]; decide) (by show _ < 0xe0; omega)
      (hfd t ht8)
    rw [show (envM m1).base 0 = m1.reg 2 from rfl] at this
    rw [hsp2, this, le8_get]
    simp only [Sym.eval, envM_vars, Nat.add_sub_cancel_left]
    rw [show (Fin.ofNat 32 r.val) = r from Fin.ext (by simp), hv]
  have hpb := hpar (off := 0x68) (r := 16) (v := spM m0 + 8) hf68 (by decide)
    (by rw [hreg1]; exact h.a6)
  have hib := hpar (off := 0x70) (r := 15) (v := spM m0 + 0x28) hf70 (by decide)
    (by rw [hreg1]; exact h.a5)
  have hpc2 : m2.pc.toNat = 0x800ea220 := hex2
  -- `csrs 0x805, a7`
  have hS28 : (spM m0 + 0x28).toNat = (spM m0).toNat + 0x28 := frame_addr hn (j := 0x28) (by decide)
  obtain ⟨m3, hn3, hpc3, hmid3, hreg3, hst3, -⟩ := compress_step (w0 := 2153291891) (P := 0x68)
    (blkA := spM m0 + 0x28) hn hmid2 (by rw [hpc2]; decide) (by rw [hpc2]; decide +kernel)
    (by rw [hpc2]; decide +kernel) (by decide)
    (by rw [show Decode.reg 2153291891 15 = 17 by decide, hreg2 17 (by decide), hreg1]; exact h.a7)
    (by decide) (by decide) (by decide) hpb hib (Sha256.foldBlocks_length _ _) hst2
    (by rw [hS28]; omega)
    (by
      simp only [srcOk, Bool.and_eq_true, hS28]
      refine ⟨by simp [readable, inRange, Layout.ramLo, Layout.ramHi]; omega, ?_⟩
      exact readBytes_isSome_of fun t ht => by
        rw [Nat.add_assoc, frame_ofNat, ← hmid2.sp]; exact hmid2.frame _ (by unfold frameSize; omega))
    (by
      have := readBytes_frame hblk2
      rwa [blk_len (by omega), hmid2.sp, ← hS28] at this)
  rw [← Sha256.foldBlocks_succ] at hst3
  have hpc3' : m3.pc.toNat = 0x800ea224 := by rw [hpc3, BitVec.toNat_add, hpc2]; rfl
  have hR3 : ∀ r : Fin 32, r.val ≠ 2 → m3.reg r = m.reg r := fun r hr2 => by
    rw [hreg3, hreg2 r hr2, hreg1]
  have hsp3 : m3.reg 2 = spM m0 := hmid3.sp
  have hrun3 : RunsIn zesuImage 5 m m3 :=
    RunsIn.step hn1 (hrun2.trans (RunsIn.step hn3 .refl))
  -- `addi a3, a4, 64; addi t0, a4, 128; mv a4, a3; bgeu a1, t0, …`
  obtain ⟨l, hl, hc, hr⟩ := segM runU3 hpre hmid3 (ro_mid hpre hn hmid3) hpc3'
  obtain ⟨hk40, hlen40, hmem40, hk41, hlen41, hmem41⟩ := u3_facts
  have hlen := (inNums hpre (by omega)).len
  have h11 : (m3.reg 11).toNat = (m0.reg 11).toNat := by rw [hR3 11 (by decide), h.body.a1]
  have h14 : m3.reg 14 = BitVec.ofNat 64 (64 * i) := by rw [hR3 14 (by decide), h.a4]
  have hnb := (inNums hpre (by omega)).hi
  have hi14 : (m3.reg 14 + 128).toNat = 64 * i + 128 := by
    rw [h14, BitVec.toNat_add]; simp; omega
  rw [show runU3_leaves = [runU3_leaves[0]!, runU3_leaves[1]!] from rfl] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · -- back to `0x800ea210`
    have hcond := hc (.geu (.var 11) (.bin .add (.var 14) (.lit 128))) (by decide)
    simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, envM_vars,
      Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl,
      show (128#64 : Word) = 128 from rfl, hi14, h11] at hcond
    obtain ⟨m4, hrun4, hm4, hex4, hso4⟩ := hr (fun o ho => by simp [runU3_leaves] at ho)
    have hmid4 := mid_leaf hn hmid3 hm4 hso4 hk40 hlen40
    have hk : ∀ r : Fin 32, (runU3_leaves[0]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m4.reg r = m3.reg r := fun r h1 h2 => reg_kept hm4 (by rw [h1, if_neg h2])
    have hadd : BitVec.ofNat 64 (64 * i) + 64 = BitVec.ofNat 64 (64 * (i + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    refine ⟨10, m4, hrun3.trans hrun4, Or.inl ⟨rfl, ⟨hex4, ⟨hmid4, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rw [hk 10 rfl (by decide), hR3 10 (by decide), h.body.a0]
    · rw [hk 11 rfl (by decide), hR3 11 (by decide), h.body.a1]
    · exact frameAt_leaf hm4 (by rw [hmid4.sp, hsp3]) hlen40 hst3
        (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
        (fun t _ => by rw [hmem40]; rfl)
    · rw [reg_of_match hm4]
      show m3.reg 10 + (m3.reg 14 + BitVec.ofNat 64 64) = _
      rw [hR3 10 (by decide), h.body.a0, h14]; congr 1
    · rw [reg_of_match hm4]
      show m3.reg 14 + BitVec.ofNat 64 64 = _
      rw [h14]; exact hadd
    · rw [hk 15 rfl (by decide), hR3 15 (by decide), h.a5]
    · rw [hk 16 rfl (by decide), hR3 16 (by decide), h.a6]
    · rw [hk 17 rfl (by decide), hR3 17 (by decide), h.a7]
    · omega
  · -- out to `0x800ea280`
    have hcond := hc (.ltu (.var 11) (.bin .add (.var 14) (.lit 128))) (by decide)
    simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, envM_vars,
      BitVec.ult, decide_eq_true_eq] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl,
      show (128#64 : Word) = 128 from rfl, hi14, h11] at hcond
    have hk64 : (m0.reg 11).toNat / 64 = i + 1 := by omega
    obtain ⟨m4, hrun4, hm4, hex4, hso4⟩ := hr (fun o ho => by simp [runU3_leaves] at ho)
    have hmid4 := mid_leaf hn hmid3 hm4 hso4 hk41 hlen41
    have hk : ∀ r : Fin 32, (runU3_leaves[1]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m4.reg r = m3.reg r := fun r h1 h2 => reg_kept hm4 (by rw [h1, if_neg h2])
    refine ⟨13, m4, hrun3.trans hrun4, Or.inr ⟨rfl, ⟨hex4, ⟨hmid4, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rw [hk 10 rfl (by decide), hR3 10 (by decide), h.body.a0]
    · rw [hk 11 rfl (by decide), hR3 11 (by decide), h.body.a1]
    · rw [hk64]
      exact frameAt_leaf hm4 (by rw [hmid4.sp, hsp3]) hlen41 hst3
        (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
        (fun t _ => by rw [hmem41]; rfl)
    · rw [reg_of_match hm4]
      show m3.reg 14 + BitVec.ofNat 64 64 = _
      rw [h14, hk64]; apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [reg_of_match hm4]
      show m3.reg 11 - (m3.reg 14 + BitVec.ofNat 64 64) = _
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, h11, h14, show (BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 64).toNat =
        64 * i + 64 by simp; omega]
      simp; omega
    · rw [reg_of_match hm4]
      show m3.reg 2 + BitVec.ofInt 64 40 = _
      rw [hsp3]; rfl
    · rw [reg_of_match hm4]; rfl

/-- At `0x800ea260` before block `i` of the aligned loop: the parameter block at `sp + 0x28`
points at the state and at the block in place. -/
structure AAt (m0 m : Machine) (i : Nat) : Prop where
  pc : m.pc.toNat = 0x800ea260
  body : Body m0 m
  st : FrameAt m 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) i))
  a3 : m.reg 13 = m0.reg 10 + BitVec.ofNat 64 (64 * i)
  a4 : m.reg 14 = BitVec.ofNat 64 (64 * i)
  a5 : m.reg 15 = spM m0 + 8
  a6 : m.reg 16 = spM m0 + 0x28
  pb : FrameAt m 0x28 (le8 (spM m0 + 8))
  ib : FrameAt m 0x30 (le8 (m0.reg 10 + BitVec.ofNat 64 (64 * i)))
  al : (m0.reg 10).toNat % 8 = 0
  lt : 64 * (i + 1) ≤ (m0.reg 11).toNat

sym_run runA2 := run zesuImage [0x800ea260, 0x800ea280] 20 0x800ea264 SM

theorem a2_facts : keepsM (runA2_leaves[0]!).S = true ∧ (runA2_leaves[0]!).S.regions.length = 1 ∧
    (∀ t < 32, (runA2_leaves[0]!).S.mem.find? (·.covers 0 (8 + t)) = none) ∧
    (∀ t < 8, (runA2_leaves[0]!).S.mem.find? (·.covers 0 (0x28 + t)) = some ⟨0, 0x28, 8, .var 15⟩) ∧
    (∀ t < 8, (runA2_leaves[0]!).S.mem.find? (·.covers 0 (0x30 + t)) =
      some ⟨0, 0x30, 8, .bin .add (.var 10) (.bin .add (.var 14) (.lit 64))⟩) ∧
    keepsM (runA2_leaves[1]!).S = true ∧ (runA2_leaves[1]!).S.regions.length = 1 ∧
    (runA2_leaves[1]!).S.mem = [] := by decide

/-- The input block `i` as the bytes at its address. -/
theorem input_blk {m0 m : Machine} {i : Nat} (hn : Nums m0) (hi : InNums m0) (hmid : Mid m0 m)
    (hlt : 64 * (i + 1) ≤ (m0.reg 11).toNat) :
    readBytes m.mem ((m0.reg 10).toNat + 64 * i) 64 = some (((msgOf m0).drop (64 * i)).take 64) := by
  have hlen := hi.len
  have := readBytes_of_list (mem := m.mem) (a := (m0.reg 10).toNat + 64 * i)
    (L := ((msgOf m0).drop (64 * i)).take 64) fun t ht => by
      have ht' : t < 64 := by rw [blk_len (by omega)] at ht; exact ht
      rw [blk_get (by omega) ht', Nat.add_assoc, input_at hn hi hmid _ (by omega)]
  rwa [blk_len (by omega)] at this

/-- One block of the aligned loop. -/
theorem a_iter {m0 m : Machine} {i : Nat} (hpre : Pre m0) (h : AAt m0 m i) :
    ∃ k m', RunsIn zesuImage k m m' ∧
      ((k = 8 ∧ AAt m0 m' (i + 1)) ∨ (k = 8 ∧ TAt m0 m')) := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al
  have hlt := h.lt
  have hi := inNums hpre (by omega)
  have hlen := hi.len
  have hnb := hi.hi
  have hA : (m0.reg 10 + BitVec.ofNat 64 (64 * i)).toNat = (m0.reg 10).toNat + 64 * i := by
    rw [toNat_add_ofNat (by omega)]
  -- `csrs 0x805, a6`
  obtain ⟨m1, hn1, hpc1, hmid1, hreg1, hst1, -⟩ := compress_step (w0 := 2153259123) (P := 0x28)
    (blkA := m0.reg 10 + BitVec.ofNat 64 (64 * i)) hn h.body.mid (by rw [h.pc]; decide)
    (by rw [h.pc]; decide +kernel) (by rw [h.pc]; decide +kernel) (by decide)
    (by rw [show Decode.reg 2153259123 15 = 16 by decide]; exact h.a6)
    (by decide) (by decide) (by decide) h.pb h.ib (Sha256.foldBlocks_length _ _) h.st
    (by rw [hA]; have := h.al; omega)
    (by
      simp only [srcOk, Bool.and_eq_true, hA]
      refine ⟨?_, ?_⟩
      · have := hi.inR
        simp only [readable, inRange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
        omega
      · simp only [present]; rw [input_blk hn hi h.body.mid hlt]; rfl)
    (by rw [hA]; exact input_blk hn hi h.body.mid hlt)
  rw [← Sha256.foldBlocks_succ] at hst1
  have hpc1' : m1.pc.toNat = 0x800ea264 := by rw [hpc1, BitVec.toNat_add, h.pc]; rfl
  -- `addi a3, a4, 64; addi a7, a4, 128; mv a4, a3; bgeu a1, a7, …`
  obtain ⟨l, hl, hc, hr⟩ := segM runA2 hpre hmid1 (ro_mid hpre hn hmid1) hpc1'
  obtain ⟨hk0, hlen0, hn0a, hf28, hf30, hk1, hlen1, hmem1⟩ := a2_facts
  have h11 : (m1.reg 11).toNat = (m0.reg 11).toNat := by rw [hreg1, h.body.a1]
  have h14 : m1.reg 14 = BitVec.ofNat 64 (64 * i) := by rw [hreg1, h.a4]
  have hi14 : (m1.reg 14 + 128).toNat = 64 * i + 128 := by
    rw [h14, BitVec.toNat_add]; simp; omega
  have hsp1 : m1.reg 2 = spM m0 := hmid1.sp
  rw [show runA2_leaves = [runA2_leaves[0]!, runA2_leaves[1]!] from rfl] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl
  · have hcond := hc (.geu (.var 11) (.bin .add (.var 14) (.lit 128))) (by decide)
    simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, envM_vars,
      Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl,
      show (128#64 : Word) = 128 from rfl, hi14, h11] at hcond
    obtain ⟨m2, hrun2, hm2, hex2, hso2⟩ := hr (fun o ho => by simp [runA2_leaves] at ho)
    have hmid2 := mid_leaf hn hmid1 hm2 hso2 hk0 hlen0
    have hk : ∀ r : Fin 32, (runA2_leaves[0]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m2.reg r = m1.reg r := fun r h1 h2 => reg_kept hm2 (by rw [h1, if_neg h2])
    have hsp2 : m2.reg 2 = m1.reg 2 := by rw [hmid2.sp, hsp1]
    have hadd : BitVec.ofNat 64 (64 * i) + 64 = BitVec.ofNat 64 (64 * (i + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    have hpar : ∀ {off : Nat} {s : Sym} {v : Word}, (∀ t < 8,
        (runA2_leaves[0]!).S.mem.find? (·.covers 0 (off + t)) = some ⟨0, off, 8, s⟩) →
        off + 8 ≤ 0xe0 → s.eval (envM m1) = v → FrameAt m2 off (le8 v) := by
      intro off s v hfd hfit hv t ht
      have ht8 : t < 8 := by rw [le8_length] at ht; exact ht
      have := mem_of_find hm2 (r := 0) (j := off + t) (by rw [hlen0]; decide)
        (by show _ < 0xe0; omega) (hfd t ht8)
      rw [show (envM m1).base 0 = m1.reg 2 from rfl] at this
      rw [hsp2, this, le8_get]
      simp only [Nat.add_sub_cancel_left, hv]
    refine ⟨8, m2, RunsIn.step hn1 hrun2, Or.inl ⟨rfl, ⟨hex2, ⟨hmid2, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, h.al, by omega⟩⟩⟩
    · rw [hk 10 rfl (by decide), hreg1, h.body.a0]
    · rw [hk 11 rfl (by decide), hreg1, h.body.a1]
    · exact frameAt_leaf hm2 hsp2 hlen0 hst1
        (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
        (fun t ht => hn0a t (by simpa [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)] using ht))
    · rw [reg_of_match hm2]
      show m1.reg 10 + (m1.reg 14 + BitVec.ofNat 64 64) = _
      rw [hreg1, h.body.a0, h14]; congr 1
    · rw [reg_of_match hm2]
      show m1.reg 14 + BitVec.ofNat 64 64 = _
      rw [h14]; exact hadd
    · rw [hk 15 rfl (by decide), hreg1, h.a5]
    · rw [hk 16 rfl (by decide), hreg1, h.a6]
    · exact hpar hf28 (by decide) (by show m1.reg 15 = _; rw [hreg1, h.a5])
    · exact hpar hf30 (by decide) (by
        show m1.reg 10 + (m1.reg 14 + BitVec.ofNat 64 64) = _
        rw [hreg1, h.body.a0, h14]; congr 1)
  · have hcond := hc (.ltu (.var 11) (.bin .add (.var 14) (.lit 128))) (by decide)
    simp only [SBool.eval, Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval, envM_vars,
      BitVec.ult, decide_eq_true_eq] at hcond
    rw [show (Fin.ofNat 32 14 : Fin 32) = 14 from rfl, show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl,
      show (128#64 : Word) = 128 from rfl, hi14, h11] at hcond
    have hk64 : (m0.reg 11).toNat / 64 = i + 1 := by omega
    obtain ⟨m2, hrun2, hm2, hex2, hso2⟩ := hr (fun o ho => by simp [runA2_leaves] at ho)
    have hmid2 := mid_leaf hn hmid1 hm2 hso2 hk1 hlen1
    have hk : ∀ r : Fin 32, (runA2_leaves[1]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m2.reg r = m1.reg r := fun r h1 h2 => reg_kept hm2 (by rw [h1, if_neg h2])
    refine ⟨8, m2, RunsIn.step hn1 hrun2, Or.inr ⟨rfl, ⟨hex2, ⟨hmid2, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rw [hk 10 rfl (by decide), hreg1, h.body.a0]
    · rw [hk 11 rfl (by decide), hreg1, h.body.a1]
    · rw [hk64]
      exact frameAt_leaf hm2 (by rw [hmid2.sp, hsp1]) hlen1 hst1
        (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
        (fun t _ => by rw [hmem1]; rfl)
    · rw [reg_of_match hm2]
      show m1.reg 14 + BitVec.ofNat 64 64 = _
      rw [h14, hk64]; apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [reg_of_match hm2]
      show m1.reg 11 - (m1.reg 14 + BitVec.ofNat 64 64) = _
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, h11, h14, show (BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 64).toNat =
        64 * i + 64 by simp; omega]
      simp; omega
    · rw [reg_of_match hm2]
      show m1.reg 2 + BitVec.ofInt 64 40 = _
      rw [hsp1]; rfl
    · rw [reg_of_match hm2]; rfl

theorem u_loop {m0 : Machine} (hpre : Pre m0) :
    ∀ d i m, (m0.reg 11).toNat / 64 = i + 1 + d → UAt m0 m i →
      ∃ k m', RunsIn zesuImage k m m' ∧ k ≤ 10 * (d + 1) + 3 ∧ TAt m0 m' := by
  intro d
  induction d with
  | zero =>
    intro i m hd h
    obtain ⟨k, m', hr, hc⟩ := u_iter hpre h
    rcases hc with ⟨rfl, hu⟩ | ⟨rfl, ht⟩
    · have := hu.lt; omega
    · exact ⟨13, m', hr, by omega, ht⟩
  | succ d ih =>
    intro i m hd h
    obtain ⟨k, m', hr, hc⟩ := u_iter hpre h
    rcases hc with ⟨rfl, hu⟩ | ⟨rfl, ht⟩
    · obtain ⟨k', m'', hr', hk', ht⟩ := ih (i + 1) m' (by omega) hu
      exact ⟨10 + k', m'', hr.trans hr', by omega, ht⟩
    · exact ⟨13, m', hr, by omega, ht⟩

theorem a_loop {m0 : Machine} (hpre : Pre m0) :
    ∀ d i m, (m0.reg 11).toNat / 64 = i + 1 + d → AAt m0 m i →
      ∃ k m', RunsIn zesuImage k m m' ∧ k ≤ 8 * (d + 1) ∧ TAt m0 m' := by
  intro d
  induction d with
  | zero =>
    intro i m hd h
    obtain ⟨k, m', hr, hc⟩ := a_iter hpre h
    rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ht⟩
    · have := ha.lt; omega
    · exact ⟨8, m', hr, by omega, ht⟩
  | succ d ih =>
    intro i m hd h
    obtain ⟨k, m', hr, hc⟩ := a_iter hpre h
    rcases hc with ⟨rfl, ha⟩ | ⟨rfl, ht⟩
    · obtain ⟨k', m'', hr', hk', ht⟩ := ih (i + 1) m' (by omega) ha
      exact ⟨8 + k', m'', hr.trans hr', by omega, ht⟩
    · exact ⟨8, m', hr, by omega, ht⟩

sym_run runD := run zesuImage [0x800ea210, 0x800ea260, 0x800ea280] 40 0x800ea1ec SM

theorem d_facts : runD_leaves = [runD_leaves[0]!, runD_leaves[1]!, runD_leaves[2]!, runD_leaves[3]!] ∧
    keepsM (runD_leaves[0]!).S = true ∧ (runD_leaves[0]!).S.regions.length = 1 ∧
    (∀ t < 32, (runD_leaves[0]!).S.mem.find? (·.covers 0 (8 + t)) = none) ∧
    (∀ t < 8, (runD_leaves[0]!).S.mem.find? (·.covers 0 (0x28 + t)) = some ⟨0, 0x28, 8, .ptr 0 8⟩) ∧
    (∀ t < 8, (runD_leaves[0]!).S.mem.find? (·.covers 0 (0x30 + t)) = some ⟨0, 0x30, 8, .var 10⟩) ∧
    keepsM (runD_leaves[1]!).S = true ∧ (runD_leaves[1]!).S.regions.length = 1 ∧
    (runD_leaves[1]!).S.mem = [] ∧
    keepsM (runD_leaves[2]!).S = true ∧ (runD_leaves[2]!).S.regions.length = 1 ∧
    (runD_leaves[2]!).S.mem = [] ∧
    keepsM (runD_leaves[3]!).S = true ∧ (runD_leaves[3]!).S.regions.length = 1 ∧
    (runD_leaves[3]!).S.mem = [] := by decide

/-- From the end of the prologue to `0x800ea280`, through the loop `a0 & 7` selects. -/
theorem blocks {m0 m : Machine} (hpre : Pre m0) (hpc : m.pc.toNat = 0x800ea1ec) (hb : Body m0 m)
    (hst : FrameAt m 8 (Sha256.leBytes Sha256.H0)) :
    ∃ k m', RunsIn zesuImage k m m' ∧ k ≤ 22 + 10 * ((m0.reg 11).toNat / 64) ∧ TAt m0 m' := by
  have hn := nums hpre
  have := hn.lo; have := hn.hi; have := hn.al
  obtain ⟨l, hl, hc, hr⟩ := segM runD hpre hb.mid (ro_mid hpre hn hb.mid) hpc
  obtain ⟨hls, hk0, hlen0, hn0a, hf28, hf30, hk1, hlen1, hmem1, hk2, hlen2, hmem2, hk3, hlen3,
    hmem3⟩ := d_facts
  rw [hls] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  have h11 : m.reg 11 = m0.reg 11 := hb.a1
  have h10 : m.reg 10 = m0.reg 10 := hb.a0
  have hsp := hb.mid.sp
  have hal : ∀ (b : Bool), ((m.reg 10 &&& 7#64) == 0#64) = b → ((m0.reg 10).toNat % 8 = 0 ↔ b = true) := by
    intro b hb
    rw [← hb, h10]
    simp only [beq_iff_eq]
    constructor
    · intro h8; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, show (7#64 : Word).toNat = 2 ^ 3 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]; simpa using h8
    · intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_and, show (7#64 : Word).toNat = 2 ^ 3 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at this
      simpa using this
  have hn64 : ∀ b : Bool, (!(m.reg 11).ult 64#64) = b → (64 ≤ (m0.reg 11).toNat ↔ b = true) := by
    intro b hb; rw [← hb, h11]; simp [BitVec.ult]
  have hst0 : Sha256.H0 = Sha256.foldBlocks (msgOf m0) 0 := rfl
  have hfold0 : ∀ {S : SState}, S.regions.length = 1 → S.mem = [] → ∀ {m'}, Match (envM m) S m' →
      m'.reg 2 = m.reg 2 → FrameAt m' 8 (Sha256.leBytes (Sha256.foldBlocks (msgOf m0) 0)) :=
    fun hl hm' _ hm hs => frameAt_leaf hm hs hl hst
      (by simp [Sha256.leBytes_length (Sha256.foldBlocks_length _ _)])
      (fun t _ => by rw [hm']; rfl)
  rcases hl with rfl | rfl | rfl | rfl
  · -- aligned, a whole block
    have c1 := hc (.eq (.bin .and (.var 10) (.lit 7)) (.lit 0)) (by decide)
    have c2 := hc (.geu (.var 11) (.lit 64)) (by decide)
    have ha8 := (hal true c1).2 rfl
    have hge := (hn64 true c2).2 rfl
    obtain ⟨m', hrun, hm', hex, hso⟩ := hr (fun o ho => by simp [runD_leaves] at ho)
    have hmid' := mid_leaf hn hb.mid hm' hso hk0 hlen0
    have hk : ∀ r : Fin 32, (runD_leaves[0]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m'.reg r = m.reg r := fun r h1 h2 => reg_kept hm' (by rw [h1, if_neg h2])
    have hsp' : m'.reg 2 = m.reg 2 := by rw [hmid'.sp, hsp]
    have hpar : ∀ {off : Nat} {s : Sym} {v : Word}, (∀ t < 8,
        (runD_leaves[0]!).S.mem.find? (·.covers 0 (off + t)) = some ⟨0, off, 8, s⟩) →
        off + 8 ≤ 0xe0 → s.eval (envM m) = v → FrameAt m' off (le8 v) := by
      intro off s v hfd hfit hv t ht
      have ht8 : t < 8 := by rw [le8_length] at ht; exact ht
      have := mem_of_find hm' (r := 0) (j := off + t) (by rw [hlen0]; decide)
        (by show _ < 0xe0; omega) (hfd t ht8)
      rw [show (envM m).base 0 = m.reg 2 from rfl] at this
      rw [hsp', this, le8_get]
      simp only [Nat.add_sub_cancel_left, hv]
    have hA : AAt m0 m' 0 := {
      pc := hex
      body := ⟨hmid', by rw [hk 10 rfl (by decide), h10], by rw [hk 11 rfl (by decide), h11]⟩
      st := by
        rw [← hst0]
        have h32 : (Sha256.leBytes Sha256.H0).length = 32 := by decide
        exact frameAt_leaf hm' hsp' hlen0 hst (by rw [h32]; decide)
          (fun t ht => hn0a t (by omega))
      a3 := by rw [reg_of_match hm']; show m.reg 10 = _; rw [h10]; simp
      a4 := by rw [reg_of_match hm']; rfl
      a5 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 8 = _; rw [hsp]; rfl
      a6 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 40 = _; rw [hsp]; rfl
      pb := hpar hf28 (by decide) (by show m.reg 2 + BitVec.ofInt 64 8 = _; rw [hsp]; rfl)
      ib := hpar hf30 (by decide) (by show m.reg 10 = _; rw [h10]; simp)
      al := ha8
      lt := by omega }
    obtain ⟨k, m'', hr', hk', ht⟩ := a_loop hpre ((m0.reg 11).toNat / 64 - 1) 0 m' (by omega) hA
    exact ⟨10 + k, m'', hrun.trans hr', by omega, ht⟩
  · -- aligned, no whole block
    have c2 := hc (.ltu (.var 11) (.lit 64)) (by decide)
    have hlt64 : (m0.reg 11).toNat < 64 := by
      simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, envM_vars, BitVec.ult,
        decide_eq_true_eq] at c2
      rw [show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl, h11] at c2
      simpa using c2
    obtain ⟨m', hrun, hm', hex, hso⟩ := hr (fun o ho => by simp [runD_leaves] at ho)
    have hmid' := mid_leaf hn hb.mid hm' hso hk1 hlen1
    have hk : ∀ r : Fin 32, (runD_leaves[1]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m'.reg r = m.reg r := fun r h1 h2 => reg_kept hm' (by rw [h1, if_neg h2])
    have hsp' : m'.reg 2 = m.reg 2 := by rw [hmid'.sp, hsp]
    have hd0 : (m0.reg 11).toNat / 64 = 0 := by omega
    have hT : TAt m0 m' := {
      pc := hex
      body := ⟨hmid', by rw [hk 10 rfl (by decide), h10], by rw [hk 11 rfl (by decide), h11]⟩
      st := by rw [hd0]; exact hfold0 hlen1 hmem1 hm' hsp'
      a3 := by rw [reg_of_match hm', hd0]; rfl
      a4 := by
        rw [reg_of_match hm']; show m.reg 11 = _
        rw [h11, Nat.mod_eq_of_lt hlt64]; simp
      a5 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 40 = _; rw [hsp]; rfl
      a6 := by rw [reg_of_match hm']; rfl }
    exact ⟨9, m', hrun, by omega, hT⟩
  · -- unaligned, no whole block
    have c2 := hc (.ltu (.var 11) (.lit 64)) (by decide)
    have hlt64 : (m0.reg 11).toNat < 64 := by
      simp only [SBool.eval, Sym.eval_var, Sym.eval_lit, envM_vars, BitVec.ult,
        decide_eq_true_eq] at c2
      rw [show (Fin.ofNat 32 11 : Fin 32) = 11 from rfl, h11] at c2
      simpa using c2
    obtain ⟨m', hrun, hm', hex, hso⟩ := hr (fun o ho => by simp [runD_leaves] at ho)
    have hmid' := mid_leaf hn hb.mid hm' hso hk2 hlen2
    have hk : ∀ r : Fin 32, (runD_leaves[2]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m'.reg r = m.reg r := fun r h1 h2 => reg_kept hm' (by rw [h1, if_neg h2])
    have hsp' : m'.reg 2 = m.reg 2 := by rw [hmid'.sp, hsp]
    have hd0 : (m0.reg 11).toNat / 64 = 0 := by omega
    have hT : TAt m0 m' := {
      pc := hex
      body := ⟨hmid', by rw [hk 10 rfl (by decide), h10], by rw [hk 11 rfl (by decide), h11]⟩
      st := by rw [hd0]; exact hfold0 hlen2 hmem2 hm' hsp'
      a3 := by rw [reg_of_match hm', hd0]; rfl
      a4 := by
        rw [reg_of_match hm']; show m.reg 11 = _
        rw [h11, Nat.mod_eq_of_lt hlt64]; simp
      a5 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 40 = _; rw [hsp]; rfl
      a6 := by rw [reg_of_match hm']; rfl }
    exact ⟨9, m', hrun, by omega, hT⟩
  · -- unaligned, a whole block
    have c2 := hc (.geu (.var 11) (.lit 64)) (by decide)
    have hge := (hn64 true c2).2 rfl
    obtain ⟨m', hrun, hm', hex, hso⟩ := hr (fun o ho => by simp [runD_leaves] at ho)
    have hmid' := mid_leaf hn hb.mid hm' hso hk3 hlen3
    have hk : ∀ r : Fin 32, (runD_leaves[3]!).S.reg r.val = .var r.val → r.val ≠ 0 →
        m'.reg r = m.reg r := fun r h1 h2 => reg_kept hm' (by rw [h1, if_neg h2])
    have hsp' : m'.reg 2 = m.reg 2 := by rw [hmid'.sp, hsp]
    have hU : UAt m0 m' 0 := {
      pc := hex
      body := ⟨hmid', by rw [hk 10 rfl (by decide), h10], by rw [hk 11 rfl (by decide), h11]⟩
      st := hfold0 hlen3 hmem3 hm' hsp'
      a3 := by rw [reg_of_match hm']; show m.reg 10 = _; rw [h10]; simp
      a4 := by rw [reg_of_match hm']; rfl
      a5 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 40 = _; rw [hsp]; rfl
      a6 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 8 = _; rw [hsp]; rfl
      a7 := by rw [reg_of_match hm']; show m.reg 2 + BitVec.ofInt 64 104 = _; rw [hsp]; rfl
      lt := by omega }
    obtain ⟨k, m'', hr', hk', ht⟩ := u_loop hpre ((m0.reg 11).toNat / 64 - 1) 0 m' (by omega) hU
    exact ⟨9 + k, m'', hrun.trans hr', by omega, ht⟩

end ZesuExec.Fn.Sha256
