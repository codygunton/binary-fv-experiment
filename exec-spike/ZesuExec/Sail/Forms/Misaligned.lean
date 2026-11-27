import ZesuExec.Sail.Forms.Mem

/-!
# Misaligned loads and stores in the Sail model

The profile's `plat_misaligned_access.load_store` is `none` (no trap), so `vmem_read_addr` and
`vmem_write_addr` split a misaligned access of `2^k` bytes into `2^k / 2^c` aligned pieces of
`2^c` bytes, `c` = the address's trailing zeros (`split_misaligned`), and run them in increasing
address order. These lemmas run that loop: the read returns the little-endian value of all the
bytes, the write writes them one piece at a time.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open PreSail
open LeanRV64DExecutable.Functions
open Register
open MemoryAccessType mem_payload page_based_mem_type


theorem upd_toNat {w : Nat} (x : BitVec w) (lo L : Nat) (y : BitVec L) (hx : x.toNat < 2 ^ lo)
    (hw : lo + L ≤ w) :
    (Sail.BitVec.updateSubrange' x lo L y).toNat = x.toNat + 2 ^ lo * y.toNat := by
  have hm : (~~~((BitVec.allOnes L).zeroExtend w <<< lo) &&& x) = x := by
    ext i hi
    by_cases h : i < lo
    · simp [h]
    · have : x[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
        have : x.toNat / 2 ^ i = 0 :=
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [this]
      simp [this]
  have hy : y.toNat < 2 ^ L := y.isLt
  have hlt : y.toNat * 2 ^ lo < 2 ^ w := by
    calc y.toNat * 2 ^ lo < 2 ^ L * 2 ^ lo := Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos _)
      _ = 2 ^ (L + lo) := by rw [Nat.pow_add]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
  have hz : ((y.zeroExtend w) <<< lo).toNat = y.toNat <<< lo := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (a := y.toNat) (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt]
  unfold Sail.BitVec.updateSubrange'
  simp only [hm]
  rw [BitVec.toNat_or, hz, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]; omega

theorem leNat_append : ∀ (l1 l2 : List (BitVec 8)),
    leNat (l1 ++ l2) = leNat l1 + 256 ^ l1.length * leNat l2
  | [], l2 => by simp [leNat]
  | b :: l1, l2 => by
    simp only [List.cons_append, leNat, leNat_append l1 l2, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ _)]; omega
/-- `untilFuelM.go` runs `k` iterations when the condition holds exactly after the last. -/
theorem go_runs {ε α : Type} (cond : α → SailME ε Bool) (body : α → SailME ε α)
    (s : State) : ∀ (k : Nat) (x : Nat → α),
    (∀ j < k, RunsME (body (x j)) s s (x (j + 1))) →
    (∀ j < k, RunsME (cond (x (j + 1))) s s (decide (j + 1 = k))) →
    RunsME (untilFuelM.go cond body (x 0) k) s s (x k)
  | 0, x, _, _ => RunsME.pure _ s
  | k + 1, x, hb, hc => by
    simp only [untilFuelM.go]
    refine RunsME.bind (hb 0 (by omega)) ?_
    refine RunsME.bind (hc 0 (by omega)) ?_
    by_cases hk : k = 0
    · subst hk; simp only [decide_true, ↓reduceIte]; exact RunsME.pure _ s
    · simp only [show (0 + 1 = k + 1) = False by simp; omega, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      have := go_runs cond body s k (fun j => x (j + 1)) (fun j hj => hb (j + 1) (by omega))
        (fun j hj => by have := hc (j + 1) (by omega); simpa using this)
      exact this

theorem go_runs' {ε α : Type} (cond : α → SailME ε Bool) (body : α → SailME ε α)
    (s : State) (k : Nat) (x : Nat → α) (init : α) (h0 : init = x 0)
    (hb : ∀ j < k, RunsME (body (x j)) s s (x (j + 1)))
    (hc : ∀ j < k, RunsME (cond (x (j + 1))) s s (decide (j + 1 = k))) :
    RunsME (untilFuelM.go cond body init k) s s (x k) := by
  subst h0; exact go_runs cond body s k x hb hc

theorem RunsME.pure_eq {ε α : Type} {v w : α} {s : State} (h : v = w) :
    RunsME (Pure.pure v : SailME ε α) s s w := h ▸ RunsME.pure v s

theorem plat_misaligned_load_run (s : State) :
    Runs (plat_misaligned_exception (Load Data) false) s s none := by rfl

theorem vmem_read_addr_split_run (s : State) (a mstatusBits : BitVec 64) (W n b : Nat)
    (bs : List (BitVec 8))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hna : is_aligned_vaddr (virtaddr.Virtaddr a) W = false)
    (hsplit : Runs (split_misaligned (virtaddr.Virtaddr a) W) s s ((n : Int), (b : Int)))
    (hn : 0 < n) (hb : 0 < b) (hW : n * b = W) (hlen : bs.length = W)
    (v : Nat → BitVec (8 * b))
    (hv : ∀ j < n, (v j).toNat = leNat ((bs.drop (j * b)).take b))
    (hpiece : ∀ j < n, Runs (mem_read (Load Data) PBMT_PMA
        (physaddr.Physaddr (Sail.BitVec.addInt a ((j : Int) * (b : Int)))) b false false false)
        s s (Sail.Ok (v j))) :
    Runs (vmem_read_addr (virtaddr.Virtaddr a) W (Load Data) false false false) s s
      (.Ok (BitVec.ofNat (8 * W) (leNat bs))) := by
  unfold vmem_read_addr
  simp only [hna, LeanRV64DExecutable.Functions.not, Bool.not_false, ↓reduceIte]
  apply RunsME.run
  refine RunsME.bind (middle := s) (value := ()) ?blk ?rest
  case blk =>
    refine RunsME.bind (RunsME.lift _ s s none (plat_misaligned_load_run s)) ?_
    exact RunsME.pure () s
  refine RunsME.bind (RunsME.lift _ s s _ hsplit) ?_
  dsimp only [misaligned_order, sys_misaligned_order_decreasing, Bool.false_eq_true, ↓reduceIte,
    Int.toNat_natCast]
  let D : Nat → BitVec (8 * n * b) := fun j => BitVec.ofNat _ (leNat (bs.take (j * b)))
  let x : Nat → BitVec (8 * n * b) × Bool × Nat :=
    fun j => (D j, decide (j = n), if j = n then n - 1 else j)
  refine RunsME.bind (middle := s) (value := (D n, true, n - 1)) ?loop ?tail
  case tail =>
    have hlt : leNat bs < 2 ^ (8 * W) := by
      have := leNat_lt bs
      rwa [hlen, show (256 : Nat) ^ W = 2 ^ (8 * W) by rw [Nat.pow_mul]] at this
    have htake : bs.take (n * b) = bs := List.take_of_length_le (by omega)
    have : BitVec.setWidth (8 * W) (D n, true, n - 1).fst = BitVec.ofNat (8 * W) (leNat bs) := by
      apply BitVec.eq_of_toNat_eq
      simp only [D, htake, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := leNat bs) (Nat.lt_of_lt_of_le hlt
        (Nat.pow_le_pow_right (by decide) (by rw [← hW, Nat.mul_assoc]; omega))), Nat.mod_eq_of_lt hlt]
    rw [this]; exact RunsME.pure _ s
  refine RunsME.bind (middle := s) (value := x n) ?go ?wrap
  case wrap =>
    simp only [x, decide_true, ↓reduceIte]
    refine RunsME.pure_eq ?_
    simp only [Prod.mk.injEq, and_true]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (D n).isLt)
  unfold untilFuelM
  refine go_runs' _ _ s n x _ ?h0 ?hb ?hc
  case h0 =>
    simp only [x, D, Nat.zero_mul, List.take_zero, leNat, Bool.false_eq_true, ↓reduceIte]
    simp only [show (0 = n) = False by simp; omega, decide_false, ↓reduceIte]
    rfl
  case hc => intro j hj; exact RunsME.pure _ s
  intro j hj
  have hjn : (j = n) = False := by simp; omega
  simp only [x]
  generalize hk : (if j = n then n - 1 else j) = k
  have hkj : j = k := by rw [← hk, if_neg (by omega)]
  subst hkj
  have hd : decide (j = n) = false := by simp; omega
  refine RunsME.bind (RunsME.lift _ s s () (assert_true_run s _)) ?_
  refine RunsME.bind (middle := s) (value := D (j + 1)) ?blk ?out
  case blk =>
    refine RunsME.bind (RunsME.lift _ s s
      (Sail.Ok (physaddr.Physaddr (Sail.BitVec.addInt a ((j : Int) * (b : Int))), PBMT_PMA,
        init_ext_ptw))
      (translateAddr_machine_load_run s _ mstatusBits mstatusRead privRead mprvZero)) ?_
    refine RunsME.bind (RunsME.lift _ s s _ (hpiece j hj)) ?_
    refine RunsME.bind (RunsME.pure () s) ?_
    have h1 : 1 ≤ 8 * (j + 1) * b := by
      have := Nat.mul_le_mul (show 8 ≤ 8 * (j + 1) by omega) hb; omega
    have e1 : (8 * ((j : Int) + 1) * (b : Int) - 1).toNat = 8 * (j + 1) * b - 1 := by
      rw [show (8 * ((j : Int) + 1) * (b : Int) - 1) = ((8 * (j + 1) * b - 1 : Nat) : Int) by
        push_cast [Int.natCast_sub h1]; rfl, Int.toNat_natCast]
    have e2 : (8 * (j : Int) * (b : Int)).toNat = 8 * j * b := by
      rw [show (8 * (j : Int) * (b : Int)) = ((8 * j * b : Nat) : Int) by push_cast; rfl,
        Int.toNat_natCast]
    have hjb : (j + 1) * b ≤ n * b := Nat.mul_le_mul_right b (by omega)
    have hlj : (bs.take (j * b)).length = j * b := by
      rw [List.length_take]; have := Nat.mul_le_mul_right b (Nat.le_of_lt hj); omega
    have hpow : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by rw [Nat.pow_mul]
    have hDj : (D j).toNat = leNat (bs.take (j * b)) := by
      simp only [D, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have := leNat_lt (bs.take (j * b))
      rw [hlj, hpow] at this
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide)
        (by have := Nat.mul_le_mul_right b (Nat.le_of_lt hj); rw [Nat.mul_assoc]; omega))
    have htk : bs.take ((j + 1) * b) = bs.take (j * b) ++ (bs.drop (j * b)).take b := by
      rw [Nat.add_mul, Nat.one_mul, List.take_add]
    have hDj1 : (D (j + 1)).toNat = leNat (bs.take ((j + 1) * b)) := by
      simp only [D, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have := leNat_lt (bs.take ((j + 1) * b))
      rw [hpow] at this
      refine Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) ?_)
      rw [List.length_take, Nat.mul_assoc]; have := Nat.min_le_left ((j + 1) * b) bs.length
      exact Nat.mul_le_mul_left 8 (Nat.le_trans this hjb)
    have hL : 8 * (j + 1) * b - 1 - 8 * j * b + 1 = 8 * b := by
      rw [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
    have hsw : (BitVec.setWidth (8 * n * b) (D j)).toNat = leNat (bs.take (j * b)) := by
      rw [BitVec.toNat_setWidth]; exact (Nat.mod_eq_of_lt (D j).isLt).trans hDj
    refine RunsME.pure_eq (BitVec.eq_of_toNat_eq ?_)
    unfold Sail.BitVec.updateSubrange
    rw [upd_toNat]
    · erw [hsw]; rw [BitVec.toNat_setWidth, e2, e1, hDj1, htk, leNat_append, hlj, hpow,
        Nat.mod_eq_of_lt (a := (v j).toNat), hv j hj, Nat.mul_assoc]
      rw [hL]; exact (v j).isLt
    · erw [hsw]; rw [e2]
      have := leNat_lt (bs.take (j * b)); rw [hlj, hpow] at this; rwa [Nat.mul_assoc]
    · rw [e1, e2, hL, Nat.mul_assoc 8 j b, Nat.mul_assoc 8 n b, ← Nat.mul_add, ← Nat.add_one_mul]
      exact Nat.mul_le_mul_left 8 hjb
  refine RunsME.pure_eq ?_
  have hn1 : ((n : Int) - 1).toNat = n - 1 := by omega
  have hj1 : ((j : Int) + 1).toNat = j + 1 := by omega
  have hsw : BitVec.setWidth (8 * n * b) (D (j + 1)) = D (j + 1) :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (D (j + 1)).isLt)
  simp only [Bool.false_eq_true, ↓reduceIte, hn1, hj1, hd]
  erw [hsw]
  by_cases hjl : j + 1 = n
  · have : (j == n - 1) = true := by simp; omega
    simp only [this, ↓reduceIte, hjl, decide_true]
    rw [show n - 1 = j by omega]; rfl
  · have : (j == n - 1) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte, hjl, decide_false]
    rfl

theorem ctz_dvd (a : BitVec 64) : a.toNat % 2 ^ (BitVec.ctz a).toNat = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < (BitVec.ctz a).toNat
  · have := BitVec.getLsbD_false_of_lt_ctz hi
    simp only [BitVec.getLsbD] at this
    simp [hi, this]
  · simp [hi]

theorem ctz_lt_of_mod {a : BitVec 64} {k : Nat} (h : a.toNat % 2 ^ k ≠ 0) :
    (BitVec.ctz a).toNat < k := by
  apply Nat.lt_of_not_le
  intro hk
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < k
  · have := BitVec.getLsbD_false_of_lt_ctz (x := a) (i := i) (by omega)
    simp only [BitVec.getLsbD] at this
    simp [hi, this]
  · simp [hi]

theorem not_aligned_of_mod {a : BitVec 64} {n : Nat} (h : a.toNat % n ≠ 0) :
    is_aligned_vaddr (virtaddr.Virtaddr a) n = false := by
  cases he : is_aligned_vaddr (virtaddr.Virtaddr a) n
  · rfl
  · exfalso; apply h
    unfold is_aligned_vaddr at he
    simp only [Sail.BitVec.toNatInt, beq_iff_eq] at he
    have he' : ((a.toNat : Int)).tmod (n : Int) = 0 := he
    rw [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)] at he'
    have h2 : ((a.toNat % n : Nat) : Int) = 0 := by rw [Int.natCast_emod]; exact he'
    exact_mod_cast h2

theorem split_misaligned_run (s : State) (a : BitVec 64) (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (hna : a.toNat % 2 ^ k ≠ 0) :
    Runs (split_misaligned (virtaddr.Virtaddr a) (2 ^ k)) s s
      (((2 ^ k / 2 ^ (BitVec.ctz a).toNat : Nat) : Int), ((2 ^ (BitVec.ctz a).toNat : Nat) : Int)) := by
  have hc := ctz_lt_of_mod hna
  have hct : Sail.BitVec.countTrailingZeros (bits_of_virtaddr (virtaddr.Virtaddr a)) =
      (BitVec.ctz a).toNat := rfl
  have hal := not_aligned_of_mod hna
  unfold split_misaligned
  simp only [hal, hct, Bool.false_or]
  generalize (BitVec.ctz a).toNat = c at hc
  rcases hk with rfl | rfl | rfl <;> (rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl) <;>
    first | omega | (simp [allowed_misaligned, sys_misaligned_allowed_within_exp,
      sys_misaligned_byte_by_byte]; rw [if_neg (fun h => absurd h.1 (by decide))]; rfl)

theorem mem_read_piece_run (st : State) (addr mstatusBits : BitVec 64) (vs : List (BitVec 8))
    (b : Nat) (hl : vs.length = b)
    (mstatusRead : st.regs.get? mstatus = some mstatusBits)
    (privRead : st.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hmem : ∀ (i : Nat) (h : i < vs.length), st.mem.get? (addr.toNat + i) = some vs[i])
    (phys : Runs (phys_access_check (Load Data) PBMT_PMA .Machine (physaddr.Physaddr addr) b false)
      st st none) :
    Runs (mem_read (Load Data) PBMT_PMA (physaddr.Physaddr addr) b false false false) st st
      (Sail.Ok (BitVec.ofNat (8 * b) (leNat vs))) := by
  subst hl
  have h := mem_read_load_run st addr mstatusBits vs mstatusRead privRead mprvZero hmem phys
  have he : leWord vs = BitVec.ofNat (8 * vs.length) (leNat vs) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_leWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := leNat_lt vs; rwa [show (256 : Nat) ^ vs.length = 2 ^ (8 * vs.length) by
      rw [Nat.pow_mul]] at this
  rwa [he] at h

theorem readable_sub {a j b W : Nat} (h : Machine.readable a W = true) (hj : j + b ≤ W) :
    Machine.readable (a + j) b = true := by
  simp only [Machine.readable, Machine.inRange, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  omega

theorem vmem_read_misaligned_run (st : State) (rs : regidx) (offset a mstatusBits : BitVec 64)
    (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (mstatusRead : st.regs.get? mstatus = some mstatusBits)
    (privRead : st.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hpma : st.regs.get? pma_regions = some zesuPmaRegions)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) (2 ^ k)) st st
      (.Ext_DataAddr_OK (virtaddr.Virtaddr a)))
    (hna : a.toNat % 2 ^ k ≠ 0) (hrd : Machine.readable a.toNat (2 ^ k) = true)
    (bs : List (BitVec 8)) (hlen : bs.length = 2 ^ k)
    (hmem : ∀ (i : Nat) (h : i < bs.length), st.mem.get? (a.toNat + i) = some bs[i])
    (v : BitVec (8 * 2 ^ k)) (hv : v.toNat = leNat bs) :
    Runs (vmem_read rs offset (2 ^ k) (Load Data) false false false) st st (.Ok v) := by
  have hc := ctz_lt_of_mod hna
  have hab := ctz_dvd a
  have hsplit := split_misaligned_run st a k hk hna
  generalize (BitVec.ctz a).toNat = c at hc hab hsplit ⊢
  have hb : 0 < 2 ^ c := Nat.two_pow_pos c
  have hdvd : 2 ^ c ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
  have hW : 2 ^ k / 2 ^ c * 2 ^ c = 2 ^ k := Nat.div_mul_cancel hdvd
  have hn : 0 < 2 ^ k / 2 ^ c := Nat.div_pos (Nat.pow_le_pow_right (by decide) (by omega)) hb
  have hfit : a.toNat + 2 ^ k ≤ 2 ^ 64 := by
    simp only [Machine.readable, Machine.inRange, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Layout.rodataLo, Layout.rodataHi, Layout.inputLo, Layout.inputHi,
      Layout.ramLo, Layout.ramHi] at hrd
    omega
  have hres : BitVec.ofNat (8 * 2 ^ k) (leNat bs) = v := by
    apply BitVec.eq_of_toNat_eq; rw [hv, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (hv ▸ v.isLt)
  refine vmem_read_of_addr_run (2 ^ k) st rs offset a v addrReg ?_
  rw [← hres]
  refine vmem_read_addr_split_run st a mstatusBits (2 ^ k) (2 ^ k / 2 ^ c) (2 ^ c) bs mstatusRead
    privRead mprvZero (not_aligned_of_mod hna) hsplit hn hb hW hlen
    (fun j => BitVec.ofNat (8 * 2 ^ c) (leNat ((bs.drop (j * 2 ^ c)).take (2 ^ c)))) ?hv ?hp
  case hv =>
    intro j hj
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := leNat_lt ((bs.drop (j * 2 ^ c)).take (2 ^ c))
    rw [show (256 : Nat) ^ _ = 2 ^ (8 * _) by rw [Nat.pow_mul]] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left 8 (List.length_take_le _ _)))
  intro j hj
  have hjb : j * 2 ^ c + 2 ^ c ≤ 2 ^ k := by
    rw [← hW, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have haddr : (Sail.BitVec.addInt a ((j : Int) * ((2 ^ c : Nat) : Int))).toNat = a.toNat + j * 2 ^ c := by
    unfold Sail.BitVec.addInt
    rw [show ((j : Int) * ((2 ^ c : Nat) : Int)) = ((j * 2 ^ c : Nat) : Int) by push_cast; rfl,
      BitVec.ofInt_natCast]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j * 2 ^ c) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hlp : ((bs.drop (j * 2 ^ c)).take (2 ^ c)).length = 2 ^ c := by
    simp only [List.length_take, List.length_drop]; omega
  refine mem_read_piece_run st _ mstatusBits _ (2 ^ c) hlp mstatusRead privRead mprvZero ?_ ?_
  · intro i hi
    erw [haddr]; rw [Nat.add_assoc]
    have hi' : j * 2 ^ c + i < bs.length := by rw [hlp] at hi; omega
    rw [hmem (j * 2 ^ c + i) hi']
    simp [List.getElem_take, List.getElem_drop]
  · refine phys_access_check_machine_load_allowed st _ (2 ^ c) (loadPma hpma hb ?_) ?_
    · erw [haddr]; exact readable_sub hrd hjb
    · refine (aligned_of_mod ?_).2
      erw [haddr]; rw [Nat.add_mul_mod_self_right]; exact hab

/-- A load of `2^k` bytes (`k ≤ 3`) whose range `Machine.readable` admits runs to the bytes'
little-endian value: the aligned case by `haligned`, the misaligned one split into pieces. -/
theorem vmem_read_any_run (st : State) (rs : regidx) (offset a mstatusBits : BitVec 64)
    (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (mstatusRead : st.regs.get? mstatus = some mstatusBits)
    (privRead : st.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hpma : st.regs.get? pma_regions = some zesuPmaRegions)
    (addrReg : Runs (get_transformed_data_addr rs offset (Load Data) (2 ^ k)) st st
      (.Ext_DataAddr_OK (virtaddr.Virtaddr a)))
    (hrd : Machine.readable a.toNat (2 ^ k) = true)
    (bs : List (BitVec 8)) (hlen : bs.length = 2 ^ k)
    (hmem : ∀ (i : Nat) (h : i < bs.length), st.mem.get? (a.toNat + i) = some bs[i])
    (v : BitVec (8 * 2 ^ k)) (hv : v.toNat = leNat bs)
    (haligned : a.toNat % 2 ^ k = 0 →
      Runs (vmem_read rs offset (2 ^ k) (Load Data) false false false) st st (.Ok v)) :
    Runs (vmem_read rs offset (2 ^ k) (Load Data) false false false) st st (.Ok v) := by
  by_cases hal : a.toNat % 2 ^ k = 0
  · exact haligned hal
  · exact vmem_read_misaligned_run st rs offset a mstatusBits k hk mstatusRead privRead mprvZero
      hpma addrReg hal hrd bs hlen hmem v hv

/-! ## Misaligned stores -/
/-- `untilFuelM.go` with a state that changes on every iteration. -/
theorem go_runs_st {ε α : Type} (cond : α → SailME ε Bool) (body : α → SailME ε α) :
    ∀ (k : Nat) (x : Nat → α) (σ : Nat → State),
    (∀ j < k, RunsME (body (x j)) (σ j) (σ (j + 1)) (x (j + 1))) →
    (∀ j < k, RunsME (cond (x (j + 1))) (σ (j + 1)) (σ (j + 1)) (decide (j + 1 = k))) →
    RunsME (untilFuelM.go cond body (x 0) k) (σ 0) (σ k) (x k)
  | 0, x, σ, _, _ => RunsME.pure _ _
  | k + 1, x, σ, hb, hc => by
    simp only [untilFuelM.go]
    refine RunsME.bind (hb 0 (by omega)) ?_
    refine RunsME.bind (hc 0 (by omega)) ?_
    by_cases hk : k = 0
    · subst hk; simp only [decide_true, ↓reduceIte]; exact RunsME.pure _ _
    · simp only [show (0 + 1 = k + 1) = False by simp; omega, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact go_runs_st cond body k (fun j => x (j + 1)) (fun j => σ (j + 1))
        (fun j hj => hb (j + 1) (by omega))
        (fun j hj => by have := hc (j + 1) (by omega); simpa using this)

/-- Byte `t` of a word's `k`-th `b`-byte piece is byte `k b + t` of the word. -/
theorem piece_byte (d : Nat) (k b t : Nat) (ht : t < b) :
    (d / 2 ^ (8 * (k * b)) % 2 ^ (8 * b)) / 2 ^ (8 * t) % 2 ^ 8 =
      d / 2 ^ (8 * (k * b + t)) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 8
  · have : i + 8 * t < 8 * b := by omega
    simp only [hi, decide_true, Bool.true_and, this]
    congr 1; rw [Nat.mul_add]; omega
  · simp [hi]

theorem go_runs_st' {ε α : Type} (cond : α → SailME ε Bool) (body : α → SailME ε α)
    (k : Nat) (x : Nat → α) (σ : Nat → State) (init : α) (h0 : init = x 0) (s0 sk : State)
    (hs0 : s0 = σ 0) (hsk : sk = σ k)
    (hb : ∀ j < k, RunsME (body (x j)) (σ j) (σ (j + 1)) (x (j + 1)))
    (hc : ∀ j < k, RunsME (cond (x (j + 1))) (σ (j + 1)) (σ (j + 1)) (decide (j + 1 = k))) :
    RunsME (untilFuelM.go cond body init k) s0 sk (x k) := by
  subst h0 hs0 hsk; exact go_runs_st cond body k x σ hb hc

theorem int_hi (j b : Nat) (hb : 0 < b) :
    (8 * ((j : Int) + 1) * (b : Int) - 1).toNat = 8 * (j + 1) * b - 1 := by
  have h1 : 1 ≤ 8 * (j + 1) * b := by
    have := Nat.mul_le_mul (show 8 ≤ 8 * (j + 1) by omega) hb; omega
  rw [show (8 * ((j : Int) + 1) * (b : Int) - 1) = ((8 * (j + 1) * b - 1 : Nat) : Int) by
    push_cast [Int.natCast_sub h1]; rfl, Int.toNat_natCast]

theorem int_lo (j b : Nat) : (8 * (j : Int) * (b : Int)).toNat = 8 * j * b := by
  rw [show (8 * (j : Int) * (b : Int)) = ((8 * j * b : Nat) : Int) by push_cast; rfl,
    Int.toNat_natCast]

theorem extract_piece {W b j : Nat} (data : BitVec (8 * W)) (hb : 0 < b) :
    (BitVec.setWidth (8 * b) (Sail.BitVec.extractLsb data (8 * ((j : Int) + 1) * (b : Int) - 1).toNat
      (8 * (j : Int) * (b : Int)).toNat)).toNat =
      data.toNat / 2 ^ (8 * (j * b)) % 2 ^ (8 * b) := by
  have hL : 8 * (j + 1) * b - 1 - 8 * j * b + 1 = 8 * b := by
    have := Nat.mul_le_mul (show 8 ≤ 8 * (j + 1) by omega) hb
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_one]; omega
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, int_hi j b hb, int_lo, hL, Nat.mod_mod]
  rw [Nat.mul_assoc]

theorem vmem_write_addr_split_run (s : State) (a mstatusBits : BitVec 64) (W n b : Nat)
    (data : BitVec (8 * W))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hpma : s.regs.get? pma_regions = some zesuPmaRegions)
    (hna : is_aligned_vaddr (virtaddr.Virtaddr a) W = false)
    (hsplit : Runs (split_misaligned (virtaddr.Virtaddr a) W) s s ((n : Int), (b : Int)))
    (hn : 0 < n) (hb : 0 < b) (hW : n * b = W) (hab : a.toNat % b = 0)
    (hwr : Machine.writable a.toNat W = true) :
    ∃ s', Runs (vmem_write_addr (virtaddr.Virtaddr a) W data (Store Data) false false false) s s'
        (.Ok true) ∧ s'.regs = s.regs ∧
      ∀ x, s'.mem.get? x = if a.toNat ≤ x ∧ x < a.toNat + W then
        some (data.extractLsb' (8 * (x - a.toNat)) 8) else s.mem.get? x := by
  have hfit : a.toNat + W ≤ 2 ^ 64 := by
    simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq,
      Layout.ramLo, Layout.ramHi] at hwr
    omega
  let Wd : Nat → BitVec (8 * b) := fun j => BitVec.ofNat (8 * b) (data.toNat / 2 ^ (8 * (j * b)))
  let σ : Nat → State := fun k => Nat.rec (motive := fun _ => State) s
    (fun j sj => afterWriteBytes sj (a.toNat + j * b) (Wd j)) k
  have hregs : ∀ k, (σ k).regs = s.regs := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => exact (afterWriteBytes_regs _ _ _).trans ih
  have hmemk : ∀ k, k ≤ n → ∀ x, (σ k).mem.get? x = if a.toNat ≤ x ∧ x < a.toNat + k * b then
      some (data.extractLsb' (8 * (x - a.toNat)) 8) else s.mem.get? x := by
    intro k; induction k with
    | zero => intro _ x; simp only [Nat.zero_mul, Nat.add_zero]; rw [if_neg (by omega)]; rfl
    | succ k ih =>
      intro hk x
      have hkb : (k + 1) * b ≤ W := by rw [← hW]; exact Nat.mul_le_mul_right b hk
      change (afterWriteBytes (σ k) (a.toNat + k * b) (Wd k)).mem.get? x = _
      by_cases hin : a.toNat + k * b ≤ x ∧ x < a.toNat + k * b + b
      · rw [show x = a.toNat + k * b + (x - a.toNat - k * b) by omega,
          afterWriteBytes_at _ _ _ _ (by omega), if_pos (by rw [Nat.succ_mul]; omega)]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Wd, BitVec.toNat_ofNat]
        rw [piece_byte _ _ _ _ (by omega)]
        congr 3; omega
      · rw [afterWriteBytes_mem_get?_of_outside _ _ _ _ (fun i => by have := i.isLt; omega),
          ih (by omega) x]
        by_cases h2 : a.toNat ≤ x ∧ x < a.toNat + k * b
        · rw [if_pos h2, if_pos (by rw [Nat.succ_mul]; omega)]
        · rw [if_neg h2, if_neg (by rw [Nat.succ_mul]; omega)]
  refine ⟨σ n, ?_, hregs n, fun x => by rw [hmemk n (Nat.le_refl n) x, hW]⟩
  unfold vmem_write_addr
  simp only [hna, LeanRV64DExecutable.Functions.not, Bool.not_false, ↓reduceIte,
    is_store_conditional, Bool.false_and, Bool.false_eq_true]
  apply RunsME.run
  refine RunsME.bind (middle := s) (value := ()) ?blk ?rest
  case blk =>
    refine RunsME.bind (RunsME.lift _ s s none (by rfl)) ?_
    exact RunsME.pure () s
  refine RunsME.bind (RunsME.lift _ s s _ hsplit) ?_
  dsimp only [misaligned_order, sys_misaligned_order_decreasing, Bool.false_eq_true, ↓reduceIte,
    Int.toNat_natCast]
  let x : Nat → Bool × Nat × Bool := fun j => (decide (j = n), if j = n then n - 1 else j, true)
  refine RunsME.bind (middle := σ n) (value := x n) ?loop ?tail
  case tail => exact RunsME.pure _ _
  refine RunsME.bind (middle := σ n) (value := x n) ?go (RunsME.pure _ _)
  unfold untilFuelM
  refine go_runs_st' _ _ n x σ _ ?h0 s (σ n) rfl rfl ?hb ?hc
  case h0 => simp only [x, show (0 = n) = False by simp; omega, decide_false, ↓reduceIte]; rfl
  case hc => intro j hj; exact RunsME.pure _ _
  intro j hj
  simp only [x]
  generalize hk : (if j = n then n - 1 else j) = k
  have hkj : j = k := by rw [← hk, if_neg (by omega)]
  subst hkj
  have hd : decide (j = n) = false := by simp; omega
  have hjb : j * b + b ≤ W := by rw [← hW, ← Nat.succ_mul]; exact Nat.mul_le_mul_right b hj
  have haddr : (Sail.BitVec.addInt a ((j : Int) * (b : Int))).toNat = a.toNat + j * b := by
    unfold Sail.BitVec.addInt
    rw [show ((j : Int) * (b : Int)) = ((j * b : Nat) : Int) by push_cast; rfl,
      BitVec.ofInt_natCast]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j * b) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hmst : (σ j).regs.get? mstatus = some mstatusBits := by rw [hregs]; exact mstatusRead
  have hprv : (σ j).regs.get? cur_privilege = some .Machine := by rw [hregs]; exact privRead
  have hpm : (σ j).regs.get? pma_regions = some zesuPmaRegions := by rw [hregs]; exact hpma
  refine RunsME.bind (RunsME.lift _ _ _ () (assert_true_run _ _)) ?_
  refine RunsME.bind (middle := σ (j + 1)) (value := true) ?blk ?out
  case blk =>
    refine RunsME.bind (RunsME.lift _ _ _
      (Sail.Ok (physaddr.Physaddr (Sail.BitVec.addInt a ((j : Int) * (b : Int))), PBMT_PMA,
        init_ext_ptw))
      (translateAddr_machine_store_run _ _ mstatusBits hmst hprv mprvZero)) ?_
    refine RunsME.bind (RunsME.lift _ _ _ () (by rfl)) ?_
    refine RunsME.bind (RunsME.lift _ _ _ (Sail.Ok ()) (mem_write_ea_store_run _ _ _)) ?_
    refine RunsME.bind (RunsME.lift _ _ (σ (j + 1)) (Sail.Ok true)
      (mem_write_value_store_run _ _ _ _ mstatusBits hmst hprv mprvZero ?phys ?hw)) ?_
    case phys =>
      refine phys_access_check_machine_store_allowed _ _ b (storePma hpm ?_) ?_
      · erw [haddr]
        simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq] at hwr ⊢
        omega
      · refine (aligned_of_mod ?_).2
        erw [haddr]; rw [Nat.add_mul_mod_self_right]; exact hab
    case hw =>
      have hv : BitVec.setWidth (8 * b) (Sail.BitVec.extractLsb data
          (8 * ((j : Int) + 1) * (b : Int) - 1).toNat (8 * (j : Int) * (b : Int)).toNat) = Wd j := by
        apply BitVec.eq_of_toNat_eq
        rw [extract_piece data hb]
        simp only [Wd, BitVec.toNat_ofNat]
      rw [hv]
      change Runs (PreSail.writeBytes (Sail.BitVec.addInt a ((j : Int) * (b : Int))).toNat (Wd j))
        (σ j) (afterWriteBytes (σ j) (a.toNat + j * b) (Wd j)) true
      rw [haddr]
      exact writeBytes_run_exact _ _ _
    exact RunsME.pure _ _
  refine RunsME.pure_eq ?_
  have hn1 : ((n : Int) - 1).toNat = n - 1 := by omega
  have hj1 : ((j : Int) + 1).toNat = j + 1 := by omega
  simp only [Bool.false_eq_true, ↓reduceIte, hn1, hj1, hd]
  by_cases hjl : j + 1 = n
  · have : (j == n - 1) = true := by simp; omega
    simp only [this, ↓reduceIte, hjl, decide_true]
    rw [show n - 1 = j by omega]
  · have : (j == n - 1) = false := by simp; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte, hjl, decide_false]

theorem low_byte (y M S : Nat) (h : S + 8 ≤ M) : y % 2 ^ M / 2 ^ S % 2 ^ 8 = y / 2 ^ S % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 8
  · simp only [hi, decide_true, Bool.true_and, show i + S < M by omega]
  · simp [hi]

theorem assert_run (st : State) (c : Bool) (msg : String) (h : c = true) :
    Runs (PreSail.assert c msg) st st () := by subst h; rfl

theorem execute_STORE_misaligned_run (st : State) (rs2 rs1 : regidx) (imm : BitVec 12) (k : Nat)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (dst mstatusBits : BitVec 64) (dataBits : BitVec 64)
    (mstatusRead : st.regs.get? mstatus = some mstatusBits)
    (privRead : st.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (hpma : st.regs.get? pma_regions = some zesuPmaRegions)
    (dataReg : Runs (rX_bits rs2) st st dataBits)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Store Data) (2 ^ k))
      st st (.Ext_DataAddr_OK (virtaddr.Virtaddr dst)))
    (hna : dst.toNat % 2 ^ k ≠ 0) (hwr : Machine.writable dst.toNat (2 ^ k) = true) :
    ∃ st', Runs (execute_STORE imm rs2 rs1 (2 ^ k)) st st' (.Retire_Success ()) ∧
      st'.regs = st.regs ∧
      ∀ x, st'.mem.get? x = if dst.toNat ≤ x ∧ x < dst.toNat + 2 ^ k then
        some (dataBits.extractLsb' (8 * (x - dst.toNat)) 8) else st.mem.get? x := by
  have hc := ctz_lt_of_mod hna
  have hab := ctz_dvd dst
  have hsplit := split_misaligned_run st dst k hk hna
  generalize (BitVec.ctz dst).toNat = c at hc hab hsplit
  have hb : 0 < 2 ^ c := Nat.two_pow_pos c
  have hW : 2 ^ k / 2 ^ c * 2 ^ c = 2 ^ k := Nat.div_mul_cancel (Nat.pow_dvd_pow 2 (by omega))
  have hn : 0 < 2 ^ k / 2 ^ c := Nat.div_pos (Nat.pow_le_pow_right (by decide) (by omega)) hb
  have hk8 : 2 ^ k ≤ 8 := by rcases hk with rfl | rfl | rfl <;> decide
  let data : BitVec (8 * 2 ^ k) :=
    BitVec.setWidth (8 * 2 ^ k)
      (Sail.BitVec.extractLsb dataBits (((2 ^ k : Nat) : Int) * 8 - 1).toNat 0)
  obtain ⟨st', hrun, hregs, hmem⟩ := vmem_write_addr_split_run st dst mstatusBits (2 ^ k)
    (2 ^ k / 2 ^ c) (2 ^ c) data mstatusRead privRead mprvZero hpma (not_aligned_of_mod hna)
    hsplit hn hb hW hab hwr
  refine ⟨st', ?_, hregs, fun x => ?_⟩
  · unfold execute_STORE
    refine Runs.bind (assert_run st _ _ (by rcases hk with rfl | rfl | rfl <;> decide)) ?_
    refine Runs.bind dataReg ?_
    refine Runs.bind (run_pure st _) ?_
    refine Runs.bind (value := Sail.Ok true) ?_ (run_pure st' _)
    unfold vmem_write
    apply RunsME.run
    refine RunsME.bind (middle := st) (value := virtaddr.Virtaddr dst) ?vaddr ?wr
    case vaddr =>
      refine RunsME.bind (RunsME.lift _ st st _ addrReg) ?_
      exact RunsME.pure _ st
    exact RunsME.lift _ st st' (Sail.Ok true) hrun
  · rw [hmem x]
    split
    · congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [data, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth,
        Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.div_one, Nat.pow_zero]
      have he : (((2 ^ k : Nat) : Int) * 8 - 1).toNat = 2 ^ k * 8 - 1 := by
        have : 1 ≤ 2 ^ k * 8 := by have := Nat.two_pow_pos k; omega
        rw [show (((2 ^ k : Nat) : Int) * 8 - 1) = ((2 ^ k * 8 - 1 : Nat) : Int) by
          push_cast [Int.natCast_sub this]; rfl, Int.toNat_natCast]
      rw [he, show 2 ^ k * 8 - 1 - 0 + 1 = 8 * 2 ^ k by have := Nat.two_pow_pos k; omega,
        Nat.mod_mod, low_byte _ _ _ (by omega)]
    · rfl

/-- `sim_store_of_exec` for an `execute` run whose final state is described byte by byte: the
`n` bytes of `v` at `addr`, every other byte and the registers as before. -/
theorem sim_store_of_exec' {img : Image} {m : Machine} {s : State} {w : Nat} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    {addr v : Word} {n : Nat} (hwr : Machine.writable addr.toNat n = true) {st' : State}
    (hregs : st'.regs = (T s m.pc).regs)
    (hmem : ∀ x, st'.mem.get? x = if addr.toNat ≤ x ∧ x < addr.toNat + n then
      some (v.extractLsb' (8 * (x - addr.toNat)) 8) else (T s m.pc).mem.get? x)
    (hexec : Runs (execute (toSail i)) (T s m.pc) st' (.Retire_Success ())) (n' : Nat) :
    ∃ s', Runs (try_step n' false) s s' false ∧
      Rel img ({ m with mem := Machine.writeBytes m.mem addr.toNat v n } : Machine).advance s' := by
  simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq,
    Layout.ramLo, Layout.ramHi] at hwr
  have hout : ∀ x, (x < addr.toNat ∨ addr.toNat + n ≤ x) → st'.mem.get? x = s.mem.get? x :=
    fun x hx => by rw [hmem x, if_neg (by omega)]; rfl
  refine sim_of_exec hR hw hd hpc hexec ?_ ?_ ?_ ?_ ?_ n'
  · rw [hregs, T_nextPC]; rfl
  · intro r _ _; rw [hregs]
  · intro j hj; rw [hregs]; exact RegsAgree.T (m := m) hR.regs m.pc j hj
  · intro x b hb
    simp only [Machine.advance] at hb
    by_cases hin : addr.toNat ≤ x.toNat ∧ x.toNat < addr.toNat + n
    · have hx : x = BitVec.ofNat 64 (addr.toNat + (x.toNat - addr.toNat)) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [hx, writeBytes_at _ _ _ _ _ (by omega) (by omega)] at hb
      cases hb
      rw [hmem, if_pos hin]
    · rw [writeBytes_outside _ _ _ _ _ (fun j hj e => hin (by
          rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))] at hb
      rw [hout _ (by omega)]; exact hR.mem x b hb
  · intro seg hseg k w' hk h1 h2 j hj
    simp only [Layout.textLo, Layout.textHi] at h1 h2
    rw [hout _ (by omega)]
    exact hR.code seg hseg k w' hk h1 h2 j hj

end ZesuExec.SailLink
