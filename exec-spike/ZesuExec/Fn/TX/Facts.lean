import ZesuExec.Fn.TX.Store

/-!
# TX: assertion facts for `leaf_auto` (programme plan S4b, `@[zesu_fact]`)

Facts of the cut assertions in the form the leaves' conditions take after `sym_simp` (registers
as `(envB σ m).vars i`, frame words as `Sym.init 0 off 8` reads), so that the infeasible-leaf rule
of `leaf_auto` closes the dead paths of the annotation file: `dead-344` (`remap` returns null:
`0x80000340` leaves with `a0 ≠ 0`), the zero-size copy (`0x80000340` with `40 c' = 0`) and the
growth overflow of `0x8000025c` (the entries list length is below `2^32`).
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- A frame word read from the initial memory of a `envB` state. -/
theorem frame_init {σ : Sig} {m : Machine} (hpre : Pre σ.A σ.g σ.m) {k : Nat} (hk : 8 ≤ k)
    (hk' : k ≤ 576) {v : Word} (h : m.load (σ.sl k) 8 = some v) :
    (Sym.init 0 (576 - k) 8).eval (envB σ m) = v := by
  apply init_eval_load (regs := shapeOf σ) (r := 0) (by simp [shapeOf])
  · rwa [show σ.sl k = ((shapeOf σ)[0]'(by simp [shapeOf])).1 + BitVec.ofNat 64 (576 - k) by
      simp only [shapeOf, List.getElem_cons_zero, Sig.sl, w, frameBytes]; bv_omega] at h
  · have := (entry_nums hpre).1
    simp only [shapeOf, List.getElem_cons_zero]
    rw [sl_toNat hpre (by decide)]
    unfold Layout.ramLo frameBytes at *; omega

/-- `dead-344`: `remap` (F0) returns null. -/
@[zesu_fact] theorem A340_a0 {σ : Sig} {m : Machine} (h : ARet remapC (unit Site33c) σ m) :
    (envB σ m).vars 10 = 0 := by
  obtain ⟨mc, _, -, ⟨-, h0, -⟩, -⟩ := h; exact h0

theorem grownCap_lt {n : Nat} (h : n < 2 ^ 32) : grownCap n < 2 ^ 34 := by
  unfold grownCap; omega

/-- After `remap`: the spilled sizes `32 c'` and `8 c'` of the grown entries buffer add up to a
nonzero `40 c'`. -/
@[zesu_fact] theorem A340_size {σ : Sig} {m : Machine} (h : ARet remapC (unit Site33c) σ m) :
    Sym.eval (envB σ m) (Sym.init 0 8 8) + Sym.eval (envB σ m) (Sym.init 0 16 8) ≠ 0#64 := by
  obtain ⟨mc, _, ⟨o, k, L, kp', hED, -, -, -, -, -, h230, h238, -, -⟩, ⟨-, -, hso⟩, -⟩ := h
  have hc := hED.1
  have hpre := hc.2.1
  have hR : ∀ {j : Nat}, 8 ≤ j → j ≤ 576 → ∀ a, InRange (mc.reg 2 - 16) 16 a →
      InRange (σ.sl j) 8 a → False := fun {j} hj hj' a h hin => by
    rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
    have h1 := sl_toNat hpre (k := 592) (by decide)
    have h2 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
    have := (entry_nums hpre).1; unfold Layout.ramLo at this
    simp only [InRange, h1, h2] at h hin; omega
  have e8 := frame_init hpre (k := 0x238) (by decide) (by decide)
    (frame_keep hpre hso (by decide) (by decide) (hR (by decide) (by decide)) h238)
  have e16 := frame_init hpre (k := 0x230) (by decide) (by decide)
    (frame_keep hpre hso (by decide) (by decide) (hR (by decide) (by decide)) h230)
  simp only [show 576 - 0x238 = 8 from rfl, show 576 - 0x230 = 16 from rfl] at e8 e16
  rw [e8, e16]
  have hEL := hED.2.2.2.1
  have hn : o.done.length < 2 ^ 32 := by have := hEL.2.1; have := hEL.2.2.2.2.1; omega
  have hg := grownCap_lt hn
  have hg0 : 0 < grownCap o.done.length := by unfold grownCap; omega
  simp only [w]
  rw [← BitVec.ofNat_add]
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  simp at this; omega

/-- At `0x8000025c` (after `toOwnedSlice` of the keys): the entries list header is as at the
call, so its length (`S-0x1b8`) and capacity (`S-0x1b0`) are below `2^32`. -/
theorem A25c_hdr {σ : Sig} {m : Machine} (h : ARet f4C Site258 σ m) :
    ∃ o : Obs, m.load (σ.sl 0x1b8) 8 = some (w o.done.length) ∧
      m.load (σ.sl 0x1b0) 8 = some o.ec ∧ o.done.length ≤ o.ec.toNat ∧ o.ec.toNat < 2 ^ 32 := by
  obtain ⟨mc, x, ⟨o, k, hIE, -, -, hKL, ha⟩, ⟨-, hso, -⟩, -⟩ := h
  have hc := hIE.1
  have hpre := hc.2.1
  have hlive := hIE.2.2.2.2.1
  have hEL := hIE.2.2.2.1
  have hres : mc.reg 10 = σ.sl 0xb8 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x118 := ha.arg 1 (by simp)
  obtain ⟨⟨hH0, -, hH16⟩, -⟩ := hKL
  have h2 := sl_toNat hpre (k := 0x1c0) (by decide)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  have hR : ∀ a, InRange (σ.sl 0x1c0) 24 a → ¬ (InRange (mc.reg 10) 24 a ∨
      InRange (mc.reg 11) 24 a ∨ InRange (mc.reg 2 - 112) 112 a ∨ InRange ToOwned.scratch 8 a ∨
      σ.A.Priv x.fst a ∨ (0 < (ToOwned.listCap mc).toNat ∧
        InRange (ToOwned.listPtr mc) ((ToOwned.listCap mc).toNat * F4.elemBytes) a)) := by
    intro a hin h
    have hs : InRange (σ.sl stackBytes) stackBytes a :=
      sl_in_stack hpre (by decide) (by decide) hin
    simp only [ToOwned.listPtr, ToOwned.listCap, hhdr, hres, f4w hH0, f4w hH16,
      show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc 112] at h
    rcases h with h | h | h | h | h | ⟨hc0, h⟩
    · have h1 := sl_toNat hpre (k := 0xb8) (by decide)
      simp only [InRange, h1, h2] at h hin; omega
    · have h1 := sl_toNat hpre (k := 0x118) (by decide)
      simp only [InRange, h1, h2] at h hin; omega
    · have h1 := sl_toNat hpre (k := 688) (by decide)
      simp only [InRange, h1, h2] at h hin; omega
    · exact scratch_not_stack hpre h hs
    · exact stack_not_priv hpre hs (priv_sub hpre hlive h)
    · refine stack_not_priv hpre hs ((hlive.2.2 (k.kq, keySize * k.kc.toNat) ?_).2.2 a ?_)
      · simp [EX, KX, hc0]
      · simpa [Nat.mul_comm, keySize, F4.elemBytes] using h
  have hin : ∀ {j : Nat}, 0x1b0 ≤ j → j ≤ 0x1b8 → ∀ a, InRange (σ.sl j) 8 a →
      InRange (σ.sl 0x1c0) 24 a := fun {j} hj hj' a h => by
    have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
    simp only [InRange, h2, h3] at h ⊢; omega
  refine ⟨o, frame_keep hpre hso (k := 0x1b8) (by decide) (by decide)
      (fun a h h' => hR a (hin (by decide) (by decide) a h') h) ?_,
    frame_keep hpre hso (k := 0x1b0) (by decide) (by decide)
      (fun a h h' => hR a (hin (by decide) (by decide) a h') h) ?_,
    hEL.2.1, hEL.2.2.2.2.1⟩
  · rw [show σ.sl 0x1b8 = σ.sl 0x1c0 + 8 by simp only [Sig.sl, w]; bv_omega]; exact hEL.1.2.1
  · rw [show σ.sl 0x1b0 = σ.sl 0x1c0 + 16 by simp only [Sig.sl, w]; bv_omega]; exact hEL.1.2.2

@[zesu_fact] theorem A25c_len {σ : Sig} {m : Machine} (h : ARet f4C Site258 σ m) :
    (Sym.eval (envB σ m) (Sym.init 0 136 8)).toNat < 2 ^ 32 := by
  have hpre : Pre σ.A σ.g σ.m := by obtain ⟨mc, x, ⟨o, k, hIE, -⟩, -⟩ := h; exact hIE.1.2.1
  obtain ⟨o, hl, -, hle, hlt⟩ := A25c_hdr h
  rw [show (136 : Nat) = 576 - 0x1b8 from rfl, frame_init hpre (by decide) (by decide) hl]
  simp only [w, BitVec.toNat_ofNat]; omega

/-! ## Growth of a full entries list (`0x8000025c`): `c' = n + 1 + (n + 1) / 2 + 1` with
`n < 2^32` neither overflows `40 c'` nor makes it zero. The statements are the leaves' conditions
in `leaf_norm` form over the length word `x`. -/

theorem grow_toNat {x : Word} (hx : x.toNat < 2 ^ 32) :
    ((x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64).toNat = grownCap x.toNat ∧
      (x + 1#64).toNat = x.toNat + 1 := by
  have h1 : (x + 1#64).toNat = x.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : ((x + 1#64) >>> ((1#64).toNat % 64)).toNat = (x.toNat + 1) / 2 := by
    rw [show (1#64).toNat % 64 = 1 from rfl, BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow]
  refine ⟨?_, h1⟩
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, h2, BitVec.toNat_ofNat]
  unfold grownCap
  have h3 : (x.toNat + 1) / 2 ≤ x.toNat + 1 := Nat.div_le_self _ _
  have h4 : (x.toNat + 1) / 2 + (x.toNat + 1) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h4, show 1 % 2 ^ 64 = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

theorem grow_val {x : Word} (hx : x.toNat < 2 ^ 32) :
    ((0#64 - if BitVec.toNat ((x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) <
        BitVec.toNat (x + 1#64) then 1 else 0) |||
      (x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) =
      BitVec.ofNat 64 (grownCap x.toNat) := by
  obtain ⟨h1, h2⟩ := grow_toNat hx
  have hg := grownCap_lt hx
  rw [if_neg (by rw [h1, h2]; unfold grownCap; omega), show (0#64 - 0 : Word) = 0#64 from rfl,
    BitVec.zero_or]
  apply BitVec.eq_of_toNat_eq
  rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[zesu_fact] theorem grow_mulhu {x : Word} (hx : x.toNat < 2 ^ 32) :
    BitVec.ofNat 64 (BitVec.toNat
      ((0#64 - if BitVec.toNat ((x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) <
        BitVec.toNat (x + 1#64) then 1 else 0) |||
      (x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) * (40#64).toNat / 2 ^ 64) = 0#64 := by
  have hg := grownCap_lt hx
  rw [grow_val hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (40#64).toNat = 40 from rfl,
    Nat.div_eq_of_lt (by omega)]

@[zesu_fact] theorem grow_bytes {x : Word} (hx : x.toNat < 2 ^ 32) :
    ((0#64 - if BitVec.toNat ((x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) <
        BitVec.toNat (x + 1#64) then 1 else 0) |||
      (x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) <<< ((5#64).toNat % 64) +
    ((0#64 - if BitVec.toNat ((x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) <
        BitVec.toNat (x + 1#64) then 1 else 0) |||
      (x + 1#64) >>> ((1#64).toNat % 64) + (x + 1#64) + 1#64) <<< ((3#64).toNat % 64) ≠ 0#64 := by
  have hg := grownCap_lt hx
  have h0 : 0 < grownCap x.toNat := by unfold grownCap; omega
  rw [grow_val hx]
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    show (5#64).toNat % 64 = 5 from rfl, show (3#64).toNat % 64 = 3 from rfl,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := grownCap x.toNat) (by omega)] at this
  have e1 : grownCap x.toNat * 2 ^ 5 % 2 ^ 64 = grownCap x.toNat * 32 := Nat.mod_eq_of_lt (by omega)
  have e2 : grownCap x.toNat * 2 ^ 3 % 2 ^ 64 = grownCap x.toNat * 8 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, Nat.mod_eq_of_lt (by omega)] at this
  simp at this; omega

/-! ## `Common` at every cut, and the saved return address -/

@[zesu_fact] theorem A068_common {σ : Sig} {m : Machine} (h : ARet f2C (unit Site064) σ m) :
    Common σ m := by
  obtain ⟨mc, _, hs, hpost, hp⟩ := h
  exact common_f2 hs.1 (hs.2.2.2.2.2.2.2.arg 0 (by simp)) (by decide) (by decide) hpost hp

@[zesu_fact] theorem A0c4_common {σ : Sig} {m : Machine} (h : AOuter σ m) : Common σ m := by
  obtain ⟨-, o, L, hs⟩ := h; exact hs.1

@[zesu_fact] theorem A0d8_common {σ : Sig} {m : Machine} (h : ARet f2C (unit Site0d4) σ m) :
    Common σ m := by
  obtain ⟨mc, _, ⟨o, L, hs, ha⟩, hpost⟩ := h
  exact (f2_ret hs.1 ha (by decide) (by decide) (by decide) hpost).1

@[zesu_fact] theorem A10c_common {σ : Sig} {m : Machine} (h : ARet f2C (unit Site108) σ m) :
    Common σ m := by
  obtain ⟨mc, _, ⟨o, k, L, hs, -, -, ha⟩, hpost⟩ := h
  exact (f2_ret hs.1.1 ha (by decide) (by decide) (by decide) hpost).1

@[zesu_fact] theorem A15c_common {σ : Sig} {m : Machine} (h : ARet f2C (unit Site158) σ m) :
    Common σ m := by
  obtain ⟨mc, _, ⟨o, k, L, hs, -, ha⟩, hpost⟩ := h
  exact (f2_ret hs.1.1 ha (by decide) (by decide) (by decide) hpost).1

@[zesu_fact] theorem A18c_common {σ : Sig} {m : Machine} (h : AKeys σ m) : Common σ m := by
  obtain ⟨-, o, k, L, hs, -⟩ := h; exact hs.1

@[zesu_fact] theorem A1a0_common {σ : Sig} {m : Machine} (h : ARet f2C (unit Site19c) σ m) :
    Common σ m := by
  obtain ⟨mc, _, ⟨o, k, L, hs, -, -, -, ha⟩, hpost⟩ := h
  exact (f2_ret hs.1 ha (by decide) (by decide) (by decide) hpost).1

@[zesu_fact] theorem A1f8_common {σ : Sig} {m : Machine} (h : ARet f1C Site1f4 σ m) :
    Common σ m := (ret_1f8 h).1

@[zesu_fact] theorem A230_common {σ : Sig} {m : Machine} (h : AKeyStore σ m) : Common σ m := by
  obtain ⟨-, o, k, L, key, kh', hIE, -⟩ := h; exact hIE.1

@[zesu_fact] theorem A25c_common {σ : Sig} {m : Machine} (h : ARet f4C Site258 σ m) :
    Common σ m := (ret_25c h).1

@[zesu_fact] theorem A340_common {σ : Sig} {m : Machine} (h : ARet remapC (unit Site33c) σ m) :
    Common σ m := (ret_340 h).1

@[zesu_fact] theorem A3d4_common {σ : Sig} {m : Machine} (h : ARet allocC Site3d0 σ m) :
    Common σ m := by
  obtain ⟨mc, L, hs, hpost⟩ := h; exact (ret_3d4 ⟨mc, hs, hpost⟩).1

@[zesu_fact] theorem A400_common {σ : Sig} {m : Machine} (h : ARet memcpyC (unit Site3fc) σ m) :
    Common σ m := (ret_400 h).1

@[zesu_fact] theorem A42c_common {σ : Sig} {m : Machine} (h : A42c σ m) : Common σ m :=
  (ret_42c h).1

@[zesu_fact] theorem A460_common {σ : Sig} {m : Machine} (h : AEntryStore σ m) : Common σ m := by
  obtain ⟨-, o, k, L, kp', hc, -⟩ := h; exact hc

@[zesu_fact] theorem A4a0_common {σ : Sig} {m : Machine} (h : ARet f5C Site49c σ m) :
    Common σ m := (ret_4a0 h).1

/-- The saved `ra` (frame offset `568`) is the entry's. -/
@[zesu_fact] theorem common_ra {σ : Sig} {m : Machine} (hc : Common σ m) :
    Sym.eval (envB σ m) (Sym.init 0 568 8) = σ.m.reg 1 :=
  saved_eval hc (BaseEnv.ofB σ m) (k := 0) (by decide)

/-- The entry's `ra` is a valid return target (`RetAligned`). -/
@[zesu_fact] theorem common_ra_aligned {σ : Sig} {m : Machine} (hc : Common σ m) :
    (σ.m.reg 1 &&& ~~~(1 : Word)).toNat % 4 = 0 :=
  hc.2.1.2.2.1

/-- `envP` changes only variables: an initial-memory read is `envB`'s (a `leaf_norm` normal form,
so the facts stated over `envB`, such as `common_ra`, apply at the cuts with `envP`). -/
@[zesu_simp] theorem envP_init (k : Nat) (σ : Sig) (m : Machine) (r off n : Nat) :
    Sym.eval (envP k σ m) (Sym.init r off n) = Sym.eval (envB σ m) (Sym.init r off n) := rfl

/-- `envS` appends a sixth region to `envB`'s five: a read of region 0 is `envB`'s. -/
@[zesu_simp] theorem envS_init (k : Nat) (σ : Sig) (m : Machine) (off n : Nat) :
    Sym.eval (envS k σ m) (Sym.init 0 off n) = Sym.eval (envB σ m) (Sym.init 0 off n) := rfl

/-! `zesu_auto TX` runs here, with the facts above and before the hand-written leaf modules, so
every leaf is attempted with the facts and its residual class is recorded with them. -/

zesu_auto TX

end ZesuExec.Fn.TX
