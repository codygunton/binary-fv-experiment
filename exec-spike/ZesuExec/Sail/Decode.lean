import ZesuExec.Sail.Rel

/-!
# `decode_sound`: Sail's decoder agrees with `decodeNat`

For each form, a lemma `dec_<form>` runs the generated `ext_decode` on a symbolic word whose fixed
fields (opcode, `funct3`, `funct7`, …) are those of the form: the `sail_decode` simp set unfolds
the clause chain of `encdec_backwards`, rewrites every field extraction into `BitVec.ofNat` of a
quotient of `w.toNat`, and decides each clause test from the fixed fields; the operand fields stay
symbolic. `decode_sound` splits `decodeNat` and applies the matching lemma.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV (State Runs)
open LeanRV64DExecutable.Functions
open Register
open Decode

-- With the B and Zbkb modules the decoder's clause chain (`encdec_backwards`) is nested
-- deeper than the default limit allows `simp` to traverse.
set_option maxRecDepth 8192

theorem extractLsb_field {n : Nat} (w : BitVec n) (hi lo : Nat) :
    Sail.BitVec.extractLsb w hi lo = BitVec.ofNat (hi - lo + 1) (w.toNat / 2 ^ lo) := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem ofNat_beq_ofNat (n x c : Nat) :
    (BitVec.ofNat n x == BitVec.ofNat n c) = decide (x % 2 ^ n = c % 2 ^ n) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.toNat_eq]

theorem ofNat_eq_ofNat (n x c : Nat) :
    (BitVec.ofNat n x = BitVec.ofNat n c) = (x % 2 ^ n = c % 2 ^ n) := by
  simp [BitVec.toNat_eq]

theorem ofNat_mod (n x m : Nat) (h : 2 ^ n = m) : BitVec.ofNat n (x % m) = BitVec.ofNat n x := by
  subst h; apply BitVec.eq_of_toNat_eq; simp

theorem extract_reg (r : BitVec 5) :
    Sail.BitVec.extractLsb r
      ((LeanRV64DExecutable.Functions.regidx_bit_width : Int) - 1).toNat 0 = r := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, LeanRV64DExecutable.Functions.regidx_bit_width]

theorem encdec_reg_backwards_eq (r : BitVec 5) :
    encdec_reg_backwards r = pure (regidx.Regidx r) := by
  simp [encdec_reg_backwards, LeanRV64DExecutable.Functions.base_E_enabled,
    LeanRV64DExecutable.Functions.not, extract_reg]

/-- The opcode field in the form the `sail_decode` simp set produces. -/
theorem opc_of_field {w : BitVec 32} {c : Nat} (h : field w.toNat 0 7 = c) :
    BitVec.setWidth 7 w = BitVec.ofNat 7 c := by
  apply BitVec.eq_of_toNat_eq; simp [field] at h; simp [← h]

/-- A field `[lo, lo + n)` in the form the `sail_decode` simp set produces. -/
theorem fld_of_field {w : BitVec 32} {lo n c : Nat} (h : field w.toNat lo n = c) :
    BitVec.ofNat n (w.toNat / 2 ^ lo) = BitVec.ofNat n c := by
  apply BitVec.eq_of_toNat_eq; simp [field] at h; simp [← h]

/-- A whole-word or low-bits comparison against a constant whose opcode differs is false. -/
theorem setWidth_ne {w : BitVec 32} {k : Nat} (h : BitVec.setWidth 7 w = BitVec.ofNat 7 k)
    (n c : Nat) (hn : 7 ≤ n) (hc : c % 128 ≠ k % 128) :
    (BitVec.setWidth n w = BitVec.ofNat n c) = False := by
  apply propext; constructor
  · intro heq
    have h1 := congrArg BitVec.toNat h
    have h2 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1 h2
    have hd : 128 ∣ 2 ^ n := by
      have : 2 ^ 7 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
      simpa using this
    have e1 : w.toNat % 2 ^ n % 128 = w.toNat % 128 := Nat.mod_mod_of_dvd _ hd
    have e2 : c % 2 ^ n % 128 = c % 128 := Nat.mod_mod_of_dvd _ hd
    simp only [Nat.reducePow] at h1
    apply hc; omega
  · intro f; exact f.elim

theorem word_ne {w : BitVec 32} {k : Nat} (h : BitVec.setWidth 7 w = BitVec.ofNat 7 k)
    (c : Nat) (hc : c % 128 ≠ k % 128) : (w = BitVec.ofNat 32 c) = False := by
  have := setWidth_ne h 32 c (by omega) hc
  simpa using this

theorem field_14_1 (x : Nat) : field x 14 1 = field x 12 3 / 4 := by
  simp only [field]; omega

theorem field_12_2 (x : Nat) : field x 12 2 = field x 12 3 % 4 := by
  simp only [field]; omega

theorem toNat_append_add {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

set_option hygiene false in
/-- Runs the generated decoder on a symbolic word whose fixed fields are in context: `hop` (the
opcode, as `field w.toNat 0 7 = c`) and any `BitVec.ofNat` field facts; decides every clause test
and compares the result with `toSail`. -/
macro "dec_tac" : tactic =>
  `(tactic| (
    have hop' := opc_of_field hop
    have h14 := fld_of_field (field_14_1 w.toNat)
    have h12 := fld_of_field (field_12_2 w.toNat)
    simp only [Nat.reducePow] at *
    obtain ⟨hpriv, ⟨sb, hsec⟩, ⟨mi, hmisa, hm⟩⟩ := Configured.decodeReads hc
    unfold Runs ext_decode
    simp [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
      EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, extractLsb_field,
      ofNat_beq_ofNat, ofNat_eq_ofNat, encdec_reg_backwards_matches,
      LeanRV64DExecutable.Functions.base_E_enabled, LeanRV64DExecutable.Functions.not,
      LeanRV64DExecutable.Functions.xlen, LeanRV64DExecutable.Functions.xlen_bytes,
      valid_load_encdec,
      encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
      encdec_reg_backwards_eq, encdec_bop_backwards_matches, encdec_bop_backwards,
      width_enc_backwards_matches, width_enc_backwards, bool_bit_backwards_matches,
      encdec_mul_op_backwards_matches, encdec_mul_op_backwards, encdec_uop_backwards,
      Nat.div_div_eq_div_mul, setWidth_ne hop', word_ne hop', *]
    simp [toSail, rg, reg, immI, immS, immB, immJ, immU, field, ofNat_mod]
    try (apply BitVec.eq_of_toNat_eq; (repeat rw [toNat_append_add])
         simp only [BitVec.toNat_ofNat]; omega)))

/-- The register reads `ext_decode` performs on a configured state. -/
theorem Configured.decodeReads {s : State} (hc : Configured s) :
    s.regs.get? cur_privilege = some .Machine ∧
    (∃ v, s.regs.get? Register.mseccfg = some v) ∧
    (∃ v, s.regs.get? Register.misa = some v ∧ _get_Misa_M v = 1#1) := by
  obtain ⟨v, hv, _⟩ := hc.mseccfg
  exact ⟨hc.privilege, ⟨v, hv⟩, hc.misa⟩

section forms
variable (w : BitVec 32) {s : State} (hc : Configured s)
include hc

theorem dec_lui (hop : field w.toNat 0 7 = 0x37) :
    Runs (ext_decode w) s s (toSail (.lui (reg w.toNat 7) (immU w.toNat))) := by
  have := opc_of_field hop; dec_tac

theorem dec_auipc (hop : field w.toNat 0 7 = 0x17) :
    Runs (ext_decode w) s s (toSail (.auipc (reg w.toNat 7) (immU w.toNat))) := by
  have := opc_of_field hop; dec_tac

theorem dec_jal (hop : field w.toNat 0 7 = 0x6f) :
    Runs (ext_decode w) s s (toSail (.jal (reg w.toNat 7) (immJ w.toNat))) := by
  have := opc_of_field hop; dec_tac

theorem dec_jalr (hop : field w.toNat 0 7 = 0x67) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.jalr (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_beq (hop : field w.toNat 0 7 = 0x63) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.beq (reg w.toNat 15) (reg w.toNat 20) (immB w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_bne (hop : field w.toNat 0 7 = 0x63) (hf3 : field w.toNat 12 3 = 1) :
    Runs (ext_decode w) s s (toSail (.bne (reg w.toNat 15) (reg w.toNat 20) (immB w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_blt (hop : field w.toNat 0 7 = 0x63) (hf3 : field w.toNat 12 3 = 4) :
    Runs (ext_decode w) s s (toSail (.blt (reg w.toNat 15) (reg w.toNat 20) (immB w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_bltu (hop : field w.toNat 0 7 = 0x63) (hf3 : field w.toNat 12 3 = 6) :
    Runs (ext_decode w) s s (toSail (.bltu (reg w.toNat 15) (reg w.toNat 20) (immB w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_bgeu (hop : field w.toNat 0 7 = 0x63) (hf3 : field w.toNat 12 3 = 7) :
    Runs (ext_decode w) s s (toSail (.bgeu (reg w.toNat 15) (reg w.toNat 20) (immB w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_lb (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.lb (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_lbu (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 4) :
    Runs (ext_decode w) s s (toSail (.lbu (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_lhu (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 5) :
    Runs (ext_decode w) s s (toSail (.lhu (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_lw (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 2) :
    Runs (ext_decode w) s s (toSail (.lw (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_ld (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 3) :
    Runs (ext_decode w) s s (toSail (.ld (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_sb (hop : field w.toNat 0 7 = 0x23) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.sb (reg w.toNat 15) (reg w.toNat 20) (immS w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_sh (hop : field w.toNat 0 7 = 0x23) (hf3 : field w.toNat 12 3 = 1) :
    Runs (ext_decode w) s s (toSail (.sh (reg w.toNat 15) (reg w.toNat 20) (immS w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_sw (hop : field w.toNat 0 7 = 0x23) (hf3 : field w.toNat 12 3 = 2) :
    Runs (ext_decode w) s s (toSail (.sw (reg w.toNat 15) (reg w.toNat 20) (immS w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_sd (hop : field w.toNat 0 7 = 0x23) (hf3 : field w.toNat 12 3 = 3) :
    Runs (ext_decode w) s s (toSail (.sd (reg w.toNat 15) (reg w.toNat 20) (immS w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_addi (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.addi (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_xori (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 4) :
    Runs (ext_decode w) s s (toSail (.xori (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_andi (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 7) :
    Runs (ext_decode w) s s (toSail (.andi (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_sltiu (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 3) :
    Runs (ext_decode w) s s (toSail (.sltiu (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_slli (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 1)
    (hf6 : field w.toNat 26 6 = 0) :
    Runs (ext_decode w) s s (toSail (.slli (reg w.toNat 7) (reg w.toNat 15)
      (BitVec.ofNat 6 (field w.toNat 20 6)))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf6; dec_tac

theorem dec_srli (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 5)
    (hf6 : field w.toNat 26 6 = 0) :
    Runs (ext_decode w) s s (toSail (.srli (reg w.toNat 7) (reg w.toNat 15)
      (BitVec.ofNat 6 (field w.toNat 20 6)))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf6; dec_tac

theorem dec_add (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.add (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_sll (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 1) :
    Runs (ext_decode w) s s (toSail (.sll (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_sltu (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 3) :
    Runs (ext_decode w) s s (toSail (.sltu (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_or (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 6) :
    Runs (ext_decode w) s s (toSail (.or (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_and (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 7) :
    Runs (ext_decode w) s s (toSail (.and (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_sub (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0x20)
    (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.sub (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_mul (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 1)
    (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.mul (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_mulhu (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 1)
    (hf3 : field w.toNat 12 3 = 3) :
    Runs (ext_decode w) s s (toSail (.mulhu (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_xor (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 4) :
    Runs (ext_decode w) s s (toSail (.xor (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_addiw (hop : field w.toNat 0 7 = 0x1b) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.addiw (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_bge (hop : field w.toNat 0 7 = 0x63) (hf3 : field w.toNat 12 3 = 5) :
    Runs (ext_decode w) s s (toSail (.bge (reg w.toNat 15) (reg w.toNat 20) (immB w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_lwu (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 6) :
    Runs (ext_decode w) s s (toSail (.lwu (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_srliw (hop : field w.toNat 0 7 = 0x1b) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 5) :
    Runs (ext_decode w) s s (toSail (.srliw (reg w.toNat 7) (reg w.toNat 15)
      (BitVec.ofNat 5 (field w.toNat 20 5)))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_subw (hop : field w.toNat 0 7 = 0x3b) (hf7 : field w.toNat 25 7 = 0x20)
    (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.subw (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_lh (hop : field w.toNat 0 7 = 0x03) (hf3 : field w.toNat 12 3 = 1) :
    Runs (ext_decode w) s s (toSail (.lh (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_ori (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 6) :
    Runs (ext_decode w) s s (toSail (.ori (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_srl (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 5) :
    Runs (ext_decode w) s s (toSail (.srl (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_divu (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 1)
    (hf3 : field w.toNat 12 3 = 5) :
    Runs (ext_decode w) s s (toSail (.divu (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7
  have := fld_of_field (show field w.toNat 12 1 = 1 by simp only [field] at hf3 ⊢; omega)
  have : w.toNat / 8192 % 4 = 2 := by simp only [field] at hf3; omega
  dec_tac

theorem dec_remu (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 1)
    (hf3 : field w.toNat 12 3 = 7) :
    Runs (ext_decode w) s s (toSail (.remu (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7
  have := fld_of_field (show field w.toNat 12 1 = 1 by simp only [field] at hf3 ⊢; omega)
  have : w.toNat / 8192 % 4 = 3 := by simp only [field] at hf3; omega
  dec_tac

theorem dec_slliw (hop : field w.toNat 0 7 = 0x1b) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 1) :
    Runs (ext_decode w) s s (toSail (.slliw (reg w.toNat 7) (reg w.toNat 15)
      (BitVec.ofNat 5 (field w.toNat 20 5)))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_slti (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 2) :
    Runs (ext_decode w) s s (toSail (.slti (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  have := opc_of_field hop; have := fld_of_field hf3; dec_tac

theorem dec_slt (hop : field w.toNat 0 7 = 0x33) (hf7 : field w.toNat 25 7 = 0)
    (hf3 : field w.toNat 12 3 = 2) :
    Runs (ext_decode w) s s (toSail (.slt (reg w.toNat 7) (reg w.toNat 15) (reg w.toNat 20))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf7; dec_tac

theorem dec_srai (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 5)
    (hf6 : field w.toNat 26 6 = 0x10) :
    Runs (ext_decode w) s s (toSail (.srai (reg w.toNat 7) (reg w.toNat 15)
      (BitVec.ofNat 6 (field w.toNat 20 6)))) := by
  have := opc_of_field hop; have := fld_of_field hf3; have := fld_of_field hf6; dec_tac

end forms

/-- Case split on an `if` in a hypothesis `ite c a b = x`. -/
theorem ite_imp {α : Type} {c : Prop} [Decidable c] {a b x : α} {P : Prop}
    (h1 : c → a = x → P) (h2 : ¬ c → b = x → P) : (if c then a else b) = x → P := by
  by_cases hc : c
  · intro h; exact h1 hc (by simpa [hc] using h)
  · intro h; exact h2 hc (by simpa [hc] using h)

/-- Sail's decoder agrees with `decodeWord` on every word of the 47 forms, from any configured
state, without changing it. -/
theorem decode_sound {w : BitVec 32} {i : Instr} {s : State} (h : decodeWord w = some i)
    (hc : Configured s) : Runs (ext_decode w) s s (toSail i) := by
  unfold decodeWord decodeNat at h
  simp only at h
  rw [if_pos (by have := w.isLt; simpa using this)] at h
  generalize hop : field w.toNat 0 7 = opc at h
  generalize hf3 : field w.toNat 12 3 = f3 at h
  generalize hf7 : field w.toNat 25 7 = f7 at h
  generalize hf6 : field w.toNat 26 6 = f6 at h
  repeat' (revert h; apply ite_imp <;> intro hcond h)
  all_goals cases h
  all_goals (subst_vars; first
        | exact dec_lui w hc (by assumption)
        | exact dec_auipc w hc (by assumption)
        | exact dec_jal w hc (by assumption)
        | exact dec_jalr w hc (by assumption) (by assumption)
        | exact dec_beq w hc (by assumption) (by assumption)
        | exact dec_bne w hc (by assumption) (by assumption)
        | exact dec_blt w hc (by assumption) (by assumption)
        | exact dec_bltu w hc (by assumption) (by assumption)
        | exact dec_bgeu w hc (by assumption) (by assumption)
        | exact dec_lb w hc (by assumption) (by assumption)
        | exact dec_lbu w hc (by assumption) (by assumption)
        | exact dec_lhu w hc (by assumption) (by assumption)
        | exact dec_lw w hc (by assumption) (by assumption)
        | exact dec_ld w hc (by assumption) (by assumption)
        | exact dec_sb w hc (by assumption) (by assumption)
        | exact dec_sh w hc (by assumption) (by assumption)
        | exact dec_sw w hc (by assumption) (by assumption)
        | exact dec_sd w hc (by assumption) (by assumption)
        | exact dec_addi w hc (by assumption) (by assumption)
        | exact dec_xori w hc (by assumption) (by assumption)
        | exact dec_andi w hc (by assumption) (by assumption)
        | exact dec_sltiu w hc (by assumption) (by assumption)
        | exact dec_slli w hc (by assumption) (by assumption) (by assumption)
        | exact dec_srli w hc (by assumption) (by assumption) (by assumption)
        | exact dec_add w hc (by assumption) (by assumption) (by assumption)
        | exact dec_sll w hc (by assumption) (by assumption) (by assumption)
        | exact dec_sltu w hc (by assumption) (by assumption) (by assumption)
        | exact dec_or w hc (by assumption) (by assumption) (by assumption)
        | exact dec_and w hc (by assumption) (by assumption) (by assumption)
        | exact dec_sub w hc (by assumption) (by assumption) (by assumption)
        | exact dec_mul w hc (by assumption) (by assumption) (by assumption)
        | exact dec_mulhu w hc (by assumption) (by assumption) (by assumption)
        | exact dec_xor w hc (by assumption) (by assumption) (by assumption)
        | exact dec_addiw w hc (by assumption) (by assumption)
        | exact dec_bge w hc (by assumption) (by assumption)
        | exact dec_lwu w hc (by assumption) (by assumption)
        | exact dec_srliw w hc (by assumption) (by assumption) (by assumption)
        | exact dec_subw w hc (by assumption) (by assumption) (by assumption)
        | exact dec_lh w hc (by assumption) (by assumption)
        | exact dec_ori w hc (by assumption) (by assumption)
        | exact dec_srl w hc (by assumption) (by assumption) (by assumption)
        | exact dec_divu w hc (by assumption) (by assumption) (by assumption)
        | exact dec_remu w hc (by assumption) (by assumption) (by assumption)
        | exact dec_slliw w hc (by assumption) (by assumption) (by assumption)
        | exact dec_slti w hc (by assumption) (by assumption)
        | exact dec_slt w hc (by assumption) (by assumption) (by assumption)
        | exact dec_srai w hc (by assumption) (by assumption) (by assumption))

end ZesuExec.SailLink
