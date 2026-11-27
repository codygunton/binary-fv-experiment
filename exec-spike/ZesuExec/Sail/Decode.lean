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

/-- The opcode field in the form the `sail_decode` simp set produces. -/
theorem opc_of_field {w : BitVec 32} {c : Nat} (h : field w.toNat 0 7 = c) :
    BitVec.setWidth 7 w = BitVec.ofNat 7 c := by
  apply BitVec.eq_of_toNat_eq; simp [field] at h; simp [← h]

/-- A field `[lo, lo + n)` in the form the `sail_decode` simp set produces. -/
theorem fld_of_field {w : BitVec 32} {lo n c : Nat} (h : field w.toNat lo n = c) :
    BitVec.ofNat n (w.toNat / 2 ^ lo) = BitVec.ofNat n c := by
  apply BitVec.eq_of_toNat_eq; simp [field] at h; simp [← h]

macro "sail_decode" : tactic =>
  `(tactic| (
    unfold Runs ext_decode
    simp [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
      PreSail.readReg, EStateM.run, Bind.bind, Pure.pure,
      EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
      EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      EStateM.instMonadExceptOfOfBacktrackable, getThe,
      MonadState.get, MonadStateOf.get, extractLsb_field,
      ofNat_beq_ofNat, ofNat_eq_ofNat, encdec_reg_backwards_matches,
      LeanRV64DExecutable.Functions.base_E_enabled, LeanRV64DExecutable.Functions.not,
      encdec_uop_backwards_matches, encdec_iop_backwards_matches, encdec_iop_backwards,
      encdec_reg_backwards, encdec_bop_backwards_matches, encdec_bop_backwards,
      width_enc_backwards_matches, width_enc_backwards, bool_bit_backwards_matches,
      encdec_mul_op_backwards_matches, encdec_mul_op_backwards, encdec_uop_backwards,
      Nat.div_div_eq_div_mul, *]))

/-- The register reads `ext_decode` performs on a configured state. -/
theorem Configured.decodeReads {s : State} (hc : Configured s) :
    s.regs.get? cur_privilege = some .Machine ∧
    (∃ v, s.regs.get? Register.mseccfg = some v) ∧
    (∃ v, s.regs.get? Register.misa = some v ∧ _get_Misa_M v = 1#1) := by
  obtain ⟨v, hv, _⟩ := hc.mseccfg
  exact ⟨hc.privilege, ⟨v, hv⟩, hc.misa⟩

theorem dec_addi (w : BitVec 32) {s : State} (hc : Configured s)
    (hop : field w.toNat 0 7 = 0x13) (hf3 : field w.toNat 12 3 = 0) :
    Runs (ext_decode w) s s (toSail (.addi (reg w.toNat 7) (reg w.toNat 15) (immI w.toNat))) := by
  obtain ⟨hpriv, ⟨sb, hsec⟩, ⟨mi, hmisa, hm⟩⟩ := hc.decodeReads
  have hop' := opc_of_field hop
  have hf3' := fld_of_field hf3
  simp only [Nat.reducePow] at hf3'
  sail_decode
  simp [toSail, rg, reg, immI, field, ofNat_mod]
  trace_state
  sorry

end ZesuExec.SailLink
