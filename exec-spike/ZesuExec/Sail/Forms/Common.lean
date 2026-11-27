import ZesuExec.Sail.Decode
import BinaryFv.RiscV.Step.FallThrough
import BinaryFv.RiscV.Step.Call
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.Memory
import BinaryFv.RiscV.Instruction.Execute.StoreByte

/-!
# Shared infrastructure for the per-form simulation theorems

`sim_of_exec` reduces `sim_<form>` to the form's `execute` contract: given `Rel img m s`, the
fetched word and its decoding, and a run of `execute (toSail i)` from the state the generated base
path reaches (`T s m.pc`: `minstret_increment` set, `nextPC = pc + 4`) to some `a` whose `nextPC`
is `m'.pc`, which agrees with `m'` on `x1 … x31` and memory, keeps the code bytes, and changes no
other register, the generated `try_step` retires to a state related to `m'`.

The register lemmas `rX_rg_run` / `wX_rg_run` read and write `x i` for an arbitrary `i : Fin 32`.
-/

set_option linter.unusedSimpArgs false

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-! ## Register file -/

/-- `st` holds `m`'s `x1 … x31` (the register half of `Rel`). -/
def RegsAgree (m : Machine) (st : State) : Prop :=
  ∀ i : Fin 32, i.val ≠ 0 → st.regs.get? (xreg i) = some (cast (xreg_type i).symm (m.regs i))

/-- Sail's write of `v` to `x i` (no effect for `i = 0`). -/
def setX (st : State) (i : Fin 32) (v : BitVec 64) : State :=
  if i.val = 0 then st else { st with regs := st.regs.insert (xreg i) (cast (xreg_type i).symm v) }

theorem get?_insert_ne {st : State} {r r' : Register} (v : RegisterType r') (h : r ≠ r') :
    (st.regs.insert r' v).get? r = st.regs.get? r := by
  rw [Std.ExtDHashMap.get?_insert]; simp [Ne.symm h]

theorem get?_insert_self {st : State} {r : Register} (v : RegisterType r) :
    (st.regs.insert r v).get? r = some v := by
  rw [Std.ExtDHashMap.get?_insert]; simp

set_option hygiene false in
/-- Split `i : Fin 32` into its 32 literal cases. -/
macro "fin32_split" i:ident : tactic =>
  `(tactic| (obtain ⟨k, hk⟩ := $i
             have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨
               k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
               k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨
               k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
             rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
               rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
               rfl | rfl | rfl | rfl | rfl | rfl | rfl))

/-- Reading `x i` from a state that holds `m`'s registers yields `m.reg i`. -/
theorem rX_rg_run {m : Machine} {st : State} (h : RegsAgree m st) (i : Fin 32) :
    Runs (rX_bits (rg i)) st st (m.reg i) := by
  fin32_split i
  · simpa [Machine.reg] using rX_x0_run st
  all_goals
    have hx := h ⟨_, hk⟩ (by simp)
    unfold Runs rX_bits rX rg
    simp only [xreg] at hx
    simp [Sail.BitVec.toNatInt, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.pure,
      EStateM.get, EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
      getThe, MonadState.get, MonadStateOf.get, Bind.bind, Pure.pure, regval_from_reg, hx,
      Machine.reg]

/-- Writing `v` to `x i`. -/
theorem wX_rg_run (st : State) (i : Fin 32) (v : BitVec 64) :
    Runs (wX_bits (rg i) v) st (setX st i v) () := by
  fin32_split i
  · exact wX_x0_run st v
  all_goals
    unfold Runs setX
    simp [wX_bits, wX, rg, xreg, PreSail.writeReg, Sail.BitVec.toNatInt, EStateM.run,
      EStateM.bind, EStateM.modifyGet,
      EStateM.pure, EStateM.instMonad, MonadState.modifyGet, MonadStateOf.modifyGet, modify,
      xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names,
      encdec_reg_forwards, encdec_reg_forwards_matches, reg_arch_name_raw_forwards,
      LeanRV64DExecutable.Functions.not, zero_extend, regval_into_reg]


theorem xreg_ne_nextPC : ∀ i, xreg i ≠ nextPC := by decide
theorem xreg_ne_PC : ∀ i, xreg i ≠ PC := by decide
theorem xreg_ne_minstret : ∀ i, xreg i ≠ minstret := by decide
theorem xreg_ne_inc : ∀ i, xreg i ≠ minstret_increment := by decide

theorem xreg_inj {i j : Fin 32} (hi : i.val ≠ 0) (hj : j.val ≠ 0) (h : xreg i = xreg j) : i = j := by
  revert i j; decide

/-- `setX` changes only `x i`. -/
theorem setX_get?_ne {st : State} {i : Fin 32} {v : BitVec 64} {r : Register} (h : r ≠ xreg i) :
    (setX st i v).regs.get? r = st.regs.get? r := by
  unfold setX; split
  · rfl
  · exact get?_insert_ne _ h

theorem setX_mem (st : State) (i : Fin 32) (v : BitVec 64) : (setX st i v).mem = st.mem := by
  unfold setX; split <;> rfl

/-- Writing `x rd` on both sides keeps the registers in agreement. -/
theorem RegsAgree.setX {m : Machine} {st : State} (h : RegsAgree m st) (rd : Fin 32)
    (v : BitVec 64) : RegsAgree (m.setReg rd v) (ZesuExec.SailLink.setX st rd v) := by
  intro j hj
  simp only [Machine.setReg]
  by_cases h0 : rd.val = 0
  · simp only [ZesuExec.SailLink.setX, h0, if_true]; exact h j hj
  · simp only [ZesuExec.SailLink.setX, h0, if_false]
    by_cases hjr : j = rd
    · subst hjr; simp [get?_insert_self]
    · have hne : xreg j ≠ xreg rd := fun e => hjr (xreg_inj hj h0 e)
      rw [get?_insert_ne _ hne]; simp [hjr, h j hj]


/-! ## Fetch -/

/-- A word the image holds at `pc` sits in some segment at index `(pc - base) / 4`. -/
theorem Image.word?_spec {img : Image} {pc w : Nat} (h : img.word? pc = some w) :
    ∃ seg ∈ img.text, ∃ k, seg.words[k]? = some w ∧ pc = seg.base + 4 * k := by
  obtain ⟨seg, hmem, hseg⟩ := List.exists_of_findSome?_eq_some h
  unfold Seg.word? at hseg
  split at hseg
  · rename_i hc
    exact ⟨seg, hmem, (pc - seg.base) / 4, hseg, by omega⟩
  · cases hseg

/-- Every decoded word is a 32-bit base (non-compressed) encoding. -/
theorem decodeNat_low {w : Nat} {i : Instr} (h : decodeNat w = some i) :
    w < 4294967296 ∧ w % 4 = 3 := by
  unfold decodeNat at h
  simp only at h
  generalize hop : Decode.field w 0 7 = opc at h
  generalize hf3 : Decode.field w 12 3 = f3 at h
  generalize hf7 : Decode.field w 25 7 = f7 at h
  generalize hf6 : Decode.field w 26 6 = f6 at h
  repeat' (revert h; apply ite_imp <;> intro hcond h)
  all_goals cases h
  all_goals (simp only [Decode.field] at *; omega)

/-- The four little-endian bytes of a 32-bit word reassemble to it. -/
theorem fetchWord_bytes {w : Nat} (hw : w < 4294967296) :
    fetchWord (BitVec.ofNat 8 (w / 256 ^ 0)) (BitVec.ofNat 8 (w / 256 ^ 1))
      (BitVec.ofNat 8 (w / 256 ^ 2)) (BitVec.ofNat 8 (w / 256 ^ 3)) = BitVec.ofNat 32 w := by
  apply BitVec.eq_of_toNat_eq
  unfold fetchWord
  repeat rw [toNat_append_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem baseEncoding_of_low {w : Nat} (h : w % 4 = 3) :
    BaseInstructionEncoding (BitVec.ofNat 8 (w / 256 ^ 0)) := by
  unfold BaseInstructionEncoding
  rw [extractLsb_field]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem to_bits_64 (n : Nat) : (to_bits (l := 64) n : BitVec 64) = BitVec.ofNat 64 n := by
  simp [to_bits, Sail.get_slice_int]; apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']

section pma
variable (a : BitVec 64) (n : Nat)

theorem matching_input (h : 0x40000000 ≤ a.toNat ∧ a.toNat + n ≤ 0x80000000) :
    matching_pma_region zesuPmaRegions (.Physaddr a) n = some zesuPmaRegions[0] := by
  have ha := a.isLt
  simp [matching_pma_region, matching_pma_region_bits_range, range_subset, zesuPmaRegions,
    zopz0zIzJ_u, bits_of_physaddr, to_bits_64, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt]
  rw [if_pos (by omega)]

theorem matching_rom (h : 0x80000000 ≤ a.toNat ∧ a.toNat + n ≤ 0x88000000) :
    matching_pma_region zesuPmaRegions (.Physaddr a) n = some zesuPmaRegions[1] := by
  have ha := a.isLt
  simp [matching_pma_region, matching_pma_region_bits_range, range_subset, zesuPmaRegions,
    zopz0zIzJ_u, bits_of_physaddr, to_bits_64, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt]
  rw [if_neg (by omega), if_pos (by omega)]

theorem matching_ram (h : 0xa0000000 ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000) :
    matching_pma_region zesuPmaRegions (.Physaddr a) n = some zesuPmaRegions[2] := by
  have ha := a.isLt
  simp [matching_pma_region, matching_pma_region_bits_range, range_subset, zesuPmaRegions,
    zopz0zIzJ_u, bits_of_physaddr, to_bits_64, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.toNatInt]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

end pma

end ZesuExec.SailLink
