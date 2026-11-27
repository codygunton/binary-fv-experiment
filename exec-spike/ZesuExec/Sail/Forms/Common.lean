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

theorem get?_insert_ne {M : Std.ExtDHashMap Register RegisterType} {r r' : Register}
    (v : RegisterType r') (h : r ≠ r') : (M.insert r' v).get? r = M.get? r := by
  rw [Std.ExtDHashMap.get?_insert]; simp [Ne.symm h]

theorem get?_insert_self {M : Std.ExtDHashMap Register RegisterType} {r : Register}
    (v : RegisterType r) : (M.insert r v).get? r = some v := by
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

theorem physaddr_bits (a : BitVec 64) :
    zero_extend (m := 64) (bits_of_physaddr (.Physaddr a)) = a := by
  apply BitVec.eq_of_toNat_eq
  simp [zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr]

set_option hygiene false in
/-- Decide a `range_subset` test of the profile's regions from interval facts `h`, `ha`. -/
macro "rs_tac" : tactic => `(tactic| (
  simp only [range_subset, zopz0zIzJ_u, physaddr_bits, to_bits_64, Sail.BitVec.toNatInt, BitVec.toNat_sub, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth, Bool.and_eq_true, decide_eq_true_eq,
    Int.ofNat_eq_natCast, Int.ofNat_le, Bool.not_eq_true, decide_eq_false_iff_not, not_and,
    Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub]
  omega))

section pma
variable (a : BitVec 64) (n : Nat)

theorem matching_input (h : 0x40000000 ≤ a.toNat ∧ a.toNat + n ≤ 0x80000000) :
    matching_pma_region zesuPmaRegions (.Physaddr a) n = some zesuPmaRegions[0] := by
  have ha := a.isLt
  simp only [matching_pma_region, matching_pma_region_bits_range, zesuPmaRegions,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rw [if_pos (by rs_tac)]

theorem matching_rom (hn : 0 < n) (h : 0x80000000 ≤ a.toNat ∧ a.toNat + n ≤ 0x88000000) :
    matching_pma_region zesuPmaRegions (.Physaddr a) n = some zesuPmaRegions[1] := by
  have ha := a.isLt
  simp only [matching_pma_region, matching_pma_region_bits_range, zesuPmaRegions,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rw [if_neg (by rs_tac), if_pos (by rs_tac)]

theorem matching_ram (h : 0xa0000000 ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000) :
    matching_pma_region zesuPmaRegions (.Physaddr a) n = some zesuPmaRegions[2] := by
  have ha := a.isLt
  simp only [matching_pma_region, matching_pma_region_bits_range, zesuPmaRegions,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rw [if_neg (by rs_tac), if_neg (by rs_tac), if_pos (by rs_tac)]

end pma

/-! ## Configured transport -/

/-- `Configured` depends only on registers other than `x1 … x31`, `PC`, `nextPC`,
`minstret_increment`, and on the presence of `minstret`. -/
theorem Configured.of_agree {s s' : State} (h : Configured s)
    (hag : ∀ r, r ≠ nextPC → r ≠ PC → r ≠ minstret → r ≠ minstret_increment →
      (∀ j, xreg j ≠ r) → s'.regs.get? r = s.regs.get? r)
    (hmi : ∃ v, s'.regs.get? minstret = some v) : Configured s' := by
  have e : ∀ r, r ≠ nextPC → r ≠ PC → r ≠ minstret → r ≠ minstret_increment →
      (∀ j, xreg j ≠ r) → s'.regs.get? r = s.regs.get? r := hag
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmi⟩
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2
  · rw [e mip (by decide) (by decide) (by decide) (by decide) (by decide),
      e mie (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10
  · rw [e _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11

/-! ## The generic step -/

/-- The state after `try_step`'s counter-increment write. -/
abbrev Inc (s : State) : State := tryStepControlFlowAfterIncrement s

/-- The state the generated base path hands to `execute`: `minstret_increment` set and
`nextPC = pc + 4`. -/
abbrev T (s : State) (pc : BitVec 64) : State := coreControlFlowNextState (Inc s) pc

theorem Inc_get? {s : State} {r : Register} (h : r ≠ minstret_increment) :
    (Inc s).regs.get? r = s.regs.get? r := get?_insert_ne _ h

theorem T_get?_inc {s : State} {pc : BitVec 64} {r : Register} (h : r ≠ nextPC) :
    (T s pc).regs.get? r = (Inc s).regs.get? r := get?_insert_ne _ h

theorem T_get? {s : State} {pc : BitVec 64} {r : Register} (h1 : r ≠ nextPC)
    (h2 : r ≠ minstret_increment) : (T s pc).regs.get? r = s.regs.get? r := by
  rw [T_get?_inc h1, Inc_get? h2]

theorem T_nextPC (s : State) (pc : BitVec 64) : (T s pc).regs.get? nextPC = some (pc + 4) := by
  simp only [T, coreControlFlowNextState, Sail.BitVec.addInt]
  exact get?_insert_self _

theorem RegsAgree.T {m : Machine} {s : State} (h : RegsAgree m s) (pc : BitVec 64) :
    RegsAgree m (T s pc) := by
  intro j hj; rw [T_get? (xreg_ne_nextPC j) (xreg_ne_inc j)]; exact h j hj

/-- Every register but `x1 … x31` and `nextPC` is as in `T s pc`. -/
def Frame (s : State) (pc : BitVec 64) (a : State) : Prop :=
  ∀ r, r ≠ nextPC → (∀ j, xreg j ≠ r) → a.regs.get? r = (T s pc).regs.get? r

/-- `a` keeps the code words of `img`. -/
def CodeKept (img : Image) (a : State) : Prop :=
  ∀ seg ∈ img.text, ∀ k w, seg.words[k]? = some w →
    Layout.textLo ≤ seg.base + 4 * k → seg.base + 4 * k < Layout.textHi →
    CodeAt a (seg.base + 4 * k) w

/-- **Generic step.** A run of the decoded instruction's `execute` from `T s m.pc` to a state `a`
that matches `m'` lifts to a retiring `try_step` from `s` to a state related to `m'`. -/
theorem sim_of_exec {img : Image} {m m' : Machine} {s a : State} {w : Nat} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    (hexec : Runs (execute (toSail i)) (T s m.pc) a (.Retire_Success ()))
    (hnext : a.regs.get? nextPC = some m'.pc) (hframe : Frame s m.pc a)
    (hregs : RegsAgree m' a) (hmem : ∀ x b, m'.mem x = some b → a.mem.get? x.toNat = some b)
    (hcode : CodeKept img a) (n : Nat) :
    ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  obtain ⟨retired, hret⟩ := hR.conf.instret
  obtain ⟨inhibit, hinh, hinh0⟩ := hR.conf.inhibit
  obtain ⟨config, hcfg, hcfg0⟩ := hR.conf.instretcfg
  obtain ⟨misaB, hmisa, _⟩ := hR.conf.misa
  obtain ⟨mstB, hmst, _⟩ := hR.conf.mstatus
  obtain ⟨hlt, hw3⟩ := decodeNat_low hd
  obtain ⟨seg, hseg, k, hk, hpck⟩ := Image.word?_spec hw
  have hc := hR.code seg hseg k w hk (by omega) (by omega)
  rw [← hpck] at hc
  have b0 := hc 0 (by decide)
  rw [Nat.add_zero] at b0
  have bytes : FetchBytesAt (Inc s) m.pc (BitVec.ofNat 8 (w / 256 ^ 0))
      (BitVec.ofNat 8 (w / 256 ^ 1)) (BitVec.ofNat 8 (w / 256 ^ 2))
      (BitVec.ofNat 8 (w / 256 ^ 3)) :=
    ⟨b0, hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)⟩
  have hpma : FetchPmaAllows (Inc s) m.pc :=
    fetchPmaAllows_of_region (by rw [Inc_get? (by decide)]; exact hR.conf.pma)
      (matching_rom m.pc 4 (by decide)
        (by simp only [Layout.textLo, Layout.textHi] at hpc; omega)) rfl
  have platform : FetchBasePlatform (Inc s) m.pc :=
    fetchBasePlatform_of_offPC (by rw [Inc_get? (by decide)]; exact hR.pc)
      (fetchBasePlatformOffPC_of_reads (by rw [Inc_get? (by decide)]; exact hmisa)
        (by rw [Inc_get? (by decide)]; exact hmst)
        (by rw [Inc_get? (by decide)]; exact hR.conf.privilege) hpc.2.2 hpma)
  have hconfInc : Configured (Inc s) :=
    Configured.of_agree hR.conf (fun r _ _ _ h4 _ => Inc_get? h4)
      ⟨retired, by rw [Inc_get? (by decide)]; exact hret⟩
  have decode : Runs (ext_decode (fetchWord (BitVec.ofNat 8 (w / 256 ^ 0))
      (BitVec.ofNat 8 (w / 256 ^ 1)) (BitVec.ofNat 8 (w / 256 ^ 2))
      (BitVec.ofNat 8 (w / 256 ^ 3)))) (Inc s) (Inc s) (toSail i) := by
    rw [fetchWord_bytes hlt]
    exact decode_sound (by simp [decodeWord, Nat.mod_eq_of_lt hlt, hd]) hconfInc
  have active := runHartActiveControlFlow n (Inc s) a m.pc _ _ _ _ (toSail i) platform bytes
    (baseEncoding_of_low hw3) decode hexec
  have agreeInc : ∀ r, r ≠ nextPC → (∀ j, xreg j ≠ r) → a.regs.get? r = (Inc s).regs.get? r :=
    fun r h1 h2 => (hframe r h1 h2).trans (T_get?_inc h1)
  have run := tryStepGenericRetires n s a m'.pc retired inhibit config _
    (by rw [Inc_get? (by decide)]; exact hR.conf.privilege) active hnext
    (agreeInc _ (by decide) (by decide)) (agreeInc _ (by decide) (by decide))
    (agreeInc _ (by decide) (by decide)) hR.conf.hart hinh hcfg hinh0 hcfg0 hret
  refine ⟨_, run, ?_⟩
  have fin : ∀ r, r ≠ PC → r ≠ minstret →
      (tryStepControlFlowAfterRetired a m'.pc retired).regs.get? r = a.regs.get? r := by
    intro r h1 h2
    simp only [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
    rw [get?_insert_ne _ h2, get?_insert_ne _ h1]
  refine ⟨?_, ?_, ?_, hmem, hcode⟩
  · refine Configured.of_agree hR.conf (fun r h1 h2 h3 h4 h5 => ?_) ⟨_, get?_insert_self _⟩
    rw [fin r h2 h3, agreeInc r h1 h5, Inc_get? h4]
  · intro j hj
    rw [fin _ (xreg_ne_PC j) (xreg_ne_minstret j)]; exact hregs j hj
  · simp only [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]
    rw [get?_insert_ne _ (by decide)]; exact get?_insert_self _

/-- Inverting `step`: the guard holds and the decoded instruction's effect is `m'`. -/
theorem step_inv {img : Image} {m m' : Machine} {w : Nat} {i : Instr}
    (hs : step img m = some m') (hw : img.word? m.pc.toNat = some w)
    (hd : decodeNat w = some i) :
    (Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0) ∧
      m.exec i = some m' := by
  unfold step at hs
  split at hs
  · rename_i hg
    rw [hw] at hs; simp only [hd] at hs
    exact ⟨hg, hs⟩
  · cases hs

/-- The common shape of the 16 register-writing forms: `execute` writes `x rd` and falls through. -/
theorem sim_wreg {img : Image} {m : Machine} {s : State} {w : Nat} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    {rd : Fin 32} {v : BitVec 64}
    (hexec : Runs (execute (toSail i)) (T s m.pc) (setX (T s m.pc) rd v) (.Retire_Success ()))
    (n : Nat) :
    ∃ s', Runs (try_step n false) s s' false ∧ Rel img (m.setReg rd v).advance s' := by
  have hmem : (setX (T s m.pc) rd v).mem = s.mem := setX_mem _ _ _
  refine sim_of_exec hR hw hd hpc hexec ?_ ?_ ?_ ?_ ?_ n
  · rw [setX_get?_ne (Ne.symm (xreg_ne_nextPC rd)), T_nextPC]
    unfold Machine.setReg; split <;> rfl
  · intro r h1 h2; exact setX_get?_ne (Ne.symm (h2 rd))
  · have h := RegsAgree.setX (RegsAgree.T (m := m) hR.regs m.pc) rd v
    unfold Machine.advance; unfold Machine.setReg at h ⊢; split <;> rename_i h0 <;>
      simp only [h0, if_true, if_false] at h <;> exact h
  · intro x b hb
    rw [hmem]
    have : (m.setReg rd v).advance.mem = m.mem := by unfold Machine.advance Machine.setReg; split <;> rfl
    rw [this] at hb; exact hR.mem x b hb
  · intro seg hseg k w hk h1 h2; unfold CodeAt; rw [hmem]; exact hR.code seg hseg k w hk h1 h2

theorem sign_extend_eq {k : Nat} (x : BitVec k) : sign_extend (m := 64) x = x.signExtend 64 := by
  simp [sign_extend, Sail.BitVec.signExtend]

theorem Machine.setReg_zero (m : Machine) (v : Word) : m.setReg ⟨0, by decide⟩ v = m := by
  simp [Machine.setReg]

/-- A fall-through instruction that changes nothing but `nextPC`'s successor. -/
theorem sim_fall {img : Image} {m : Machine} {s : State} {w : Nat} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    (hexec : Runs (execute (toSail i)) (T s m.pc) (T s m.pc) (.Retire_Success ())) (n : Nat) :
    ∃ s', Runs (try_step n false) s s' false ∧ Rel img m.advance s' := by
  have := sim_wreg (rd := ⟨0, by decide⟩) (v := 0) hR hw hd hpc hexec n
  rwa [Machine.setReg_zero] at this

/-- The state after `execute` overwrote `nextPC` with a jump target `t`. -/
abbrev J (s : State) (pc t : BitVec 64) : State :=
  { T s pc with regs := (T s pc).regs.insert nextPC t }

/-- A control transfer to `t` that also writes the link `link` to `x rd` (`rd = 0`: no link). -/
theorem sim_ctl {img : Image} {m : Machine} {s : State} {w : Nat} {i : Instr}
    (hR : Rel img m s) (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some i)
    (hpc : Layout.textLo ≤ m.pc.toNat ∧ m.pc.toNat < Layout.textHi ∧ m.pc.toNat % 4 = 0)
    {rd : Fin 32} {t link : Word}
    (hexec : Runs (execute (toSail i)) (T s m.pc) (setX (J s m.pc t) rd link)
      (.Retire_Success ()))
    (n : Nat) :
    ∃ s', Runs (try_step n false) s s' false ∧ Rel img { m.setReg rd link with pc := t } s' := by
  have hmem : (setX (J s m.pc t) rd link).mem = s.mem := setX_mem _ _ _
  refine sim_of_exec hR hw hd hpc hexec ?_ ?_ ?_ ?_ ?_ n
  · rw [setX_get?_ne (Ne.symm (xreg_ne_nextPC rd))]; exact get?_insert_self _
  · intro r h1 h2; rw [setX_get?_ne (Ne.symm (h2 rd))]; exact get?_insert_ne _ h1
  · have hJ : RegsAgree m (J s m.pc t) := fun j hj => by
      rw [get?_insert_ne _ (xreg_ne_nextPC j)]; exact RegsAgree.T (m := m) hR.regs m.pc j hj
    exact hJ.setX rd link
  · intro x b hb
    rw [hmem]
    have : ({ m.setReg rd link with pc := t } : Machine).mem = m.mem := by
      unfold Machine.setReg; split <;> rfl
    rw [this] at hb; exact hR.mem x b hb
  · intro seg hseg k w hk h1 h2; unfold CodeAt; rw [hmem]; exact hR.code seg hseg k w hk h1 h2

/-- A 4-aligned jump target passes the generated `jump_to` alignment checks. -/
theorem jump_aligned {t : BitVec 64} (h : t.toNat % 4 = 0) :
    Sail.BitVec.access t 0 = 0#1 ∧ Sail.BitVec.access t 1 = 0#1 :=
  ⟨(fetchAligned_of_mod_four h).1, (fetchAligned_of_mod_four h).2.1⟩

/-- `misa` read for the `Zca` gate of `jump_to`. -/
theorem T_zca {img : Image} {m : Machine} {s : State} (hR : Rel img m s) (pc : BitVec 64) :
    ∃ z, Runs (currentlyEnabled extension.Ext_Zca) (T s pc) (T s pc) z := by
  obtain ⟨mi, hmi, _⟩ := hR.conf.misa
  exact ⟨_, currentlyEnabledZca_run _ mi (by rw [T_get? (by decide) (by decide)]; exact hmi)⟩

theorem T_pc {img : Image} {m : Machine} {s : State} (hR : Rel img m s) (pc : BitVec 64) :
    Runs (readReg PC) (T s pc) (T s pc) m.pc :=
  readReg_run _ PC _ (by rw [T_get? (by decide) (by decide)]; exact hR.pc)

end ZesuExec.SailLink
