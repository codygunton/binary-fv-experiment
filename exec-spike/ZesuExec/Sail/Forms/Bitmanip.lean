import ZesuExec.Sail.Forms.Common

/-!
# Simulation of the bit-manipulation forms (S12b)

`maxu` (Zbb), `pack packh` (Zbkb), `rev8` (Zbb/Zbkb), `clz` (Zbb), `bext bset bclri` (Zbs): the
generated model compiles `Zba;Zbb;Zbs;Zbkb` since S12b. Each family gets a result function that
copies the generated `execute_*` body, one `execute_*_run` contract (as `BinaryFv`'s
`execute_RTYPE_run`), the agreement of the result with `Machine.exec`, and `sim_<form>`.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV
open PreSail
open LeanRV64DExecutable.Functions
open Register

variable {img : Image} {m m' : Machine} {s : State} {w : Nat}

/-! ## Execute contracts and results -/

def zbbResult (op : brop_zbb) (rs1Val rs2Val : BitVec 64) : BitVec 64 :=
  match op with
  | .ANDN => rs1Val &&& (Complement.complement rs2Val)
  | .ORN => rs1Val ||| (Complement.complement rs2Val)
  | .XNOR => Complement.complement (rs1Val ^^^ rs2Val)
  | .MAX => if zopz0zK_s rs1Val rs2Val then rs1Val else rs2Val
  | .MAXU => if zopz0zK_u rs1Val rs2Val then rs1Val else rs2Val
  | .MIN => if zopz0zI_s rs1Val rs2Val then rs1Val else rs2Val
  | .MINU => if zopz0zI_u rs1Val rs2Val then rs1Val else rs2Val
  | .ROL => rotate_bits_left rs1Val (Sail.BitVec.extractLsb rs2Val (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)
  | .ROR => rotate_bits_right rs1Val (Sail.BitVec.extractLsb rs2Val (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)

theorem execute_ZBB_RTYPE_run (state sFinal : State) (rs2 rs1 rd : regidx) (op : brop_zbb)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (zbbResult op rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_ZBB_RTYPE rs2 rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [zbbResult] at hwrite
  all_goals
    unfold execute_ZBB_RTYPE
    refine Runs.bind hrs1 (Runs.bind hrs2 ?_)
    refine Runs.bind hwrite ?_
    rfl

def zbkbResult (op : brop_zbkb) (rs1Val rs2Val : BitVec 64) : BitVec 64 :=
  match op with
  | .PACK => Sail.BitVec.extractLsb rs2Val 31 0 ++ Sail.BitVec.extractLsb rs1Val 31 0
  | .PACKH => zero_extend (m := 64) (Sail.BitVec.extractLsb rs2Val 7 0 ++ Sail.BitVec.extractLsb rs1Val 7 0)

theorem execute_ZBKB_RTYPE_run (state sFinal : State) (rs2 rs1 rd : regidx) (op : brop_zbkb)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (zbkbResult op rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_ZBKB_RTYPE rs2 rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [zbkbResult] at hwrite
  all_goals
    unfold execute_ZBKB_RTYPE
    refine Runs.bind hrs1 (Runs.bind hrs2 ?_)
    refine Runs.bind hwrite ?_
    rfl

theorem pack_eq (a b : BitVec 64) : zbkbResult .PACK a b = (a &&& 0xffffffff) ||| (b <<< 32) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [zbkbResult]; rw [BitVec.getLsbD_append]
  simp only [Sail.BitVec.extractLsb]
  iterate 64 (rcases i with _ | i; · simp)
  omega

theorem packh_eq (a b : BitVec 64) :
    zbkbResult .PACKH a b = (a &&& 0xff) ||| ((b &&& 0xff) <<< 8) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [zbkbResult, zero_extend, Sail.BitVec.zeroExtend, BitVec.getLsbD_setWidth]
  rw [BitVec.getLsbD_append]
  simp only [Sail.BitVec.extractLsb]
  iterate 64 (rcases i with _ | i; · simp)
  omega

def zbsResult (op : brop_zbs) (rs1Val rs2Val : BitVec 64) : BitVec 64 :=
  let mask : BitVec 64 :=
    Sail.shift_bits_left (zero_extend (m := 64) 1#1) (Sail.BitVec.extractLsb rs2Val 5 0)
  match op with
  | .BCLR => rs1Val &&& (Complement.complement mask)
  | .BEXT => zero_extend (m := 64) (bool_to_bit ((rs1Val &&& mask) != zeros (n := 64)))
  | .BINV => rs1Val ^^^ mask
  | .BSET => rs1Val ||| mask

theorem execute_ZBS_RTYPE_run (state sFinal : State) (rs2 rs1 rd : regidx) (op : brop_zbs)
    (rs1Val rs2Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hrs2 : Runs (rX_bits rs2) state state rs2Val)
    (hwrite : Runs (wX_bits rd (zbsResult op rs1Val rs2Val)) state sFinal ()) :
    Runs (execute_ZBS_RTYPE rs2 rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [zbsResult] at hwrite
  all_goals
    unfold execute_ZBS_RTYPE
    refine Runs.bind hrs1 (Runs.bind hrs2 ?_)
    refine Runs.bind hwrite ?_
    rfl

def zbsIResult (op : biop_zbs) (shamt : BitVec 6) (rs1Val : BitVec 64) : BitVec 64 :=
  let mask : BitVec 64 := Sail.shift_bits_left (zero_extend (m := 64) 1#1) shamt
  match op with
  | .BCLRI => rs1Val &&& (Complement.complement mask)
  | .BEXTI => zero_extend (m := 64) (bool_to_bit ((rs1Val &&& mask) != zeros (n := 64)))
  | .BINVI => rs1Val ^^^ mask
  | .BSETI => rs1Val ||| mask

theorem execute_ZBS_IOP_run (state sFinal : State) (shamt : BitVec 6) (rs1 rd : regidx)
    (op : biop_zbs) (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (zbsIResult op shamt rs1Val)) state sFinal ()) :
    Runs (execute_ZBS_IOP shamt rs1 rd op) state sFinal (.Retire_Success ()) := by
  cases op <;> simp only [zbsIResult] at hwrite
  all_goals
    unfold execute_ZBS_IOP
    refine Runs.bind hrs1 ?_
    refine Runs.bind hwrite ?_
    rfl

theorem execute_REV8_run (state sFinal : State) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (rev8 rs1Val)) state sFinal ()) :
    Runs (execute_REV8 rs1 rd) state sFinal (.Retire_Success ()) := by
  unfold execute_REV8
  refine Runs.bind hrs1 ?_
  refine Runs.bind hwrite ?_
  rfl

theorem execute_CLZ_run (state sFinal : State) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hrs1 : Runs (rX_bits rs1) state state rs1Val)
    (hwrite : Runs (wX_bits rd (to_bits (l := 64) (Sail.BitVec.countLeadingZeros rs1Val)))
      state sFinal ()) :
    Runs (execute_CLZ rs1 rd) state sFinal (.Retire_Success ()) := by
  unfold execute_CLZ
  refine Runs.bind hrs1 ?_
  refine Runs.bind hwrite ?_
  rfl

theorem zbs_mask (b : BitVec 64) :
    Sail.shift_bits_left (zero_extend (m := 64) 1#1) (Sail.BitVec.extractLsb b 5 0) =
      1#64 <<< (b.toNat % 64) := by
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq']
  rw [extractLsb_field]; simp [zero_extend, Sail.BitVec.zeroExtend]

theorem zbsI_mask (sh : BitVec 6) :
    Sail.shift_bits_left (zero_extend (m := 64) 1#1) sh = 1#64 <<< sh.toNat := by
  simp [Sail.shift_bits_left, BitVec.shiftLeft_eq', zero_extend, Sail.BitVec.zeroExtend]

theorem bset_eq (a b : BitVec 64) : zbsResult .BSET a b = a ||| (1#64 <<< (b.toNat % 64)) := by
  simp only [zbsResult]; rw [zbs_mask]

theorem bext_eq (a b : BitVec 64) :
    zbsResult .BEXT a b = if a &&& (1#64 <<< (b.toNat % 64)) = 0 then 0 else 1 := by
  simp only [zbsResult]; rw [zbs_mask]
  generalize a &&& 1#64 <<< (b.toNat % 64) = v
  by_cases h : v = 0#64
  · subst h; rfl
  · have : (v != zeros (n := 64)) = true := by simpa [zeros] using h
    simp [this, h, bool_to_bit, bool_bit_forwards, zero_extend, Sail.BitVec.zeroExtend]

theorem bclri_eq (sh : BitVec 6) (a : BitVec 64) :
    zbsIResult .BCLRI sh a = a &&& ~~~(1#64 <<< sh.toNat) := by
  simp only [zbsIResult]; rw [zbsI_mask]

theorem clz_eq (a : BitVec 64) : to_bits (l := 64) (Sail.BitVec.countLeadingZeros a) = a.clz := by
  apply BitVec.eq_of_toNat_eq
  simp [to_bits, Sail.get_slice_int, Sail.BitVec.countLeadingZeros]
  exact a.clz.isLt

theorem maxu_eq (a b : BitVec 64) :
    zbbResult .MAXU a b = if b.ult a then a else b := by
  by_cases h : b.toNat < a.toNat <;>
    simp [zbbResult, zopz0zK_u, BitVec.ult, Sail.BitVec.toNatInt, h]

theorem rev8_eq (x : Word) : rev8 x = Machine.rev8 x := by
  unfold rev8
  simp only [Id.run, forIn, ForIn'.forIn', IntRange.forIn', Sail.BitVec.length]
  repeat (rw [IntRange.forIn'.loop]; first | rw [dif_pos (by decide)] | rw [dif_neg (by decide)]
          simp only [bind_pure_comp, map_pure, pure_bind])
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb, Machine.rev8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [zeros, pure]
  iterate 64 (rcases i with _ | i; · simp)
  omega

/-! ## The simulation theorems -/

theorem sim_rev8 {rd rs1 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.rev8 rd rs1))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_REV8 (rg rs1) (rg rd)) _ _ _
  refine execute_REV8_run _ _ _ _ (m.reg rs1) (rX_rg_run hag rs1) ?_
  rw [rev8_eq]; exact wX_rg_run _ rd _

theorem sim_maxu {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.maxu rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_ZBB_RTYPE (rg rs2) (rg rs1) (rg rd) .MAXU) _ _ _
  refine execute_ZBB_RTYPE_run _ _ _ _ _ .MAXU (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [maxu_eq]; exact wX_rg_run _ rd _

theorem sim_pack {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.pack rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_ZBKB_RTYPE (rg rs2) (rg rs1) (rg rd) .PACK) _ _ _
  refine execute_ZBKB_RTYPE_run _ _ _ _ _ .PACK (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [pack_eq]; exact wX_rg_run _ rd _

theorem sim_packh {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.packh rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_ZBKB_RTYPE (rg rs2) (rg rs1) (rg rd) .PACKH) _ _ _
  refine execute_ZBKB_RTYPE_run _ _ _ _ _ .PACKH (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [packh_eq]; exact wX_rg_run _ rd _

theorem sim_bext {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bext rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_ZBS_RTYPE (rg rs2) (rg rs1) (rg rd) .BEXT) _ _ _
  refine execute_ZBS_RTYPE_run _ _ _ _ _ .BEXT (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [bext_eq]; exact wX_rg_run _ rd _

theorem sim_bset {rd rs1 rs2 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bset rd rs1 rs2))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_ZBS_RTYPE (rg rs2) (rg rs1) (rg rd) .BSET) _ _ _
  refine execute_ZBS_RTYPE_run _ _ _ _ _ .BSET (m.reg rs1) (m.reg rs2) (rX_rg_run hag rs1)
    (rX_rg_run hag rs2) ?_
  rw [bset_eq]; exact wX_rg_run _ rd _

theorem sim_bclri {rd rs1 : Fin 32} {sh : BitVec 6} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.bclri rd rs1 sh))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_ZBS_IOP sh (rg rs1) (rg rd) .BCLRI) _ _ _
  refine execute_ZBS_IOP_run _ _ sh _ _ .BCLRI (m.reg rs1) (rX_rg_run hag rs1) ?_
  rw [bclri_eq]; exact wX_rg_run _ rd _

theorem sim_clz {rd rs1 : Fin 32} (hR : Rel img m s)
    (hw : img.word? m.pc.toNat = some w) (hd : decodeNat w = some (.clz rd rs1))
    (hs : step img m = some m') :
    ∀ n, ∃ s', Runs (try_step n false) s s' false ∧ Rel img m' s' := by
  intro n
  obtain ⟨hpc, hex⟩ := step_inv hs hw hd
  simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at hex
  subst hex
  refine sim_wreg hR hw hd hpc ?_ n
  have hag := RegsAgree.T (m := m) hR.regs m.pc
  change Runs (execute_CLZ (rg rs1) (rg rd)) _ _ _
  refine execute_CLZ_run _ _ _ _ (m.reg rs1) (rX_rg_run hag rs1) ?_
  rw [clz_eq]; exact wX_rg_run _ rd _

end ZesuExec.SailLink
