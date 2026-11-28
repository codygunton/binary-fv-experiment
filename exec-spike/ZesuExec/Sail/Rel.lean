import BinaryFv.RiscV.Logic.Framing
import ZesuExec.Image

/-!
# Relating the concrete machine to the specialised Sail model

`Configured` fixes the registers that the specialised `try_step` reads on the retiring path of the
33 forms, other than `x1 … x31`, `PC` and `nextPC` (`tools/reach.py` lists the candidates; the
retiring path reads `cur_privilege`, `hart_state`, `misa`, `mstatus`, `mseccfg`, `pma_regions`,
`mcountinhibit`, `minstretcfg`, `minstret`). Each field fixes presence and, where the path
branches on the value, the value. Three further fields state the profile invariants that the
specialisation patch assumes but the specialised path no longer reads: I2 `mip & mie = 0`,
I3 `htif_tohost_base = None`, I5 `elp = NO_LP_EXPECTED`.

`Rel img m s` says that `s` is configured, agrees with `m` on `x1 … x31`, `PC` and every present
byte, and holds every instruction word of `img` that lies in `.text`.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV (State Runs)
open LeanRV64DExecutable.Functions
open Register

deriving instance DecidableEq for misaligned_exception
deriving instance DecidableEq for PMAMisalignedExceptions
deriving instance DecidableEq for MemoryRegionType
deriving instance DecidableEq for AtomicSupport
deriving instance DecidableEq for Reservability
deriving instance DecidableEq for PMA
deriving instance DecidableEq for PMA_Region
deriving instance DecidableEq for PointerMaskingMode

/-- The attributes the profile configuration gives every region (copied from the stock RAM
region by `01-profile-config.patch`), with the region's own memory type (`main`: MainMemory and
coherent; otherwise IOMemory, not coherent; never cacheable) and `readable`/`writable`/`executable`. -/
def zesuPma (main x r w : Bool) : PMA where
  mem_type := if main then .MainMemory else .IOMemory
  cacheable := false
  coherent := main
  executable := x
  readable := r
  writable := w
  read_idempotent := true
  write_idempotent := true
  misaligned_exceptions := { load_store := none, vector := none, amo := .AccessFault }
  atomic_support := .AMOCASQ
  reservability := .RsrvEventual
  supports_cbo_zero := true
  supports_pte_read := true
  supports_pte_write := true

/-- The value `sail_model_init` writes to `pma_regions` under the profile configuration:
input, program ROM, RAM. -/
def zesuPmaRegions : List PMA_Region :=
  [ { base := 0x40000000#64, size := 0x40000000#64, attributes := zesuPma false false true false,
      include_in_device_tree := true },
    { base := 0x80000000#64, size := 0x8000000#64, attributes := zesuPma false true true false,
      include_in_device_tree := true },
    { base := 0xa0000000#64, size := 0x20000000#64, attributes := zesuPma true false true true,
      include_in_device_tree := true } ]

/-- The profile invariants and the registers read by the retiring path of every proved form. -/
structure Configured (s : State) : Prop where
  /-- I1 -/
  privilege : s.regs.get? cur_privilege = some .Machine
  /-- I4 -/
  hart : s.regs.get? hart_state = some (.HART_ACTIVE ())
  /-- I2 (not read by the specialised path) -/
  interrupts : ∃ p e, s.regs.get? mip = some p ∧ s.regs.get? mie = some e ∧ p &&& e = 0
  /-- I3 (not read by the specialised path) -/
  htif : s.regs.get? htif_tohost_base = some none
  /-- I5 (not read by the specialised path) -/
  elp : s.regs.get? Register.elp = some 0#1
  /-- I6; `mstatus` is read by every memory access. -/
  mstatus : ∃ v, s.regs.get? Register.mstatus = some v ∧ _get_Mstatus_MPRV v = 0#1
  /-- Read by the `Zca` alignment gates; the `M` bit gates the decoding of `mul`, `mulhu`. -/
  misa : ∃ v, s.regs.get? Register.misa = some v ∧ _get_Misa_M v = 1#1
  /-- Read by the decoder (`get_xLPE`) and by pointer masking of data addresses. -/
  mseccfg : ∃ v, s.regs.get? Register.mseccfg = some v ∧
    pmm_mode_backwards (_get_Seccfg_PMM v) = .PMM_Disabled
  /-- Read by every physical access check. -/
  pma : s.regs.get? pma_regions = some zesuPmaRegions
  /-- `should_inc_minstret`: retirement counting is enabled. -/
  inhibit : ∃ v, s.regs.get? mcountinhibit = some v ∧ _get_Counterin_IR v = 0#1
  instretcfg : ∃ v, s.regs.get? minstretcfg = some v ∧ _get_CountSmcntrpmf_MINH v = 0#1
  /-- Read and incremented by the step postlude. -/
  instret : ∃ v, s.regs.get? minstret = some v

/-- `Configured` implies the profile invariants I1 to I4 (and I5, I6). -/
theorem Configured.invariants {s : State} (h : Configured s) :
    s.regs.get? cur_privilege = some .Machine ∧
    (∃ p e, s.regs.get? mip = some p ∧ s.regs.get? mie = some e ∧ p &&& e = 0) ∧
    s.regs.get? htif_tohost_base = some none ∧
    s.regs.get? hart_state = some (.HART_ACTIVE ()) ∧
    s.regs.get? Register.elp = some 0#1 ∧
    (∃ v, s.regs.get? Register.mstatus = some v ∧ _get_Mstatus_MPRV v = 0#1) :=
  ⟨h.privilege, h.interrupts, h.htif, h.hart, h.elp, h.mstatus⟩

/-- Boolean check of `Configured`, used by the differential test (engine A). -/
def configuredB (s : State) : Bool :=
  (match s.regs.get? cur_privilege with | some .Machine => true | _ => false) &&
  (match s.regs.get? hart_state with | some (.HART_ACTIVE ()) => true | _ => false) &&
  (match s.regs.get? mip, s.regs.get? mie with
    | some p, some e => p &&& e == 0 | _, _ => false) &&
  (match s.regs.get? htif_tohost_base with | some none => true | _ => false) &&
  (match s.regs.get? Register.elp with | some v => v == 0#1 | none => false) &&
  (match s.regs.get? Register.mstatus with | some v => _get_Mstatus_MPRV v == 0#1 | none => false) &&
  (match s.regs.get? Register.misa with | some v => _get_Misa_M v == 1#1 | none => false) &&
  (match s.regs.get? Register.mseccfg with
    | some v => decide (pmm_mode_backwards (_get_Seccfg_PMM v) = .PMM_Disabled) | none => false) &&
  (match s.regs.get? pma_regions with | some r => decide (r = zesuPmaRegions) | none => false) &&
  (match s.regs.get? mcountinhibit with | some v => _get_Counterin_IR v == 0#1 | none => false) &&
  (match s.regs.get? minstretcfg with
    | some v => _get_CountSmcntrpmf_MINH v == 0#1 | none => false) &&
  (match s.regs.get? minstret with | some _ => true | none => false)

theorem configuredB_sound {s : State} (h : configuredB s = true) : Configured s := by
  simp only [configuredB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · revert h1; generalize s.regs.get? cur_privilege = o
    rcases o with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp
  · revert h2; generalize s.regs.get? hart_state = o
    rcases o with _ | ⟨⟨⟩ | _⟩ <;> simp
  · revert h3; generalize s.regs.get? mip = o; generalize s.regs.get? mie = o'
    rcases o with _ | p <;> rcases o' with _ | e <;> simp
  · revert h4; generalize s.regs.get? htif_tohost_base = o
    rcases o with _ | (_ | v) <;> simp <;> rfl
  · revert h5; generalize s.regs.get? Register.elp = o
    rcases o with _ | v <;> simp
  · revert h6; generalize s.regs.get? Register.mstatus = o
    rcases o with _ | v <;> simp
  · revert h7; generalize s.regs.get? Register.misa = o
    rcases o with _ | v <;> simp
  · revert h8; generalize s.regs.get? Register.mseccfg = o
    rcases o with _ | v <;> simp
  · revert h9; generalize s.regs.get? pma_regions = o
    rcases o with _ | v <;> simp
  · revert h10; generalize s.regs.get? mcountinhibit = o
    rcases o with _ | v <;> simp
  · revert h11; generalize s.regs.get? minstretcfg = o
    rcases o with _ | v <;> simp
  · revert h12; generalize s.regs.get? minstret = o
    rcases o with _ | v <;> simp

/-- `x1 … x31`; index 0 (the hard-wired zero) maps to `x1` and is never used. -/
def xreg : Fin 32 → Register
  | ⟨1, _⟩ => x1 | ⟨2, _⟩ => x2 | ⟨3, _⟩ => x3 | ⟨4, _⟩ => x4 | ⟨5, _⟩ => x5 | ⟨6, _⟩ => x6
  | ⟨7, _⟩ => x7 | ⟨8, _⟩ => x8 | ⟨9, _⟩ => x9 | ⟨10, _⟩ => x10 | ⟨11, _⟩ => x11
  | ⟨12, _⟩ => x12 | ⟨13, _⟩ => x13 | ⟨14, _⟩ => x14 | ⟨15, _⟩ => x15 | ⟨16, _⟩ => x16
  | ⟨17, _⟩ => x17 | ⟨18, _⟩ => x18 | ⟨19, _⟩ => x19 | ⟨20, _⟩ => x20 | ⟨21, _⟩ => x21
  | ⟨22, _⟩ => x22 | ⟨23, _⟩ => x23 | ⟨24, _⟩ => x24 | ⟨25, _⟩ => x25 | ⟨26, _⟩ => x26
  | ⟨27, _⟩ => x27 | ⟨28, _⟩ => x28 | ⟨29, _⟩ => x29 | ⟨30, _⟩ => x30 | ⟨31, _⟩ => x31
  | _ => x1

/-- Every `xreg i` holds a 64-bit word. -/
theorem xreg_type (i : Fin 32) : RegisterType (xreg i) = BitVec 64 := by
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩
  | ⟨10, _⟩ | ⟨11, _⟩ | ⟨12, _⟩ | ⟨13, _⟩ | ⟨14, _⟩ | ⟨15, _⟩ | ⟨16, _⟩ | ⟨17, _⟩ | ⟨18, _⟩
  | ⟨19, _⟩ | ⟨20, _⟩ | ⟨21, _⟩ | ⟨22, _⟩ | ⟨23, _⟩ | ⟨24, _⟩ | ⟨25, _⟩ | ⟨26, _⟩ | ⟨27, _⟩
  | ⟨28, _⟩ | ⟨29, _⟩ | ⟨30, _⟩ | ⟨31, _⟩ => rfl
  | ⟨n + 32, h⟩ => exact absurd h (by omega)

/-- The four little-endian bytes of the instruction word `w` at `a`. -/
def CodeAt (s : State) (a w : Nat) : Prop :=
  ∀ j, j < 4 → s.mem.get? (a + j) = some (BitVec.ofNat 8 (w / 256 ^ j))

/-- The simulation relation. `regs` reads `x i` at its 64-bit type (`xreg_type`); `code` covers
the words of `img` that lie in `.text`, the only addresses `step` fetches from. -/
structure Rel (img : Image) (m : Machine) (s : State) : Prop where
  conf : Configured s
  regs : ∀ i : Fin 32, i.val ≠ 0 →
    s.regs.get? (xreg i) = some (cast (xreg_type i).symm (m.regs i))
  pc : s.regs.get? Register.PC = some m.pc
  mem : ∀ a b, m.mem a = some b → s.mem.get? a.toNat = some b
  code : ∀ seg ∈ img.text, ∀ k w, seg.words[k]? = some w →
    Layout.textLo ≤ seg.base + 4 * k → seg.base + 4 * k < Layout.textHi →
    CodeAt s (seg.base + 4 * k) w

/-- Sail's register index of `x i`. -/
def rg (i : Fin 32) : regidx := .Regidx (BitVec.ofNat 5 i.val)

/-- Sail's AST for each of the 33 forms. -/
def toSail : Instr → instruction
  | .lui rd imm => .UTYPE (imm, rg rd, .LUI)
  | .auipc rd imm => .UTYPE (imm, rg rd, .AUIPC)
  | .jal rd imm => .JAL (imm, rg rd)
  | .jalr rd rs1 imm => .JALR (imm, rg rs1, rg rd)
  | .beq rs1 rs2 imm => .BTYPE (imm, rg rs2, rg rs1, .BEQ)
  | .bne rs1 rs2 imm => .BTYPE (imm, rg rs2, rg rs1, .BNE)
  | .blt rs1 rs2 imm => .BTYPE (imm, rg rs2, rg rs1, .BLT)
  | .bltu rs1 rs2 imm => .BTYPE (imm, rg rs2, rg rs1, .BLTU)
  | .bgeu rs1 rs2 imm => .BTYPE (imm, rg rs2, rg rs1, .BGEU)
  | .lb rd rs1 imm => .LOAD (imm, rg rs1, rg rd, false, 1)
  | .lbu rd rs1 imm => .LOAD (imm, rg rs1, rg rd, true, 1)
  | .lhu rd rs1 imm => .LOAD (imm, rg rs1, rg rd, true, 2)
  | .lw rd rs1 imm => .LOAD (imm, rg rs1, rg rd, false, 4)
  | .ld rd rs1 imm => .LOAD (imm, rg rs1, rg rd, false, 8)
  | .sb rs1 rs2 imm => .STORE (imm, rg rs2, rg rs1, 1)
  | .sh rs1 rs2 imm => .STORE (imm, rg rs2, rg rs1, 2)
  | .sw rs1 rs2 imm => .STORE (imm, rg rs2, rg rs1, 4)
  | .sd rs1 rs2 imm => .STORE (imm, rg rs2, rg rs1, 8)
  | .addi rd rs1 imm => .ITYPE (imm, rg rs1, rg rd, .ADDI)
  | .andi rd rs1 imm => .ITYPE (imm, rg rs1, rg rd, .ANDI)
  | .xori rd rs1 imm => .ITYPE (imm, rg rs1, rg rd, .XORI)
  | .sltiu rd rs1 imm => .ITYPE (imm, rg rs1, rg rd, .SLTIU)
  | .slli rd rs1 sh => .SHIFTIOP (sh, rg rs1, rg rd, .SLLI)
  | .srli rd rs1 sh => .SHIFTIOP (sh, rg rs1, rg rd, .SRLI)
  | .add rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .ADD)
  | .sub rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .SUB)
  | .and rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .AND)
  | .or rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .OR)
  | .sll rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .SLL)
  | .sltu rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .SLTU)
  | .mul rd rs1 rs2 =>
    .MUL (rg rs2, rg rs1, rg rd, { result_part := .Low, signed_rs1 := .Signed, signed_rs2 := .Signed })
  | .mulhu rd rs1 rs2 =>
    .MUL (rg rs2, rg rs1, rg rd,
      { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned })
  | .xor rd rs1 rs2 => .RTYPE (rg rs2, rg rs1, rg rd, .XOR)
  | .addiw rd rs1 imm => .ADDIW (imm, rg rs1, rg rd)
  | .bge rs1 rs2 imm => .BTYPE (imm, rg rs2, rg rs1, .BGE)

end ZesuExec.SailLink
