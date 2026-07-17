import BinaryFv.Keccak.Reth.Proof.Helpers.Memset.Frame

/-!
# The constant byte store

Byte assembly for `memset`: reducing the generated `sb` of `a1`'s low byte to a single memory write.
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.RiscV.Sep
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## New foundational facts for the constant byte store -/

/-- The low-byte extraction of a width-64 word is its width-8 truncation. -/
theorem extractLsb_lowbyte (x : BitVec 64) :
    Sail.BitVec.extractLsb x 7 0 = BitVec.setWidth 8 x := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  bv_decide

/-- Reading `a1 = x11` via `rX_bits` (the byte-store data source). -/
theorem rX_bits_x11_run (s : State) (v : BitVec 64) (h : s.regs.get? x11 = some v) :
    Runs (rX_bits (.Regidx 11#5)) s s v := by
  have r11 : (Sail.BitVec.toNatInt (11#5)).toNat = 11 := by decide
  unfold Runs
  simp [rX_bits, rX, r11, h, PreSail.readReg, EStateM.run, EStateM.bind,
    EStateM.get, EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe,
    regval_from_reg]

/-- Aligned byte store reading an *arbitrary* source register value `dataFull` and writing its low
byte `bval = extractLsb dataFull 7 0`.  Unlike `execute_STORE_byte_run` (which requires the register
to already hold a zero-extended byte `setWidth 64 dataBits`), this reads the full register and lets
the generated truncation `extractLsb (rX_bits rs2) 7 0` produce the stored byte, so it is valid for
any `a1`. -/
theorem execute_STORE_sb_full_run (s s' : State) (rs2 rs1 : regidx) (imm : BitVec 12)
    (dstBits mstatusBits dataFull : BitVec 64) (bval : BitVec (8 * 1))
    (hbval : bval = Sail.BitVec.extractLsb dataFull 7 0)
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits rs2) s s dataFull)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Store Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 1) s s false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat bval) s s' true) :
    Runs (execute_STORE imm rs2 rs1 1) s s' (.Retire_Success ()) := by
  subst hbval
  unfold execute_STORE
  refine Runs.bind (assert_true_run s _) ?_
  refine Runs.bind dataReg ?_
  refine Runs.bind (run_pure s _) ?_
  refine Runs.bind
    (vmem_write_byte_run s s' rs1 (sign_extend (m := 64) imm) dstBits mstatusBits _
      mstatusRead privRead mprvZero addrReg physAccess noMMIO ?hw) ?_
  case hw => exact hwrite
  exact run_pure s' _

end BinaryFv.Keccak
