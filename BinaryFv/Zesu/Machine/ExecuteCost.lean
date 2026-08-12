import BinaryFv.Zesu.Machine.Target
import BinaryFv.RiscV.Instruction.Execute.Load
import BinaryFv.RiscV.Logic.SepLogic

/-!
# The cost of the execute half

Fetch and decode are measured elsewhere and are unshareable. This module measures the remaining
part: applying an `execute` contract for one instruction.

**This is the only place a motif lemma can win**, so its rate is what decides Case A. A lemma for
the Case A shape is proved once — chaining ten execute contracts internally — and then applied at
seven sites, turning 70 execute obligations into 10 plus 7 applications. Whether that trade is worth
anything depends entirely on the ratio measured here against the ~360ms of fetch and ~50ms of decode
that each of the 70 instructions pays either way.

Each theorem below applies `execute_LOAD_lbu_run` with its twelve premises abstract. That isolates
the elaboration cost of the contract application itself, with no memory reasoning mixed in, which is
exactly the quantity a motif lemma would amortise.
-/

namespace BinaryFv.Zesu.Machine

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register
open MemoryAccessType mem_payload page_based_mem_type read_kind
open BinaryFv.RiscV.Sep

theorem exec_1 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_2 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_3 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_4 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_5 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_6 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_7 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_8 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_9 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

theorem exec_10 (s s' : State) (imm : BitVec 12) (rs1 rd : regidx)
    (srcBits mstatusBits : BitVec 64) (v : BitVec (8 * 1))
    (mstatusRead : s.regs.get? mstatus = some mstatusBits)
    (privRead : s.regs.get? cur_privilege = some .Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (addrReg : Runs (get_transformed_data_addr rs1 (sign_extend (m := 64) imm) (Load Data) 1) s s
      (.Ext_DataAddr_OK (virtaddr.Virtaddr srcBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr srcBits) 1 = true)
    (physAccess : Runs (phys_access_check (Load Data) PBMT_PMA .Machine
      (physaddr.Physaddr srcBits) 1 false) s s none)
    (noMMIO : Runs (within_mmio_readable (physaddr.Physaddr srcBits) 1) s s false)
    (hmem : ∀ (i : Nat) (h : i < (leBytes 1 v).length),
      s.mem.get? (srcBits.toNat + i) = some (leBytes 1 v)[i])
    (hwrite : Runs (wX_bits rd (zero_extend (m := 64) v)) s s' ()) :
    Runs (execute_LOAD imm rs1 rd true 1) s s' (.Retire_Success ()) :=
  execute_LOAD_lbu_run s s' imm rs1 rd srcBits mstatusBits v mstatusRead privRead mprvZero
    addrReg aligned physAccess noMMIO hmem hwrite

end BinaryFv.Zesu.Machine
