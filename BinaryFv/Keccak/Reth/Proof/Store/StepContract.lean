import BinaryFv.RiscV.Step.Hart
import BinaryFv.RiscV.Step.TryStep
import BinaryFv.RiscV.Step.Postlude
import BinaryFv.RiscV.Step.LandingPad
import BinaryFv.RiscV.Platform.Fetch
import BinaryFv.RiscV.Platform.FetchMemory
import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Instruction.Execute.Store
import BinaryFv.Keccak.Reth.Proof.Store.Decode

/-!
# Normal-execution `try_step` rule for the real ELF store `sd a3, 0(a0)`

This module packages the delivered aligned double-word store-execute contract
(`execute_STORE_dword_run`) and the delivered decode fact (`ext_decode_sd_run`) through the
authoritative generated `try_step`.

The concrete instruction is `10cdc: 00d53023  sd a3, 0(a0)`, i.e. the AST node
`.STORE (imm = 0, rs2 = a3 = x13, rs1 = a0 = x10, width = 8)`, whose little-endian instruction
bytes are `23 30 d5 00`.

The one structural difference from the XOR packaging is that the store's execute effect is a
physical memory write (`PreSail.writeBytes`) rather than a register write, so the post-execute state
`s'` is opaque.  `writeBytes_preserves_regs` shows that `writeBytes` only touches `.mem`, hence
`s'.regs = (coreStoreNextState …).regs`; with that single rewrite the register/counter/postlude
bookkeeping is identical to the XOR contract (minus the XOR's `x16` write).
-/

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-- The store's data register `a3 = x13` (the `rs2` field of the decoded `sd`). -/
abbrev a3reg : regidx := .Regidx 13#5

/-- The store's address register `a0 = x10` (the `rs1` field of the decoded `sd`). -/
abbrev a0reg : regidx := .Regidx 10#5

/-! ## Lifting the store execute through the `execute` dispatcher -/

/-- The state after the base-instruction path writes the generated next PC (identical to
the other per-instruction next-state constructors). -/
def coreStoreNextState (state : State) (pc : BitVec 64) : State :=
  { state with regs := state.regs.insert nextPC (Sail.BitVec.addInt pc 4) }

/-- Lift the delivered aligned double-word store execute through the `execute` dispatcher. -/
theorem executeCoreStoreDispatchRuns (afterNext s' : State)
    (dstBits mstatusBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (mstatusRead : afterNext.regs.get? mstatus = some mstatusBits)
    (privRead : afterNext.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits a3reg) afterNext afterNext dataBits)
    (addrReg : Runs (get_transformed_data_addr a0reg (sign_extend (m := 64) 0#12) (Store Data) 8)
      afterNext afterNext (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstBits) 8 false) afterNext afterNext none)
    (noMMIO : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8) afterNext afterNext false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat dataBits) afterNext s' true) :
    Runs (execute (.STORE (0#12, a3reg, a0reg, 8))) afterNext s' (.Retire_Success ()) := by
  change Runs (execute_STORE 0#12 a3reg a0reg 8) afterNext s' _
  exact execute_STORE_dword_run afterNext s' a3reg a0reg dstBits mstatusBits dataBits
    mstatusRead privRead mprvZero dataReg addrReg aligned physAccess noMMIO hwrite

/-! ## Active-hart retirement -/

/-- Compose explicit base-fetch, decoder, and store-execute premises with the fixed `sd` slice. -/
theorem runHartActiveCoreStoreRetires (stepNo : Nat) (state s' : State) (pc : BitVec 64)
    (dstBits mstatusBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (platform : FetchBasePlatform state pc) (interrupts : InterruptDisabled state)
    (fetchBytes : FetchBytesBaseContract state pc 0x23#8 0x30#8 0xd5#8 0x00#8)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (notExpected : LandingPadNotExpected state)
    (mstatusReadExec : (coreStoreNextState state pc).regs.get? mstatus = some mstatusBits)
    (privReadExec : (coreStoreNextState state pc).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits a3reg) (coreStoreNextState state pc) (coreStoreNextState state pc)
      dataBits)
    (addrReg : Runs (get_transformed_data_addr a0reg (sign_extend (m := 64) 0#12) (Store Data) 8)
      (coreStoreNextState state pc) (coreStoreNextState state pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstBits) 8 false)
      (coreStoreNextState state pc) (coreStoreNextState state pc) none)
    (noMMIOwrite : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8)
      (coreStoreNextState state pc) (coreStoreNextState state pc) false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat dataBits) (coreStoreNextState state pc) s'
      true) :
    Runs (run_hart_active stepNo) state s'
      (.Step_Execute (.Retire_Success (),
        zero_extend (m := 32) (fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8))) := by
  have base : BaseInstructionEncoding 0x23#8 := by unfold BaseInstructionEncoding; decide
  have fetch : Runs (fetch ()) state state (.F_Base (fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8)) :=
    fetch_base_of_fetchBytes state pc 0x23#8 0x30#8 0xd5#8 0x00#8 platform base fetchBytes
  rcases platform with ⟨misaBits, mstatusBitsF, pcRead, misaRead, mstatusReadF, privilegeRead,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
  have dispatch : Runs (dispatchInterrupt Privilege.Machine) state state none := by
    unfold Runs
    exact dispatchInterrupt_disabled state Privilege.Machine interrupts
  have landingPad : Runs (is_landing_pad_expected ()) state state false :=
    landingPad_notExpected state notExpected
  have nextPc : Runs (Sail.writeReg nextPC (Sail.BitVec.addInt pc 4)) state
      (coreStoreNextState state pc) PUnit.unit := by
    simpa [coreStoreNextState] using writeNextPc_run state pc
  have wordEq : fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8 = (0x00d53023 : BitVec 32) := by decide
  have decode : Runs (ext_decode (fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8)) state state
      (.STORE (0#12, a3reg, a0reg, 8)) := by
    rw [wordEq]
    exact ext_decode_sd_run state privilegeRead mseccfgBits mseccfgRead
  have execute : Runs (execute (.STORE (0#12, a3reg, a0reg, 8))) (coreStoreNextState state pc) s'
      (.Retire_Success ()) :=
    executeCoreStoreDispatchRuns (coreStoreNextState state pc) s' dstBits mstatusBits dataBits
      mstatusReadExec privReadExec mprvZero dataReg addrReg aligned physAccess noMMIOwrite hwrite
  exact runHartActiveBaseRetires stepNo state state (coreStoreNextState state pc) s'
    Privilege.Machine (fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8)
    (.STORE (0#12, a3reg, a0reg, 8)) pc privilegeRead dispatch fetch decode landingPad pcRead
    nextPc execute

/-- Feed exact Machine sparse-RAM fetch through the fixed `sd` instruction-retirement slice. -/
theorem runHartActiveCoreStoreRetiresWithFetchMemory (stepNo : Nat) (state s' : State)
    (pc : BitVec 64) (dstBits mstatusBits : BitVec 64) (dataBits : BitVec (8 * 8))
    (platform : FetchBasePlatform state pc) (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc 0x23#8 0x30#8 0xd5#8 0x00#8)
    (interrupts : InterruptDisabled state)
    (mseccfgBits : BitVec 64) (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits)
    (notExpected : LandingPadNotExpected state)
    (mstatusReadExec : (coreStoreNextState state pc).regs.get? mstatus = some mstatusBits)
    (privReadExec : (coreStoreNextState state pc).regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits a3reg) (coreStoreNextState state pc) (coreStoreNextState state pc)
      dataBits)
    (addrReg : Runs (get_transformed_data_addr a0reg (sign_extend (m := 64) 0#12) (Store Data) 8)
      (coreStoreNextState state pc) (coreStoreNextState state pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstBits) 8 false)
      (coreStoreNextState state pc) (coreStoreNextState state pc) none)
    (noMMIOwrite : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8)
      (coreStoreNextState state pc) (coreStoreNextState state pc) false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat dataBits) (coreStoreNextState state pc) s'
      true) :
    Runs (run_hart_active stepNo) state s'
      (.Step_Execute (.Retire_Success (),
        zero_extend (m := 32) (fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8))) := by
  have fetchBytes : FetchBytesBaseContract state pc 0x23#8 0x30#8 0xd5#8 0x00#8 :=
    fetch_bytes_machine_instructionFetch_fetch_word_run state pc 0x23#8 0x30#8 0xd5#8 0x00#8
      platform noMMIO bytes
  exact runHartActiveCoreStoreRetires stepNo state s' pc dstBits mstatusBits dataBits platform
    interrupts fetchBytes mseccfgBits mseccfgRead notExpected mstatusReadExec privReadExec mprvZero
    dataReg addrReg aligned physAccess noMMIOwrite hwrite

/-! ## `try_step` packaging -/

/-- The state after the generated `try_step` counter-increment write. -/
def tryStepCoreStoreAfterIncrement (state : State) : State :=
  { state with regs := state.regs.insert minstret_increment true }

/-- The state after the generated `try_step` PC-tick postlude (built on the store's opaque
post-write state `s'`). -/
def tryStepCoreStoreAfterTick (s' : State) (pc : BitVec 64) : State :=
  { s' with regs := s'.regs.insert PC (Sail.BitVec.addInt pc 4) }

/-- The state after the generated `try_step` retired-counter write. -/
def tryStepCoreStoreAfterRetired (s' : State) (pc retired : BitVec 64) : State :=
  { tryStepCoreStoreAfterTick s' pc with
    regs := (tryStepCoreStoreAfterTick s' pc).regs.insert minstret
      (Sail.BitVec.addInt retired 1) }

/--
Lift the fixed real-ELF `sd a3, 0(a0)` store slice through the authoritative generated `try_step`.

The store-execute preconditions and the decoder's `mseccfg`-presence fact are kept as explicit
hypotheses (about `coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc` and
`tryStepCoreStoreAfterIncrement state` respectively) so that they can be discharged at the
SepLogic-`Triple` layer.  The store's physical write yields the opaque post-state `s'`; since
`writeBytes` preserves the register file, the counter/postlude bookkeeping matches the XOR contract.
-/
theorem tryStepCoreStoreRetires (stepNo : Nat) (state s' : State)
    (pc dstBits mstatusBits retired : BitVec 64) (dataBits : BitVec (8 * 8))
    (inhibit : BitVec 32) (config : BitVec 64)
    (platform : FetchBasePlatform (tryStepCoreStoreAfterIncrement state) pc)
    (noMMIO : FetchMemoryNoMMIO (tryStepCoreStoreAfterIncrement state) pc)
    (bytes : FetchBytesAt (tryStepCoreStoreAfterIncrement state) pc 0x23#8 0x30#8 0xd5#8 0x00#8)
    (interrupts : InterruptDisabled (tryStepCoreStoreAfterIncrement state))
    (mseccfgBits : BitVec 64)
    (mseccfgRead : (tryStepCoreStoreAfterIncrement state).regs.get? mseccfg = some mseccfgBits)
    (notExpected : LandingPadNotExpected (tryStepCoreStoreAfterIncrement state))
    (mstatusReadExec :
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc).regs.get? mstatus =
        some mstatusBits)
    (privReadExec :
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc).regs.get? cur_privilege =
        some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (dataReg : Runs (rX_bits a3reg)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc) dataBits)
    (addrReg : Runs (get_transformed_data_addr a0reg (sign_extend (m := 64) 0#12) (Store Data) 8)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc)
      (.Ext_DataAddr_OK (virtaddr.Virtaddr dstBits)))
    (aligned : is_aligned_vaddr (virtaddr.Virtaddr dstBits) 8 = true)
    (physAccess : Runs (phys_access_check (Store Data) PBMT_PMA .Machine
      (physaddr.Physaddr dstBits) 8 false)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc) none)
    (noMMIOwrite : Runs (within_mmio_writable (physaddr.Physaddr dstBits) 8)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc) false)
    (hwrite : Runs (PreSail.writeBytes dstBits.toNat dataBits)
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc) s' true)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepCoreStoreAfterRetired s' pc retired) false := by
  have active := runHartActiveCoreStoreRetiresWithFetchMemory stepNo
    (tryStepCoreStoreAfterIncrement state) s' pc dstBits mstatusBits dataBits platform noMMIO
    bytes interrupts mseccfgBits mseccfgRead notExpected mstatusReadExec privReadExec mprvZero
    dataReg addrReg aligned physAccess noMMIOwrite hwrite
  have regsEq : s'.regs =
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc).regs :=
    writeBytes_preserves_regs dstBits.toNat dataBits
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc) s' hwrite
  rcases platform with ⟨misaBits, mstatusBitsF, pcRead, misaRead, mstatusReadF, privilegeAfterInc,
    pcLow0, pcLow1, alignedVaddr, alignedPaddr, pmpDisabled, pmaAllows⟩
  have privilege : state.regs.get? cur_privilege = some Privilege.Machine := by
    calc
      state.regs.get? cur_privilege =
          (tryStepCoreStoreAfterIncrement state).regs.get? cur_privilege := by
            symm
            simpa [tryStepCoreStoreAfterIncrement] using
              writeReg_read_unchanged state minstret_increment cur_privilege true (by decide)
      _ = some Privilege.Machine := privilegeAfterInc
  have shouldIncrement : Runs (should_inc_minstret Privilege.Machine) state state true :=
    shouldIncMinstretMachine state inhibit config inhibitRead configRead notInhibited machineEnabled
  have increment : Runs (Sail.writeReg minstret_increment true) state
      (tryStepCoreStoreAfterIncrement state) PUnit.unit := by
    simpa [tryStepCoreStoreAfterIncrement] using writeReg_run state minstret_increment true
  have hartAfterIncrement :
      (tryStepCoreStoreAfterIncrement state).regs.get? hart_state = some (.HART_ACTIVE ()) := by
    calc
      (tryStepCoreStoreAfterIncrement state).regs.get? hart_state =
          state.regs.get? hart_state := by
            simpa [tryStepCoreStoreAfterIncrement] using
              writeReg_read_unchanged state minstret_increment hart_state true (by decide)
      _ = some (.HART_ACTIVE ()) := hartRead
  have hartAfterActive : s'.regs.get? hart_state = some (.HART_ACTIVE ()) := by
    rw [regsEq]
    calc
      (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc).regs.get? hart_state =
          (tryStepCoreStoreAfterIncrement state).regs.get? hart_state := by
            simpa [coreStoreNextState] using
              writeReg_read_unchanged (tryStepCoreStoreAfterIncrement state) nextPC hart_state
                (Sail.BitVec.addInt pc 4) (by decide)
      _ = some (.HART_ACTIVE ()) := hartAfterIncrement
  have nextPcAfterActive : s'.regs.get? nextPC = some (Sail.BitVec.addInt pc 4) := by
    rw [regsEq]
    change
      ((tryStepCoreStoreAfterIncrement state).regs.insert nextPC (Sail.BitVec.addInt pc 4)).get?
          nextPC =
        some (Sail.BitVec.addInt pc 4)
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have tick : Runs (tick_pc ()) s' (tryStepCoreStoreAfterTick s' pc) () := by
    simpa [tryStepCoreStoreAfterTick] using
      tickPc_run s' (Sail.BitVec.addInt pc 4) nextPcAfterActive
  have incrementAfterWrite :
      (tryStepCoreStoreAfterIncrement state).regs.get? minstret_increment = some true := by
    change (state.regs.insert minstret_increment true).get? minstret_increment = some true
    rw [Std.ExtDHashMap.get?_insert]
    simp
  have incrementAfterTick :
      (tryStepCoreStoreAfterTick s' pc).regs.get? minstret_increment = some true := by
    calc
      (tryStepCoreStoreAfterTick s' pc).regs.get? minstret_increment =
          s'.regs.get? minstret_increment := by
            simpa [tryStepCoreStoreAfterTick] using
              writeReg_read_unchanged s' PC minstret_increment (Sail.BitVec.addInt pc 4) (by decide)
      _ = (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc).regs.get?
          minstret_increment := by rw [regsEq]
      _ = (tryStepCoreStoreAfterIncrement state).regs.get? minstret_increment := by
            simpa [coreStoreNextState] using
              writeReg_read_unchanged (tryStepCoreStoreAfterIncrement state) nextPC
                minstret_increment (Sail.BitVec.addInt pc 4) (by decide)
      _ = some true := incrementAfterWrite
  have retiredAfterTick :
      (tryStepCoreStoreAfterTick s' pc).regs.get? minstret = some retired := by
    calc
      (tryStepCoreStoreAfterTick s' pc).regs.get? minstret = s'.regs.get? minstret := by
            simpa [tryStepCoreStoreAfterTick] using
              writeReg_read_unchanged s' PC minstret (Sail.BitVec.addInt pc 4) (by decide)
      _ = (coreStoreNextState (tryStepCoreStoreAfterIncrement state) pc).regs.get? minstret := by
            rw [regsEq]
      _ = (tryStepCoreStoreAfterIncrement state).regs.get? minstret := by
            simpa [coreStoreNextState] using
              writeReg_read_unchanged (tryStepCoreStoreAfterIncrement state) nextPC minstret
                (Sail.BitVec.addInt pc 4) (by decide)
      _ = state.regs.get? minstret := by
            simpa [tryStepCoreStoreAfterIncrement] using
              writeReg_read_unchanged state minstret_increment minstret true (by decide)
      _ = some retired := retiredRead
  have writeRetired : Runs (Sail.writeReg minstret (Sail.BitVec.addInt retired 1))
      (tryStepCoreStoreAfterTick s' pc)
      (tryStepCoreStoreAfterRetired s' pc retired) PUnit.unit := by
    simpa [tryStepCoreStoreAfterRetired] using
      writeReg_run (tryStepCoreStoreAfterTick s' pc) minstret (Sail.BitVec.addInt retired 1)
  exact tryStepRetires stepNo state (tryStepCoreStoreAfterIncrement state) s'
    (tryStepCoreStoreAfterTick s' pc) (tryStepCoreStoreAfterRetired s' pc retired) Privilege.Machine
    retired (zero_extend (m := 32) (fetchWord 0x23#8 0x30#8 0xd5#8 0x00#8)) privilege shouldIncrement
    increment hartAfterIncrement active hartAfterActive tick incrementAfterTick retiredAfterTick
    writeRetired

end BinaryFv.Keccak
