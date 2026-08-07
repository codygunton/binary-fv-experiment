import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterRuns

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

/-- The canonical decoder's success epilogue builds an 832-byte `RawStatelessInput` on its
stack, stores the zero success status at result offset 832, and copies that payload to result. -/
def rawResultSuccessSites : Array Nat := #[0x12f90, 0x12f94, 0x12f98, 0x12f9c, 0x12fa0, 0x12fa4,
  0x12fa8]

def rawResultSuccessWords : Array Nat := #[0x61613023, 0x60913423, 0x28013503, 0x34051023,
  0x2d010593, 0x34000613, 0xd44fd06f]

/-- This fact is checked directly against immutable ELF bytes, not source or debug mappings. -/
def rawResultSuccessBlockValid : Bool :=
  rawResultSuccessSites.zip rawResultSuccessWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_result_success_block_valid : rawResultSuccessBlockValid = true := by
  native_decide

/-- The decoder writes chain-config fields into the final root-object tail before result copy.
The stores cover offsets 736, 744, 752/760, 768/776, and 784/792/800/808 relative to the root. -/
def rawChainConfigResultStoreSites : Array Nat := #[
  0x12e64, 0x12e68, 0x12e6c, 0x12e70, 0x12e8c, 0x12e90, 0x12e94, 0x12e98, 0x12e9c, 0x12ea0]

def rawChainConfigResultStoreWords : Array Nat := #[
  0x5ce13023, 0x5cf13423, 0x5d013823, 0x5d113c23, 0x5a813823, 0x5ba13c23, 0x5f613023,
  0x5f513423, 0x5f313823, 0x5f210c23]

/-- The field-placement evidence is checked only against the immutable decoder image. -/
def rawChainConfigResultStoresValid : Bool :=
  rawChainConfigResultStoreSites.zip rawChainConfigResultStoreWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_chain_config_result_stores_valid : rawChainConfigResultStoresValid = true := by
  native_decide

/-- Generated Sail decodes the ELF-pinned stores that materialize the chain-config tail of the
stack root.  This fixes each source register and stack offset without asserting an unobserved Zig
optional-value encoding. -/
theorem raw_chain_config_result_stores_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x5a813823 : BitVec 32)) state state
        (.STORE (1456#12, .Regidx 8#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5ba13c23 : BitVec 32)) state state
        (.STORE (1464#12, .Regidx 26#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5ce13023 : BitVec 32)) state state
        (.STORE (1472#12, .Regidx 14#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5cf13423 : BitVec 32)) state state
        (.STORE (1480#12, .Regidx 15#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5d013823 : BitVec 32)) state state
        (.STORE (1488#12, .Regidx 16#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5d113c23 : BitVec 32)) state state
        (.STORE (1496#12, .Regidx 17#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f613023 : BitVec 32)) state state
        (.STORE (1504#12, .Regidx 22#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f513423 : BitVec 32)) state state
        (.STORE (1512#12, .Regidx 21#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f313823 : BitVec 32)) state state
        (.STORE (1520#12, .Regidx 19#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f210c23 : BitVec 32)) state state
        (.STORE (1528#12, .Regidx 18#5, .Regidx 2#5, 1)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  decode_run

/-- Every byte-load instruction used by the present 24-byte blob-schedule branch is pinned to the
immutable decoder image.  The non-contiguous groups reflect the intervening endian assembly. -/
def rawBlobSchedulePresentLoadSites : Array Nat := #[
  0x12cbc, 0x12cc0, 0x12cc4, 0x12cc8, 0x12ccc, 0x12cd0, 0x12cd4, 0x12cd8,
  0x12cdc, 0x12ce0, 0x12ce4, 0x12ce8, 0x12d08, 0x12d0c, 0x12d10, 0x12d14,
  0x12d40, 0x12d44, 0x12d48, 0x12d4c, 0x12d70, 0x12d74, 0x12d78, 0x12d7c]

def rawBlobSchedulePresentLoadWords : Array Nat := #[
  0x000bc503, 0x001bc583, 0x002bc603, 0x003bc683, 0x004bc703, 0x005bc783,
  0x006bc803, 0x007bc883, 0x008bc283, 0x009bc303, 0x00abc383, 0x00bbce03,
  0x00cbc583, 0x00dbc683, 0x00ebc783, 0x00fbce83, 0x010bc683, 0x011bc303,
  0x012bc383, 0x013bce03, 0x015bc383, 0x014bce03, 0x016bce83, 0x017bcf03]

def rawBlobSchedulePresentLoadsValid : Bool :=
  rawBlobSchedulePresentLoadSites.zip rawBlobSchedulePresentLoadWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_present_loads_valid : rawBlobSchedulePresentLoadsValid = true := by
  native_decide

/-- The first six schedule bytes are assembled by four shifts and three ORs at the immutable
ELF PCs between the two contiguous load groups. -/
def rawBlobSchedulePresentAssemblySites : Array Nat :=
  #[0x12cec, 0x12cf0, 0x12cf4, 0x12cf8, 0x12cfc, 0x12d00, 0x12d04]

def rawBlobSchedulePresentAssemblyWords : Array Nat :=
  #[0x00859593, 0x01061613, 0x01869693, 0x00879793, 0x00a5e533, 0x00c6e633, 0x00e7e733]

def rawBlobSchedulePresentAssemblyValid : Bool :=
  rawBlobSchedulePresentAssemblySites.zip rawBlobSchedulePresentAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_present_assembly_valid : rawBlobSchedulePresentAssemblyValid = true := by
  native_decide

/-- Schedule bytes 6--15 are assembled by a second, longer fragment of six shifts and four ORs
between the second and third contiguous load groups. -/
def rawBlobScheduleSecondAssemblySites : Array Nat :=
  #[0x12d18, 0x12d1c, 0x12d20, 0x12d24, 0x12d28, 0x12d2c, 0x12d30, 0x12d34, 0x12d38, 0x12d3c]

def rawBlobScheduleSecondAssemblyWords : Array Nat :=
  #[0x01081813, 0x01889893, 0x00831313, 0x01039393, 0x018e1e13, 0x00869693,
    0x0108e833, 0x005368b3, 0x007e62b3, 0x00b6e5b3]

def rawBlobScheduleSecondAssemblyValid : Bool :=
  rawBlobScheduleSecondAssemblySites.zip rawBlobScheduleSecondAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_second_assembly_valid :
    rawBlobScheduleSecondAssemblyValid = true := by
  native_decide

/-- Schedule bytes 14--19 are assembled by a third fragment of five shifts and three ORs between
the third and fourth contiguous load groups. -/
def rawBlobScheduleThirdAssemblySites : Array Nat :=
  #[0x12d50, 0x12d54, 0x12d58, 0x12d5c, 0x12d60, 0x12d64, 0x12d68, 0x12d6c]

def rawBlobScheduleThirdAssemblyWords : Array Nat :=
  #[0x01079793, 0x018e9e93, 0x00831313, 0x01039393, 0x018e1e13, 0x00fee7b3, 0x00d366b3, 0x007e6333]

def rawBlobScheduleThirdAssemblyValid : Bool :=
  rawBlobScheduleThirdAssemblySites.zip rawBlobScheduleThirdAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_third_assembly_valid :
    rawBlobScheduleThirdAssemblyValid = true := by
  native_decide

/-- The fourth and final assembly fragment folds the branch's twenty-four bytes into the three
64-bit schedule words held in `s6`, `s5`, and `s3`. -/
def rawBlobScheduleFourthAssemblySites : Array Nat :=
  #[0x12d80, 0x12d84, 0x12d88, 0x12d8c, 0x12d90, 0x12d94, 0x12d98, 0x12d9c, 0x12da0,
    0x12da4, 0x12da8, 0x12dac, 0x12db0, 0x12db4, 0x12db8, 0x12dbc, 0x12dc0]

def rawBlobScheduleFourthAssemblyWords : Array Nat :=
  #[0x00839393, 0x01c3e3b3, 0x010e9e93, 0x018f1f13, 0x01df6e33, 0x00a66533, 0x00e86633,
    0x0112e733, 0x00b7e5b3, 0x00d366b3, 0x007e67b3, 0x02061613, 0x02059593, 0x02079793,
    0x00a66b33, 0x00e5eab3, 0x00d7e9b3]

def rawBlobScheduleFourthAssemblyValid : Bool :=
  rawBlobScheduleFourthAssemblySites.zip rawBlobScheduleFourthAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_fourth_assembly_valid :
    rawBlobScheduleFourthAssemblyValid = true := by
  native_decide

/-- Generated Sail decodes the immutable first endian-assembly fragment without consulting source
or debug metadata. -/
theorem raw_blob_schedule_present_assembly_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00859593 : BitVec 32)) state state
        (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) ∧
      Runs (ext_decode (0x01061613 : BitVec 32)) state state
        (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) ∧
      Runs (ext_decode (0x01869693 : BitVec 32)) state state
        (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) ∧
      Runs (ext_decode (0x00879793 : BitVec 32)) state state
        (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) ∧
      Runs (ext_decode (0x00a5e533 : BitVec 32)) state state
        (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .OR)) ∧
      Runs (ext_decode (0x00c6e633 : BitVec 32)) state state
        (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) ∧
      Runs (ext_decode (0x00e7e733 : BitVec 32)) state state
        (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  decode_run

/-- The present-blob-schedule branch begins by loading byte zero of its checked 24-byte span. -/
theorem raw_blob_schedule_first_lbu_image_bytes :
    Artifacts.programImage.readByte? 0x12cbc = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12cbd = some 0xc5 ∧
        Artifacts.programImage.readByte? 0x12cbe = some 0x0b ∧
          Artifacts.programImage.readByte? 0x12cbf = some 0x00 := by
  native_decide

/-- The first present-blob-schedule read is fetched from the immutable canonical ELF image. -/
theorem raw_blob_schedule_first_lbu_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cbc)
      0x03#8 0xc5#8 0x0b#8 0x00#8 := by
  rcases raw_blob_schedule_first_lbu_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cbc (by omega)
    afterIncrement 0x03 0xc5 0x0b 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the ELF-pinned first byte load of the present schedule payload. -/
theorem raw_blob_schedule_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0xc5#8 0x0b#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 23#5, .Regidx 10#5, true, 1)) := by
  decode_run

private theorem rX_x23_run (state : State) (value : BitVec 64)
    (stored : state.regs.get? x23 = some value) :
    Runs (rX_bits (.Regidx 23#5)) state state value := by
  have index : (Sail.BitVec.toNatInt (23#5)).toNat = 23 := by decide
  unfold Runs
  simp [rX_bits, rX, index, stored, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, regval_from_reg]



/-- The first six present-schedule bytes are assembled little-endian by these four shifts and
three ORs before the decoder continues with bytes 12--23.  These contracts retain the generated
Sail bit-vector expressions so a later live trace can connect them to the actual byte reads. -/
theorem raw_blob_schedule_second_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x11 = some value) :
    Runs (execute_SHIFTIOP 8#6 (.Regidx 11#5) (.Regidx 11#5) .SLLI) state
      { state with regs := (state.regs.insert x11
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 8#6 (.Regidx 11#5) (.Regidx 11#5) value
    (rX_x11_run state value stored)
    (wX_x11_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_third_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x12 = some value) :
    Runs (execute_SHIFTIOP 16#6 (.Regidx 12#5) (.Regidx 12#5) .SLLI) state
      { state with regs := (state.regs.insert x12
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 16#6 (.Regidx 12#5) (.Regidx 12#5) value
    (rX_x12_run state value stored)
    (wX_x12_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 16#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_fourth_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x13 = some value) :
    Runs (execute_SHIFTIOP 24#6 (.Regidx 13#5) (.Regidx 13#5) .SLLI) state
      { state with regs := (state.regs.insert x13
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 24#6 (.Regidx 13#5) (.Regidx 13#5) value
    (rX_x13_run state value stored)
    (wX_x13_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 24#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_sixth_byte_shift_execute (state : State) (value : BitVec 64)
    (stored : state.regs.get? x15 = some value) :
    Runs (execute_SHIFTIOP 8#6 (.Regidx 15#5) (.Regidx 15#5) .SLLI) state
      { state with regs := (state.regs.insert x15
        (Sail.shift_bits_left value
          (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
      (.Retire_Success ()) := by
  exact execute_SHIFTIOP_slli_run state _ 8#6 (.Regidx 15#5) (.Regidx 15#5) value
    (rX_x15_run state value stored)
    (wX_x15_run state (Sail.shift_bits_left value
      (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)))

theorem raw_blob_schedule_first_word_low_or_execute (state : State) (high low : BitVec 64)
    (highStored : state.regs.get? x11 = some high) (lowStored : state.regs.get? x10 = some low) :
    Runs (execute_RTYPE (.Regidx 10#5) (.Regidx 11#5) (.Regidx 10#5) .OR) state
      { state with regs := state.regs.insert x10 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 10#5) (.Regidx 11#5) (.Regidx 10#5) high low
    (rX_x11_run state high highStored) (rX_x10_run state low lowStored)
    (wX_x10_run state (high ||| low))

theorem raw_blob_schedule_first_word_high_or_execute (state : State) (high low : BitVec 64)
    (highStored : state.regs.get? x13 = some high) (lowStored : state.regs.get? x12 = some low) :
    Runs (execute_RTYPE (.Regidx 12#5) (.Regidx 13#5) (.Regidx 12#5) .OR) state
      { state with regs := state.regs.insert x12 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 12#5) (.Regidx 13#5) (.Regidx 12#5) high low
    (rX_x13_run state high highStored) (rX_x12_run state low lowStored)
    (wX_x12_run state (high ||| low))

theorem raw_blob_schedule_second_word_low_or_execute (state : State) (high low : BitVec 64)
    (highStored : state.regs.get? x15 = some high) (lowStored : state.regs.get? x14 = some low) :
    Runs (execute_RTYPE (.Regidx 14#5) (.Regidx 15#5) (.Regidx 14#5) .OR) state
      { state with regs := state.regs.insert x14 (high ||| low) } (.Retire_Success ()) := by
  exact execute_RTYPE_or_run state _ (.Regidx 14#5) (.Regidx 15#5) (.Regidx 14#5) high low
    (rX_x15_run state high highStored) (rX_x14_run state low lowStored)
    (wX_x14_run state (high ||| low))

theorem raw_blob_schedule_second_byte_shift_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cec)
      0x93#8 0x95#8 0x85#8 0x00#8 := by
  have image : Artifacts.programImage.readByte? 0x12cec = some 0x93 ∧
      Artifacts.programImage.readByte? 0x12ced = some 0x95 ∧
        Artifacts.programImage.readByte? 0x12cee = some 0x85 ∧
          Artifacts.programImage.readByte? 0x12cef = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cec (by omega) afterIncrement
    0x93 0x95 0x85 0x00 read0 read1 read2 read3

theorem raw_blob_schedule_second_byte_shift_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x93#8 0x95#8 0x85#8 0x00#8)) state state
      (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) := by
  decode_run

private theorem raw_blob_schedule_lbu_address (state : State)
    (imm base mstatusBits mseccfgBits : BitVec 64)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled) :
    Runs (get_transformed_data_addr (.Regidx 23#5) imm
      (MemoryAccessType.Load mem_payload.Data) 1) state state
      (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + imm))) := by
  exact get_transformed_data_addr_machine_load_run state (.Regidx 23#5) base imm mstatusBits
    mseccfgBits (rX_x23_run state base baseRead) mstatusRead privilegeRead mprvZero mseccfgRead
    pmmDisabled

/-- Shared `lbu`-from-`s7` execution contract for the present blob-schedule branch.  The
destination is left general: each site supplies its own generated `wX_bits` reduction, so this
factors the address transformation and physical byte read out of the individual byte proofs. -/
private theorem raw_blob_schedule_lbu_execute_general (state post : State) (immBits : BitVec 12)
    (imm base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8) (rd : regidx)
    (immAgree : sign_extend (m := 64) immBits = imm)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + imm)) 1 false false false) state state (.Ok data))
    (write : Runs (wX_bits rd (zero_extend (m := 64) data)) state post ()) :
    Runs (execute_LOAD immBits (.Regidx 23#5) rd true 1) state post (.Retire_Success ()) := by
  apply execute_LOAD_run _ _ immBits (.Regidx 23#5) rd true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) immBits)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + imm))) := by
      simpa [immAgree] using raw_blob_schedule_lbu_address state imm base mstatusBits mseccfgBits
        baseRead mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run _ (.Regidx 23#5) (sign_extend (m := 64) immBits) (base + imm)
      mstatusBits data mstatusRead privilegeRead mprvZero address
      (BinaryFv.RiscV.is_aligned_vaddr_one _) (by simpa [immAgree] using hread)
  · exact write

/-- The first schedule-payload byte read executes from `s7` and writes zero-extended `a0`. -/
theorem raw_blob_schedule_first_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr base) 1 false false false) state state (.Ok data)) :
    Runs (execute_LOAD 0#12 (.Regidx 23#5) (.Regidx 10#5) true 1) state
      { state with regs := state.regs.insert x10 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 0#12 (.Regidx 23#5) (.Regidx 10#5) true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 0#12)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr base)) := by
      simpa using raw_blob_schedule_lbu_address state 0#64 base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 0#12) base mstatusBits
      data mstatusRead privilegeRead mprvZero address (BinaryFv.RiscV.is_aligned_vaddr_one _)
      (by simpa using hread)
  · exact wX_x10_run state (zero_extend (m := 64) data)

/-- The second present-schedule byte load is fetched from the immutable canonical ELF image. -/
theorem raw_blob_schedule_second_lbu_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cc0)
      0x83#8 0xc5#8 0x1b#8 0x00#8 := by
  have image : Artifacts.programImage.readByte? 0x12cc0 = some 0x83 ∧
      Artifacts.programImage.readByte? 0x12cc1 = some 0xc5 ∧
        Artifacts.programImage.readByte? 0x12cc2 = some 0x1b ∧
          Artifacts.programImage.readByte? 0x12cc3 = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x12cc0 (by omega)
    afterIncrement 0x83 0xc5 0x1b 0x00 read0 read1 read2 read3

/-- Generated Sail decodes the ELF-pinned second byte load of the present schedule payload. -/
theorem raw_blob_schedule_second_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x83#8 0xc5#8 0x1b#8 0x00#8)) state state
      (.LOAD (1#12, .Regidx 23#5, .Regidx 11#5, true, 1)) := by
  decode_run

/-- The second schedule-payload byte read executes from `s7 + 1` and writes zero-extended `a1`. -/
theorem raw_blob_schedule_second_lbu_execute (state : State)
    (base mstatusBits mseccfgBits : BitVec 64) (data : BitVec 8)
    (baseRead : state.regs.get? x23 = some base)
    (mstatusRead : state.regs.get? mstatus = some mstatusBits)
    (privilegeRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mprvZero : _get_Mstatus_MPRV mstatusBits = 0#1)
    (mseccfgRead : state.regs.get? Register.mseccfg = some mseccfgBits)
    (pmmDisabled : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled)
    (hread : Runs (mem_read (MemoryAccessType.Load mem_payload.Data) page_based_mem_type.PBMT_PMA
      (physaddr.Physaddr (base + 1#64)) 1 false false false) state state (.Ok data)) :
    Runs (execute_LOAD 1#12 (.Regidx 23#5) (.Regidx 11#5) true 1) state
      { state with regs := state.regs.insert x11 (zero_extend (m := 64) data) }
      (.Retire_Success ()) := by
  apply execute_LOAD_run state _ 1#12 (.Regidx 23#5) (.Regidx 11#5) true 1 data (by decide)
  · have address : Runs (get_transformed_data_addr (.Regidx 23#5) (sign_extend (m := 64) 1#12)
        (MemoryAccessType.Load mem_payload.Data) 1) state state
        (.Ext_DataAddr_OK (virtaddr.Virtaddr (base + 1#64))) := by
      simpa using raw_blob_schedule_lbu_address state 1#64 base mstatusBits mseccfgBits baseRead
        mstatusRead privilegeRead mprvZero mseccfgRead pmmDisabled
    exact vmem_read_byte_run state (.Regidx 23#5) (sign_extend (m := 64) 1#12) (base + 1#64)
      mstatusBits data mstatusRead privilegeRead mprvZero address
      (BinaryFv.RiscV.is_aligned_vaddr_one _) (by simpa using hread)
  · exact wX_x11_run state (zero_extend (m := 64) data)

/-- Kernel-checked composition of the first four concrete schedule-byte retirements.  Instantiating
this trace requires the corresponding successive runtime fetch/platform/read premises. -/
theorem raw_blob_schedule_first_four_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (first : Runs (try_step stepNo false) state0 state1 false)
    (second : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (third : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (fourth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [first, second, third, fourth]

/-- The four shifts and three ORs at `0x12cec–0x12d04` are seven contiguous retiring instructions,
so their exact retirements compose without an intervening parser instruction. -/
theorem raw_blob_schedule_assembly_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 : State)
    (shift8 : Runs (try_step stepNo false) state0 state1 false)
    (shift16 : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (shift24 : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (shift8' : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (lowOr : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (highOr : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (secondLowOr : Runs (try_step (stepNo + 6) false) state6 state7 false) :
    Trace stepNo 7 state0 state7 := by
  trace_steps [shift8, shift16, shift24, shift8', lowOr, highOr, secondLowOr]

/-- The second contiguous read group at `0x12d08–0x12d14` covers schedule bytes 12--15. -/
theorem raw_blob_schedule_second_group_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (thirteenth : Runs (try_step stepNo false) state0 state1 false)
    (fourteenth : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (fifteenth : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (sixteenth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [thirteenth, fourteenth, fifteenth, sixteenth]

/-- The remaining eight schedule-byte reads at `0x12ccc–0x12ce8` are contiguous, so their exact
retirements compose directly. -/
theorem raw_blob_schedule_middle_eight_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 state8 : State)
    (fifth : Runs (try_step stepNo false) state0 state1 false)
    (sixth : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (seventh : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (eighth : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (ninth : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (tenth : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (eleventh : Runs (try_step (stepNo + 6) false) state6 state7 false)
    (twelfth : Runs (try_step (stepNo + 7) false) state7 state8 false) :
    Trace stepNo 8 state0 state8 := by
  trace_steps [fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth]

/-- Compose the first four schedule-byte reads, the eight remaining reads of the present branch,
and the seven contiguous assembly instructions.  Every one of the nineteen instructions now has an
exact actual-PC retirement theorem, so each fragment is discharged from immutable ELF bytes and
generated Sail rather than assumed.  What still has to come from the live decoder run is the
dynamic data: each read's physical byte and the successive fetch/platform/counter premises. -/
theorem raw_blob_schedule_present_prefix_trace (stepNo : Nat)
    (state0 state4 state12 state19 : State)
    (firstReads : Trace stepNo 4 state0 state4)
    (remainingReads : Trace (stepNo + 4) 8 state4 state12)
    (assembly : Trace (stepNo + 12) 7 state12 state19) :
    Trace stepNo 19 state0 state19 := by
  have reads : Trace stepNo 12 state0 state12 := by
    simpa only [Nat.add_assoc] using Trace.append firstReads remainingReads
  have combined := Trace.append reads assembly
  simpa only [Nat.reduceAdd] using combined

/-- The second assembly fragment at `0x12d18–0x12d3c` is ten contiguous retiring instructions:
six shifts scaling schedule bytes 6--15, then four ORs folding them into `a6`, `a7`, `t0`, `a1`. -/
theorem raw_blob_schedule_second_assembly_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 state8 state9 state10 : State)
    (a6Shift : Runs (try_step stepNo false) state0 state1 false)
    (a7Shift : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (t1Shift : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (t2Shift : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (t3Shift : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (a3Shift : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (a6Or : Runs (try_step (stepNo + 6) false) state6 state7 false)
    (a7Or : Runs (try_step (stepNo + 7) false) state7 state8 false)
    (t0Or : Runs (try_step (stepNo + 8) false) state8 state9 false)
    (a1Or : Runs (try_step (stepNo + 9) false) state9 state10 false) :
    Trace stepNo 10 state0 state10 := by
  trace_steps [a6Shift, a7Shift, t1Shift, t2Shift, t3Shift, a3Shift, a6Or, a7Or, t0Or, a1Or]

/-- Extend the 19-step prefix through the second read group and the second assembly fragment,
covering every instruction from `0x12cbc` to `0x12d3c` inclusive.  As with the shorter prefix,
each fragment is discharged by exact actual-PC retirements; what remains to come from a live
decoder run is the dynamic data behind those retirements' premises. -/
theorem raw_blob_schedule_present_extended_trace (stepNo : Nat)
    (state0 state19 state23 state33 : State)
    (prefix19 : Trace stepNo 19 state0 state19)
    (secondGroup : Trace (stepNo + 19) 4 state19 state23)
    (secondAssembly : Trace (stepNo + 23) 10 state23 state33) :
    Trace stepNo 33 state0 state33 := by
  have throughReads : Trace stepNo 23 state0 state23 := by
    simpa only [Nat.add_assoc] using Trace.append prefix19 secondGroup
  have combined := Trace.append throughReads secondAssembly
  simpa only [Nat.reduceAdd] using combined

/-- The third contiguous read group at `0x12d40–0x12d4c` covers schedule bytes 16--19. -/
theorem raw_blob_schedule_third_group_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (seventeenth : Runs (try_step stepNo false) state0 state1 false)
    (eighteenth : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (nineteenth : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (twentieth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [seventeenth, eighteenth, nineteenth, twentieth]

/-- The third assembly fragment at `0x12d50–0x12d6c` is eight contiguous retiring instructions. -/
theorem raw_blob_schedule_third_assembly_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 state5 state6 state7 state8 : State)
    (a5Shift : Runs (try_step stepNo false) state0 state1 false)
    (t4Shift : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (t1Shift : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (t2Shift : Runs (try_step (stepNo + 3) false) state3 state4 false)
    (t3Shift : Runs (try_step (stepNo + 4) false) state4 state5 false)
    (a5Or : Runs (try_step (stepNo + 5) false) state5 state6 false)
    (a3Or : Runs (try_step (stepNo + 6) false) state6 state7 false)
    (t1Or : Runs (try_step (stepNo + 7) false) state7 state8 false) :
    Trace stepNo 8 state0 state8 := by
  trace_steps [a5Shift, t4Shift, t1Shift, t2Shift, t3Shift, a5Or, a3Or, t1Or]

/-- The fourth contiguous read group at `0x12d70–0x12d7c` covers the branch's final schedule bytes.
The decoder reads offset 21 before 20, so the group is not offset-ordered. -/
theorem raw_blob_schedule_fourth_group_lbu_trace (stepNo : Nat)
    (state0 state1 state2 state3 state4 : State)
    (twentyFirst : Runs (try_step stepNo false) state0 state1 false)
    (twentySecond : Runs (try_step (stepNo + 1) false) state1 state2 false)
    (twentyThird : Runs (try_step (stepNo + 2) false) state2 state3 false)
    (twentyFourth : Runs (try_step (stepNo + 3) false) state3 state4 false) :
    Trace stepNo 4 state0 state4 := by
  trace_steps [twentyFirst, twentySecond, twentyThird, twentyFourth]

/-- Every instruction from `0x12cbc` through `0x12d7c` -- all twenty-four schedule-byte reads and
the three intervening endian-assembly fragments -- now has an exact actual-PC retirement theorem,
and they compose into one forty-nine step trace.  This fixes the branch's complete instruction
sequence; instantiating it still requires the live decoder run's dynamic data, namely each read's
physical byte together with the successive fetch, platform, and counter premises. -/
theorem raw_blob_schedule_present_branch_trace (stepNo : Nat)
    (state0 state33 state37 state45 state49 : State)
    (through33 : Trace stepNo 33 state0 state33)
    (thirdGroup : Trace (stepNo + 33) 4 state33 state37)
    (thirdAssembly : Trace (stepNo + 37) 8 state37 state45)
    (fourthGroup : Trace (stepNo + 45) 4 state45 state49) :
    Trace stepNo 49 state0 state49 := by
  have a : Trace stepNo 37 state0 state37 := by
    simpa only [Nat.add_assoc] using Trace.append through33 thirdGroup
  have b : Trace stepNo 45 state0 state45 := by
    simpa only [Nat.add_assoc] using Trace.append a thirdAssembly
  have c := Trace.append b fourthGroup
  simpa only [Nat.reduceAdd] using c

/-- The fourth assembly fragment at `0x12d80–0x12dc0` is seventeen contiguous retiring
instructions.  It folds the branch's twenty-four bytes into the three 64-bit schedule words,
leaving them in `s6` (`x22`), `s5` (`x21`), and `s3` (`x19`). -/
theorem raw_blob_schedule_fourth_assembly_trace (stepNo : Nat)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 : State)
    (step0 : Runs (try_step stepNo false) s0 s1 false)
    (step1 : Runs (try_step (stepNo + 1) false) s1 s2 false)
    (step2 : Runs (try_step (stepNo + 2) false) s2 s3 false)
    (step3 : Runs (try_step (stepNo + 3) false) s3 s4 false)
    (step4 : Runs (try_step (stepNo + 4) false) s4 s5 false)
    (step5 : Runs (try_step (stepNo + 5) false) s5 s6 false)
    (step6 : Runs (try_step (stepNo + 6) false) s6 s7 false)
    (step7 : Runs (try_step (stepNo + 7) false) s7 s8 false)
    (step8 : Runs (try_step (stepNo + 8) false) s8 s9 false)
    (step9 : Runs (try_step (stepNo + 9) false) s9 s10 false)
    (step10 : Runs (try_step (stepNo + 10) false) s10 s11 false)
    (step11 : Runs (try_step (stepNo + 11) false) s11 s12 false)
    (step12 : Runs (try_step (stepNo + 12) false) s12 s13 false)
    (step13 : Runs (try_step (stepNo + 13) false) s13 s14 false)
    (step14 : Runs (try_step (stepNo + 14) false) s14 s15 false)
    (step15 : Runs (try_step (stepNo + 15) false) s15 s16 false)
    (step16 : Runs (try_step (stepNo + 16) false) s16 s17 false) :
    Trace stepNo 17 s0 s17 := by
  trace_steps [step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10,
    step11, step12, step13, step14, step15, step16]

/-- The complete present blob-schedule byte assembly: every instruction from `0x12cbc` through
`0x12dc0` composes into one sixty-six step trace.  The branch's twenty-four bytes are read and
folded into its three 64-bit schedule words with no instruction assumed and none skipped.
Instantiation still requires the live decoder run's dynamic data -- each read's physical byte and
the successive fetch, platform, and counter premises -- so this is the branch's exact instruction
sequence, not a claim that it was executed. -/
theorem raw_blob_schedule_present_assembly_complete_trace (stepNo : Nat)
    (state0 state49 state66 : State)
    (through49 : Trace stepNo 49 state0 state49)
    (fourthAssembly : Trace (stepNo + 49) 17 state49 state66) :
    Trace stepNo 66 state0 state66 := by
  simpa only [Nat.reduceAdd] using Trace.append through49 fourthAssembly

end BinaryFv.Zesu.MachineExecution
