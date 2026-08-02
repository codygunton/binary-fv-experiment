import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.Artifacts.PrimitiveReadInventory
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

theorem raw_error_auipc_image_bytes :
    Artifacts.programImage.readByte? 0x13780 = some 0x17 ∧
      Artifacts.programImage.readByte? 0x13781 = some 0x25 ∧
        Artifacts.programImage.readByte? 0x13782 = some 0x20 ∧
          Artifacts.programImage.readByte? 0x13783 = some 0x04 := by
  native_decide

theorem raw_error_auipc_fetch (state : State)
    (loaded : Artifacts.programImage.matchesMemory state.mem) :
    FetchBytesAt (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x13780)
      0x17#8 0x25#8 0x20#8 0x04#8 := by
  rcases raw_error_auipc_image_bytes with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory
      (tryStepControlFlowAfterIncrement state).mem := by
    simpa [tryStepControlFlowAfterIncrement] using loaded
  exact fetchBytesAt_of_image_bytes Artifacts.programImage
    (tryStepControlFlowAfterIncrement state) 0x13780 (by omega)
    afterIncrement 0x17 0x25 0x20 0x04 read0 read1 read2 read3

theorem raw_error_auipc_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x17#8 0x25#8 0x20#8 0x04#8)) state state
      (.UTYPE (0x4202#20, .Regidx 10#5, .AUIPC)) := by
  unfold Runs
  rw [extDecode_eq]
  simp [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, getThe,
    MonadState.get, MonadStateOf.get, fetchWord, encdec_reg_backwards,
    encdec_uop_backwards, encdec_reg_backwards_matches, encdec_uop_backwards_matches,
    LeanRV64DExecutable.Functions.base_E_enabled, LeanRV64DExecutable.Functions.not,
    Sail.BitVec.access, Sail.BitVec.extractLsb,
    LeanRV64DExecutable.Functions.regidx_bit_width, privilege, mseccfg]

theorem raw_error_ret_image_bytes :
    Artifacts.programImage.readByte? 0x13788 = some 0x67 ∧
      Artifacts.programImage.readByte? 0x13789 = some 0x80 ∧
        Artifacts.programImage.readByte? 0x1378a = some 0x00 ∧
          Artifacts.programImage.readByte? 0x1378b = some 0x00 := by
  native_decide

theorem raw_error_ret_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x67#8 0x80#8 0x00#8 0x00#8)) state state
      (.JALR (0#12, .Regidx 1#5, .Regidx 0#5)) := by
  decode_run

end BinaryFv.Zesu.MachineExecution
