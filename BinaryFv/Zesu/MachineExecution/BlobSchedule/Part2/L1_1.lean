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

/-- The present-blob-schedule branch begins by loading byte zero of its checked 24-byte span. -/
theorem raw_blob_schedule_first_lbu_image_bytes :
    Artifacts.programImage.readByte? 0x12cbc = some 0x03 ∧
      Artifacts.programImage.readByte? 0x12cbd = some 0xc5 ∧
        Artifacts.programImage.readByte? 0x12cbe = some 0x0b ∧
          Artifacts.programImage.readByte? 0x12cbf = some 0x00 := by
  native_decide

/-- Generated Sail decodes the ELF-pinned first byte load of the present schedule payload. -/
theorem raw_blob_schedule_first_lbu_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (fetchWord 0x03#8 0xc5#8 0x0b#8 0x00#8)) state state
      (.LOAD (0#12, .Regidx 23#5, .Regidx 10#5, true, 1)) := by
  decode_run

end BinaryFv.Zesu.MachineExecution
