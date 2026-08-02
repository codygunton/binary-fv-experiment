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

/-! The first concrete accessor result: the exported error leaf terminates with the pinned `ret`.
The AUIPC/load prefix is kept as a separate pending region because its generated Sail decoder needs
an explicit simplification lemma for the ZICCLSM encoding.
-/

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
