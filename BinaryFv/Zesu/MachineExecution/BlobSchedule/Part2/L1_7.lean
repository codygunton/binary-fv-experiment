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

end BinaryFv.Zesu.MachineExecution
