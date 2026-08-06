import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_5
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_6
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_7
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_8
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_9
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_10
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_11
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_12
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_13
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_14
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_15
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_16
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_17

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

theorem raw_blob_schedule_sixth_byte_shift_retire_exact (stepNo : Nat) (state : State)
    (value retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (stored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x12cf8)).regs.get? x15 = some value)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ()))
    (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config)
    (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1)
    (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8)
          with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x12cf8)).regs.insert x15 (Sail.shift_bits_left value
              (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0))) }
        (BitVec.ofNat 64 0x12cfc) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cf8 = some 0x93 ∧ Artifacts.programImage.readByte? 0x12cf9 = some 0x97 ∧ Artifacts.programImage.readByte? 0x12cfa = some 0x87 ∧ Artifacts.programImage.readByte? 0x12cfb = some 0x00 := by native_decide
  rcases image with ⟨read0, read1, read2, read3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage (tryStepControlFlowAfterIncrement state) 0x12cf8 (by omega) afterIncrement 0x93 0x97 0x87 0x00 read0 read1 read2 read3
  have decode : Runs (ext_decode (fetchWord 0x93#8 0x97#8 0x87#8 0x00#8)) (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cf8) retired inhibit config 0x93#8 0x97#8 0x87#8 0x00 (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) x15 (Sail.shift_bits_left value (Sail.BitVec.extractLsb 8#6 (LeanRV64DExecutable.Functions.log2_xlen -i 1) 0)) platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected (raw_blob_schedule_sixth_byte_shift_execute (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cf8)) value stored) (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

theorem raw_blob_schedule_first_word_low_or_retire_exact (stepNo : Nat) (state : State)
    (high low retired : BitVec 64) (inhibit : BitVec 32) (config mseccfgBits : BitVec 64)
    (loaded : Artifacts.programImage.matchesMemory state.mem)
    (platform : FetchBasePlatform (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc))
    (fetchNoMMIO : FetchMemoryNoMMIO (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc))
    (interrupts : InterruptDisabled (tryStepControlFlowAfterIncrement state))
    (notExpected : LandingPadNotExpected (tryStepControlFlowAfterIncrement state))
    (privilege : (tryStepControlFlowAfterIncrement state).regs.get? cur_privilege = some Privilege.Machine)
    (mseccfg : (tryStepControlFlowAfterIncrement state).regs.get? Register.mseccfg = some mseccfgBits)
    (highStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)).regs.get? x11 = some high)
    (lowStored : (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)).regs.get? x10 = some low)
    (hartRead : state.regs.get? hart_state = some (.HART_ACTIVE ())) (inhibitRead : state.regs.get? mcountinhibit = some inhibit)
    (configRead : state.regs.get? minstretcfg = some config) (notInhibited : _get_Counterin_IR inhibit = 0#1)
    (machineEnabled : _get_CountSmcntrpmf_MINH config = 0#1) (retiredRead : state.regs.get? minstret = some retired) :
    Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)
        with regs := ((coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)).regs.insert x10 (high ||| low)) }
        (BitVec.ofNat 64 0x12d00) retired) false := by
  have image : Artifacts.programImage.readByte? 0x12cfc = some 0x33 ∧ Artifacts.programImage.readByte? 0x12cfd = some 0xe5 ∧ Artifacts.programImage.readByte? 0x12cfe = some 0xa5 ∧ Artifacts.programImage.readByte? 0x12cff = some 0x00 := by native_decide
  rcases image with ⟨r0,r1,r2,r3⟩
  have afterIncrement : Artifacts.programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem := by simpa [tryStepControlFlowAfterIncrement] using loaded
  have bytes := fetchBytesAt_of_image_bytes Artifacts.programImage (tryStepControlFlowAfterIncrement state) 0x12cfc (by omega) afterIncrement 0x33 0xe5 0xa5 0x00 r0 r1 r2 r3
  have decode : Runs (ext_decode (fetchWord 0x33#8 0xe5#8 0xa5#8 0x00#8)) (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .OR)) := by decode_run
  simpa only using tryStepFallThroughWriteRegRetires stepNo state (BitVec.ofNat 64 0x12cfc) retired inhibit config 0x33#8 0xe5#8 0xa5#8 0x00 (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .OR)) x10 (high ||| low) platform fetchNoMMIO bytes interrupts (by rfl) decode notExpected (raw_blob_schedule_first_word_low_or_execute (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x12cfc)) high low highStored lowStored) (by decide) (by decide) (by decide) (by decide) hartRead inhibitRead configRead notInhibited machineEnabled retiredRead

end BinaryFv.Zesu.MachineExecution
