import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.Artifacts.PrimitiveReadInventory
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

theorem raw_error_auipc_execute (state sFinal : State) (pcVal : BitVec 64)
    (hpc : Runs (readReg PC) state state pcVal)
    (hwrite : Runs (wX_bits (.Regidx 10#5)
      (pcVal + sign_extend (m := 64) (0x4202#20 ++ 0x000#12))) state sFinal ()) :
    Runs (execute_UTYPE 0x4202#20 (.Regidx 10#5) .AUIPC) state sFinal
      (.Retire_Success ()) := by
  exact execute_UTYPE_auipc_run state sFinal 0x4202#20 (.Regidx 10#5) pcVal hpc hwrite

theorem raw_error_load_execute (state sFinal : State) (data : BitVec 32)
    (hread : Runs (vmem_read (.Regidx 10#5) (sign_extend (m := 64) 0x8a4#12) 4
      (MemoryAccessType.Load mem_payload.Data) false false false) state state (.Ok data))
    (hwrite : Runs (wX_bits (.Regidx 10#5) (extend_value false data)) state sFinal ()) :
    Runs (execute_LOAD 0x8a4#12 (.Regidx 10#5) (.Regidx 10#5) false 4) state sFinal
      (.Retire_Success ()) := by
  exact execute_LOAD_lw_run state sFinal 0x8a4#12 (.Regidx 10#5) (.Regidx 10#5) data hread hwrite

theorem raw_error_prefix_runs (state afterAuipc afterLoad : State) (pcVal : BitVec 64)
    (data : BitVec 32)
    (hpc : Runs (readReg PC) state state pcVal)
    (hAuipc : Runs (wX_bits (.Regidx 10#5)
      (pcVal + sign_extend (m := 64) (0x4202#20 ++ 0x000#12))) state afterAuipc ())
    (hread : Runs (vmem_read (.Regidx 10#5) (sign_extend (m := 64) 0x8a4#12) 4
      (MemoryAccessType.Load mem_payload.Data) false false false)
      afterAuipc afterAuipc (.Ok data))
    (hLoad : Runs (wX_bits (.Regidx 10#5) (extend_value false data)) afterAuipc afterLoad ()) :
    Runs (execute_UTYPE 0x4202#20 (.Regidx 10#5) .AUIPC >>= fun _ =>
      execute_LOAD 0x8a4#12 (.Regidx 10#5) (.Regidx 10#5) false 4)
      state afterLoad (.Retire_Success ()) := by
  apply Runs.bind (raw_error_auipc_execute state afterAuipc pcVal hpc hAuipc)
  exact raw_error_load_execute afterAuipc afterLoad data hread hLoad

theorem raw_error_ret_execute (state sFinal : State) (linkVal rs1Val : BitVec 64)
    (helpElp : Runs (update_elp_state (.Regidx 1#5)) state state ())
    (hlink : Runs (get_next_pc ()) state state linkVal)
    (hrs1 : Runs (rX_bits (.Regidx 1#5)) state state rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) 0#12) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) state state zcaEnabled)
    (hwrite : Runs (wX_bits (.Regidx 0#5) linkVal)
      { state with regs := (state.regs.insert nextPC
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) 0#12) 0 0#1)) } sFinal ()) :
    Runs (execute_JALR 0#12 (.Regidx 1#5) (.Regidx 0#5)) state sFinal
      (.Retire_Success ()) := by
  exact execute_JALR_run state sFinal 0#12 (.Regidx 1#5) (.Regidx 0#5)
    linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca hwrite

theorem raw_error_body_runs (state afterAuipc afterLoad final : State) (pcVal : BitVec 64)
    (data : BitVec 32) (linkVal rs1Val : BitVec 64)
    (hpc : Runs (readReg PC) state state pcVal)
    (hAuipc : Runs (wX_bits (.Regidx 10#5)
      (pcVal + sign_extend (m := 64) (0x4202#20 ++ 0x000#12))) state afterAuipc ())
    (hread : Runs (vmem_read (.Regidx 10#5) (sign_extend (m := 64) 0x8a4#12) 4
      (MemoryAccessType.Load mem_payload.Data) false false false)
      afterAuipc afterAuipc (.Ok data))
    (hLoad : Runs (wX_bits (.Regidx 10#5) (extend_value false data)) afterAuipc afterLoad ())
    (helpElp : Runs (update_elp_state (.Regidx 1#5)) afterLoad afterLoad ())
    (hlink : Runs (get_next_pc ()) afterLoad afterLoad linkVal)
    (hrs1 : Runs (rX_bits (.Regidx 1#5)) afterLoad afterLoad rs1Val)
    (hbit1 : Sail.BitVec.access (rs1Val + sign_extend (m := 64) 0#12) 1 = 0#1)
    (zcaEnabled : Bool)
    (hzca : Runs (currentlyEnabled extension.Ext_Zca) afterLoad afterLoad zcaEnabled)
    (hwrite : Runs (wX_bits (.Regidx 0#5) linkVal)
      { afterLoad with regs := (afterLoad.regs.insert nextPC
          (Sail.BitVec.update (rs1Val + sign_extend (m := 64) 0#12) 0 0#1)) } final ()) :
    Runs (execute_UTYPE 0x4202#20 (.Regidx 10#5) .AUIPC >>= fun _ =>
      execute_LOAD 0x8a4#12 (.Regidx 10#5) (.Regidx 10#5) false 4 >>= fun _ =>
      execute_JALR 0#12 (.Regidx 1#5) (.Regidx 0#5))
      state final (.Retire_Success ()) := by
  exact Runs.bind (raw_error_auipc_execute state afterAuipc pcVal hpc hAuipc)
    (Runs.bind (raw_error_load_execute afterAuipc afterLoad data hread hLoad)
      (raw_error_ret_execute afterLoad final linkVal rs1Val helpElp hlink hrs1 hbit1 zcaEnabled hzca
        hwrite))

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
