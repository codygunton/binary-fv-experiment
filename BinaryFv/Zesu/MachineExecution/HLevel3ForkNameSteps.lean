import BinaryFv.Zesu.MachineExecution.InstructionClassSteps
import BinaryFv.RiscV.Instruction.Execute.Arithmetic
import BinaryFv.RiscV.Instruction.Execute.RegisterOp
import BinaryFv.RiscV.Elfling.Seg
import BinaryFv.ProofProgress.OwnedPc

/-!
# Exact steps for the Level 3 fork-name dispatcher

The inlined dispatcher starts at `0x1221c`. This module first proves its two `ADDI` steps.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

def forkNameSchemaIndex (schema : Nat) : BitVec 64 :=
  iTypeResult .ADDI (0xfff#12) (BitVec.ofNat 64 schema)

def forkNameTableOffset (index : BitVec 64) : BitVec 64 :=
  shiftIopResult .SLLI (3#6) index

/-- Exact `0x1221c: addi a0,a0,-1`. -/
theorem forkNameSubtractOneStep (stepNo schema : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1221c))
    (schemaAt : state.regs.get? x10 = some (BitVec.ofNat 64 schema))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1221c retired x10 (forkNameSchemaIndex schema)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1221c
  have sourceAtPremise : premise.regs.get? x10 = some (BitVec.ofNat 64 schema) :=
    (stepPremiseState_writes state 0x1221c).get x10 (by decide) |>.trans schemaAt
  have execute : Runs (execute (.ITYPE (0xfff, .Regidx 10#5, .Regidx 10#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x10 (forkNameSchemaIndex schema) }
      (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xfff (.Regidx 10#5) (.Regidx 10#5) .ADDI) _ _ _
    exact execute_ITYPE_run premise _ 0xfff (.Regidx 10#5) (.Regidx 10#5) .ADDI
      (BitVec.ofNat 64 schema) (rX_x10_run premise _ sourceAtPremise)
      (wX_x10_run premise _)
  exact configuredRegisterWriteStep stepNo 0x1221c state x10 (forkNameSchemaIndex schema)
    (.ITYPE (0xfff, .Regidx 10#5, .Regidx 10#5, .ADDI)) 0x13 0x05 0xf5 0xff
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12220: li a2,20`. -/
theorem forkNameLoadLimitStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12220))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12220 retired x12 20) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12220
  have execute : Runs (execute (.ITYPE (20, .Regidx 0#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 20 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 20 (.Regidx 0#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 20 0 = 20#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 20 (.Regidx 0#5)
      (.Regidx 12#5) .ADDI 0 (rX_x0_run premise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12220 state x12 20
    (.ITYPE (20, .Regidx 0#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0x40 0x01
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

private theorem forkNameBltuCondition (state : State) (index limit : BitVec 64)
    (indexAt : state.regs.get? x10 = some index)
    (limitAt : state.regs.get? x12 = some limit) :
    Runs (bTypeTaken (.Regidx 10#5) (.Regidx 12#5) .BLTU) state state
      (zopz0zI_u limit index) := by
  unfold bTypeTaken
  refine Runs.bind (rX_x12_run state limit limitAt) ?_
  refine Runs.bind (rX_x10_run state index indexAt) ?_
  rfl

/-- Exact not-taken `0x12224: bltu a2,a0,0x12638`. -/
theorem forkNameBoundsAcceptedStep (stepNo : Nat) (state : State) (index : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12224))
    (indexAt : state.regs.get? x10 = some index)
    (limitAt : state.regs.get? x12 = some 20)
    (accepted : zopz0zI_u 20 index = false)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12224)
        0x12228 retired) false := by
  apply configuredBranchNotTakenStep stepNo 0x12224 state 0x414 (.Regidx 10#5)
    (.Regidx 12#5) .BLTU 0x63 0x6a 0xa6 0x40 configured atPc loaded
  · configured_decode configured
  · simpa only [accepted] using forkNameBltuCondition
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12224)
      index 20
      ((stepPremiseState_writes state 0x12224).get x10 (by decide) |>.trans indexAt)
      ((stepPremiseState_writes state 0x12224).get x12 (by decide) |>.trans limitAt)
  · native_decide
  · rfl

/-- Exact taken `0x12224: bltu a2,a0,0x12638`. -/
theorem forkNameBoundsRejectedStep (stepNo : Nat) (state : State) (index : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12224))
    (indexAt : state.regs.get? x10 = some index)
    (limitAt : state.regs.get? x12 = some 20)
    (rejected : zopz0zI_u 20 index = true)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x12224 0x12638)
        0x12638 retired) false := by
  apply configuredBranchTakenStep stepNo 0x12224 0x12638 state 0x414 (.Regidx 10#5)
    (.Regidx 12#5) .BLTU 0x63 0x6a 0xa6 0x40 configured atPc loaded
  · configured_decode configured
  · simpa only [rejected] using forkNameBltuCondition
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12224)
      index 20
      ((stepPremiseState_writes state 0x12224).get x10 (by decide) |>.trans indexAt)
      ((stepPremiseState_writes state 0x12224).get x12 (by decide) |>.trans limitAt)
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · rfl

/-- Exact `0x12228: slli a0,a0,3`. -/
theorem forkNameScaleIndexStep (stepNo : Nat) (state : State) (index : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12228))
    (indexAt : state.regs.get? x10 = some index)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12228 retired x10 (forkNameTableOffset index)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12228
  have indexAtPremise : premise.regs.get? x10 = some index :=
    (stepPremiseState_writes state 0x12228).get x10 (by decide) |>.trans indexAt
  have execute : Runs (execute (.SHIFTIOP (3, .Regidx 10#5, .Regidx 10#5, .SLLI))) premise
      { premise with regs := premise.regs.insert x10 (forkNameTableOffset index) }
      (.Retire_Success ()) := by
    change Runs (execute_SHIFTIOP 3 (.Regidx 10#5) (.Regidx 10#5) .SLLI) _ _ _
    exact execute_SHIFTIOP_run premise _ 3 (.Regidx 10#5) (.Regidx 10#5) .SLLI index
      (rX_x10_run premise index indexAtPremise) (wX_x10_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12228 state x10 (forkNameTableOffset index)
    (.SHIFTIOP (3, .Regidx 10#5, .Regidx 10#5, .SLLI)) 0x13 0x15 0x35 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x1222c: auipc a2,5`. -/
theorem forkNameTableBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1222c))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1222c retired x12 0x1722c) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1222c
  have pcAtPremise : premise.regs.get? PC = some (0x1222c : BitVec 64) := by
    calc
      premise.regs.get? PC = (tryStepControlFlowAfterIncrement state).regs.get? PC := by
        simpa [premise, coreControlFlowNextState] using
          writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
            (Sail.BitVec.addInt 0x1222c 4) (by decide)
      _ = state.regs.get? PC := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment PC true (by decide)
      _ = some 0x1222c := atPc
  have execute : Runs (execute (.UTYPE (5, .Regidx 12#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x12 0x1722c } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 5 (.Regidx 12#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 5 (.Regidx 12#5) 0x1222c
      (readReg_run premise PC _ pcAtPremise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x1222c state x12 0x1722c
    (.UTYPE (5, .Regidx 12#5, .AUIPC)) 0x17 0x56 0x00 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12230: addi a2,a2,-4`. -/
theorem forkNameTableBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12230))
    (baseAt : state.regs.get? x12 = some 0x1722c)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12230 retired x12 0x17228) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12230
  have baseAtPremise : premise.regs.get? x12 = some 0x1722c :=
    (stepPremiseState_writes state 0x12230).get x12 (by decide) |>.trans baseAt
  have execute : Runs (execute (.ITYPE (0xffc, .Regidx 12#5, .Regidx 12#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x12 0x17228 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0xffc (.Regidx 12#5) (.Regidx 12#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0xffc 0x1722c = 0x17228#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 0xffc (.Regidx 12#5)
      (.Regidx 12#5) .ADDI 0x1722c (rX_x12_run premise _ baseAtPremise)
      (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12230 state x12 0x17228
    (.ITYPE (0xffc, .Regidx 12#5, .Regidx 12#5, .ADDI)) 0x13 0x06 0xc6 0xff
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12234: add a0,a2,a0`. -/
theorem forkNameTableAddressStep (stepNo : Nat) (state : State) (offset : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12234))
    (offsetAt : state.regs.get? x10 = some offset)
    (baseAt : state.regs.get? x12 = some 0x17228)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12234 retired x10 (0x17228 + offset)) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12234
  have offsetAtPremise : premise.regs.get? x10 = some offset :=
    (stepPremiseState_writes state 0x12234).get x10 (by decide) |>.trans offsetAt
  have baseAtPremise : premise.regs.get? x12 = some 0x17228 :=
    (stepPremiseState_writes state 0x12234).get x12 (by decide) |>.trans baseAt
  have execute : Runs (execute (.RTYPE (.Regidx 10#5, .Regidx 12#5, .Regidx 10#5, .ADD))) premise
      { premise with regs := premise.regs.insert x10 (0x17228 + offset) }
      (.Retire_Success ()) := by
    change Runs (execute_RTYPE (.Regidx 10#5) (.Regidx 12#5) (.Regidx 10#5) .ADD) _ _ _
    exact execute_RTYPE_run premise _ (.Regidx 10#5) (.Regidx 12#5) (.Regidx 10#5)
      .ADD 0x17228 offset (rX_x12_run premise _ baseAtPremise)
      (rX_x10_run premise _ offsetAtPremise) (wX_x10_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12234 state x10 (0x17228 + offset)
    (.RTYPE (.Regidx 10#5, .Regidx 12#5, .Regidx 10#5, .ADD)) 0x33 0x05 0xa6 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12238: ld a0,0(a0)`. -/
theorem forkNameLoadTargetStep (stepNo address target : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12238))
    (addressAt : state.regs.get? x10 = some (BitVec.ofNat 64 address))
    (rep : UIntRep 8 state.mem address target)
    (pma : LoadPmaAllows state (BitVec.ofNat 64 address) 8)
    (notMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 address) 8)
    (fits : address < 2 ^ 64)
    (aligned : address % 8 = 0)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12238 retired x10 (BitVec.ofNat 64 target)) false := by
  apply configuredDwordLoadStep stepNo 0x12238 state 0 (.Regidx 10#5) (.Regidx 10#5)
    x10 address 0 target (BitVec.ofNat 64 target) 0x03 0x35 0x05 0x00
    configured atPc rep pma notMMIO fits aligned loaded
    (addressEq := by
      change BitVec.ofNat 64 address + sign_extend (m := 64) (0#12) =
        BitVec.ofNat 64 (address + 0)
      rw [show sign_extend (m := 64) (0#12) = 0#64 by native_decide]
      simp)
    (baseRun := by
      intro premise writes
      exact rX_x10_run premise _ ((writes x10 (by decide)).trans addressAt))
    (writeRun := by intro premise; exact wX_x10_run premise _)
    (decode := by configured_decode configured) (base := by rfl)

/-- Exact `0x1223c: li t4,8`. -/
theorem forkNameLoadElementSizeStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1223c))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x1223c retired x29 8) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x1223c
  have execute : Runs (execute (.ITYPE (8, .Regidx 0#5, .Regidx 29#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x29 8 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 8 (.Regidx 0#5) (.Regidx 29#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 8 0 = 8#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 8 (.Regidx 0#5)
      (.Regidx 29#5) .ADDI 0 (rX_x0_run premise) (wX_x29_run premise _)
  exact configuredRegisterWriteStep stepNo 0x1223c state x29 8
    (.ITYPE (8, .Regidx 0#5, .Regidx 29#5, .ADDI)) 0x93 0x0e 0x80 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12240: auipc a2,5`. -/
theorem forkNameNamesBaseHighStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12240))
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12240 retired x12 0x17240) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12240
  have pcAtPremise : premise.regs.get? PC = some (0x12240 : BitVec 64) := by
    calc
      premise.regs.get? PC = (tryStepControlFlowAfterIncrement state).regs.get? PC := by
        simpa [premise, coreControlFlowNextState] using
          writeReg_read_unchanged (tryStepControlFlowAfterIncrement state) nextPC PC
            (Sail.BitVec.addInt 0x12240 4) (by decide)
      _ = state.regs.get? PC := by
        simpa [tryStepControlFlowAfterIncrement] using
          writeReg_read_unchanged state minstret_increment PC true (by decide)
      _ = some 0x12240 := atPc
  have execute : Runs (execute (.UTYPE (5, .Regidx 12#5, .AUIPC))) premise
      { premise with regs := premise.regs.insert x12 0x17240 } (.Retire_Success ()) := by
    change Runs (execute_UTYPE 5 (.Regidx 12#5) .AUIPC) _ _ _
    simpa using execute_UTYPE_auipc_run premise _ 5 (.Regidx 12#5) 0x12240
      (readReg_run premise PC _ pcAtPremise) (wX_x12_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12240 state x12 0x17240
    (.UTYPE (5, .Regidx 12#5, .AUIPC)) 0x17 0x56 0x00 0x00
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12244: addi t5,a2,0x6c6`. -/
theorem forkNameNamesBaseLowStep (stepNo : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12244))
    (baseAt : state.regs.get? x12 = some 0x17240)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (afterRegisterWrite state 0x12244 retired x30 0x17906) false := by
  let premise := coreControlFlowNextState (tryStepControlFlowAfterIncrement state) 0x12244
  have baseAtPremise : premise.regs.get? x12 = some 0x17240 :=
    (stepPremiseState_writes state 0x12244).get x12 (by decide) |>.trans baseAt
  have execute : Runs (execute (.ITYPE (0x6c6, .Regidx 12#5, .Regidx 30#5, .ADDI))) premise
      { premise with regs := premise.regs.insert x30 0x17906 } (.Retire_Success ()) := by
    change Runs (execute_ITYPE 0x6c6 (.Regidx 12#5) (.Regidx 30#5) .ADDI) _ _ _
    have resultEq : iTypeResult .ADDI 0x6c6 0x17240 = 0x17906#64 := by native_decide
    simpa only [resultEq] using execute_ITYPE_run premise _ 0x6c6 (.Regidx 12#5)
      (.Regidx 30#5) .ADDI 0x17240 (rX_x12_run premise _ baseAtPremise)
      (wX_x30_run premise _)
  exact configuredRegisterWriteStep stepNo 0x12244 state x30 0x17906
    (.ITYPE (0x6c6, .Regidx 12#5, .Regidx 30#5, .ADDI)) 0x13 0x0f 0x66 0x6c
    configured atPc loaded (by configured_decode configured) execute
    (pcFits := by native_decide) (base := by rfl)

/-- Exact `0x12248: jr a0`. -/
theorem forkNameJumpTargetStep (stepNo : Nat) (state : State) (target : BitVec 64)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x12248))
    (targetAt : state.regs.get? x10 = some target)
    (targetAligned : Sail.BitVec.access target 1 = 0#1)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ retired, Runs (try_step stepNo false) state
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement state) 0x12248
          (Sail.BitVec.update target 0 0#1))
        (Sail.BitVec.update target 0 0#1) retired) false := by
  apply configuredJrStep stepNo 0x12248 state (.Regidx 10#5) target
    0x67 0x00 0x05 0x00 configured atPc loaded
  · configured_decode configured
  · exact rX_x10_run _ target
      ((stepPremiseState_writes state 0x12248).get x10 (by decide) |>.trans targetAt)
  · exact targetAligned
  · native_decide
  · rfl

def forkNameOwnPc (pc : BitVec 64) : Prop :=
  pcInList [0x1221c, 0x12220, 0x12224, 0x12228, 0x1222c, 0x12230,
    0x12234, 0x12238, 0x1223c, 0x12240, 0x12244, 0x12248] pc

def forkNameWrites (register : Register) : Prop :=
  stepBookkeeping register ∨ register = x10 ∨ register = x12 ∨
    register = x29 ∨ register = x30

private theorem forkNameInstructionDisjoint (register : Register)
    (preserved : instructionPreserved register) : ¬forkNameWrites register := by
  intro writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 writes
  all_goals simp_all [instructionPreserved, platformPreserved]

private theorem forkNamePlatformDisjoint (register : Register)
    (preserved : platformPreserved register) : ¬forkNameWrites register := by
  intro writes
  rcases writes with writes | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved writes
  all_goals simp_all [platformPreserved]

/-- Exact accepted fork-name dispatch from `0x1221c` to one linked jump-table target. -/
theorem forkNameAcceptedRun (fromStep schema tableAddress target : Nat) (state : State)
    (configured : ConfiguredMachinePre EndpointMachinePc state)
    (atPc : state.regs.get? PC = some (BitVec.ofNat 64 0x1221c))
    (schemaAt : state.regs.get? x10 = some (BitVec.ofNat 64 schema))
    (accepted : zopz0zI_u 20 (forkNameSchemaIndex schema) = false)
    (tableAddressEq : BitVec.ofNat 64 tableAddress =
      0x17228 + forkNameTableOffset (forkNameSchemaIndex schema))
    (targetRep : UIntRep 8 state.mem tableAddress target)
    (targetPma : LoadPmaAllows state (BitVec.ofNat 64 tableAddress) 8)
    (targetNotMMIO : LoadMMIOAddressExcluded (BitVec.ofNat 64 tableAddress) 8)
    (tableAddressFits : tableAddress < 2 ^ 64)
    (tableAddressAligned : tableAddress % 8 = 0)
    (targetAligned : Sail.BitVec.access (BitVec.ofNat 64 target) 1 = 0#1)
    (targetUpdate : Sail.BitVec.update (BitVec.ofNat 64 target) 0 0#1 =
      BitVec.ofNat 64 target)
    (loaded : Artifacts.programImage.fileBytesLoadedFaithfully state.mem) :
    ∃ after, Seg forkNameOwnPc (fun _ => False)
      (fun _ _ _ _ _ => False) forkNameWrites noMemory [] fromStep 12 state after
      (BitVec.ofNat 64 target) := by
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil forkNameOwnPc (fun _ => False)
    (fun _ _ _ _ _ => False) forkNameWrites noMemory fromStep ⟨retired, retiredRead⟩ atPc
  have configuredOfSeg {kv n cur pc}
      (seg : Seg forkNameOwnPc (fun _ => False)
        (fun _ _ _ _ _ => False) forkNameWrites noMemory kv fromStep n state cur pc) :
      ConfiguredMachinePre EndpointMachinePc cur :=
    configured.mono (seg.agree forkNameInstructionDisjoint) seg.retired
  have loadedOfSeg {kv n cur pc}
      (seg : Seg forkNameOwnPc (fun _ => False)
        (fun _ _ _ _ _ => False) forkNameWrites noMemory kv fromStep n state cur pc) :
      Artifacts.programImage.fileBytesLoadedFaithfully cur.mem := by
    rw [seg.memEq noMemory_empty]
    exact loaded
  obtain ⟨s1, seg1⟩ := seg0.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x10 (forkNameSchemaIndex schema) 0x12220
    (forkNameSubtractOneStep fromStep schema state configured atPc schemaAt loaded)
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s2, seg2⟩ := seg1.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x12 20 0x12224
    (forkNameLoadLimitStep (fromStep + 1) s1 (configuredOfSeg seg1) seg1.atPc
      (loadedOfSeg seg1))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s3, seg3⟩ := seg2.stepFallThrough 0x12228
    (by owned_pc [forkNameOwnPc, pcInList]) (by simp)
    (forkNameBoundsAcceptedStep (fromStep + 2) s2 (forkNameSchemaIndex schema)
      (configuredOfSeg seg2) seg2.atPc
      (seg2.reg x10 _ (by simp)) (seg2.reg x12 _ (by simp)) accepted (loadedOfSeg seg2))
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  have seg3' := seg3.forget (kv' := []) (by simp)
  obtain ⟨s4, seg4⟩ := seg3'.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x10 (forkNameTableOffset (forkNameSchemaIndex schema)) 0x1222c
    (forkNameScaleIndexStep (fromStep + 3) s3 (forkNameSchemaIndex schema)
      (configuredOfSeg seg3') seg3'.atPc
      ((seg3.reg x10 _ (by simp)).trans rfl) (loadedOfSeg seg3'))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s5, seg5⟩ := seg4.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x12 0x1722c 0x12230
    (forkNameTableBaseHighStep (fromStep + 4) s4 (configuredOfSeg seg4) seg4.atPc
      (loadedOfSeg seg4))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have seg5' := seg5.forget (kv' := [⟨x10,
      forkNameTableOffset (forkNameSchemaIndex schema)⟩]) (by simp)
  obtain ⟨s6, seg6⟩ := seg5'.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x12 0x17228 0x12234
    (forkNameTableBaseLowStep (fromStep + 5) s5 (configuredOfSeg seg5') seg5'.atPc
      (seg5.reg x12 _ (by simp)) (loadedOfSeg seg5'))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have seg6' := seg6.forget (kv' := [⟨x12, 0x17228⟩]) (by simp)
  obtain ⟨s7, seg7⟩ := seg6'.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x10 (0x17228 + forkNameTableOffset (forkNameSchemaIndex schema)) 0x12238
    (forkNameTableAddressStep (fromStep + 6) s6
      (forkNameTableOffset (forkNameSchemaIndex schema)) (configuredOfSeg seg6') seg6'.atPc
      (seg6.reg x10 _ (by simp)) (seg6.reg x12 _ (by simp)) (loadedOfSeg seg6'))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have targetRep7 : UIntRep 8 s7.mem tableAddress target := by
    rw [seg7.memEq noMemory_empty]
    exact targetRep
  have targetPma7 : LoadPmaAllows s7 (BitVec.ofNat 64 tableAddress) 8 :=
    loadPmaAllows_of_agree (seg7.agree forkNamePlatformDisjoint) targetPma
  have seg7' := seg7.forget (kv' := [⟨x12, 0x17228⟩]) (by simp)
  obtain ⟨s8, seg8⟩ := seg7'.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x10 (BitVec.ofNat 64 target) 0x1223c
    (forkNameLoadTargetStep (fromStep + 7) tableAddress target s7
      (configuredOfSeg seg7') seg7'.atPc
      (by simpa [tableAddressEq] using seg7.reg x10 _ (by simp)) targetRep7 targetPma7
      targetNotMMIO tableAddressFits tableAddressAligned (loadedOfSeg seg7'))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s9, seg9⟩ := seg8.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x29 8 0x12240
    (forkNameLoadElementSizeStep (fromStep + 8) s8 (configuredOfSeg seg8) seg8.atPc
      (loadedOfSeg seg8))
    (by native_decide) (by intro r h; exact Or.inl h)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have seg9' := seg9.forget
    (kv' := [⟨x29, 8⟩, ⟨x10, BitVec.ofNat 64 target⟩]) (by simp)
  obtain ⟨s10, seg10⟩ := seg9'.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x12 0x17240 0x12244
    (forkNameNamesBaseHighStep (fromStep + 9) s9 (configuredOfSeg seg9') seg9'.atPc
      (loadedOfSeg seg9'))
    (by native_decide) (by intro r h; exact Or.inl h) (Or.inr (Or.inr (Or.inl rfl)))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  obtain ⟨s11, seg11⟩ := seg10.step (by owned_pc [forkNameOwnPc, pcInList])
    (by simp) x30 0x17906 0x12248
    (forkNameNamesBaseLowStep (fromStep + 10) s10 (configuredOfSeg seg10) seg10.atPc
      (seg10.reg x12 _ (by simp)) (loadedOfSeg seg10))
    (by native_decide) (by intro r h; exact Or.inl h)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) (by decide) (by simp [RegsOutside, stepBookkeeping])
  have jumpRun := forkNameJumpTargetStep (fromStep + 11) s11
    (BitVec.ofNat 64 target) (configuredOfSeg seg11) seg11.atPc
    (seg11.reg x10 _ (by simp)) targetAligned (loadedOfSeg seg11)
  obtain ⟨s12, seg12⟩ := seg11.stepJump (BitVec.ofNat 64 target)
    (by owned_pc [forkNameOwnPc, pcInList]) (by simp)
    (by simpa only [targetUpdate, Nat.zero_add, Nat.add_assoc] using jumpRun)
    (by intro r h; exact Or.inl h) (by simp [RegsOutside, stepBookkeeping])
  exact ⟨s12, seg12.forget (kv' := []) (by simp)⟩

end BinaryFv.Zesu.MachineExecution
