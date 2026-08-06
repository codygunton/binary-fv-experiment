import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts
import BinaryFv.Zesu.MachineExecution.HasExactErePrefixProof
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterWriteStep
import BinaryFv.Zesu.MachineExecution.RegisterRuns
import BinaryFv.Zesu.MachineExecution.Level2SavedFrame
import BinaryFv.RiscV.Step.TryStepStackAddi
import BinaryFv.RiscV.Step.TryStepStackAddiMemory
import BinaryFv.Zesu.MachineExecution.OwnedPc
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L1_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L1_2
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L2_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L2_2
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L3_1
import BinaryFv.Zesu.MachineExecution.Level2Epilogue.L4_1

/-!
# Shared `zesu_decode_raw` epilogue

The wrapper paths meet at `0x1035c`.  This module proves that common instruction sequence; callers
supply the value already selected for `a0`, the normalized status in `a1`, and the ordinary
machine frame carried from their own path.  No source-function ABI is assigned to an inline child.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register
open RegisterWriteStep

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! ## The shared opening phase of both epilogue compositions

`wrapper_epilogue_to_exit` and `wrapper_epilogue_complete` both begin with the same 34 lines: the
first stack restore, the `ra` reload, and the eight facts about the resulting state. That block was
character-identical in the two proofs, so every one of these `simp` calls -- including the
`cases register <;> simp_all` agreement proof and the two twelve-lemma register reads -- ran twice.

Proved once here against explicit state expressions. Callers keep their `let`-bound names; `let` is
definitionally transparent, so the lemmas apply directly. -/

variable {base state : State}

/-! ## Write-set frames for the two stack restores

Both `addi sp, sp, imm` steps write only the bookkeeping registers and `x2`, so agreement across them
is a frame fact -- no need to case-split forty registers against a deep state term. Proving
`stackAgree` that way cost **11.4s of `wrapper_epilogue_to_exit`'s 13.3s**, 8.5s of it in the closing
`simp_all`; through the frame it is free. -/

/-- `decoderPreserved` is `platformPreserved` plus `x1`, so it inherits its disjointness. -/
theorem decoderPreserved_disjoint : RegSet.Disjoint decoderPreserved stepBookkeeping :=
  fun r hr => platformPreserved_disjoint r hr.2

/-- `decoderPreserved` is disjoint from a stack-restore write set. -/
theorem decoderPreserved_disjoint_sp :
    RegSet.Disjoint decoderPreserved (RegSet.union stepBookkeeping (RegSet.only x2)) :=
  decoderPreserved_disjoint.union
    (RegSet.Disjoint.only (by simp [decoderPreserved, platformPreserved]))

/-- The first stack restoration writes only the bookkeeping registers and `x2`. -/
theorem wrapperAfterFirstStackRestore_writes (state : State) (retired stack : BitVec 64) :
    WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x2)) state
      (wrapperAfterFirstStackRestore state retired stack) :=
  afterRegisterWrite_writes state (BitVec.ofNat 64 0x10360) retired x2
    (stack + sign_extend (m := 64) 0x230#12)

/-- The final stack restoration writes only the bookkeeping registers and `x2`. -/
theorem wrapperAfterFinalStackRestore_writes (state : State) (retired stack : BitVec 64) :
    WritesOnlyRegs (RegSet.union stepBookkeeping (RegSet.only x2)) state
      (wrapperAfterFinalStackRestore state retired stack) :=
  afterRegisterWrite_writes state (BitVec.ofNat 64 0x10374) retired x2
    (stack + sign_extend (m := 64) 0x7f0#12)

/-- The first stack restore preserves everything the decoder contract preserves. -/
theorem epilogue_afterFirstStackRestore_agree (state : State) (retired stack : BitVec 64) :
    Agree decoderPreserved state (wrapperAfterFirstStackRestore state retired stack) :=
  (wrapperAfterFirstStackRestore_writes state retired stack).agree decoderPreserved_disjoint_sp

/-- The final stack restore preserves everything the decoder contract preserves. -/
theorem epilogue_afterFinalStackRestore_agree (state : State) (retired stack : BitVec 64) :
    Agree decoderPreserved state (wrapperAfterFinalStackRestore state retired stack) :=
  (wrapperAfterFinalStackRestore_writes state retired stack).agree decoderPreserved_disjoint_sp


/-- The first stack restore preserves decoder agreement. -/
theorem epilogue_afterFirst_agree (agree : Agree decoderPreserved base state)
    (retiredFirst stack : BitVec 64) :
    Agree decoderPreserved base (wrapperAfterFirstStackRestore state retiredFirst stack) :=
  agree.trans (epilogue_afterFirstStackRestore_agree state retiredFirst stack)

/-- The `ra` reload preserves decoder agreement. -/
theorem epilogue_afterRa_agree (agree : Agree decoderPreserved base state)
    (retiredFirst retiredRa stack link : BitVec 64) :
    Agree decoderPreserved base
      (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
        (BitVec.ofNat 64 0x10364) retiredRa x1 link) :=
  (epilogue_afterFirst_agree agree retiredFirst stack).trans
    (afterRegisterWrite_agree_of (P := decoderPreserved) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved])
      (by simp [decoderPreserved, platformPreserved]) (by simp [decoderPreserved, platformPreserved]))

/-- Neither instruction touches memory, so the pinned code stays intact. -/
theorem epilogue_afterRa_code (code : canonicalContractParams.env.CodeIntact state)
    (retiredFirst retiredRa stack link : BitVec 64) :
    canonicalContractParams.env.CodeIntact
      (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
        (BitVec.ofNat 64 0x10364) retiredRa x1 link) := by
  simpa [wrapperAfterFirstStackRestore, afterRegisterWrite_mem] using code

/-- Neither instruction touches memory. -/
theorem epilogue_afterRa_mem (retiredFirst retiredRa stack link : BitVec 64) :
    (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
      (BitVec.ofNat 64 0x10364) retiredRa x1 link).mem = state.mem := rfl

/-- The stack pointer after the `+560` restore. -/
theorem epilogue_afterRa_sp (retiredFirst retiredRa stack link : BitVec 64) :
    (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
      (BitVec.ofNat 64 0x10364) retiredRa x1 link).regs.get? x2
      = some (stack + sign_extend (m := 64) (0x230#12)) :=
  ((afterRegisterWrite_writes _ _ _ _ _).get x2 (by decide)).trans
    (tryStepStackAddiAfterRetired_stackPointer state (BitVec.ofNat 64 0x10360) 0x230#12 stack
      retiredFirst)

/-- `a0` is carried through both instructions. -/
theorem epilogue_afterRa_a0 {result : BitVec 64} (resultValue : state.regs.get? x10 = some result)
    (retiredFirst retiredRa stack link : BitVec 64) :
    (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
      (BitVec.ofNat 64 0x10364) retiredRa x1 link).regs.get? x10 = some result := by
  simp [afterRegisterWrite, wrapperAfterFirstStackRestore,
    tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
    tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
    tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, resultValue]

/-- `a1` is carried through both instructions. -/
theorem epilogue_afterRa_a1 {status : BitVec 64} (statusValue : state.regs.get? x11 = some status)
    (retiredFirst retiredRa stack link : BitVec 64) :
    (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
      (BitVec.ofNat 64 0x10364) retiredRa x1 link).regs.get? x11 = some status := by
  simp [afterRegisterWrite, wrapperAfterFirstStackRestore,
    tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick, tryStepStackAddiAfterRetired,
    tryStepStackAddiAfterTick, tryStepStackAddiAfterActive, stackAddiRetiredState, stackAddiNextState,
    tryStepStackAddiAfterIncrement, coreControlFlowNextState, tryStepControlFlowAfterIncrement,
    Std.ExtDHashMap.get?_insert, statusValue]

/-- The pc after the `ra` reload is the first saved-register load. -/
theorem epilogue_afterRa_pc (retiredFirst retiredRa stack link : BitVec 64) :
    (afterRegisterWrite (wrapperAfterFirstStackRestore state retiredFirst stack)
      (BitVec.ofNat 64 0x10364) retiredRa x1 link).regs.get? PC
      = some (BitVec.ofNat 64 0x10368) :=
  afterRegisterWrite_pc _ (BitVec.ofNat 64 0x10364) retiredRa x1 link

end BinaryFv.Zesu.MachineExecution
