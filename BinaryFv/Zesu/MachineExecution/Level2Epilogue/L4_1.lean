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

/-- Restore the three saved callee registers in the wrapper's real epilogue.  This begins at
`0x10368`, immediately after `wrapper_epilogue_first_restore_and_ra`; the saved values are
arbitrary frame contents, not ABI defaults. -/
structure WrapperEpilogueSavedRegistersResult (fromStep : Nat) (base before after : State)
    (stackBase link savedS0 savedS1 savedS2 stack result status : BitVec 64) : Prop where
  trace : Trace fromStep 3 before after
  confined : WrapperPrefix fromStep 3 before after
  pc : after.regs.get? PC = some (BitVec.ofNat 64 0x10374)
  memory : after.mem = before.mem
  ra : after.regs.get? x1 = some link
  s0 : after.regs.get? x8 = some savedS0
  s1 : after.regs.get? x9 = some savedS1
  s2 : after.regs.get? x18 = some savedS2
  sp : after.regs.get? x2 = some stack
  a0 : after.regs.get? x10 = some result
  a1 : after.regs.get? x11 = some status
  frame : WrapperSavedRegisterFrame stackBase.toNat link savedS0 savedS1 savedS2 after
  code : canonicalContractParams.env.CodeIntact after
  agree : Agree decoderPreserved base after
  retired : RetiredCounterPresent after

end BinaryFv.Zesu.MachineExecution
