import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Level2Contracts

/-!
# The terminal frame a wrapper route hands to the status store

`WrapperTerminalRouteFrame` is a plain record of machine facts: it mentions no dispatch proof and
depends on nothing the outcome-dispatch module proves. Stating it here lets `Level2Capstone` compose
routes through the epilogue without waiting on `Level2OutcomeDispatch`, whose elaboration is one of
the build's longest single-core segments.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.RiscV
open BinaryFv.Zesu.Contracts BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
open PreSail LeanRV64DExecutable.Functions Register

/-- Facts shared by every wrapper route arriving at the status store.  Memory framing and live
register values remain separate because the tag-zero route performs a real payload-adjacent store,
while rejection routes leave memory unchanged. -/
structure WrapperTerminalRouteFrame (base before after : State) (fromStep steps : Nat)
    (terminalPc result status : BitVec 64) : Prop where
  trace : Trace fromStep steps before after
  atTerminal : after.regs.get? PC = some terminalPc
  resultValue : after.regs.get? x10 = some result
  statusValue : after.regs.get? x11 = some status
  platform : Agree platformPreserved base after
  code : canonicalContractParams.env.CodeIntact after
  retired : RetiredCounterPresent after

end BinaryFv.Zesu.MachineExecution
