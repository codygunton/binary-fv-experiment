import BinaryFv.RiscV.HartPrimitives
import BinaryFv.RiscV.Framing

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV

/--
The generated Sail decoder maps the concrete `sd a3, 0(a0)` instruction word `0x00d53023` to the
`STORE` AST node `(imm = 0, rs2 = a3 = x13, rs1 = a0 = x10, width = 8)`.  Here `rs2` is the data
register and `rs1` the address register, matching `execute_STORE`'s use of `rX_bits rs2` as the
stored data.

The decoder is not fully state independent: before any opcode matching it evaluates
`currentlyEnabled Ext_Zicfilp`, which reads `cur_privilege` and (in machine mode) `mseccfg` via
`get_xLPE`.  The decoded result does not depend on the *values* of these registers, but the run
throws `Unreachable` when they are absent, so the two register-presence hypotheses below are
required (they hold on any configured machine, e.g. after `configureDirectCallMachine`).  This is a
`Runs` fact directly usable to discharge the `decode` hypothesis of the `try_step` packaging
(`CoreStepContract`, `CoreTryStepContract`, ...).
-/
theorem ext_decode_sd_run (state : State)
    (privRead : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64)
    (mseccfgRead : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00d53023 : BitVec 32)) state state
      (.STORE (0#12, .Regidx 13#5, .Regidx 10#5, 8)) := by
  unfold Runs
  rw [extDecode_eq]
  simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
    PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, EStateM.instMonad,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, MonadState.get, MonadStateOf.get,
    privRead, mseccfgRead]
  rfl

end BinaryFv.Keccak
