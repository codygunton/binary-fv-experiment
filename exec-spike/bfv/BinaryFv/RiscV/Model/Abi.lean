-- exec-spike repair: the model's submodules, not its root module `LeanRV64DExecutable`, which
-- declares the Sail `main` (and `sail_model_init`) and so cannot be linked into `zesu-difftest`.
import LeanRV64DExecutable.Flow
import LeanRV64DExecutable.Common
import LeanRV64DExecutable.Prelude
import LeanRV64DExecutable.Xlen
import LeanRV64DExecutable.PlatformConfig
import LeanRV64DExecutable.SysRegs
import LeanRV64DExecutable.InterruptRegs
import LeanRV64DExecutable.SysControl
import LeanRV64DExecutable.Platform
import LeanRV64DExecutable.Pma
import LeanRV64DExecutable.VmemTlb
import LeanRV64DExecutable.Step
import LeanRV64DExecutable.Main

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions

/-- The architectural integer register used as the direct-call stack pointer. -/
def stackPointer : regidx := .Regidx 2#5

/-- The architectural zero register `x0`. -/
def zeroRegister : regidx := .Regidx 0#5

end BinaryFv.RiscV
