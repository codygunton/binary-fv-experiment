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
import BinaryFv.RiscV.Model.Address

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def initialState : State := default

/-- The selected direct-call path uses RV64M multiplication and division instructions. -/
def enableMExtension : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12 1#1)

end BinaryFv.RiscV
