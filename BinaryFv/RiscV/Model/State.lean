import LeanRV64DExecutable
import BinaryFv.RiscV.Model.Address

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

abbrev State := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def initialState : State := default

def initializeModel : SailM Unit :=
  sail_model_init ()

/-- The selected direct-call path uses RV64M multiplication and division instructions. -/
def enableMExtension : SailM Unit := do
  writeReg misa (Sail.BitVec.updateSubrange (← readReg misa) 12 12 1#1)

end BinaryFv.RiscV
