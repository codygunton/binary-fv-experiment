import LeanRV64DExecutable
import ZesuExec.Sail.ModelInit

/-! `modelInit` (used by engine A of `zesu-difftest`) is the generated `sail_model_init`. -/

namespace ZesuExec.SailLink

theorem modelInit_eq : modelInit = LeanRV64DExecutable.Functions.sail_model_init () := rfl

end ZesuExec.SailLink
