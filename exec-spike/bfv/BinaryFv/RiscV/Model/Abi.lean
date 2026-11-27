import LeanRV64DExecutable

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions

/-- The architectural integer register used as the direct-call stack pointer. -/
def stackPointer : regidx := .Regidx 2#5

/-- The architectural zero register `x0`. -/
def zeroRegister : regidx := .Regidx 0#5

end BinaryFv.RiscV
