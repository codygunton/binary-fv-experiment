import BinaryFv.RiscV.Instruction.Frame.StackPointer

/-!
# Frame-coverage inventory entries

One decoded word paired with its constructor and static x2-frame status. Which words a binary has is
a target fact.
-/

namespace BinaryFv.RiscV

open LeanRV64DExecutable.Functions

structure FrameCoverageEntry where
  word : DecodedWord
  constructor : ExecutionConstructor
  status : X2FrameStatus

end BinaryFv.RiscV
