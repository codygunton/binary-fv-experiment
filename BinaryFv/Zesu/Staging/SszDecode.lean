import BinaryFv.Zesu.MachineExecution.HLevel3SszDecodeSteps
import BinaryFv.Zesu.Staging.MemReadInt

/-!
# Level 3 `ssz.decode` parent composition

This module connects parent-owned `ssz.decode` segments to their proved child contracts.
-/

namespace BinaryFv.Zesu.Staging

open BinaryFv.RiscV
open BinaryFv.Zesu.MachineExecution
open PreSail LeanRV64DExecutable.Functions Register

/-- The first represented four-byte schema word at the `mem.readInt` child boundary. -/
def sszDecodeSchemaWordArgs (args : DecodeInlineArgs) (bound : 4 ≤ args.boundary.input.size)
    (fits : args.boundary.inputAddress + args.boundary.input.size ≤ 2 ^ 64) :
    MemReadIntArgs where
  address := args.boundary.inputAddress
  byte0 := args.boundary.input[0].toNat
  byte1 := args.boundary.input[1].toNat
  byte2 := args.boundary.input[2].toNat
  byte3 := args.boundary.input[3].toNat
  sourceFits := by omega

/-- The typed parent handoff satisfies the proved `mem.readInt` entry contract. -/
theorem memReadIntEntry_of_sszDecodeSchemaWord (args : DecodeInlineArgs) (template : EndpointState)
    (state : State) (entry : SszDecodeSchemaWordEntry args state) :
    memReadIntEntry
      (sszDecodeSchemaWordArgs args entry.inputAtLeastFour entry.input.1)
      { template with machine := state } := by
  have bound := entry.inputAtLeastFour
  refine ⟨entry.atPc, entry.sourceAt, ?_, ?_, ?_, ?_, ?_, ?_, entry.access.configured,
    entry.code⟩
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 0 (by omega)
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 1 (by omega)
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 2 (by omega)
  · simpa [sszDecodeSchemaWordArgs] using entry.input.uintRepAt 3 (by omega)
  · intro offset offsetBound
    exact entry.access.inputLoad offset 1 (by omega)
  · intro offset offsetBound
    exact entry.access.inputNoMMIO offset 1 (by omega)

end BinaryFv.Zesu.Staging
