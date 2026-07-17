import BinaryFv.RiscV.ELF.Elf64
import BinaryFv.SSZ.SpecBridge.Decode

namespace BinaryFv.SSZ

namespace RiscvSpec

/-- A fixed ELF together with the parser result and target-layout validation it must satisfy. -/
structure ValidatedElf where
  bytes : ByteArray
  parsed : Except BinaryFv.RiscV.ElfError BinaryFv.RiscV.Elf64
  parsed_eq : BinaryFv.RiscV.Elf64.parse bytes = parsed
  layoutValid : Bool
  layout_valid : layoutValid = true

/-- Failures that are not observable SSZ rejections and must be ruled out by the final proof. -/
inductive ExecutionError where
  | invalidArtifact
  | fuelExhausted
  | trapped
  | badReturn
  | malformedResult
  | outOfMemory
  | notImplemented
  deriving DecidableEq, Repr

/--
The Stage-1 execution boundary. Later layers replace this body with full linked-ELF Sail execution
starting at `zesu_decode_raw`, while preserving this error-aware observable interface.
-/
def execute (_binary : ValidatedElf) (_input : ByteArray) : Except ExecutionError DecodeOutcome :=
  .error .notImplemented

end RiscvSpec

/-- Every byte array in the fixed two-MiB input domain must have the same observable outcome. -/
def rootComplianceClaim (binary : RiscvSpec.ValidatedElf) : Prop :=
  forall input : ByteArray,
    input.size < 2 * 1024 * 1024 ->
      RiscvSpec.execute binary input = .ok (SszSpec.decode input)

end BinaryFv.SSZ
