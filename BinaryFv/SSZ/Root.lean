import BinaryFv.RiscV.ELF.Elf64
import BinaryFv.SSZ.SpecBridge.Decode

namespace BinaryFv.SSZ

namespace RiscvSpec

/--
The parsed ELF describes a nonempty, pairwise-disjoint load layout whose entry point lies in an
executable load segment. This predicate is stated over the parsed image rather than an unrelated
caller-supplied flag.
-/
def IsExecutableLoadLayout (bytes : ByteArray) (elf : BinaryFv.RiscV.Elf64) : Prop :=
  elf.bytes = bytes ∧
  elf.loadSegments.size > 0 ∧
  BinaryFv.RiscV.Elf64.loadSegmentsAreDisjoint elf.loadSegments.toList = true ∧
  (elf.loadSegments.toList.any fun segment =>
    segment.executable && segment.containsMemoryRange elf.header.entry 1) = true

/-- A fixed ELF whose bytes parse successfully and satisfy the required executable load layout. -/
structure ValidatedElf where
  bytes : ByteArray
  elf : BinaryFv.RiscV.Elf64
  parsed_ok : BinaryFv.RiscV.Elf64.parse bytes = .ok elf
  layout : IsExecutableLoadLayout bytes elf

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
