import BinaryFv.RiscV.ELF.Elf64
import BinaryFv.Specs.SSZ.Decode

namespace BinaryFv.Zesu

namespace RiscvSpec

def IsExecutableLoadLayout (bytes : ByteArray) (elf : BinaryFv.RiscV.Elf64) : Prop :=
  elf.bytes = bytes ∧ elf.loadSegments.size > 0 ∧
  BinaryFv.RiscV.Elf64.loadSegmentsAreDisjoint elf.loadSegments.toList = true ∧
  (elf.loadSegments.toList.any fun segment =>
    segment.executable && segment.containsMemoryRange elf.header.entry 1) = true

structure ValidatedElf where
  bytes : ByteArray
  elf : BinaryFv.RiscV.Elf64
  parsed_ok : BinaryFv.RiscV.Elf64.parse bytes = .ok elf
  layout : IsExecutableLoadLayout bytes elf

inductive ExecutionError where
  | invalidArtifact | fuelExhausted | trapped | badReturn | malformedResult | outOfMemory | notImplemented
  deriving DecidableEq, Repr

def execute (_binary : ValidatedElf) (_input : ByteArray) : Except ExecutionError BinaryFv.Specs.SSZ.DecodeOutcome :=
  .error .notImplemented

end RiscvSpec

end BinaryFv.Zesu
