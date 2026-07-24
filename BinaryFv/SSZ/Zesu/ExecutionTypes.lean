import BinaryFv.RiscV.ELF.Elf64

/-!
# Types of the public execution API

The caller-facing types of `RiscvSpec.execute`: what counts as a validated ELF, and the distinct
execution errors. They live below `Interface.lean` so the source-named runner modules under
`Entrypoints/ZesuDecodeRaw/` can consume them while `Interface.lean` — the small public API —
imports those modules to implement `execute`.
-/

namespace BinaryFv.SSZ

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

/-- Why an execution produced no `DecodeOutcome`. Each names a distinct, real failure, and none of
them is a decode rejection: a rejection is a `DecodeOutcome`, not an error.

* `invalidArtifact` — the caller's ELF is not the pinned binary, or the input is outside the
  theorem's bound (which claims nothing for it), or the artifact's symbol table lacks an entry point.
* `fuelExhausted` — the step budget ran out, in the decode call or in an accessor call.
* `trapped` — the machine stalled or faulted.
* `badReturn` — a return code or recorded status the ABI does not document.
* `malformedResult` — a documented return whose result memory does not match the pinned layout.
* `outOfMemory` — the decoder reported an exhausted arena. Deliberately *not* a rejection: the
  specification is a total function with no out-of-memory outcome, so calling this a rejection could
  contradict a spec acceptance.

There is no `notImplemented`: `execute` is implemented, and removing the constructor is what keeps
a future stub from reintroducing one silently. -/
inductive ExecutionError where
  | invalidArtifact | fuelExhausted | trapped | badReturn | malformedResult | outOfMemory
  deriving DecidableEq, Repr

end RiscvSpec

end BinaryFv.SSZ
