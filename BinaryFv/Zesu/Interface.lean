import BinaryFv.Zesu.ExecutionTypes
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Runner

/-!
# The public execution API

`execute` is the whole caller-facing surface of the SSZ proof: hand it the validated ELF and an
input, and it answers with a `DecodeOutcome` or a specific `ExecutionError`. It is deliberately a
one-line delegation — the artifact gate, the Sail state construction, the sentinel run, the exported
accessor calls, and the result classification all live in source-named modules under
`Entrypoints/ZesuDecodeRaw/`, where each has its own proofs.

The types themselves are in `ExecutionTypes.lean` so those modules can consume them without
importing this one.
-/

namespace BinaryFv.Zesu

namespace RiscvSpec

open BinaryFv.Specs.SSZ

/-- Run the pinned decoder on `input`.

Rejects a caller-supplied ELF that is not the pinned artifact and an input outside the theorem's
bound, then builds the entry state, runs `zesu_decode_raw` to its return sentinel, executes
`zesu_raw_result` and `zesu_raw_error`, and classifies what came back. Every failure mode keeps its
own error; none of them becomes a rejection. -/
def execute (binary : ValidatedElf) (input : ByteArray) : Except ExecutionError DecodeOutcome :=
  Entrypoints.ZesuDecodeRaw.executeChecked binary input

/-- The public API is exactly the runner's checked entry — stated so a future edit that quietly
inserts a second decision point here has to break this. -/
theorem execute_eq_executeChecked (binary : ValidatedElf) (input : ByteArray) :
    execute binary input = Entrypoints.ZesuDecodeRaw.executeChecked binary input := rfl

end RiscvSpec

end BinaryFv.Zesu
