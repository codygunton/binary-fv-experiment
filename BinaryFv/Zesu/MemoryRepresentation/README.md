# Zesu memory representations

This directory defines how bytes in Sail machine memory represent the logical values used by Zesu and
the SSZ specification. It provides the shared vocabulary that lets contracts describe values without
repeating byte offsets, pointer layouts, and guarded memory reads.

- `Observers.lean` safely reads byte ranges and structured values from machine state.
- `PrimitiveReads.lean` connects guarded machine-memory observations to the corresponding SizzLean
  integer readers.
- `Containers.lean`, `RawV4.lean`, and `Result.lean` describe Zesu's concrete layouts for decoded
  containers, complete V4 values, and call results.

These definitions are not routine contracts. `Contracts/` uses them to state behavior, while execution
proofs establish that the binary creates or preserves the represented values.
