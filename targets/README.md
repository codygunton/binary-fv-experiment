# Verification targets

Each target directory owns the source adapter, exact wrapper/specification material, conformance
tests, and target-specific documentation needed to reproduce its proof-facing artifact.

`common/` is the only shared target code: a minimal freestanding RV64 process entry and runtime.
`ssz/` is the sole protocol family. Generic binary, ELF, RISC-V, execution, and proof
infrastructure belongs in `BinaryFv/`, not here.
