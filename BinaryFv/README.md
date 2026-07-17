# BinaryFv Lean library

`BinaryFv/` is the root Lean source tree. Its dependency direction is:

```text
Binary -> RiscV -> protocol target
```

- `Binary/` defines architecture-independent addresses and loadable program images.
- `RiscV/` owns reusable generated-Sail model integration, ELF parsing, machine/platform setup,
  execution, separation logic, instruction/step rules, analysis, and generic proof bridges.
- `Keccak/SpecBridge/` connects byte/lane representations to the executable Keccak specification.
- `Keccak/Reth/` contains facts, execution setup, and proofs for the exact Reth RustCrypto ELF.

Import `BinaryFv.Binary`, `BinaryFv.RiscV`, or `BinaryFv.Keccak` rather than reaching across layer
boundaries through unrelated leaf modules.
