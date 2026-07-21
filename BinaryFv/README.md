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
- `SSZ/` contains the Zesu Amsterdam V4 decoder proof: handwritten per-routine contracts
  (`SSZ/Zesu/Contracts/`), the deterministically generated Elfling scaffold and its validation against
  the canonical ELF/Sail control flow (`SSZ/Zesu/Elfling/`), and the `SSZ/Root.lean` capstone.

Import `BinaryFv.Binary`, `BinaryFv.RiscV`, `BinaryFv.Keccak`, or `BinaryFv.SSZ` rather than reaching
across layer boundaries through unrelated leaf modules.
