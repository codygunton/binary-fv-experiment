# BinaryFv Lean library

`BinaryFv/` is the root Lean source tree. Its dependency direction is:

```text
Specs -> verified program target
Binary -> RiscV -> verified program target
```

- `Binary/` defines architecture-independent addresses and loadable program images.
- `RiscV/` owns reusable generated-Sail model integration, ELF parsing, machine/platform setup,
  execution, separation logic, instruction/step rules, analysis, and generic proof bridges.
- `Specs/SSZ/` contains the implementation-independent executable Ethereum SSZ specification.
- `Zesu/` contains the Amsterdam V4 decoder proof: facts extracted from the pinned binary,
  handwritten source-function contracts, the generated Elfling model and its validation against the
  canonical ELF/Sail control flow, contract-validation tests kept outside the theorem graph, and the
  `Zesu/Root.lean` capstone.

Import `BinaryFv.Binary`, `BinaryFv.RiscV`, `BinaryFv.Specs`, or `BinaryFv.Zesu` rather than reaching
across layer boundaries through unrelated leaf modules.
