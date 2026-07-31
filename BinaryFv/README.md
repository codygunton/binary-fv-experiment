# BinaryFv Lean library

`BinaryFv/` is the root Lean source tree. Its dependency direction is:

```text
Binary -> RiscV -> verified program target
```

- `Binary/` defines architecture-independent addresses and loadable program images.
- `RiscV/` owns reusable generated-Sail model integration, ELF parsing, machine/platform setup,
  execution, separation logic, instruction/step rules, analysis, and generic proof bridges.
- `Zesu/` contains the Amsterdam V4 decoder proof: the pinned specification bridge, handwritten
  per-routine contracts, the deterministically generated Elfling scaffold and its validation against
  the canonical ELF/Sail control flow, and the `Zesu/Root.lean` capstone.

Import `BinaryFv.Binary`, `BinaryFv.RiscV`, or `BinaryFv.Zesu` rather than reaching across layer
boundaries through unrelated leaf modules.
