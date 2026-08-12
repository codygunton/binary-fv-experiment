# Zesu proof tree

This tree contains facts about the shipped Zesu `ssz_decode_root.main` RV64 ELF. Start at
[`Root.lean`](Root.lean): `root_compliance` converts the six immediate Level 1 contracts into the
exported SSZ/RLP compliance statement.

- `Artifacts`: immutable production-image bindings.
- `Contracts`: Zesu machine/semantic relations and the fixed known-divergence policy.
- `DecodedValue`: observers and native-memory representations of decoded Zesu values.
- `Elflings`: generated source-function-instance and machine-region identifiers.
- `Entrypoints/SszDecodeRoot`: endpoint boundaries, Level 1 assumptions, and Level 0 composition.
- `MachineExecution`: concrete Sail execution of parent-owned instructions.

Implementation-independent EVM-Sail decoding semantics live in `BinaryFv/Specs/SSZ`. The archived
tree also had `ControlFlow` and `Runtime` Lean subtrees; this endpoint currently has no standalone
Lean CFG API or discharged runtime proof, so their facts remain generated build evidence and selected
Level 1 contracts rather than empty proof namespaces.
