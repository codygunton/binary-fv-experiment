# Zesu proof tree

This tree contains facts about the shipped Zesu `ssz_decode_root.main` RV64 ELF. Start at
[`Root.lean`](Root.lean): `root_compliance` converts its sole `hLevel2` premise through
`level1Contracts_of_level2` and `exportedContracts_of_level1` into the exported SSZ/RLP compliance
result, evaluates its confined trace with the computable RISC-V runner, and equates the normalized
Zesu outcome with the pinned EVM-Sail decoder outcome. The relational form remains available as
`complianceModulo_of_level2`.

- `Artifacts`: immutable production-image bindings.
- `Contracts`: Zesu machine/semantic relations and the fixed known-divergence policy.
- `DecodedValue`: observers and native-memory representations of decoded Zesu values.
- `Elflings`: generated source-function-instance and machine-region identifiers.
- `Entrypoints/SszDecodeRoot`: endpoint boundaries, Level 1 and Level 2 assumptions, and the named
  refinement edges leading to `root_compliance`.
- `MachineExecution`: concrete Sail execution of parent-owned instructions and discharged leaves.

Implementation-independent EVM-Sail decoding semantics live in `BinaryFv/Specs/SSZ`. The archived
tree also had `ControlFlow` and `Runtime` Lean subtrees. This endpoint's CFG remains generated and
validated by the Nix evidence pipeline; its proved allocator, `memcpy`, and bare-metal runtime leaves
live in `MachineExecution`, so empty target-specific namespaces are intentionally omitted.
