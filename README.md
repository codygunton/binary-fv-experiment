# Binary FV Experiment

This repository develops Lean proofs relating shipped RV64 binaries to executable specifications.
The active target is authentic upstream [Zesu](deps/zesu), while the stateless-input specification is
the Lean extraction of pinned [EVM-Sail](deps/evm-sail). Nix pins and builds both inputs.

The previous locally grafted Zesu decoder, Etheorem/SizzLean specification, and target-specific
proofs were removed during the upstream pivot. Their complete history and proof-authoring tooling are
preserved on `archive/zesu-grafted-decoder-level4`; an all-ref recovery bundle is documented in
`STATUS.md`. The current `root_compliance hLevel2` theorem executes the authentic linked binary and
compares its canonical outcome with the pinned EVM-Sail decoder.

## Build

```sh
git submodule update --init
nix build -L .#evmSailLeanExtraction  # regenerate, compile, and smoke-test EVM-Sail Lean
nix build -L .#zesuRv64Object         # authentic upstream Zesu RV64 object
nix build -L .#binaryFvLean           # reusable BinaryFv/RISC-V Lean library
nix flake check
```

`deps/` makes the exact sources browsable; Nix independently fetches the same revisions and is the
authoritative build. The proof target links upstream Zesu's relocatable zkVM RV64 object to the
verified bare-metal entry, memory-context, and terminal ABI used by the endpoint runner.

## Layout

- `BinaryFv/Binary` and `BinaryFv/RiscV`: reusable binary and Sail-RISC-V proof infrastructure.
- `deps/zesu`: authentic Zesu at zkevm v0.6.2.
- `deps/evm-sail`: version-matched executable EVM semantics and SSZ stateless-input decoder.
- `nix/evm-sail.nix`: reproducible Sail-to-Lean extraction and executable smoke test.
- `tools/`: retained ELF/DWARF/CFG, profiling, proof-template retrieval, and n-gram tooling.
- `docs/research/evm-sail-ssz-feasibility.md`: extraction assessment and candidate divergences.
- `docs/research/grafted-zesu-deletion-audit.md`: per-subsystem recovery and deletion rationale.

The public theorem normalizes exactly the seven reviewed Zesu divergences before asserting equality.
`hLevel2` contains only the 17 outstanding Level 2 function-instance contracts; the endpoint
initialization, RISC-V execution, parent glue, and discharged leaves are proved in Lean.

## Trust boundary

Generated Lean is rebuilt from pinned Sail sources and compiled; `tests/evm-sail/DecodeSmoke.lean`
also executes one accepted input and one schema mutation. This establishes an executable candidate
specification, not Zesu compliance. ELF facts, empirical traces, source mappings, and retrieval
suggestions remain evidence or authoring aids until connected by Lean proofs.
