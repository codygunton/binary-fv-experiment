# Nix build system

- `targets.nix` builds authentic upstream Zesu's relocatable RV64 object.
- `evm-sail.nix` regenerates, compiles, and smoke-tests the pinned Sail Lean extraction.
- `proof.nix` builds the reusable BinaryFv/RISC-V Lean library.
- `analysis.nix` exposes object statistics and disassembly.
- `checks.nix` defines the flake checks and applications.

The linked verification ELF, target ABI adapter, machine-region database, and visualization package
will be restored only after they are derived from the authentic upstream target.
