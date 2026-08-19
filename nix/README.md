# Nix build system

- `targets.nix` builds authentic upstream Zesu's relocatable RV64 object.
- `evm-sail.nix` compiles the reviewed EVM-Sail Lean snapshot and defines its regeneration check.
- `proof.nix` builds the reviewed Sail RISC-V Lean snapshot and the reusable BinaryFv Lean library.
- `analysis.nix` exposes object statistics and disassembly.
- `checks.nix` defines the flake checks and applications.

The linked verification ELF, target ABI adapter, machine-region database, and visualization package
will be restored only after they are derived from the authentic upstream target.
