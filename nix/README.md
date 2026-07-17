# Nix build system

- `riscv.nix` defines the pinned RV64 toolchain, ISA/ABI flags, QEMU path, and developer shell.
- `targets.nix` builds the exact Reth Keccak and Zesu SSZ artifacts and their runnable apps.
- `analysis.nix` produces disassemblies, symbol/size data, CFG reports, and comparison statistics.
- `proof.nix` materializes generated Sail/spec/artifact Lean sources and builds the root library.
- `checks.nix` exposes flake checks and applications.

Target source belongs under `targets/`; these files only describe reproducible construction and
validation.
