# Nix build system

- `riscv.nix` defines the pinned RV64 toolchain, ISA/ABI flags, QEMU path, and developer shell.
- `targets.nix` builds the exact Zesu SSZ artifacts and their runnable apps.
- `analysis.nix` produces disassemblies, symbol/size data, CFG reports, and summary statistics.
- `proof.nix` materializes generated Sail/spec/artifact Lean sources and builds the root library.
- `checks.nix` exposes flake checks and applications.

The pinned target objects, DWARF sidecars, ABI manifest, and the deterministic SSZ Elfling scaffold
are built by `targets.nix`/`proof.nix` and exposed as flake packages; the root README's "Regenerating
deterministic artifacts" section lists the `nix build .#…` command for each.

Target source belongs under `targets/`; these files only describe reproducible construction and
validation.
