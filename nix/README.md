# Nix build system

- `riscv.nix` defines the pinned RV64 toolchain, ISA/ABI flags, QEMU path, and developer shell.
- `targets.nix` builds the exact Zesu SSZ artifacts, checks, and runnable programs.
- `analysis.nix` produces disassemblies, symbol/size data, CFG reports, and summary statistics.
- `proof.nix` materializes generated Sail/spec/artifact Lean sources and builds the root library.
- `checks.nix` exposes flake checks and applications.

The pinned target objects, DWARF sidecars, ABI manifest, and the deterministic SSZ Elfling scaffold
are built by `targets.nix`/`proof.nix` and exposed as flake packages; the root README's "Regenerating
deterministic artifacts" section lists the `nix build .#…` command for each.

Repository-owned integration inputs for a concrete implementation belong under
`verification-target/`; pinned external source enters through `flake.nix`. These Nix files describe
reproducible construction and validation, while optional output links belong under `build/`.
