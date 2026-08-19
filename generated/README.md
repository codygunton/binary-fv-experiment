# Generated Sail Lean source

These directories contain reviewed generated Lean source. Normal proof builds compile these files
without running either Sail generator.

- `evm-sail-lean` comes from EVM-Sail `d0e4aabd` with Sail `25cc260d`.
- `sail-riscv-lean` comes from Sail RISC-V `65ddde80` with Sail 0.20.1.

Do not edit generated files. Build the two regeneration checks after a source pin, Sail version,
generation option, patch, or snapshot changes. The checks regenerate each complete tree and compare
all source files. The scheduled workflow runs the same checks each week.

EVM-Sail assigns unstable numeric suffixes to generated `k_ex..._` existential names. Its comparison
renames those identifiers by first occurrence. The check does not normalize other source text.

```sh
nix build -L .#evmSailLeanRegenerationCheck
nix build -L .#sailRiscvLeanRegenerationCheck
```
