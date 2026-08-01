# Shared RV64 runtime

`riscv64_start.S` enters C `main` without an operating system. `riscv64_runtime.c` supplies the
minimal memory and process-exit support needed by the freestanding adapters.

This code makes target libraries runnable under `qemu-riscv64` for conformance and measurement. The
Lean proofs bypass CLI parsing and enter the exported protocol ABI directly.
