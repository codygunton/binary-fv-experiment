# Shared RV64 runtime

`riscv64_start.S` enters the freestanding Zig `main` under the Linux RISC-V process ABI.
`riscv64_runtime.c` supplies raw read/write/exit syscalls, bounded input and allocator storage, and
the minimal memory functions needed by the endpoint.

This code makes the exact linked endpoint runnable under `qemu-riscv64` for conformance and
measurement. It has no libc dependency; the production ELF, evidence harness, CFG, and machine
proofs therefore share one instruction image.
