# Pinned Zesu Amsterdam V4 decoder

This directory contains the source inputs and test harness for the exact decoder binary proved by
BinaryFv.

- [`adapter/main.c`](adapter/main.c) exposes the Zesu raw decoder as a freestanding RV64 executable.
- [`abi_manifest.zig`](abi_manifest.zig) asks the pinned Zig compiler to report the sizes,
  alignments, and field offsets used by the Lean memory representations.
- [`spec/`](spec/) contains the independent SizzLean-backed Lean oracle.
- [`tests/`](tests/) contains differential tests, boundary cases, generator regressions, and checks
  of the exported result/status accessors.
- [`docs/field-correspondence.md`](docs/field-correspondence.md) records the mapping between Zig and
  specification fields.

The compliance proof targets the exact Nix-built ELF and the public
`zesu_decode_raw(input, len) -> i32` ABI. A successful call stores an inline result in a private
global; `zesu_raw_result` returns its address and `zesu_raw_error` returns the recorded status. The
QEMU adapter is for execution and measurement, not part of that public contract.
