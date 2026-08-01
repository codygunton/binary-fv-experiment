# Zesu Amsterdam V4 SSZ

`adapter/main.c` exposes the selected repaired Zesu raw decoder as a freestanding RV64 executable.
`tests/` contains binary-specific differential, boundary, extraction, and sink-observability checks.
`probe/` builds a host-only view of private Zesu source functions so their behavior and allocation
events can be compared with the handwritten Lean contract meanings. The probe is never linked into
the verified RV64 binary.
`docs/field-correspondence.md` identifies which Zesu result field represents each field of the
Amsterdam V4 value, including the encoding of optional values and variable-length collections. The
Lean predicates and observers that formalize this relationship live under
`BinaryFv/Zesu/MemoryRepresentation/`. The reusable specification itself lives in
`BinaryFv/Specs/SSZ`.

The adapter exists for QEMU execution and static measurement. The compliance proof targets the
exported `zesu_decode_raw` ABI and the exact Nix-built ELF, not stdin parsing or output formatting.
