# BinaryFv Lean library

`Binary/` defines architecture-independent addresses and program images. `RiscV/` integrates the
generated Sail model and provides reusable ELF loading, machine execution, separation logic,
instruction rules, and proof bridges. No implementation-specific proof or executable SSZ
specification is currently part of the root library.

Import `BinaryFv.Binary` or `BinaryFv.RiscV`; target adapters must depend on these generic layers,
never the reverse.
