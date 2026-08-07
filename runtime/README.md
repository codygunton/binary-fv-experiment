# Shared runtime sources

This directory contains freestanding implementation support shared by concrete binary targets.
Architecture-specific source lives in its own subdirectory; it is build input, not a verification
target or a Lean specification.

`riscv64/` supplies the startup and minimal C runtime linked into the Zesu executable.
