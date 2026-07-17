# Developer tools

`analyze_rv64.py` performs target-independent direct-control-flow analysis over an RV64
disassembly. Nix invokes it to produce machine-readable and Markdown reports for each retained ELF.

Target-specific vector and differential checks live beside their targets under `targets/*/*/tests/`.
