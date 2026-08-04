# Zesu tests

This directory contains tests tied to the concrete Zesu implementation and binary. The differential
and boundary tests compare the public decoder with the pinned Ethereum execution-specs reference and
the executable Lean SSZ specification. The remaining tests check output observability, deterministic
Elfling generation, relocation stability, and agreement between production objects and their DWARF
sidecars.

These tests are regression and falsification evidence. The compliance argument itself is expressed by
the Lean refinement from `BinaryFv/Specs/SSZ` through Zesu's contracts to machine execution.
