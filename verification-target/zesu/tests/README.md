# Zesu tests

This directory contains tests tied to the concrete Zesu implementation and binary. The differential
and boundary tests compare the public decoder with the pinned Ethereum execution-specs reference and
the executable Lean SSZ specification. The remaining tests check output observability, deterministic
Elfling generation, relocation stability, and agreement between production objects and their DWARF
sidecars.

These tests are regression and falsification evidence. The compliance argument itself is expressed by
the Lean refinement from `BinaryFv/Specs/SSZ` through Zesu's contracts to machine execution.

`lean/ZesuVerification/` contains Lean checks tied to the production binary. The occurrence checks
compare extracted instructions, call boundaries, and source bindings with committed evidence. The
scaled checks repeat those tests over the complete reachable occurrence inventory and make every
coverage gap explicit. The composition witnesses exercise call/return splicing and loop discharge on
small positive and negative examples. Mutation probes alter representative evidence fields and require
the corresponding checker to reject them. These modules live in the dedicated
`ZesuVerificationTests` Lake library, outside the production `BinaryFv` theorem library.
