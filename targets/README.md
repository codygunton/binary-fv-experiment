# Verification targets

Each target directory owns only the inputs and checks specific to one concrete binary: its adapter,
ABI extraction material, source probes, binary-facing tests, and implementation correspondence
documentation.

`zesu/` is the Zesu Amsterdam V4 decoder target. Reusable specifications belong in
`BinaryFv/Specs/`; shared freestanding support belongs in `runtime/`; and generic verification
infrastructure belongs in `BinaryFv/`.
