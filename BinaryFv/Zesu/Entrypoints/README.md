# Zesu entrypoints

This directory contains end-to-end proofs for functions that callers can invoke through Zesu's binary
interface. Each child directory is named after one exported function and connects its ABI boundary,
machine execution, result interpretation, and semantic contract.

Entrypoint proofs compose lower layers; they do not redefine them. Source function meanings come from
`Contracts/`, memory values from `MemoryRepresentation/`, and concrete execution facts from
`MachineExecution/`. The resulting exported guarantees feed `BinaryFv/Zesu/Root.lean`.

Currently `ZesuDecodeRaw/` covers the `zesu_decode_raw` entrypoint.
