# SSZ specification

`Decode.lean` wraps the pinned EVM-Sail Lean extraction as the implementation-independent reference
computation for stateless-input SSZ decoding and transaction RLP decoding. It contains no Zesu
artifact, machine-state, known-bug, or native-layout declarations.
