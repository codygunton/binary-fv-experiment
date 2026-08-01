# `zesu_decode_raw` entrypoint

This directory proves the behavior of Zesu's exported `zesu_decode_raw` function at its real binary
calling boundary. `Execution.lean` sets up the call, follows the machine execution to its return point,
and interprets the resulting status and output value.

The proof connects that execution to the exported decoder contract. The final comparison with the
implementation-independent SSZ oracle is assembled in `BinaryFv/Zesu/Root.lean`.
