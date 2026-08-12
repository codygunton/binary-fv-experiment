import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts

/-!
# Closed Level 2 runtime leaves

The bare-metal Level 2 inventory contains no host-runtime child: `read_input`, `write_output`, and
`zkvm_exit` are genuine assembly functions outside the inlined decoder/encoder children selected at
this level. This module remains as the stable import point for future unconditional leaf proofs.
-/
