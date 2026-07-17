import BinaryFv.RiscV.Instruction.Frame.Store.Frame

/-!
# STORE instruction framing

Umbrella for the STORE `x2` frame. The proof is split into the `PreservesX2` calculus, the PMP/PMA
checks, the CLINT/HTIF/signature platform paths, address translation, and the exported frame.
-/
