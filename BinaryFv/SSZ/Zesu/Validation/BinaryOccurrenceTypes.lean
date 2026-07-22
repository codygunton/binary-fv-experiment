/-!
# Row C: production-ELF occurrence-evidence types

The compact, deterministic per-occurrence evidence captured from the UNCHANGED production RV64 ELF under
pinned QEMU (executed-PC/edge summary + in-region stores + input byte loads + entry `sp`/`a0`), plus the
check-result record the diagnostic checker produces. Only observed, reduced facts live in `OccEvidence`;
the expected binding / meaning / memory layout live in `BinaryOccurrenceCheck`.

These are validation (falsification/regression) types — never imported by the theorem dependency graph.
-/

namespace BinaryFv.SSZ.Zesu.Validation

/-- Compact production-ELF evidence for one occurrence on one input arm. Addresses are guest virtual
addresses (large `Nat`s, deterministic under `setarch -R`). -/
structure OccEvidence where
  arm : String
  entryPc : Nat
  regions : List (Nat × Nat)                       -- (start, end) of each occurrence code region
  declaredEdges : List (Nat × Nat)                 -- the generated CFG edges (source, target)
  firstExecuted : Nat                              -- first executed PC in the boundary window
  occInsnCount : Nat                               -- dynamic instruction count inside the regions
  occExecEdges : List (Nat × Nat)                  -- executed non-fallthrough edges with source in-region
  inRegionStores : List (Nat × Nat × Nat × Nat)    -- (pc, addr, width, value) stores inside the regions
  inputByteLoads : List (Nat × Nat)                -- (addr, value) 1-byte loads from the input buffer
  sp : Nat                                         -- x2 at the occurrence entry
  a0 : Nat                                         -- x10 (indirect-return result slot) at entry
  deriving Repr, DecidableEq

/-- The checker's per-occurrence result. `Option` fields are `none` on arms where the check does not
apply (the readU64 children do not execute on the absent/malformed arms). -/
structure CheckResult where
  entryReached : Bool
  edgesSubsetOfCfg : Bool
  childOffsetsFromLoads : Option Bool
  decodedBlobSchedule : Option (List Nat)
  resultSlotOnStack : Bool
  withinStepBound : Bool
  noAllocation : Bool
  inputPreserved : Bool
  codePreserved : Bool
  noUnclassifiedWrites : Bool
  deriving BEq, Repr, DecidableEq

end BinaryFv.SSZ.Zesu.Validation
