/-!
# Evidence types for the small binary-validation example

`FunctionInstanceEvidence` contains the reduced facts observed while the unchanged production ELF executed:
control flow, stores, input loads, and entry registers. Expected bindings, meanings, and memory
regions remain in `BinaryFunctionInstanceCheck`; they are not baked into the observation record.

These validation-only types are not part of the compliance theorem.
-/

namespace BinaryFv.SSZ.Zesu.Validation

/-- Compact production-ELF evidence for one functionInstance on one input arm. Fixed addresses are exact
guest virtual addresses. Stack addresses are translated by one common delta to a stable synthetic SP;
this preserves every checked stack-relative offset while removing host-selected stack-base drift. -/
structure FunctionInstanceEvidence where
  arm : String
  entryPc : Nat
  regions : List (Nat × Nat)                       -- (start, end) of each functionInstance code region
  declaredEdges : List (Nat × Nat)                 -- the generated CFG edges (source, target)
  firstExecuted : Nat                              -- first executed PC in the boundary window
  functionInstanceInsnCount : Nat                               -- dynamic instruction count inside the regions
  functionInstanceExecEdges : List (Nat × Nat)                  -- executed non-fallthrough edges with source in-region
  inRegionStores : List (Nat × Nat × Nat × Nat)    -- (pc, addr, width, value) stores inside the regions
  inputByteLoads : List (Nat × Nat)                -- (addr, value) 1-byte loads from the input buffer
  sp : Nat                                         -- x2 at the functionInstance entry
  a0 : Nat                                         -- x10 (indirect-return result slot) at entry
  deriving Repr, DecidableEq

/-- The checker's per-functionInstance result. `Option` fields are `none` on arms where the check does not
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
