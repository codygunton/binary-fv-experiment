import BinaryFv.Zesu.Elflings.GeneratedProgramCfg
import BinaryFv.Zesu.Elflings.GeneratedProgramEdgeClass
import BinaryFv.Zesu.Elflings.GeneratedProgramInstructions
import BinaryFv.Zesu.Elflings.GeneratedProgramNesting
import BinaryFv.Zesu.Elflings.GeneratedProgramReachablePartition
import BinaryFv.Zesu.Elflings.GeneratedProvenanceCheck
import BinaryFv.Zesu.Elflings.GeneratedReachabilityExact

/-!
# Evidence: generated-artifact validation

Checks that the *generated* description of the pinned binary is faithful and exact — the CFG
inventory, the edge classification, the instruction and nesting tables, the reachable partition, the
provenance check, and reachability equality in both directions.

These are genuine kernel-checked theorems, not tests, and CI builds this target. They are separated
from `BinaryFv` because `root_compliance` does not depend on any of them: they validate the
generator's output rather than participating in the conformance argument. Keeping them out of the
compliance target's import closure is what lets the compliance proof build without waiting on them
— they are the slowest evidence in the project and none of it is load-bearing for the theorem.

Add a module here when it validates generated data. Add it to `BinaryFv.Zesu` instead when
`root_compliance` needs it, and the layer audit in `nix/proof.nix` will keep you honest either way.
-/
