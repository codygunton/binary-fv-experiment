import BinaryFv.SSZ.SpecBridge.Decode
import BinaryFv.SSZ.Zesu.Artifact.Image
import BinaryFv.SSZ.Zesu.Artifact.AbiManifest
import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.Analysis.Decode
import BinaryFv.SSZ.Zesu.Analysis.FunctionWords
import BinaryFv.SSZ.Zesu.Analysis.Reachability
import BinaryFv.SSZ.Zesu.Analysis.AllocatorCalls
import BinaryFv.SSZ.Zesu.Analysis.Primitives
import BinaryFv.SSZ.Zesu.Execution.Representation
import BinaryFv.SSZ.Zesu.Execution.AllocatorVtable
import BinaryFv.SSZ.Zesu.Execution.Observer
import BinaryFv.SSZ.Zesu.Proof.Runtime.BumpAllocator
import BinaryFv.SSZ.Zesu.Proof.Runtime.AllocationBound
import BinaryFv.SSZ.Zesu.Proof.Runtime.MemoryCopy
import BinaryFv.SSZ.Zesu.Proof.Primitives
import BinaryFv.SSZ.Zesu.Interface
import BinaryFv.SSZ.Root

/-!
# `BinaryFv.SSZ`

Umbrella for the Amsterdam V4 SSZ target. The specification bridge is pure; the Zesu artifact,
machine execution, and proof layers will be added beneath this target without introducing a reverse
dependency into the generic RISC-V library.
-/
