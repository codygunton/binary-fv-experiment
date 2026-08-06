import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L1_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_2
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L2_3
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L3_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L4_1
import BinaryFv.Zesu.MachineExecution.Level2OutcomeDispatch.L5_1

/-!
# Split by dependency layer for build parallelism

Re-export of 9 modules this file was divided into. It held 55 declarations in a dependency DAG only 5 deep, elaborated strictly in sequence -- Lean elaborates a module on essentially one core, and Lake parallelises only *across* modules.

The pieces are named `L<layer>_<chunk>`. Declarations in the same layer depend on nothing in that layer, so the chunks of a layer are mutually independent and build concurrently; only the layer count is serial. A contiguous split is impossible here -- a single hub definition near the top, referenced throughout, invalidates every contiguous cut, which is why this is layered rather than sliced.

**Add a declaration to the earliest layer whose dependencies it satisfies**, and to the smallest chunk of that layer. Do not import across chunks of the same layer -- that serialises them and defeats the split.
-/
