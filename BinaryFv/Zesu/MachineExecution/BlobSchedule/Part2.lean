import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_5
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_6
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_7
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_8
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_9
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_10
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_11
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_12
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_13
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_14
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_15
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_16
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L1_17
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L2_5
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L3_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_1
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_2
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_3
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_4
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_5
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_6
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_7
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_8
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_9
import BinaryFv.Zesu.MachineExecution.BlobSchedule.Part2.L4_10

/-!
# Split by dependency layer for build parallelism

Re-export of 36 modules this file was divided into. It held 70 declarations in a dependency DAG only 4 deep, elaborated strictly in sequence -- Lean elaborates a module on essentially one core, and Lake parallelises only *across* modules.

The pieces are named `L<layer>_<chunk>`. Declarations in the same layer depend on nothing in that layer, so the chunks of a layer are mutually independent and build concurrently; only the layer count is serial. A contiguous split is impossible here -- a single hub definition near the top, referenced throughout, invalidates every contiguous cut, which is why this is layered rather than sliced.

**Add a declaration to the earliest layer whose dependencies it satisfies**, and to the smallest chunk of that layer. Do not import across chunks of the same layer -- that serialises them and defeats the split.
-/
