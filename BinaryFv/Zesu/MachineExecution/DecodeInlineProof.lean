import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_10
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_11
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_12
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_13
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_14
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_15
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_16
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_17
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_18
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_19
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_20
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L1_21
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_5
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_6
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_7
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_8
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L2_9
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L3_4
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L4_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L5_3
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L6_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L7_1
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L7_2
import BinaryFv.Zesu.MachineExecution.DecodeInlineProof.L8_1

/-!
# Split by dependency layer for build parallelism

Re-export of 44 modules this file was divided into. It held 83 declarations in a dependency DAG only 8 deep, elaborated strictly in sequence -- Lean elaborates a module on essentially one core, and Lake parallelises only *across* modules.

The pieces are named `L<layer>_<chunk>`. Declarations in the same layer depend on nothing in that layer, so the chunks of a layer are mutually independent and build concurrently; only the layer count is serial. A contiguous split is impossible here -- a single hub definition near the top, referenced throughout, invalidates every contiguous cut, which is why this is layered rather than sliced.

**Add a declaration to the earliest layer whose dependencies it satisfies**, and to the smallest chunk of that layer. Do not import across chunks of the same layer -- that serialises them and defeats the split.
-/
