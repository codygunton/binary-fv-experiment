import BinaryFv.RiscV.Elfling.FunctionTrace
import BinaryFv.RiscV.Elfling.Contract
import BinaryFv.RiscV.Elfling.Boundary
import BinaryFv.RiscV.Elfling.BoundaryTests
import BinaryFv.RiscV.Elfling.SuccessorTrace
import BinaryFv.RiscV.Elfling.SentinelBridge
import BinaryFv.RiscV.Elfling.SentinelBridgeWitness

/-!
# `BinaryFv.RiscV.Elfling`

Generated Sail execution confined to a source-associated function instance, and the Hoare-style contract
interface proved against it. Generic over the binary under analysis: nothing here names a routine,
an address, or an instruction word.
-/
