import BinaryFv.RiscV.Elfling.FunctionTrace
import BinaryFv.RiscV.Elfling.Contract
import BinaryFv.RiscV.Elfling.Boundary
import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.RiscV.Elfling.SentinelBridge
import BinaryFv.RiscV.Elfling.ProgramGeometry

/-!
# `BinaryFv.RiscV.Elfling`

Generated Sail execution confined to a source-associated occurrence, and the Hoare-style contract
interface proved against it. Generic over the binary under analysis: nothing here names a source function,
an address, or an instruction word.
-/
