import BinaryFv.Binary.Elfling.Source
import BinaryFv.Binary.Elfling.FunctionInstance
import BinaryFv.Binary.Elfling.Elfling

/-!
# `BinaryFv.Binary.Elfling`

Source-associated decomposition of a linked binary, independent of any instruction set.

`Source` is address-free identity and is what handwritten contracts index by. `FunctionInstance` is the
generated, untrusted, address-bearing function instance data. The split is what lets a contract survive
relinking at a different text base without edits.
-/
