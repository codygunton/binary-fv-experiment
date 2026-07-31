import BinaryFv.Binary.Elfling.Source
import BinaryFv.Binary.Elfling.Instance
import BinaryFv.Binary.Elfling.FunctionInstance

/-!
# `BinaryFv.Binary.Elfling`

Source-associated decomposition of a linked binary, independent of any instruction set.

`Source` is address-free identity and is what handwritten contracts index by. `Instance` is the
generated, untrusted, address-bearing occurrence data. The split is what lets a contract survive
relinking at a different text base without edits.
-/
