import BinaryFv.Binary.Elfling.Instance

/-!
Compatibility vocabulary for generated artifacts that use the clearer “function instance” name.
The underlying address-free identity remains `InstanceId`; this adds no binding or decomposition
claim.
-/

namespace BinaryFv.Binary.Elfling

abbrev FunctionInstanceId := InstanceId

end BinaryFv.Binary.Elfling
