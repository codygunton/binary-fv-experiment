import SszBridge.Core

namespace BinaryFv.Zesu

/-- The observable SSZ decoder result: a complete V4 value or a normalized rejection. -/
inductive DecodeOutcome where
  | accepted (value : SszBridge.RawV4)
  | rejected
  deriving Repr

namespace SszSpec

/--
The pinned SizzLean bridge is the specification oracle. All bridge-level errors, including invalid
SSZ, unknown forks, and quarantined V3 framing, have the single observable outcome `rejected`.
-/
def decode (input : ByteArray) : DecodeOutcome :=
  match SszBridge.decodeStatelessInput input with
  | .ok value => .accepted value
  | .error _ => .rejected

end SszSpec

end BinaryFv.Zesu
