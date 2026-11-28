import ZesuExec.Fn.F4.Spec

/-!
# F5 `array_list.Aligned(input.AccessListEntry,null).toOwnedSlice` (`0x800d6554`, 138 instructions)

The shared statement `ToOwned.Pre` / `ToOwned.Post` (`F4/Spec.lean`) with
`entriesElementBytes = 40` and `entriesEmptyPointer = 8` (`ArrayListContract.v`,
`EntriesToOwnedSliceContract.v`); the allocator calls pass log2 alignment 3.
-/

namespace ZesuExec.Fn.F5
open ZesuExec

def entry : Nat := 0x800d6554
def bound : Nat := 204

/-- `entriesElementBytes`, `entriesEmptyPointer`. -/
def elemBytes : Nat := 40
def emptyPtr : Word := BitVec.ofNat 64 8

abbrev Pre (A : AllocContract zesuImage) (L : List (Word × Nat)) (items : List Byte) :=
  ToOwned.Pre elemBytes A L items
abbrev Post (A : AllocContract zesuImage) (L : List (Word × Nat)) (items : List Byte) :=
  ToOwned.Post elemBytes A L items emptyPtr

end ZesuExec.Fn.F5
