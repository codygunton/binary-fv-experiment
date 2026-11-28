import ZesuExec.Fn.MergeInPlace.Slice

/-!
# `sort.block.mergeInPlace__anon_11564` (`0x80098ddc`): the copy's `Cfg`

A 0x110-byte frame saving `ra`, `s0`…`s11` at 0x108 … 0xa8 (no kept registers: the body uses
`s1`…`s11` as scratch). Elements are 32 bytes whose first 16 are a byte slice; the key is the
string it points to (`sliceKey`), and `pre` asks every input element's string to be present,
readable and disjoint from the items and the frame (`SlicePre`).
-/

namespace ZesuExec.Fn.MergeInPlace.C11564
open ZesuExec

def cfg : Cfg where
  entry := 0x80098ddc
  fs := 0x110
  saved := [(0xa8, 27), (0xb0, 26), (0xb8, 25), (0xc0, 24), (0xc8, 23), (0xd0, 22), (0xd8, 21),
    (0xe0, 20), (0xe8, 19), (0xf0, 18), (0xf8, 9), (0x100, 8), (0x108, 1)]
  kept := []
  key := sliceKey
  pre := SlicePre 0x110

end ZesuExec.Fn.MergeInPlace.C11564
