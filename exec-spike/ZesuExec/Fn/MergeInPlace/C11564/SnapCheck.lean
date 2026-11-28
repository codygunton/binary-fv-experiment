import ZesuExec.Fn.MergeInPlace.Spec
import ZesuExec.Fn.MergeInPlace.Model
import ZesuExec.Fn.MergeInPlace.Snap
import ZesuExec.Fn.MergeInPlace.C11564.Snaps

/-!
# `sort.block.mergeInPlace__anon_11564`: `Post` on the Unicorn snapshots (contract rule (b))

The snapshots `test/snapshots/M11564` (`tools/snap.py --fn M11564`, inputs
`tools/snap_inputs/merge_slices.json`: elements whose leading slice points to strings of 0–40
bytes, equal strings at different addresses, one pointer in several elements, strings that are
prefixes of others, an empty run either way, elements before `A` and after `B`), rendered by
`tools/snap_post.py --kind keyed` into `Snaps.lean`.
-/

namespace ZesuExec.Fn.MergeInPlace.C11564

/-- Contract rule (b): `Post` (the return, the write set in the 0x110-byte frame and the range, and
`MergeOf` by `lexLt` on the strings the elements' slices point to) holds on every Unicorn snapshot
of the copy. -/
theorem post_snapshot : snaps.all (SnapOk 0x110 snapSliceKey) = true := by decide +kernel

end ZesuExec.Fn.MergeInPlace.C11564
