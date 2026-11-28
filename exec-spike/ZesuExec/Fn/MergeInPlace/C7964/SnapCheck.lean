import ZesuExec.Fn.MergeInPlace.Spec
import ZesuExec.Fn.MergeInPlace.Model
import ZesuExec.Fn.MergeInPlace.Snap
import ZesuExec.Fn.MergeInPlace.C7964.Snaps

/-!
# `sort.block.mergeInPlace__anon_7964`: `Post` on the Unicorn snapshots (contract rule (b))

The snapshots `test/snapshots/M7964` (`tools/snap.py --fn M7964`, inputs
`tools/snap_inputs/merge.json`: runs of lengths 0–4 each, equal elements across the runs, an
empty run either way, elements before `A` and after `B`, elements differing only in their last
byte), rendered by `tools/snap_post.py --kind merge` into `Snaps.lean`.
-/

namespace ZesuExec.Fn.MergeInPlace.C7964

/-- Contract rule (b): `Post` (the return, the write set in the 0x70-byte frame and the range, and
`MergeOf` by `lexLt` on the elements) holds on every Unicorn snapshot of the copy. -/
theorem post_snapshot : snaps.all (SnapOk 0x70 idKey) = true := by decide +kernel

end ZesuExec.Fn.MergeInPlace.C7964
