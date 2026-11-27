import ZesuExec.Fn.F5.Spec
import ZesuExec.Fn.F4.Regions

/-! # F5 symbolic runs: entry, after `free` (length 0), after `remap`, `alloc`, `memcpy`, `free` -/

namespace ZesuExec.Fn.F5
open ZesuExec ZesuExec.Sym ZesuExec.Fn.ToOwned

sym_run run0 := run zesuImage [] 400 entry S0

/-- Length 0, capacity > 0: after `free`. -/
def S1f : SState := (run0_leaves[4]!).S.override (callOv (run0_leaves[4]!).S 200 none)
sym_run run1f := run zesuImage [] 400 0x800d65f8 S1f

/-- Length > 0: after `remap` (returns null). -/
def S1 : SState := (run0_leaves[8]!).S.override (callOv (run0_leaves[8]!).S 100 (some (.lit 0)))
sym_run run1 := run zesuImage [] 400 0x800d6638 S1

/-- After `alloc`. -/
def S2 : SState := (run1_leaves[1]!).S.override (callOv (run1_leaves[1]!).S 300 none)
sym_run run2 := run zesuImage [] 400 0x800d66f8 S2

/-- After `memcpy` (registers unchanged). -/
def S3 : SState := (run2_leaves[1]!).S
sym_run run3 := run zesuImage [] 400 0x800d6714 S3

/-- After `free` of the old buffer. -/
def S4 : SState := (run3_leaves[1]!).S.override (callOv (run3_leaves[1]!).S 400 none)
sym_run run4 := run zesuImage [] 400 0x800d6744 S4

end ZesuExec.Fn.F5
