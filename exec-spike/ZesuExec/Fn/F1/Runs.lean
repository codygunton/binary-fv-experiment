import ZesuExec.Fn.F1.Regions
import ZesuExec.Fn.Stage

/-! # F1 symbolic runs: entry, after `remap`, after `alloc`, after `memcpy`, after `free` -/

namespace ZesuExec.Fn.F1
open ZesuExec ZesuExec.Sym

sym_run run0 := run zesuImage [] 400 entry S0

def S1 : SState := (run0_leaves[4]!).S.override (callOv (run0_leaves[4]!).S 100 (some (.lit 0)))
sym_run run1 := run zesuImage [] 400 0x800cb4f8 S1

def S2a : SState := (run0_leaves[2]!).S.override (callOv (run0_leaves[2]!).S 200 none)
sym_run run2a := run zesuImage [] 400 0x800cb55c S2a

def S2b : SState := (run1_leaves[1]!).S.override (callOv (run1_leaves[1]!).S 300 none)
sym_run run2b := run zesuImage [] 400 0x800cb55c S2b

def S3a : SState := (run2a_leaves[0]!).S
sym_run run3a := run zesuImage [] 400 0x800cb588 S3a

def S3b : SState := (run2b_leaves[0]!).S
sym_run run3b := run zesuImage [] 400 0x800cb588 S3b

def S4b : SState := (run3b_leaves[1]!).S.override (callOv (run3b_leaves[1]!).S 400 none)
sym_run run4b := run zesuImage [] 400 0x800cb5a8 S4b

end ZesuExec.Fn.F1
