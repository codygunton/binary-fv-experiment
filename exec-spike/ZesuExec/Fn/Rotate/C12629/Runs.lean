import ZesuExec.Fn.Rotate.Cuts

/-!
# `mem.rotate__anon_12629` (`0x800a8f30`, 77 instructions, 6 loops): copy data and runs

Element size 64, a 16-byte frame saving `s0`, `ra` at 0, 8. The map's eight cut points; the
inner loops' byte pointers (`lo`, `hi`): `t1`/`t2`, `t0`/`t1`, `a7`/`t0`.
-/

namespace ZesuExec.Fn.Rotate.C12629
open ZesuExec ZesuExec.Sym

def cfg : Cfg where
  entry := 0x800a8f30
  E := 64
  fs := 16
  saved := [(0, 8), (8, 1)]
  kept := [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def entry : Nat := 0x800a8f30
def o1 : Nat := 0x800a8f5c
def i1 : Nat := 0x800a8f70
def o2 : Nat := 0x800a8fbc
def i2 : Nat := 0x800a8fd0
def o3 : Nat := 0x800a9014
def i3 : Nat := 0x800a9028
def epi : Nat := 0x800a9054
def cutPcs : List Nat := [entry, o1, i1, o2, i2, o3, i3, epi]

sym_run runE := run zesuImage cutPcs 200 entry (S0 cfg)
sym_run runO1 := run zesuImage cutPcs 200 o1 SO
sym_run runI1 := run zesuImage cutPcs 200 i1 (SI 6 7)
sym_run runO2 := run zesuImage cutPcs 200 o2 SO
sym_run runI2 := run zesuImage cutPcs 200 i2 (SI 5 6)
sym_run runO3 := run zesuImage cutPcs 200 o3 SO
sym_run runI3 := run zesuImage cutPcs 200 i3 (SI 17 5)
sym_run runEp := run zesuImage cutPcs 200 epi (SE cfg)

end ZesuExec.Fn.Rotate.C12629
