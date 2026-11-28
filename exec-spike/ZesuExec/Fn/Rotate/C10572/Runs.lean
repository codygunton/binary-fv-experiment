import ZesuExec.Fn.Rotate.Cuts

/-!
# `mem.rotate__anon_10572` (`0x8007cc68`, 85 instructions, 6 loops): copy data and runs

Element size 104, a 16-byte frame saving `s0`, `ra` at 0, 8. The map's eight cut points; the
inner loops' byte pointers (`lo`, `hi`): `t2`/`t3`, `t1`/`t2`, `t0`/`t1`.
-/

namespace ZesuExec.Fn.Rotate.C10572
open ZesuExec ZesuExec.Sym

def cfg : Cfg where
  entry := 0x8007cc68
  E := 104
  fs := 16
  saved := [(0, 8), (8, 1)]
  kept := [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def entry : Nat := 0x8007cc68
def o1 : Nat := 0x8007cc9c
def i1 : Nat := 0x8007ccb0
def o2 : Nat := 0x8007cd08
def i2 : Nat := 0x8007cd1c
def o3 : Nat := 0x8007cd6c
def i3 : Nat := 0x8007cd80
def epi : Nat := 0x8007cdac
def cutPcs : List Nat := [entry, o1, i1, o2, i2, o3, i3, epi]

sym_run runE := run zesuImage cutPcs 200 entry (S0 cfg)
sym_run runO1 := run zesuImage cutPcs 200 o1 SO
sym_run runI1 := run zesuImage cutPcs 200 i1 (SI 7 28)
sym_run runO2 := run zesuImage cutPcs 200 o2 SO
sym_run runI2 := run zesuImage cutPcs 200 i2 (SI 6 7)
sym_run runO3 := run zesuImage cutPcs 200 o3 SO
sym_run runI3 := run zesuImage cutPcs 200 i3 (SI 5 6)
sym_run runEp := run zesuImage cutPcs 200 epi (SE cfg)

end ZesuExec.Fn.Rotate.C10572
