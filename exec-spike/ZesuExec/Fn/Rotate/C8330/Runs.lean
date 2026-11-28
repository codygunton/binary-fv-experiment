import ZesuExec.Fn.Rotate.Cuts

/-!
# `mem.rotate__anon_8330` (`0x8006464c`, 88 instructions, 6 loops): copy data and runs

Element size 48, a 32-byte frame saving `s1`, `s0`, `ra` at 8, 16, 24. The map's eight cut
points; the inner loops' byte pointers (`lo`, `hi`): `t4`/`t5`, `t3`/`t4`, `t0`/`t1`.
-/

namespace ZesuExec.Fn.Rotate.C8330
open ZesuExec ZesuExec.Sym

def cfg : Cfg where
  entry := 0x8006464c
  E := 48
  fs := 32
  saved := [(8, 9), (16, 8), (24, 1)]
  kept := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def entry : Nat := 0x8006464c
def o1 : Nat := 0x80064688
def i1 : Nat := 0x8006469c
def o2 : Nat := 0x800646f8
def i2 : Nat := 0x8006470c
def o3 : Nat := 0x80064758
def i3 : Nat := 0x8006476c
def epi : Nat := 0x80064798
def cutPcs : List Nat := [entry, o1, i1, o2, i2, o3, i3, epi]

sym_run runE := run zesuImage cutPcs 200 entry (S0 cfg)
sym_run runO1 := run zesuImage cutPcs 200 o1 SO
sym_run runI1 := run zesuImage cutPcs 200 i1 (SI 29 30)
sym_run runO2 := run zesuImage cutPcs 200 o2 SO
sym_run runI2 := run zesuImage cutPcs 200 i2 (SI 28 29)
sym_run runO3 := run zesuImage cutPcs 200 o3 SO
sym_run runI3 := run zesuImage cutPcs 200 i3 (SI 5 6)
sym_run runEp := run zesuImage cutPcs 200 epi (SE cfg)

end ZesuExec.Fn.Rotate.C8330
