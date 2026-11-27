import ZesuExec.Fn.F6.Regions

/-!
# F6 symbolic runs: from the entry, from every call-return point, from the three loop heads
-/

namespace ZesuExec.Fn.F6
open ZesuExec ZesuExec.Sym

sym_run runE := run zesuImage cuts 400 entry S0
sym_run run0 := run zesuImage cuts 400 ret0 (SC xN)
sym_run runS0 := run zesuImage cuts 400 0x800d5d38 (SC xN)
sym_run runS1 := run zesuImage cuts 400 0x800d5dc0 (SC xN)
sym_run runS2 := run zesuImage cuts 400 0x800d5dec (SC xN)
sym_run runS3 := run zesuImage cuts 400 0x800d5e18 (SC xN)
sym_run runS4 := run zesuImage cuts 400 0x800d5e44 (SC xN)
sym_run runS5 := run zesuImage cuts 400 0x800d5e70 (SC xN)
sym_run runS6 := run zesuImage cuts 400 0x800d5e9c (SC xN)
sym_run runS7 := run zesuImage cuts 400 0x800d5ec8 (SC xN)
sym_run runS8 := run zesuImage cuts 400 0x800d5ef4 (SC xN)
sym_run run9 := run zesuImage cuts 400 ret9 (SC xN)
sym_run run10 := run zesuImage cuts 400 ret10 (SC xN)
sym_run run11 := run zesuImage cuts 400 ret11 (SC xN)
sym_run run12 := run zesuImage cuts 400 ret12 (SC xN)
sym_run run13 := run zesuImage cuts 400 ret13 (SC xN)
sym_run run14 := run zesuImage cuts 400 ret14 (SC xN)
sym_run run15 := run zesuImage cuts 400 ret15 (SC x15)
sym_run run16 := run zesuImage cuts 400 ret16 (SC x16)
sym_run run17 := run zesuImage cuts 400 ret17 (SC x16)
sym_run run18 := run zesuImage cuts 400 ret18 (SC x18)
sym_run runL9 := run zesuImage cuts 400 loop9 (SC xL)
sym_run runL10 := run zesuImage cuts 400 loop10 (SC xL)
sym_run runL11 := run zesuImage cuts 400 loop11 (SC xL)

end ZesuExec.Fn.F6
