import ZesuExec.Fn.TX.Regions
import ZesuExec.Sym.Tactic

/-!
# TX runs (programme plan S6 step 5): one `sym_run` per cut point, all with the plan's cut list
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym

sym_run runEntry := run zesuImage cutPcs 300 cEntry SEntry
sym_run run068 := run zesuImage cutPcs 300 c068 S068
sym_run run0c4 := run zesuImage cutPcs 300 c0c4 SBody
sym_run run0d8 := run zesuImage cutPcs 300 c0d8 SBody
sym_run run10c := run zesuImage cutPcs 300 c10c S10c
sym_run run15c := run zesuImage cutPcs 300 c15c SBody
sym_run run18c := run zesuImage cutPcs 300 c18c SBody
sym_run run1a0 := run zesuImage cutPcs 300 c1a0 S1a0
sym_run run1f8 := run zesuImage cutPcs 300 c1f8 SBody
sym_run run230 := run zesuImage cutPcs 300 c230 S230
sym_run run25c := run zesuImage cutPcs 300 c25c SBody
sym_run run340 := run zesuImage cutPcs 300 c340 SSpill
sym_run run3d4 := run zesuImage cutPcs 300 c3d4 SBody
sym_run run400 := run zesuImage cutPcs 300 c400 SSpill
sym_run run42c := run zesuImage cutPcs 300 c42c SBody
sym_run run460 := run zesuImage cutPcs 300 c460 S460
sym_run run4a0 := run zesuImage cutPcs 300 c4a0 SBody

end ZesuExec.Fn.TX
