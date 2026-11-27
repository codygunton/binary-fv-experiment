import ZesuExec.Fn.DTF.Leaves
import ZesuExec.Fn.DTF.Keep

/-!
# DTF leaves closed by `leaf_keep` (programme plan S7 step 4), in table order

Each instance checks by `decide` `KeepCheck` (the leaf ends at a plain cut without obligations,
writes only frame words below the save area, and carries the target's shape, arms, `rest` and
budget over from the source) and `SrcOk` (the source's facts follow from its assertion), and takes
the source's cut lemma. Generated from `KeepCheck` over all leaves (`OPEN/DTF/CUTS.md`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

theorem DTF.leaf_8000059c_0 : LeafGoal DTF.plan DTF.plan.cuts[3]! ((DTF.plan.leaves 0x8000059c)[0]!) :=
  leaf_keep (table[3]!) (table[57]'(by decide)) ((leavesAt 0x8000059c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000059c (by decide) (by decide)
theorem DTF.leaf_8000059c_1 : LeafGoal DTF.plan DTF.plan.cuts[3]! ((DTF.plan.leaves 0x8000059c)[1]!) :=
  leaf_keep (table[3]!) (table[57]'(by decide)) ((leavesAt 0x8000059c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000059c (by decide) (by decide)
theorem DTF.leaf_800005f0_0 : LeafGoal DTF.plan DTF.plan.cuts[5]! ((DTF.plan.leaves 0x800005f0)[0]!) :=
  leaf_keep (table[5]!) (table[57]'(by decide)) ((leavesAt 0x800005f0)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800005f0 (by decide) (by decide)
theorem DTF.leaf_800005f0_1 : LeafGoal DTF.plan DTF.plan.cuts[5]! ((DTF.plan.leaves 0x800005f0)[1]!) :=
  leaf_keep (table[5]!) (table[57]'(by decide)) ((leavesAt 0x800005f0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800005f0 (by decide) (by decide)
theorem DTF.leaf_800005f0_2 : LeafGoal DTF.plan DTF.plan.cuts[5]! ((DTF.plan.leaves 0x800005f0)[2]!) :=
  leaf_keep (table[5]!) (table[57]'(by decide)) ((leavesAt 0x800005f0)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800005f0 (by decide) (by decide)
theorem DTF.leaf_8000065c_0 : LeafGoal DTF.plan DTF.plan.cuts[7]! ((DTF.plan.leaves 0x8000065c)[0]!) :=
  leaf_keep (table[7]!) (table[57]'(by decide)) ((leavesAt 0x8000065c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000065c (by decide) (by decide)
theorem DTF.leaf_8000065c_1 : LeafGoal DTF.plan DTF.plan.cuts[7]! ((DTF.plan.leaves 0x8000065c)[1]!) :=
  leaf_keep (table[7]!) (table[57]'(by decide)) ((leavesAt 0x8000065c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000065c (by decide) (by decide)
theorem DTF.leaf_800006b0_0 : LeafGoal DTF.plan DTF.plan.cuts[9]! ((DTF.plan.leaves 0x800006b0)[0]!) :=
  leaf_keep (table[9]!) (table[57]'(by decide)) ((leavesAt 0x800006b0)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800006b0 (by decide) (by decide)
theorem DTF.leaf_800006b0_1 : LeafGoal DTF.plan DTF.plan.cuts[9]! ((DTF.plan.leaves 0x800006b0)[1]!) :=
  leaf_keep (table[9]!) (table[57]'(by decide)) ((leavesAt 0x800006b0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800006b0 (by decide) (by decide)
theorem DTF.leaf_800006b0_2 : LeafGoal DTF.plan DTF.plan.cuts[9]! ((DTF.plan.leaves 0x800006b0)[2]!) :=
  leaf_keep (table[9]!) (table[57]'(by decide)) ((leavesAt 0x800006b0)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800006b0 (by decide) (by decide)
theorem DTF.leaf_8000071c_0 : LeafGoal DTF.plan DTF.plan.cuts[11]! ((DTF.plan.leaves 0x8000071c)[0]!) :=
  leaf_keep (table[11]!) (table[57]'(by decide)) ((leavesAt 0x8000071c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000071c (by decide) (by decide)
theorem DTF.leaf_8000071c_1 : LeafGoal DTF.plan DTF.plan.cuts[11]! ((DTF.plan.leaves 0x8000071c)[1]!) :=
  leaf_keep (table[11]!) (table[57]'(by decide)) ((leavesAt 0x8000071c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000071c (by decide) (by decide)
theorem DTF.leaf_80000770_0 : LeafGoal DTF.plan DTF.plan.cuts[13]! ((DTF.plan.leaves 0x80000770)[0]!) :=
  leaf_keep (table[13]!) (table[57]'(by decide)) ((leavesAt 0x80000770)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000770 (by decide) (by decide)
theorem DTF.leaf_80000770_1 : LeafGoal DTF.plan DTF.plan.cuts[13]! ((DTF.plan.leaves 0x80000770)[1]!) :=
  leaf_keep (table[13]!) (table[57]'(by decide)) ((leavesAt 0x80000770)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000770 (by decide) (by decide)
theorem DTF.leaf_80000770_2 : LeafGoal DTF.plan DTF.plan.cuts[13]! ((DTF.plan.leaves 0x80000770)[2]!) :=
  leaf_keep (table[13]!) (table[57]'(by decide)) ((leavesAt 0x80000770)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000770 (by decide) (by decide)
theorem DTF.leaf_800007dc_0 : LeafGoal DTF.plan DTF.plan.cuts[15]! ((DTF.plan.leaves 0x800007dc)[0]!) :=
  leaf_keep (table[15]!) (table[57]'(by decide)) ((leavesAt 0x800007dc)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800007dc (by decide) (by decide)
theorem DTF.leaf_800007dc_1 : LeafGoal DTF.plan DTF.plan.cuts[15]! ((DTF.plan.leaves 0x800007dc)[1]!) :=
  leaf_keep (table[15]!) (table[57]'(by decide)) ((leavesAt 0x800007dc)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800007dc (by decide) (by decide)
theorem DTF.leaf_80000830_0 : LeafGoal DTF.plan DTF.plan.cuts[17]! ((DTF.plan.leaves 0x80000830)[0]!) :=
  leaf_keep (table[17]!) (table[57]'(by decide)) ((leavesAt 0x80000830)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000830 (by decide) (by decide)
theorem DTF.leaf_80000830_1 : LeafGoal DTF.plan DTF.plan.cuts[17]! ((DTF.plan.leaves 0x80000830)[1]!) :=
  leaf_keep (table[17]!) (table[57]'(by decide)) ((leavesAt 0x80000830)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000830 (by decide) (by decide)
theorem DTF.leaf_80000830_2 : LeafGoal DTF.plan DTF.plan.cuts[17]! ((DTF.plan.leaves 0x80000830)[2]!) :=
  leaf_keep (table[17]!) (table[57]'(by decide)) ((leavesAt 0x80000830)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000830 (by decide) (by decide)
theorem DTF.leaf_8000089c_0 : LeafGoal DTF.plan DTF.plan.cuts[19]! ((DTF.plan.leaves 0x8000089c)[0]!) :=
  leaf_keep (table[19]!) (table[57]'(by decide)) ((leavesAt 0x8000089c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000089c (by decide) (by decide)
theorem DTF.leaf_8000089c_1 : LeafGoal DTF.plan DTF.plan.cuts[19]! ((DTF.plan.leaves 0x8000089c)[1]!) :=
  leaf_keep (table[19]!) (table[57]'(by decide)) ((leavesAt 0x8000089c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000089c (by decide) (by decide)
theorem DTF.leaf_80000910_0 : LeafGoal DTF.plan DTF.plan.cuts[21]! ((DTF.plan.leaves 0x80000910)[0]!) :=
  leaf_keep (table[21]!) (table[57]'(by decide)) ((leavesAt 0x80000910)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000910 (by decide) (by decide)
theorem DTF.leaf_80000910_1 : LeafGoal DTF.plan DTF.plan.cuts[21]! ((DTF.plan.leaves 0x80000910)[1]!) :=
  leaf_keep (table[21]!) (table[57]'(by decide)) ((leavesAt 0x80000910)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000910 (by decide) (by decide)
theorem DTF.leaf_80000994_0 : LeafGoal DTF.plan DTF.plan.cuts[23]! ((DTF.plan.leaves 0x80000994)[0]!) :=
  leaf_keep (table[23]!) (table[57]'(by decide)) ((leavesAt 0x80000994)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000994 (by decide) (by decide)
theorem DTF.leaf_80000994_1 : LeafGoal DTF.plan DTF.plan.cuts[23]! ((DTF.plan.leaves 0x80000994)[1]!) :=
  leaf_keep (table[23]!) (table[57]'(by decide)) ((leavesAt 0x80000994)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000994 (by decide) (by decide)
theorem DTF.leaf_80000994_2 : LeafGoal DTF.plan DTF.plan.cuts[23]! ((DTF.plan.leaves 0x80000994)[2]!) :=
  leaf_keep (table[23]!) (table[57]'(by decide)) ((leavesAt 0x80000994)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000994 (by decide) (by decide)
theorem DTF.leaf_80000a00_0 : LeafGoal DTF.plan DTF.plan.cuts[25]! ((DTF.plan.leaves 0x80000a00)[0]!) :=
  leaf_keep (table[25]!) (table[57]'(by decide)) ((leavesAt 0x80000a00)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000a00 (by decide) (by decide)
theorem DTF.leaf_80000a00_1 : LeafGoal DTF.plan DTF.plan.cuts[25]! ((DTF.plan.leaves 0x80000a00)[1]!) :=
  leaf_keep (table[25]!) (table[57]'(by decide)) ((leavesAt 0x80000a00)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000a00 (by decide) (by decide)
theorem DTF.leaf_80000a00_3 : LeafGoal DTF.plan DTF.plan.cuts[25]! ((DTF.plan.leaves 0x80000a00)[3]!) :=
  leaf_keep (table[25]!) (table[57]'(by decide)) ((leavesAt 0x80000a00)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000a00 (by decide) (by decide)
theorem DTF.leaf_80000a70_0 : LeafGoal DTF.plan DTF.plan.cuts[27]! ((DTF.plan.leaves 0x80000a70)[0]!) :=
  leaf_keep (table[27]!) (table[57]'(by decide)) ((leavesAt 0x80000a70)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000a70 (by decide) (by decide)
theorem DTF.leaf_80000a70_1 : LeafGoal DTF.plan DTF.plan.cuts[27]! ((DTF.plan.leaves 0x80000a70)[1]!) :=
  leaf_keep (table[27]!) (table[57]'(by decide)) ((leavesAt 0x80000a70)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000a70 (by decide) (by decide)
theorem DTF.leaf_80000af8_0 : LeafGoal DTF.plan DTF.plan.cuts[29]! ((DTF.plan.leaves 0x80000af8)[0]!) :=
  leaf_keep (table[29]!) (table[57]'(by decide)) ((leavesAt 0x80000af8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000af8 (by decide) (by decide)
theorem DTF.leaf_80000af8_1 : LeafGoal DTF.plan DTF.plan.cuts[29]! ((DTF.plan.leaves 0x80000af8)[1]!) :=
  leaf_keep (table[29]!) (table[57]'(by decide)) ((leavesAt 0x80000af8)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000af8 (by decide) (by decide)
theorem DTF.leaf_80000b80_0 : LeafGoal DTF.plan DTF.plan.cuts[31]! ((DTF.plan.leaves 0x80000b80)[0]!) :=
  leaf_keep (table[31]!) (table[57]'(by decide)) ((leavesAt 0x80000b80)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000b80 (by decide) (by decide)
theorem DTF.leaf_80000b80_1 : LeafGoal DTF.plan DTF.plan.cuts[31]! ((DTF.plan.leaves 0x80000b80)[1]!) :=
  leaf_keep (table[31]!) (table[57]'(by decide)) ((leavesAt 0x80000b80)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000b80 (by decide) (by decide)
theorem DTF.leaf_80000b80_2 : LeafGoal DTF.plan DTF.plan.cuts[31]! ((DTF.plan.leaves 0x80000b80)[2]!) :=
  leaf_keep (table[31]!) (table[57]'(by decide)) ((leavesAt 0x80000b80)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000b80 (by decide) (by decide)
theorem DTF.leaf_80000bec_0 : LeafGoal DTF.plan DTF.plan.cuts[33]! ((DTF.plan.leaves 0x80000bec)[0]!) :=
  leaf_keep (table[33]!) (table[57]'(by decide)) ((leavesAt 0x80000bec)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000bec (by decide) (by decide)
theorem DTF.leaf_80000bec_1 : LeafGoal DTF.plan DTF.plan.cuts[33]! ((DTF.plan.leaves 0x80000bec)[1]!) :=
  leaf_keep (table[33]!) (table[57]'(by decide)) ((leavesAt 0x80000bec)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000bec (by decide) (by decide)
theorem DTF.leaf_80000bec_3 : LeafGoal DTF.plan DTF.plan.cuts[33]! ((DTF.plan.leaves 0x80000bec)[3]!) :=
  leaf_keep (table[33]!) (table[57]'(by decide)) ((leavesAt 0x80000bec)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000bec (by decide) (by decide)
theorem DTF.leaf_80000c5c_0 : LeafGoal DTF.plan DTF.plan.cuts[35]! ((DTF.plan.leaves 0x80000c5c)[0]!) :=
  leaf_keep (table[35]!) (table[57]'(by decide)) ((leavesAt 0x80000c5c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000c5c (by decide) (by decide)
theorem DTF.leaf_80000c5c_1 : LeafGoal DTF.plan DTF.plan.cuts[35]! ((DTF.plan.leaves 0x80000c5c)[1]!) :=
  leaf_keep (table[35]!) (table[57]'(by decide)) ((leavesAt 0x80000c5c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000c5c (by decide) (by decide)
theorem DTF.leaf_80000ce4_0 : LeafGoal DTF.plan DTF.plan.cuts[37]! ((DTF.plan.leaves 0x80000ce4)[0]!) :=
  leaf_keep (table[37]!) (table[57]'(by decide)) ((leavesAt 0x80000ce4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000ce4 (by decide) (by decide)
theorem DTF.leaf_80000ce4_1 : LeafGoal DTF.plan DTF.plan.cuts[37]! ((DTF.plan.leaves 0x80000ce4)[1]!) :=
  leaf_keep (table[37]!) (table[57]'(by decide)) ((leavesAt 0x80000ce4)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000ce4 (by decide) (by decide)
theorem DTF.leaf_80000d6c_0 : LeafGoal DTF.plan DTF.plan.cuts[39]! ((DTF.plan.leaves 0x80000d6c)[0]!) :=
  leaf_keep (table[39]!) (table[57]'(by decide)) ((leavesAt 0x80000d6c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000d6c (by decide) (by decide)
theorem DTF.leaf_80000d6c_1 : LeafGoal DTF.plan DTF.plan.cuts[39]! ((DTF.plan.leaves 0x80000d6c)[1]!) :=
  leaf_keep (table[39]!) (table[57]'(by decide)) ((leavesAt 0x80000d6c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000d6c (by decide) (by decide)
theorem DTF.leaf_80000d6c_2 : LeafGoal DTF.plan DTF.plan.cuts[39]! ((DTF.plan.leaves 0x80000d6c)[2]!) :=
  leaf_keep (table[39]!) (table[57]'(by decide)) ((leavesAt 0x80000d6c)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000d6c (by decide) (by decide)
theorem DTF.leaf_80000dd8_0 : LeafGoal DTF.plan DTF.plan.cuts[41]! ((DTF.plan.leaves 0x80000dd8)[0]!) :=
  leaf_keep (table[41]!) (table[57]'(by decide)) ((leavesAt 0x80000dd8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000dd8 (by decide) (by decide)
theorem DTF.leaf_80000dd8_1 : LeafGoal DTF.plan DTF.plan.cuts[41]! ((DTF.plan.leaves 0x80000dd8)[1]!) :=
  leaf_keep (table[41]!) (table[57]'(by decide)) ((leavesAt 0x80000dd8)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000dd8 (by decide) (by decide)
theorem DTF.leaf_80000dd8_3 : LeafGoal DTF.plan DTF.plan.cuts[41]! ((DTF.plan.leaves 0x80000dd8)[3]!) :=
  leaf_keep (table[41]!) (table[57]'(by decide)) ((leavesAt 0x80000dd8)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000dd8 (by decide) (by decide)
theorem DTF.leaf_80000e48_0 : LeafGoal DTF.plan DTF.plan.cuts[43]! ((DTF.plan.leaves 0x80000e48)[0]!) :=
  leaf_keep (table[43]!) (table[57]'(by decide)) ((leavesAt 0x80000e48)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000e48 (by decide) (by decide)
theorem DTF.leaf_80000e48_1 : LeafGoal DTF.plan DTF.plan.cuts[43]! ((DTF.plan.leaves 0x80000e48)[1]!) :=
  leaf_keep (table[43]!) (table[57]'(by decide)) ((leavesAt 0x80000e48)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000e48 (by decide) (by decide)
theorem DTF.leaf_80000ed0_0 : LeafGoal DTF.plan DTF.plan.cuts[45]! ((DTF.plan.leaves 0x80000ed0)[0]!) :=
  leaf_keep (table[45]!) (table[57]'(by decide)) ((leavesAt 0x80000ed0)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000ed0 (by decide) (by decide)
theorem DTF.leaf_80000ed0_1 : LeafGoal DTF.plan DTF.plan.cuts[45]! ((DTF.plan.leaves 0x80000ed0)[1]!) :=
  leaf_keep (table[45]!) (table[57]'(by decide)) ((leavesAt 0x80000ed0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000ed0 (by decide) (by decide)
theorem DTF.leaf_80000f58_0 : LeafGoal DTF.plan DTF.plan.cuts[47]! ((DTF.plan.leaves 0x80000f58)[0]!) :=
  leaf_keep (table[47]!) (table[57]'(by decide)) ((leavesAt 0x80000f58)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000f58 (by decide) (by decide)
theorem DTF.leaf_80000f58_1 : LeafGoal DTF.plan DTF.plan.cuts[47]! ((DTF.plan.leaves 0x80000f58)[1]!) :=
  leaf_keep (table[47]!) (table[57]'(by decide)) ((leavesAt 0x80000f58)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000f58 (by decide) (by decide)
theorem DTF.leaf_80000f58_2 : LeafGoal DTF.plan DTF.plan.cuts[47]! ((DTF.plan.leaves 0x80000f58)[2]!) :=
  leaf_keep (table[47]!) (table[57]'(by decide)) ((leavesAt 0x80000f58)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000f58 (by decide) (by decide)
theorem DTF.leaf_80000fc4_0 : LeafGoal DTF.plan DTF.plan.cuts[49]! ((DTF.plan.leaves 0x80000fc4)[0]!) :=
  leaf_keep (table[49]!) (table[57]'(by decide)) ((leavesAt 0x80000fc4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000fc4 (by decide) (by decide)
theorem DTF.leaf_80000fc4_1 : LeafGoal DTF.plan DTF.plan.cuts[49]! ((DTF.plan.leaves 0x80000fc4)[1]!) :=
  leaf_keep (table[49]!) (table[57]'(by decide)) ((leavesAt 0x80000fc4)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000fc4 (by decide) (by decide)
theorem DTF.leaf_80000fc4_3 : LeafGoal DTF.plan DTF.plan.cuts[49]! ((DTF.plan.leaves 0x80000fc4)[3]!) :=
  leaf_keep (table[49]!) (table[57]'(by decide)) ((leavesAt 0x80000fc4)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80000fc4 (by decide) (by decide)
theorem DTF.leaf_80001034_0 : LeafGoal DTF.plan DTF.plan.cuts[51]! ((DTF.plan.leaves 0x80001034)[0]!) :=
  leaf_keep (table[51]!) (table[57]'(by decide)) ((leavesAt 0x80001034)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001034 (by decide) (by decide)
theorem DTF.leaf_80001034_1 : LeafGoal DTF.plan DTF.plan.cuts[51]! ((DTF.plan.leaves 0x80001034)[1]!) :=
  leaf_keep (table[51]!) (table[57]'(by decide)) ((leavesAt 0x80001034)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001034 (by decide) (by decide)
theorem DTF.leaf_800010b8_0 : LeafGoal DTF.plan DTF.plan.cuts[53]! ((DTF.plan.leaves 0x800010b8)[0]!) :=
  leaf_keep (table[53]!) (table[57]'(by decide)) ((leavesAt 0x800010b8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800010b8 (by decide) (by decide)
theorem DTF.leaf_800010b8_1 : LeafGoal DTF.plan DTF.plan.cuts[53]! ((DTF.plan.leaves 0x800010b8)[1]!) :=
  leaf_keep (table[53]!) (table[57]'(by decide)) ((leavesAt 0x800010b8)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800010b8 (by decide) (by decide)
theorem DTF.leaf_800010b8_2 : LeafGoal DTF.plan DTF.plan.cuts[53]! ((DTF.plan.leaves 0x800010b8)[2]!) :=
  leaf_keep (table[53]!) (table[57]'(by decide)) ((leavesAt 0x800010b8)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800010b8 (by decide) (by decide)
theorem DTF.leaf_80001124_0 : LeafGoal DTF.plan DTF.plan.cuts[55]! ((DTF.plan.leaves 0x80001124)[0]!) :=
  leaf_keep (table[55]!) (table[57]'(by decide)) ((leavesAt 0x80001124)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001124 (by decide) (by decide)
theorem DTF.leaf_80001124_1 : LeafGoal DTF.plan DTF.plan.cuts[55]! ((DTF.plan.leaves 0x80001124)[1]!) :=
  leaf_keep (table[55]!) (table[57]'(by decide)) ((leavesAt 0x80001124)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001124 (by decide) (by decide)
theorem DTF.leaf_80001124_3 : LeafGoal DTF.plan DTF.plan.cuts[55]! ((DTF.plan.leaves 0x80001124)[3]!) :=
  leaf_keep (table[55]!) (table[57]'(by decide)) ((leavesAt 0x80001124)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001124 (by decide) (by decide)
theorem DTF.leaf_800011b4_0 : LeafGoal DTF.plan DTF.plan.cuts[56]! ((DTF.plan.leaves 0x800011b4)[0]!) :=
  leaf_keep (table[56]!) (table[57]'(by decide)) ((leavesAt 0x800011b4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800011b4 (by decide) (by decide)
theorem DTF.leaf_800011b4_1 : LeafGoal DTF.plan DTF.plan.cuts[56]! ((DTF.plan.leaves 0x800011b4)[1]!) :=
  leaf_keep (table[56]!) (table[57]'(by decide)) ((leavesAt 0x800011b4)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800011b4 (by decide) (by decide)
theorem DTF.leaf_800011b4_4 : LeafGoal DTF.plan DTF.plan.cuts[56]! ((DTF.plan.leaves 0x800011b4)[4]!) :=
  leaf_keep (table[56]!) (table[57]'(by decide)) ((leavesAt 0x800011b4)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_800011b4 (by decide) (by decide)
theorem DTF.leaf_800012f0_0 : LeafGoal DTF.plan DTF.plan.cuts[60]! ((DTF.plan.leaves 0x800012f0)[0]!) :=
  leaf_keep (table[60]!) (table[57]'(by decide)) ((leavesAt 0x800012f0)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800012f0 (by decide) (by decide)
theorem DTF.leaf_800012f0_1 : LeafGoal DTF.plan DTF.plan.cuts[60]! ((DTF.plan.leaves 0x800012f0)[1]!) :=
  leaf_keep (table[60]!) (table[57]'(by decide)) ((leavesAt 0x800012f0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800012f0 (by decide) (by decide)
theorem DTF.leaf_800012f0_2 : LeafGoal DTF.plan DTF.plan.cuts[60]! ((DTF.plan.leaves 0x800012f0)[2]!) :=
  leaf_keep (table[60]!) (table[57]'(by decide)) ((leavesAt 0x800012f0)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800012f0 (by decide) (by decide)
theorem DTF.leaf_800013c8_0 : LeafGoal DTF.plan DTF.plan.cuts[62]! ((DTF.plan.leaves 0x800013c8)[0]!) :=
  leaf_keep (table[62]!) (table[63]'(by decide)) ((leavesAt 0x800013c8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800013c8 (by decide) (by decide)
theorem DTF.leaf_800013c8_1 : LeafGoal DTF.plan DTF.plan.cuts[62]! ((DTF.plan.leaves 0x800013c8)[1]!) :=
  leaf_keep (table[62]!) (table[63]'(by decide)) ((leavesAt 0x800013c8)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800013c8 (by decide) (by decide)
theorem DTF.leaf_800013fc_0 : LeafGoal DTF.plan DTF.plan.cuts[63]! ((DTF.plan.leaves 0x800013fc)[0]!) :=
  leaf_keep (table[63]!) (table[64]'(by decide)) ((leavesAt 0x800013fc)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800013fc (by decide) (by decide)
theorem DTF.leaf_80001468_0 : LeafGoal DTF.plan DTF.plan.cuts[65]! ((DTF.plan.leaves 0x80001468)[0]!) :=
  leaf_keep (table[65]!) (table[57]'(by decide)) ((leavesAt 0x80001468)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001468 (by decide) (by decide)
theorem DTF.leaf_80001468_1 : LeafGoal DTF.plan DTF.plan.cuts[65]! ((DTF.plan.leaves 0x80001468)[1]!) :=
  leaf_keep (table[65]!) (table[57]'(by decide)) ((leavesAt 0x80001468)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001468 (by decide) (by decide)
theorem DTF.leaf_80001468_2 : LeafGoal DTF.plan DTF.plan.cuts[65]! ((DTF.plan.leaves 0x80001468)[2]!) :=
  leaf_keep (table[65]!) (table[57]'(by decide)) ((leavesAt 0x80001468)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001468 (by decide) (by decide)
theorem DTF.leaf_8000155c_0 : LeafGoal DTF.plan DTF.plan.cuts[67]! ((DTF.plan.leaves 0x8000155c)[0]!) :=
  leaf_keep (table[67]!) (table[57]'(by decide)) ((leavesAt 0x8000155c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000155c (by decide) (by decide)
theorem DTF.leaf_8000155c_1 : LeafGoal DTF.plan DTF.plan.cuts[67]! ((DTF.plan.leaves 0x8000155c)[1]!) :=
  leaf_keep (table[67]!) (table[57]'(by decide)) ((leavesAt 0x8000155c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000155c (by decide) (by decide)
theorem DTF.leaf_8000155c_2 : LeafGoal DTF.plan DTF.plan.cuts[67]! ((DTF.plan.leaves 0x8000155c)[2]!) :=
  leaf_keep (table[67]!) (table[57]'(by decide)) ((leavesAt 0x8000155c)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000155c (by decide) (by decide)
theorem DTF.leaf_80001650_0 : LeafGoal DTF.plan DTF.plan.cuts[69]! ((DTF.plan.leaves 0x80001650)[0]!) :=
  leaf_keep (table[69]!) (table[57]'(by decide)) ((leavesAt 0x80001650)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001650 (by decide) (by decide)
theorem DTF.leaf_80001650_1 : LeafGoal DTF.plan DTF.plan.cuts[69]! ((DTF.plan.leaves 0x80001650)[1]!) :=
  leaf_keep (table[69]!) (table[57]'(by decide)) ((leavesAt 0x80001650)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001650 (by decide) (by decide)
theorem DTF.leaf_80001650_2 : LeafGoal DTF.plan DTF.plan.cuts[69]! ((DTF.plan.leaves 0x80001650)[2]!) :=
  leaf_keep (table[69]!) (table[57]'(by decide)) ((leavesAt 0x80001650)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001650 (by decide) (by decide)
theorem DTF.leaf_80001708_1 : LeafGoal DTF.plan DTF.plan.cuts[71]! ((DTF.plan.leaves 0x80001708)[1]!) :=
  leaf_keep (table[71]!) (table[63]'(by decide)) ((leavesAt 0x80001708)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001708 (by decide) (by decide)
theorem DTF.leaf_80001748_0 : LeafGoal DTF.plan DTF.plan.cuts[72]! ((DTF.plan.leaves 0x80001748)[0]!) :=
  leaf_keep (table[72]!) (table[63]'(by decide)) ((leavesAt 0x80001748)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001748 (by decide) (by decide)
theorem DTF.leaf_80001748_1 : LeafGoal DTF.plan DTF.plan.cuts[72]! ((DTF.plan.leaves 0x80001748)[1]!) :=
  leaf_keep (table[72]!) (table[63]'(by decide)) ((leavesAt 0x80001748)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001748 (by decide) (by decide)
theorem DTF.leaf_800017a0_1 : LeafGoal DTF.plan DTF.plan.cuts[73]! ((DTF.plan.leaves 0x800017a0)[1]!) :=
  leaf_keep (table[73]!) (table[63]'(by decide)) ((leavesAt 0x800017a0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800017a0 (by decide) (by decide)
theorem DTF.leaf_800017d8_0 : LeafGoal DTF.plan DTF.plan.cuts[75]! ((DTF.plan.leaves 0x800017d8)[0]!) :=
  leaf_keep (table[75]!) (table[63]'(by decide)) ((leavesAt 0x800017d8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800017d8 (by decide) (by decide)
theorem DTF.leaf_800017d8_1 : LeafGoal DTF.plan DTF.plan.cuts[75]! ((DTF.plan.leaves 0x800017d8)[1]!) :=
  leaf_keep (table[75]!) (table[63]'(by decide)) ((leavesAt 0x800017d8)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800017d8 (by decide) (by decide)
theorem DTF.leaf_800017d8_2 : LeafGoal DTF.plan DTF.plan.cuts[75]! ((DTF.plan.leaves 0x800017d8)[2]!) :=
  leaf_keep (table[75]!) (table[63]'(by decide)) ((leavesAt 0x800017d8)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800017d8 (by decide) (by decide)
theorem DTF.leaf_800018a4_0 : LeafGoal DTF.plan DTF.plan.cuts[77]! ((DTF.plan.leaves 0x800018a4)[0]!) :=
  leaf_keep (table[77]!) (table[63]'(by decide)) ((leavesAt 0x800018a4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800018a4 (by decide) (by decide)
theorem DTF.leaf_800018a4_1 : LeafGoal DTF.plan DTF.plan.cuts[77]! ((DTF.plan.leaves 0x800018a4)[1]!) :=
  leaf_keep (table[77]!) (table[63]'(by decide)) ((leavesAt 0x800018a4)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800018a4 (by decide) (by decide)
theorem DTF.leaf_800018fc_1 : LeafGoal DTF.plan DTF.plan.cuts[78]! ((DTF.plan.leaves 0x800018fc)[1]!) :=
  leaf_keep (table[78]!) (table[63]'(by decide)) ((leavesAt 0x800018fc)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800018fc (by decide) (by decide)
theorem DTF.leaf_80001940_0 : LeafGoal DTF.plan DTF.plan.cuts[79]! ((DTF.plan.leaves 0x80001940)[0]!) :=
  leaf_keep (table[79]!) (table[63]'(by decide)) ((leavesAt 0x80001940)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001940 (by decide) (by decide)
theorem DTF.leaf_80001940_1 : LeafGoal DTF.plan DTF.plan.cuts[79]! ((DTF.plan.leaves 0x80001940)[1]!) :=
  leaf_keep (table[79]!) (table[63]'(by decide)) ((leavesAt 0x80001940)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001940 (by decide) (by decide)
theorem DTF.leaf_80001998_1 : LeafGoal DTF.plan DTF.plan.cuts[80]! ((DTF.plan.leaves 0x80001998)[1]!) :=
  leaf_keep (table[80]!) (table[63]'(by decide)) ((leavesAt 0x80001998)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001998 (by decide) (by decide)
theorem DTF.leaf_800019dc_0 : LeafGoal DTF.plan DTF.plan.cuts[81]! ((DTF.plan.leaves 0x800019dc)[0]!) :=
  leaf_keep (table[81]!) (table[63]'(by decide)) ((leavesAt 0x800019dc)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800019dc (by decide) (by decide)
theorem DTF.leaf_800019dc_1 : LeafGoal DTF.plan DTF.plan.cuts[81]! ((DTF.plan.leaves 0x800019dc)[1]!) :=
  leaf_keep (table[81]!) (table[63]'(by decide)) ((leavesAt 0x800019dc)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800019dc (by decide) (by decide)
theorem DTF.leaf_80001a34_1 : LeafGoal DTF.plan DTF.plan.cuts[82]! ((DTF.plan.leaves 0x80001a34)[1]!) :=
  leaf_keep (table[82]!) (table[63]'(by decide)) ((leavesAt 0x80001a34)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001a34 (by decide) (by decide)
theorem DTF.leaf_80001aa4_0 : LeafGoal DTF.plan DTF.plan.cuts[85]! ((DTF.plan.leaves 0x80001aa4)[0]!) :=
  leaf_keep (table[85]!) (table[63]'(by decide)) ((leavesAt 0x80001aa4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001aa4 (by decide) (by decide)
theorem DTF.leaf_80001aa4_1 : LeafGoal DTF.plan DTF.plan.cuts[85]! ((DTF.plan.leaves 0x80001aa4)[1]!) :=
  leaf_keep (table[85]!) (table[63]'(by decide)) ((leavesAt 0x80001aa4)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001aa4 (by decide) (by decide)
theorem DTF.leaf_80001aa4_2 : LeafGoal DTF.plan DTF.plan.cuts[85]! ((DTF.plan.leaves 0x80001aa4)[2]!) :=
  leaf_keep (table[85]!) (table[63]'(by decide)) ((leavesAt 0x80001aa4)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001aa4 (by decide) (by decide)
theorem DTF.leaf_80001b10_0 : LeafGoal DTF.plan DTF.plan.cuts[87]! ((DTF.plan.leaves 0x80001b10)[0]!) :=
  leaf_keep (table[87]!) (table[63]'(by decide)) ((leavesAt 0x80001b10)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001b10 (by decide) (by decide)
theorem DTF.leaf_80001b10_1 : LeafGoal DTF.plan DTF.plan.cuts[87]! ((DTF.plan.leaves 0x80001b10)[1]!) :=
  leaf_keep (table[87]!) (table[63]'(by decide)) ((leavesAt 0x80001b10)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001b10 (by decide) (by decide)
theorem DTF.leaf_80001b10_2 : LeafGoal DTF.plan DTF.plan.cuts[87]! ((DTF.plan.leaves 0x80001b10)[2]!) :=
  leaf_keep (table[87]!) (table[63]'(by decide)) ((leavesAt 0x80001b10)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001b10 (by decide) (by decide)
theorem DTF.leaf_80001bcc_0 : LeafGoal DTF.plan DTF.plan.cuts[89]! ((DTF.plan.leaves 0x80001bcc)[0]!) :=
  leaf_keep (table[89]!) (table[63]'(by decide)) ((leavesAt 0x80001bcc)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001bcc (by decide) (by decide)
theorem DTF.leaf_80001bcc_1 : LeafGoal DTF.plan DTF.plan.cuts[89]! ((DTF.plan.leaves 0x80001bcc)[1]!) :=
  leaf_keep (table[89]!) (table[63]'(by decide)) ((leavesAt 0x80001bcc)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001bcc (by decide) (by decide)
theorem DTF.leaf_80001bcc_2 : LeafGoal DTF.plan DTF.plan.cuts[89]! ((DTF.plan.leaves 0x80001bcc)[2]!) :=
  leaf_keep (table[89]!) (table[63]'(by decide)) ((leavesAt 0x80001bcc)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001bcc (by decide) (by decide)
theorem DTF.leaf_80001ccc_0 : LeafGoal DTF.plan DTF.plan.cuts[93]! ((DTF.plan.leaves 0x80001ccc)[0]!) :=
  leaf_keep (table[93]!) (table[63]'(by decide)) ((leavesAt 0x80001ccc)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001ccc (by decide) (by decide)
theorem DTF.leaf_80001ccc_1 : LeafGoal DTF.plan DTF.plan.cuts[93]! ((DTF.plan.leaves 0x80001ccc)[1]!) :=
  leaf_keep (table[93]!) (table[63]'(by decide)) ((leavesAt 0x80001ccc)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001ccc (by decide) (by decide)
theorem DTF.leaf_80001d88_0 : LeafGoal DTF.plan DTF.plan.cuts[96]! ((DTF.plan.leaves 0x80001d88)[0]!) :=
  leaf_keep (table[96]!) (table[63]'(by decide)) ((leavesAt 0x80001d88)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001d88 (by decide) (by decide)
theorem DTF.leaf_80001d88_1 : LeafGoal DTF.plan DTF.plan.cuts[96]! ((DTF.plan.leaves 0x80001d88)[1]!) :=
  leaf_keep (table[96]!) (table[63]'(by decide)) ((leavesAt 0x80001d88)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001d88 (by decide) (by decide)
theorem DTF.leaf_80001d88_2 : LeafGoal DTF.plan DTF.plan.cuts[96]! ((DTF.plan.leaves 0x80001d88)[2]!) :=
  leaf_keep (table[96]!) (table[63]'(by decide)) ((leavesAt 0x80001d88)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001d88 (by decide) (by decide)
theorem DTF.leaf_80001df4_0 : LeafGoal DTF.plan DTF.plan.cuts[98]! ((DTF.plan.leaves 0x80001df4)[0]!) :=
  leaf_keep (table[98]!) (table[63]'(by decide)) ((leavesAt 0x80001df4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001df4 (by decide) (by decide)
theorem DTF.leaf_80001df4_1 : LeafGoal DTF.plan DTF.plan.cuts[98]! ((DTF.plan.leaves 0x80001df4)[1]!) :=
  leaf_keep (table[98]!) (table[63]'(by decide)) ((leavesAt 0x80001df4)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001df4 (by decide) (by decide)
theorem DTF.leaf_80001df4_2 : LeafGoal DTF.plan DTF.plan.cuts[98]! ((DTF.plan.leaves 0x80001df4)[2]!) :=
  leaf_keep (table[98]!) (table[63]'(by decide)) ((leavesAt 0x80001df4)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001df4 (by decide) (by decide)
theorem DTF.leaf_80001ef8_0 : LeafGoal DTF.plan DTF.plan.cuts[102]! ((DTF.plan.leaves 0x80001ef8)[0]!) :=
  leaf_keep (table[102]!) (table[63]'(by decide)) ((leavesAt 0x80001ef8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001ef8 (by decide) (by decide)
theorem DTF.leaf_80001ef8_1 : LeafGoal DTF.plan DTF.plan.cuts[102]! ((DTF.plan.leaves 0x80001ef8)[1]!) :=
  leaf_keep (table[102]!) (table[63]'(by decide)) ((leavesAt 0x80001ef8)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001ef8 (by decide) (by decide)
theorem DTF.leaf_80001fac_0 : LeafGoal DTF.plan DTF.plan.cuts[104]! ((DTF.plan.leaves 0x80001fac)[0]!) :=
  leaf_keep (table[104]!) (table[63]'(by decide)) ((leavesAt 0x80001fac)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001fac (by decide) (by decide)
theorem DTF.leaf_80001fac_1 : LeafGoal DTF.plan DTF.plan.cuts[104]! ((DTF.plan.leaves 0x80001fac)[1]!) :=
  leaf_keep (table[104]!) (table[63]'(by decide)) ((leavesAt 0x80001fac)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001fac (by decide) (by decide)
theorem DTF.leaf_80001fac_2 : LeafGoal DTF.plan DTF.plan.cuts[104]! ((DTF.plan.leaves 0x80001fac)[2]!) :=
  leaf_keep (table[104]!) (table[63]'(by decide)) ((leavesAt 0x80001fac)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001fac (by decide) (by decide)
theorem DTF.leaf_80001fac_3 : LeafGoal DTF.plan DTF.plan.cuts[104]! ((DTF.plan.leaves 0x80001fac)[3]!) :=
  leaf_keep (table[104]!) (table[152]'(by decide)) ((leavesAt 0x80001fac)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001fac (by decide) (by decide)
theorem DTF.leaf_80001fac_4 : LeafGoal DTF.plan DTF.plan.cuts[104]! ((DTF.plan.leaves 0x80001fac)[4]!) :=
  leaf_keep (table[104]!) (table[152]'(by decide)) ((leavesAt 0x80001fac)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001fac (by decide) (by decide)
theorem DTF.leaf_80001fac_5 : LeafGoal DTF.plan DTF.plan.cuts[104]! ((DTF.plan.leaves 0x80001fac)[5]!) :=
  leaf_keep (table[104]!) (table[151]'(by decide)) ((leavesAt 0x80001fac)[5]!) (List.getElem_mem _)
    (by decide) DTF.cut_80001fac (by decide) (by decide)
theorem DTF.leaf_80002064_0 : LeafGoal DTF.plan DTF.plan.cuts[106]! ((DTF.plan.leaves 0x80002064)[0]!) :=
  leaf_keep (table[106]!) (table[63]'(by decide)) ((leavesAt 0x80002064)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002064 (by decide) (by decide)
theorem DTF.leaf_80002064_1 : LeafGoal DTF.plan DTF.plan.cuts[106]! ((DTF.plan.leaves 0x80002064)[1]!) :=
  leaf_keep (table[106]!) (table[63]'(by decide)) ((leavesAt 0x80002064)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002064 (by decide) (by decide)
theorem DTF.leaf_800020c0_0 : LeafGoal DTF.plan DTF.plan.cuts[108]! ((DTF.plan.leaves 0x800020c0)[0]!) :=
  leaf_keep (table[108]!) (table[63]'(by decide)) ((leavesAt 0x800020c0)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800020c0 (by decide) (by decide)
theorem DTF.leaf_800020c0_1 : LeafGoal DTF.plan DTF.plan.cuts[108]! ((DTF.plan.leaves 0x800020c0)[1]!) :=
  leaf_keep (table[108]!) (table[63]'(by decide)) ((leavesAt 0x800020c0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800020c0 (by decide) (by decide)
theorem DTF.leaf_800020c0_2 : LeafGoal DTF.plan DTF.plan.cuts[108]! ((DTF.plan.leaves 0x800020c0)[2]!) :=
  leaf_keep (table[108]!) (table[63]'(by decide)) ((leavesAt 0x800020c0)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800020c0 (by decide) (by decide)
theorem DTF.leaf_800021b0_0 : LeafGoal DTF.plan DTF.plan.cuts[112]! ((DTF.plan.leaves 0x800021b0)[0]!) :=
  leaf_keep (table[112]!) (table[63]'(by decide)) ((leavesAt 0x800021b0)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800021b0 (by decide) (by decide)
theorem DTF.leaf_800021b0_1 : LeafGoal DTF.plan DTF.plan.cuts[112]! ((DTF.plan.leaves 0x800021b0)[1]!) :=
  leaf_keep (table[112]!) (table[63]'(by decide)) ((leavesAt 0x800021b0)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800021b0 (by decide) (by decide)
theorem DTF.leaf_800021b0_2 : LeafGoal DTF.plan DTF.plan.cuts[112]! ((DTF.plan.leaves 0x800021b0)[2]!) :=
  leaf_keep (table[112]!) (table[63]'(by decide)) ((leavesAt 0x800021b0)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800021b0 (by decide) (by decide)
theorem DTF.leaf_8000221c_0 : LeafGoal DTF.plan DTF.plan.cuts[114]! ((DTF.plan.leaves 0x8000221c)[0]!) :=
  leaf_keep (table[114]!) (table[63]'(by decide)) ((leavesAt 0x8000221c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000221c (by decide) (by decide)
theorem DTF.leaf_8000221c_1 : LeafGoal DTF.plan DTF.plan.cuts[114]! ((DTF.plan.leaves 0x8000221c)[1]!) :=
  leaf_keep (table[114]!) (table[63]'(by decide)) ((leavesAt 0x8000221c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000221c (by decide) (by decide)
theorem DTF.leaf_8000221c_2 : LeafGoal DTF.plan DTF.plan.cuts[114]! ((DTF.plan.leaves 0x8000221c)[2]!) :=
  leaf_keep (table[114]!) (table[63]'(by decide)) ((leavesAt 0x8000221c)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000221c (by decide) (by decide)
theorem DTF.leaf_800022e4_0 : LeafGoal DTF.plan DTF.plan.cuts[116]! ((DTF.plan.leaves 0x800022e4)[0]!) :=
  leaf_keep (table[116]!) (table[153]'(by decide)) ((leavesAt 0x800022e4)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_800022e4 (by decide) (by decide)
theorem DTF.leaf_800022e4_2 : LeafGoal DTF.plan DTF.plan.cuts[116]! ((DTF.plan.leaves 0x800022e4)[2]!) :=
  leaf_keep (table[116]!) (table[63]'(by decide)) ((leavesAt 0x800022e4)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800022e4 (by decide) (by decide)
theorem DTF.leaf_800022e4_3 : LeafGoal DTF.plan DTF.plan.cuts[116]! ((DTF.plan.leaves 0x800022e4)[3]!) :=
  leaf_keep (table[116]!) (table[117]'(by decide)) ((leavesAt 0x800022e4)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_800022e4 (by decide) (by decide)
theorem DTF.leaf_8000230c_0 : LeafGoal DTF.plan DTF.plan.cuts[118]! ((DTF.plan.leaves 0x8000230c)[0]!) :=
  leaf_keep (table[118]!) (table[63]'(by decide)) ((leavesAt 0x8000230c)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000230c (by decide) (by decide)
theorem DTF.leaf_8000230c_1 : LeafGoal DTF.plan DTF.plan.cuts[118]! ((DTF.plan.leaves 0x8000230c)[1]!) :=
  leaf_keep (table[118]!) (table[63]'(by decide)) ((leavesAt 0x8000230c)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000230c (by decide) (by decide)
theorem DTF.leaf_8000230c_2 : LeafGoal DTF.plan DTF.plan.cuts[118]! ((DTF.plan.leaves 0x8000230c)[2]!) :=
  leaf_keep (table[118]!) (table[63]'(by decide)) ((leavesAt 0x8000230c)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000230c (by decide) (by decide)
theorem DTF.leaf_80002378_0 : LeafGoal DTF.plan DTF.plan.cuts[120]! ((DTF.plan.leaves 0x80002378)[0]!) :=
  leaf_keep (table[120]!) (table[63]'(by decide)) ((leavesAt 0x80002378)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002378 (by decide) (by decide)
theorem DTF.leaf_80002378_1 : LeafGoal DTF.plan DTF.plan.cuts[120]! ((DTF.plan.leaves 0x80002378)[1]!) :=
  leaf_keep (table[120]!) (table[63]'(by decide)) ((leavesAt 0x80002378)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002378 (by decide) (by decide)
theorem DTF.leaf_80002378_2 : LeafGoal DTF.plan DTF.plan.cuts[120]! ((DTF.plan.leaves 0x80002378)[2]!) :=
  leaf_keep (table[120]!) (table[63]'(by decide)) ((leavesAt 0x80002378)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002378 (by decide) (by decide)
theorem DTF.leaf_800024ec_1 : LeafGoal DTF.plan DTF.plan.cuts[126]! ((DTF.plan.leaves 0x800024ec)[1]!) :=
  leaf_keep (table[126]!) (table[63]'(by decide)) ((leavesAt 0x800024ec)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_800024ec (by decide) (by decide)
theorem DTF.leaf_800024ec_2 : LeafGoal DTF.plan DTF.plan.cuts[126]! ((DTF.plan.leaves 0x800024ec)[2]!) :=
  leaf_keep (table[126]!) (table[63]'(by decide)) ((leavesAt 0x800024ec)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800024ec (by decide) (by decide)
theorem DTF.leaf_8000252c_2 : LeafGoal DTF.plan DTF.plan.cuts[127]! ((DTF.plan.leaves 0x8000252c)[2]!) :=
  leaf_keep (table[127]!) (table[63]'(by decide)) ((leavesAt 0x8000252c)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000252c (by decide) (by decide)
theorem DTF.leaf_8000252c_3 : LeafGoal DTF.plan DTF.plan.cuts[127]! ((DTF.plan.leaves 0x8000252c)[3]!) :=
  leaf_keep (table[127]!) (table[63]'(by decide)) ((leavesAt 0x8000252c)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000252c (by decide) (by decide)
theorem DTF.leaf_8000252c_4 : LeafGoal DTF.plan DTF.plan.cuts[127]! ((DTF.plan.leaves 0x8000252c)[4]!) :=
  leaf_keep (table[127]!) (table[63]'(by decide)) ((leavesAt 0x8000252c)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_8000252c (by decide) (by decide)
theorem DTF.leaf_80002600_1 : LeafGoal DTF.plan DTF.plan.cuts[129]! ((DTF.plan.leaves 0x80002600)[1]!) :=
  leaf_keep (table[129]!) (table[63]'(by decide)) ((leavesAt 0x80002600)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002600 (by decide) (by decide)
theorem DTF.leaf_80002600_2 : LeafGoal DTF.plan DTF.plan.cuts[129]! ((DTF.plan.leaves 0x80002600)[2]!) :=
  leaf_keep (table[129]!) (table[63]'(by decide)) ((leavesAt 0x80002600)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002600 (by decide) (by decide)
theorem DTF.leaf_80002600_3 : LeafGoal DTF.plan DTF.plan.cuts[129]! ((DTF.plan.leaves 0x80002600)[3]!) :=
  leaf_keep (table[129]!) (table[63]'(by decide)) ((leavesAt 0x80002600)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002600 (by decide) (by decide)
theorem DTF.leaf_80002654_2 : LeafGoal DTF.plan DTF.plan.cuts[130]! ((DTF.plan.leaves 0x80002654)[2]!) :=
  leaf_keep (table[130]!) (table[63]'(by decide)) ((leavesAt 0x80002654)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002654 (by decide) (by decide)
theorem DTF.leaf_80002654_3 : LeafGoal DTF.plan DTF.plan.cuts[130]! ((DTF.plan.leaves 0x80002654)[3]!) :=
  leaf_keep (table[130]!) (table[63]'(by decide)) ((leavesAt 0x80002654)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002654 (by decide) (by decide)
theorem DTF.leaf_80002654_4 : LeafGoal DTF.plan DTF.plan.cuts[130]! ((DTF.plan.leaves 0x80002654)[4]!) :=
  leaf_keep (table[130]!) (table[63]'(by decide)) ((leavesAt 0x80002654)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002654 (by decide) (by decide)
theorem DTF.leaf_800026d4_2 : LeafGoal DTF.plan DTF.plan.cuts[132]! ((DTF.plan.leaves 0x800026d4)[2]!) :=
  leaf_keep (table[132]!) (table[63]'(by decide)) ((leavesAt 0x800026d4)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_800026d4 (by decide) (by decide)
theorem DTF.leaf_800026d4_3 : LeafGoal DTF.plan DTF.plan.cuts[132]! ((DTF.plan.leaves 0x800026d4)[3]!) :=
  leaf_keep (table[132]!) (table[63]'(by decide)) ((leavesAt 0x800026d4)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_800026d4 (by decide) (by decide)
theorem DTF.leaf_800026d4_4 : LeafGoal DTF.plan DTF.plan.cuts[132]! ((DTF.plan.leaves 0x800026d4)[4]!) :=
  leaf_keep (table[132]!) (table[63]'(by decide)) ((leavesAt 0x800026d4)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_800026d4 (by decide) (by decide)
theorem DTF.leaf_80002754_2 : LeafGoal DTF.plan DTF.plan.cuts[134]! ((DTF.plan.leaves 0x80002754)[2]!) :=
  leaf_keep (table[134]!) (table[63]'(by decide)) ((leavesAt 0x80002754)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002754 (by decide) (by decide)
theorem DTF.leaf_80002754_3 : LeafGoal DTF.plan DTF.plan.cuts[134]! ((DTF.plan.leaves 0x80002754)[3]!) :=
  leaf_keep (table[134]!) (table[63]'(by decide)) ((leavesAt 0x80002754)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002754 (by decide) (by decide)
theorem DTF.leaf_80002754_4 : LeafGoal DTF.plan DTF.plan.cuts[134]! ((DTF.plan.leaves 0x80002754)[4]!) :=
  leaf_keep (table[134]!) (table[63]'(by decide)) ((leavesAt 0x80002754)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002754 (by decide) (by decide)
theorem DTF.leaf_80002820_5 : LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[5]!) :=
  leaf_keep (table[136]!) (table[63]'(by decide)) ((leavesAt 0x80002820)[5]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002820 (by decide) (by decide)
theorem DTF.leaf_80002820_6 : LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[6]!) :=
  leaf_keep (table[136]!) (table[63]'(by decide)) ((leavesAt 0x80002820)[6]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002820 (by decide) (by decide)
theorem DTF.leaf_80002820_7 : LeafGoal DTF.plan DTF.plan.cuts[136]! ((DTF.plan.leaves 0x80002820)[7]!) :=
  leaf_keep (table[136]!) (table[63]'(by decide)) ((leavesAt 0x80002820)[7]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002820 (by decide) (by decide)
theorem DTF.leaf_800029c8_3 : LeafGoal DTF.plan DTF.plan.cuts[140]! ((DTF.plan.leaves 0x800029c8)[3]!) :=
  leaf_keep (table[140]!) (table[63]'(by decide)) ((leavesAt 0x800029c8)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_800029c8 (by decide) (by decide)
theorem DTF.leaf_80002a08_1 : LeafGoal DTF.plan DTF.plan.cuts[141]! ((DTF.plan.leaves 0x80002a08)[1]!) :=
  leaf_keep (table[141]!) (table[63]'(by decide)) ((leavesAt 0x80002a08)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002a08 (by decide) (by decide)
theorem DTF.leaf_80002b50_0 : LeafGoal DTF.plan DTF.plan.cuts[145]! ((DTF.plan.leaves 0x80002b50)[0]!) :=
  leaf_keep (table[145]!) (table[151]'(by decide)) ((leavesAt 0x80002b50)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002b50 (by decide) (by decide)
theorem DTF.leaf_80002b50_2 : LeafGoal DTF.plan DTF.plan.cuts[145]! ((DTF.plan.leaves 0x80002b50)[2]!) :=
  leaf_keep (table[145]!) (table[63]'(by decide)) ((leavesAt 0x80002b50)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002b50 (by decide) (by decide)
theorem DTF.leaf_80002b50_3 : LeafGoal DTF.plan DTF.plan.cuts[145]! ((DTF.plan.leaves 0x80002b50)[3]!) :=
  leaf_keep (table[145]!) (table[63]'(by decide)) ((leavesAt 0x80002b50)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002b50 (by decide) (by decide)
theorem DTF.leaf_80002b50_4 : LeafGoal DTF.plan DTF.plan.cuts[145]! ((DTF.plan.leaves 0x80002b50)[4]!) :=
  leaf_keep (table[145]!) (table[63]'(by decide)) ((leavesAt 0x80002b50)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002b50 (by decide) (by decide)
theorem DTF.leaf_80002c68_0 : LeafGoal DTF.plan DTF.plan.cuts[147]! ((DTF.plan.leaves 0x80002c68)[0]!) :=
  leaf_keep (table[147]!) (table[153]'(by decide)) ((leavesAt 0x80002c68)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002c68 (by decide) (by decide)
theorem DTF.leaf_80002c68_1 : LeafGoal DTF.plan DTF.plan.cuts[147]! ((DTF.plan.leaves 0x80002c68)[1]!) :=
  leaf_keep (table[147]!) (table[63]'(by decide)) ((leavesAt 0x80002c68)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002c68 (by decide) (by decide)
theorem DTF.leaf_80002c94_0 : LeafGoal DTF.plan DTF.plan.cuts[148]! ((DTF.plan.leaves 0x80002c94)[0]!) :=
  leaf_keep (table[148]!) (table[150]'(by decide)) ((leavesAt 0x80002c94)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002c94 (by decide) (by decide)
theorem DTF.leaf_80002c94_2 : LeafGoal DTF.plan DTF.plan.cuts[148]! ((DTF.plan.leaves 0x80002c94)[2]!) :=
  leaf_keep (table[148]!) (table[63]'(by decide)) ((leavesAt 0x80002c94)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002c94 (by decide) (by decide)
theorem DTF.leaf_80002c94_3 : LeafGoal DTF.plan DTF.plan.cuts[148]! ((DTF.plan.leaves 0x80002c94)[3]!) :=
  leaf_keep (table[148]!) (table[63]'(by decide)) ((leavesAt 0x80002c94)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002c94 (by decide) (by decide)
theorem DTF.leaf_80002c94_4 : LeafGoal DTF.plan DTF.plan.cuts[148]! ((DTF.plan.leaves 0x80002c94)[4]!) :=
  leaf_keep (table[148]!) (table[63]'(by decide)) ((leavesAt 0x80002c94)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002c94 (by decide) (by decide)
theorem DTF.leaf_80002db8_0 : LeafGoal DTF.plan DTF.plan.cuts[150]! ((DTF.plan.leaves 0x80002db8)[0]!) :=
  leaf_keep (table[150]!) (table[151]'(by decide)) ((leavesAt 0x80002db8)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002db8 (by decide) (by decide)
theorem DTF.leaf_80002dbc_0 : LeafGoal DTF.plan DTF.plan.cuts[151]! ((DTF.plan.leaves 0x80002dbc)[0]!) :=
  leaf_keep (table[151]!) (table[152]'(by decide)) ((leavesAt 0x80002dbc)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002dbc (by decide) (by decide)
theorem DTF.leaf_80002f54_0 : LeafGoal DTF.plan DTF.plan.cuts[156]! ((DTF.plan.leaves 0x80002f54)[0]!) :=
  leaf_keep (table[156]!) (table[116]'(by decide)) ((leavesAt 0x80002f54)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002f54 (by decide) (by decide)
theorem DTF.leaf_80002f54_1 : LeafGoal DTF.plan DTF.plan.cuts[156]! ((DTF.plan.leaves 0x80002f54)[1]!) :=
  leaf_keep (table[156]!) (table[116]'(by decide)) ((leavesAt 0x80002f54)[1]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002f54 (by decide) (by decide)
theorem DTF.leaf_80002f90_0 : LeafGoal DTF.plan DTF.plan.cuts[157]! ((DTF.plan.leaves 0x80002f90)[0]!) :=
  leaf_keep (table[157]!) (table[150]'(by decide)) ((leavesAt 0x80002f90)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002f90 (by decide) (by decide)
theorem DTF.leaf_80002f90_2 : LeafGoal DTF.plan DTF.plan.cuts[157]! ((DTF.plan.leaves 0x80002f90)[2]!) :=
  leaf_keep (table[157]!) (table[63]'(by decide)) ((leavesAt 0x80002f90)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002f90 (by decide) (by decide)
theorem DTF.leaf_80002f90_3 : LeafGoal DTF.plan DTF.plan.cuts[157]! ((DTF.plan.leaves 0x80002f90)[3]!) :=
  leaf_keep (table[157]!) (table[63]'(by decide)) ((leavesAt 0x80002f90)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002f90 (by decide) (by decide)
theorem DTF.leaf_80002f90_4 : LeafGoal DTF.plan DTF.plan.cuts[157]! ((DTF.plan.leaves 0x80002f90)[4]!) :=
  leaf_keep (table[157]!) (table[63]'(by decide)) ((leavesAt 0x80002f90)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80002f90 (by decide) (by decide)
theorem DTF.leaf_80003064_0 : LeafGoal DTF.plan DTF.plan.cuts[159]! ((DTF.plan.leaves 0x80003064)[0]!) :=
  leaf_keep (table[159]!) (table[152]'(by decide)) ((leavesAt 0x80003064)[0]!) (List.getElem_mem _)
    (by decide) DTF.cut_80003064 (by decide) (by decide)
theorem DTF.leaf_80003064_2 : LeafGoal DTF.plan DTF.plan.cuts[159]! ((DTF.plan.leaves 0x80003064)[2]!) :=
  leaf_keep (table[159]!) (table[63]'(by decide)) ((leavesAt 0x80003064)[2]!) (List.getElem_mem _)
    (by decide) DTF.cut_80003064 (by decide) (by decide)
theorem DTF.leaf_80003064_3 : LeafGoal DTF.plan DTF.plan.cuts[159]! ((DTF.plan.leaves 0x80003064)[3]!) :=
  leaf_keep (table[159]!) (table[63]'(by decide)) ((leavesAt 0x80003064)[3]!) (List.getElem_mem _)
    (by decide) DTF.cut_80003064 (by decide) (by decide)
theorem DTF.leaf_80003064_4 : LeafGoal DTF.plan DTF.plan.cuts[159]! ((DTF.plan.leaves 0x80003064)[4]!) :=
  leaf_keep (table[159]!) (table[63]'(by decide)) ((leavesAt 0x80003064)[4]!) (List.getElem_mem _)
    (by decide) DTF.cut_80003064 (by decide) (by decide)

end ZesuExec.Fn.DTF
