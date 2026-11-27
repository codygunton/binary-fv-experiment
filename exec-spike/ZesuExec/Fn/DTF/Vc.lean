import ZesuExec.Fn.DTF.Cuts

/-!
# DTF plan and automation (programme plan S7 step 3)

`zesu_plan DTF`, the run equations under the names `zesu_assemble` takes (`DTF.run_<pc>`, the
`sym_run` theorems of `Runs.lean`; without them the kernel would re-evaluate all 161 runs in
`DTF.reach_from`), and `zesu_auto DTF`. Hand-written items are in `Leaves.lean`, the assembly in
`Reach.lean`.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Vc

zesu_plan DTF := vcPlan

theorem DTF.run_8000050c : run zesuImage cutPcs 300 0x8000050c (stateAt 0x8000050c) = some run_8000050c_leaves := _root_.ZesuExec.Fn.DTF.run_8000050c
theorem DTF.run_80000574 : run zesuImage cutPcs 300 0x80000574 (stateAt 0x80000574) = some run_80000574_leaves := _root_.ZesuExec.Fn.DTF.run_80000574
theorem DTF.run_80000588 : run zesuImage cutPcs 300 0x80000588 (stateAt 0x80000588) = some run_80000588_leaves := _root_.ZesuExec.Fn.DTF.run_80000588
theorem DTF.run_8000059c : run zesuImage cutPcs 300 0x8000059c (stateAt 0x8000059c) = some run_8000059c_leaves := _root_.ZesuExec.Fn.DTF.run_8000059c
theorem DTF.run_800005dc : run zesuImage cutPcs 300 0x800005dc (stateAt 0x800005dc) = some run_800005dc_leaves := _root_.ZesuExec.Fn.DTF.run_800005dc
theorem DTF.run_800005f0 : run zesuImage cutPcs 300 0x800005f0 (stateAt 0x800005f0) = some run_800005f0_leaves := _root_.ZesuExec.Fn.DTF.run_800005f0
theorem DTF.run_80000634 : run zesuImage cutPcs 300 0x80000634 (stateAt 0x80000634) = some run_80000634_leaves := _root_.ZesuExec.Fn.DTF.run_80000634
theorem DTF.run_8000065c : run zesuImage cutPcs 300 0x8000065c (stateAt 0x8000065c) = some run_8000065c_leaves := _root_.ZesuExec.Fn.DTF.run_8000065c
theorem DTF.run_8000069c : run zesuImage cutPcs 300 0x8000069c (stateAt 0x8000069c) = some run_8000069c_leaves := _root_.ZesuExec.Fn.DTF.run_8000069c
theorem DTF.run_800006b0 : run zesuImage cutPcs 300 0x800006b0 (stateAt 0x800006b0) = some run_800006b0_leaves := _root_.ZesuExec.Fn.DTF.run_800006b0
theorem DTF.run_800006f4 : run zesuImage cutPcs 300 0x800006f4 (stateAt 0x800006f4) = some run_800006f4_leaves := _root_.ZesuExec.Fn.DTF.run_800006f4
theorem DTF.run_8000071c : run zesuImage cutPcs 300 0x8000071c (stateAt 0x8000071c) = some run_8000071c_leaves := _root_.ZesuExec.Fn.DTF.run_8000071c
theorem DTF.run_8000075c : run zesuImage cutPcs 300 0x8000075c (stateAt 0x8000075c) = some run_8000075c_leaves := _root_.ZesuExec.Fn.DTF.run_8000075c
theorem DTF.run_80000770 : run zesuImage cutPcs 300 0x80000770 (stateAt 0x80000770) = some run_80000770_leaves := _root_.ZesuExec.Fn.DTF.run_80000770
theorem DTF.run_800007b4 : run zesuImage cutPcs 300 0x800007b4 (stateAt 0x800007b4) = some run_800007b4_leaves := _root_.ZesuExec.Fn.DTF.run_800007b4
theorem DTF.run_800007dc : run zesuImage cutPcs 300 0x800007dc (stateAt 0x800007dc) = some run_800007dc_leaves := _root_.ZesuExec.Fn.DTF.run_800007dc
theorem DTF.run_8000081c : run zesuImage cutPcs 300 0x8000081c (stateAt 0x8000081c) = some run_8000081c_leaves := _root_.ZesuExec.Fn.DTF.run_8000081c
theorem DTF.run_80000830 : run zesuImage cutPcs 300 0x80000830 (stateAt 0x80000830) = some run_80000830_leaves := _root_.ZesuExec.Fn.DTF.run_80000830
theorem DTF.run_80000874 : run zesuImage cutPcs 300 0x80000874 (stateAt 0x80000874) = some run_80000874_leaves := _root_.ZesuExec.Fn.DTF.run_80000874
theorem DTF.run_8000089c : run zesuImage cutPcs 300 0x8000089c (stateAt 0x8000089c) = some run_8000089c_leaves := _root_.ZesuExec.Fn.DTF.run_8000089c
theorem DTF.run_800008e8 : run zesuImage cutPcs 300 0x800008e8 (stateAt 0x800008e8) = some run_800008e8_leaves := _root_.ZesuExec.Fn.DTF.run_800008e8
theorem DTF.run_80000910 : run zesuImage cutPcs 300 0x80000910 (stateAt 0x80000910) = some run_80000910_leaves := _root_.ZesuExec.Fn.DTF.run_80000910
theorem DTF.run_80000960 : run zesuImage cutPcs 300 0x80000960 (stateAt 0x80000960) = some run_80000960_leaves := _root_.ZesuExec.Fn.DTF.run_80000960
theorem DTF.run_80000994 : run zesuImage cutPcs 300 0x80000994 (stateAt 0x80000994) = some run_80000994_leaves := _root_.ZesuExec.Fn.DTF.run_80000994
theorem DTF.run_800009d8 : run zesuImage cutPcs 300 0x800009d8 (stateAt 0x800009d8) = some run_800009d8_leaves := _root_.ZesuExec.Fn.DTF.run_800009d8
theorem DTF.run_80000a00 : run zesuImage cutPcs 300 0x80000a00 (stateAt 0x80000a00) = some run_80000a00_leaves := _root_.ZesuExec.Fn.DTF.run_80000a00
theorem DTF.run_80000a48 : run zesuImage cutPcs 300 0x80000a48 (stateAt 0x80000a48) = some run_80000a48_leaves := _root_.ZesuExec.Fn.DTF.run_80000a48
theorem DTF.run_80000a70 : run zesuImage cutPcs 300 0x80000a70 (stateAt 0x80000a70) = some run_80000a70_leaves := _root_.ZesuExec.Fn.DTF.run_80000a70
theorem DTF.run_80000ac4 : run zesuImage cutPcs 300 0x80000ac4 (stateAt 0x80000ac4) = some run_80000ac4_leaves := _root_.ZesuExec.Fn.DTF.run_80000ac4
theorem DTF.run_80000af8 : run zesuImage cutPcs 300 0x80000af8 (stateAt 0x80000af8) = some run_80000af8_leaves := _root_.ZesuExec.Fn.DTF.run_80000af8
theorem DTF.run_80000b4c : run zesuImage cutPcs 300 0x80000b4c (stateAt 0x80000b4c) = some run_80000b4c_leaves := _root_.ZesuExec.Fn.DTF.run_80000b4c
theorem DTF.run_80000b80 : run zesuImage cutPcs 300 0x80000b80 (stateAt 0x80000b80) = some run_80000b80_leaves := _root_.ZesuExec.Fn.DTF.run_80000b80
theorem DTF.run_80000bc4 : run zesuImage cutPcs 300 0x80000bc4 (stateAt 0x80000bc4) = some run_80000bc4_leaves := _root_.ZesuExec.Fn.DTF.run_80000bc4
theorem DTF.run_80000bec : run zesuImage cutPcs 300 0x80000bec (stateAt 0x80000bec) = some run_80000bec_leaves := _root_.ZesuExec.Fn.DTF.run_80000bec
theorem DTF.run_80000c34 : run zesuImage cutPcs 300 0x80000c34 (stateAt 0x80000c34) = some run_80000c34_leaves := _root_.ZesuExec.Fn.DTF.run_80000c34
theorem DTF.run_80000c5c : run zesuImage cutPcs 300 0x80000c5c (stateAt 0x80000c5c) = some run_80000c5c_leaves := _root_.ZesuExec.Fn.DTF.run_80000c5c
theorem DTF.run_80000cb0 : run zesuImage cutPcs 300 0x80000cb0 (stateAt 0x80000cb0) = some run_80000cb0_leaves := _root_.ZesuExec.Fn.DTF.run_80000cb0
theorem DTF.run_80000ce4 : run zesuImage cutPcs 300 0x80000ce4 (stateAt 0x80000ce4) = some run_80000ce4_leaves := _root_.ZesuExec.Fn.DTF.run_80000ce4
theorem DTF.run_80000d38 : run zesuImage cutPcs 300 0x80000d38 (stateAt 0x80000d38) = some run_80000d38_leaves := _root_.ZesuExec.Fn.DTF.run_80000d38
theorem DTF.run_80000d6c : run zesuImage cutPcs 300 0x80000d6c (stateAt 0x80000d6c) = some run_80000d6c_leaves := _root_.ZesuExec.Fn.DTF.run_80000d6c
theorem DTF.run_80000db0 : run zesuImage cutPcs 300 0x80000db0 (stateAt 0x80000db0) = some run_80000db0_leaves := _root_.ZesuExec.Fn.DTF.run_80000db0
theorem DTF.run_80000dd8 : run zesuImage cutPcs 300 0x80000dd8 (stateAt 0x80000dd8) = some run_80000dd8_leaves := _root_.ZesuExec.Fn.DTF.run_80000dd8
theorem DTF.run_80000e20 : run zesuImage cutPcs 300 0x80000e20 (stateAt 0x80000e20) = some run_80000e20_leaves := _root_.ZesuExec.Fn.DTF.run_80000e20
theorem DTF.run_80000e48 : run zesuImage cutPcs 300 0x80000e48 (stateAt 0x80000e48) = some run_80000e48_leaves := _root_.ZesuExec.Fn.DTF.run_80000e48
theorem DTF.run_80000e9c : run zesuImage cutPcs 300 0x80000e9c (stateAt 0x80000e9c) = some run_80000e9c_leaves := _root_.ZesuExec.Fn.DTF.run_80000e9c
theorem DTF.run_80000ed0 : run zesuImage cutPcs 300 0x80000ed0 (stateAt 0x80000ed0) = some run_80000ed0_leaves := _root_.ZesuExec.Fn.DTF.run_80000ed0
theorem DTF.run_80000f24 : run zesuImage cutPcs 300 0x80000f24 (stateAt 0x80000f24) = some run_80000f24_leaves := _root_.ZesuExec.Fn.DTF.run_80000f24
theorem DTF.run_80000f58 : run zesuImage cutPcs 300 0x80000f58 (stateAt 0x80000f58) = some run_80000f58_leaves := _root_.ZesuExec.Fn.DTF.run_80000f58
theorem DTF.run_80000f9c : run zesuImage cutPcs 300 0x80000f9c (stateAt 0x80000f9c) = some run_80000f9c_leaves := _root_.ZesuExec.Fn.DTF.run_80000f9c
theorem DTF.run_80000fc4 : run zesuImage cutPcs 300 0x80000fc4 (stateAt 0x80000fc4) = some run_80000fc4_leaves := _root_.ZesuExec.Fn.DTF.run_80000fc4
theorem DTF.run_8000100c : run zesuImage cutPcs 300 0x8000100c (stateAt 0x8000100c) = some run_8000100c_leaves := _root_.ZesuExec.Fn.DTF.run_8000100c
theorem DTF.run_80001034 : run zesuImage cutPcs 300 0x80001034 (stateAt 0x80001034) = some run_80001034_leaves := _root_.ZesuExec.Fn.DTF.run_80001034
theorem DTF.run_80001084 : run zesuImage cutPcs 300 0x80001084 (stateAt 0x80001084) = some run_80001084_leaves := _root_.ZesuExec.Fn.DTF.run_80001084
theorem DTF.run_800010b8 : run zesuImage cutPcs 300 0x800010b8 (stateAt 0x800010b8) = some run_800010b8_leaves := _root_.ZesuExec.Fn.DTF.run_800010b8
theorem DTF.run_800010fc : run zesuImage cutPcs 300 0x800010fc (stateAt 0x800010fc) = some run_800010fc_leaves := _root_.ZesuExec.Fn.DTF.run_800010fc
theorem DTF.run_80001124 : run zesuImage cutPcs 300 0x80001124 (stateAt 0x80001124) = some run_80001124_leaves := _root_.ZesuExec.Fn.DTF.run_80001124
theorem DTF.run_800011b4 : run zesuImage cutPcs 300 0x800011b4 (stateAt 0x800011b4) = some run_800011b4_leaves := _root_.ZesuExec.Fn.DTF.run_800011b4
theorem DTF.run_800011f0 : run zesuImage cutPcs 300 0x800011f0 (stateAt 0x800011f0) = some run_800011f0_leaves := _root_.ZesuExec.Fn.DTF.run_800011f0
theorem DTF.run_800011f8 : run zesuImage cutPcs 300 0x800011f8 (stateAt 0x800011f8) = some run_800011f8_leaves := _root_.ZesuExec.Fn.DTF.run_800011f8
theorem DTF.run_80001254 : run zesuImage cutPcs 300 0x80001254 (stateAt 0x80001254) = some run_80001254_leaves := _root_.ZesuExec.Fn.DTF.run_80001254
theorem DTF.run_800012f0 : run zesuImage cutPcs 300 0x800012f0 (stateAt 0x800012f0) = some run_800012f0_leaves := _root_.ZesuExec.Fn.DTF.run_800012f0
theorem DTF.run_8000134c : run zesuImage cutPcs 300 0x8000134c (stateAt 0x8000134c) = some run_8000134c_leaves := _root_.ZesuExec.Fn.DTF.run_8000134c
theorem DTF.run_800013c8 : run zesuImage cutPcs 300 0x800013c8 (stateAt 0x800013c8) = some run_800013c8_leaves := _root_.ZesuExec.Fn.DTF.run_800013c8
theorem DTF.run_800013fc : run zesuImage cutPcs 300 0x800013fc (stateAt 0x800013fc) = some run_800013fc_leaves := _root_.ZesuExec.Fn.DTF.run_800013fc
theorem DTF.run_80001400 : run zesuImage cutPcs 300 0x80001400 (stateAt 0x80001400) = some run_80001400_leaves := _root_.ZesuExec.Fn.DTF.run_80001400
theorem DTF.run_80001468 : run zesuImage cutPcs 300 0x80001468 (stateAt 0x80001468) = some run_80001468_leaves := _root_.ZesuExec.Fn.DTF.run_80001468
theorem DTF.run_800014bc : run zesuImage cutPcs 300 0x800014bc (stateAt 0x800014bc) = some run_800014bc_leaves := _root_.ZesuExec.Fn.DTF.run_800014bc
theorem DTF.run_8000155c : run zesuImage cutPcs 300 0x8000155c (stateAt 0x8000155c) = some run_8000155c_leaves := _root_.ZesuExec.Fn.DTF.run_8000155c
theorem DTF.run_800015b0 : run zesuImage cutPcs 300 0x800015b0 (stateAt 0x800015b0) = some run_800015b0_leaves := _root_.ZesuExec.Fn.DTF.run_800015b0
theorem DTF.run_80001650 : run zesuImage cutPcs 300 0x80001650 (stateAt 0x80001650) = some run_80001650_leaves := _root_.ZesuExec.Fn.DTF.run_80001650
theorem DTF.run_800016a4 : run zesuImage cutPcs 300 0x800016a4 (stateAt 0x800016a4) = some run_800016a4_leaves := _root_.ZesuExec.Fn.DTF.run_800016a4
theorem DTF.run_80001708 : run zesuImage cutPcs 300 0x80001708 (stateAt 0x80001708) = some run_80001708_leaves := _root_.ZesuExec.Fn.DTF.run_80001708
theorem DTF.run_80001748 : run zesuImage cutPcs 300 0x80001748 (stateAt 0x80001748) = some run_80001748_leaves := _root_.ZesuExec.Fn.DTF.run_80001748
theorem DTF.run_800017a0 : run zesuImage cutPcs 300 0x800017a0 (stateAt 0x800017a0) = some run_800017a0_leaves := _root_.ZesuExec.Fn.DTF.run_800017a0
theorem DTF.run_800017c4 : run zesuImage cutPcs 300 0x800017c4 (stateAt 0x800017c4) = some run_800017c4_leaves := _root_.ZesuExec.Fn.DTF.run_800017c4
theorem DTF.run_800017d8 : run zesuImage cutPcs 300 0x800017d8 (stateAt 0x800017d8) = some run_800017d8_leaves := _root_.ZesuExec.Fn.DTF.run_800017d8
theorem DTF.run_80001828 : run zesuImage cutPcs 300 0x80001828 (stateAt 0x80001828) = some run_80001828_leaves := _root_.ZesuExec.Fn.DTF.run_80001828
theorem DTF.run_800018a4 : run zesuImage cutPcs 300 0x800018a4 (stateAt 0x800018a4) = some run_800018a4_leaves := _root_.ZesuExec.Fn.DTF.run_800018a4
theorem DTF.run_800018fc : run zesuImage cutPcs 300 0x800018fc (stateAt 0x800018fc) = some run_800018fc_leaves := _root_.ZesuExec.Fn.DTF.run_800018fc
theorem DTF.run_80001940 : run zesuImage cutPcs 300 0x80001940 (stateAt 0x80001940) = some run_80001940_leaves := _root_.ZesuExec.Fn.DTF.run_80001940
theorem DTF.run_80001998 : run zesuImage cutPcs 300 0x80001998 (stateAt 0x80001998) = some run_80001998_leaves := _root_.ZesuExec.Fn.DTF.run_80001998
theorem DTF.run_800019dc : run zesuImage cutPcs 300 0x800019dc (stateAt 0x800019dc) = some run_800019dc_leaves := _root_.ZesuExec.Fn.DTF.run_800019dc
theorem DTF.run_80001a34 : run zesuImage cutPcs 300 0x80001a34 (stateAt 0x80001a34) = some run_80001a34_leaves := _root_.ZesuExec.Fn.DTF.run_80001a34
theorem DTF.run_80001a5c : run zesuImage cutPcs 300 0x80001a5c (stateAt 0x80001a5c) = some run_80001a5c_leaves := _root_.ZesuExec.Fn.DTF.run_80001a5c
theorem DTF.run_80001a70 : run zesuImage cutPcs 300 0x80001a70 (stateAt 0x80001a70) = some run_80001a70_leaves := _root_.ZesuExec.Fn.DTF.run_80001a70
theorem DTF.run_80001aa4 : run zesuImage cutPcs 300 0x80001aa4 (stateAt 0x80001aa4) = some run_80001aa4_leaves := _root_.ZesuExec.Fn.DTF.run_80001aa4
theorem DTF.run_80001ae8 : run zesuImage cutPcs 300 0x80001ae8 (stateAt 0x80001ae8) = some run_80001ae8_leaves := _root_.ZesuExec.Fn.DTF.run_80001ae8
theorem DTF.run_80001b10 : run zesuImage cutPcs 300 0x80001b10 (stateAt 0x80001b10) = some run_80001b10_leaves := _root_.ZesuExec.Fn.DTF.run_80001b10
theorem DTF.run_80001b60 : run zesuImage cutPcs 300 0x80001b60 (stateAt 0x80001b60) = some run_80001b60_leaves := _root_.ZesuExec.Fn.DTF.run_80001b60
theorem DTF.run_80001bcc : run zesuImage cutPcs 300 0x80001bcc (stateAt 0x80001bcc) = some run_80001bcc_leaves := _root_.ZesuExec.Fn.DTF.run_80001bcc
theorem DTF.run_80001c24 : run zesuImage cutPcs 300 0x80001c24 (stateAt 0x80001c24) = some run_80001c24_leaves := _root_.ZesuExec.Fn.DTF.run_80001c24
theorem DTF.run_80001c84 : run zesuImage cutPcs 300 0x80001c84 (stateAt 0x80001c84) = some run_80001c84_leaves := _root_.ZesuExec.Fn.DTF.run_80001c84
theorem DTF.run_80001c98 : run zesuImage cutPcs 300 0x80001c98 (stateAt 0x80001c98) = some run_80001c98_leaves := _root_.ZesuExec.Fn.DTF.run_80001c98
theorem DTF.run_80001ccc : run zesuImage cutPcs 300 0x80001ccc (stateAt 0x80001ccc) = some run_80001ccc_leaves := _root_.ZesuExec.Fn.DTF.run_80001ccc
theorem DTF.run_80001d40 : run zesuImage cutPcs 300 0x80001d40 (stateAt 0x80001d40) = some run_80001d40_leaves := _root_.ZesuExec.Fn.DTF.run_80001d40
theorem DTF.run_80001d54 : run zesuImage cutPcs 300 0x80001d54 (stateAt 0x80001d54) = some run_80001d54_leaves := _root_.ZesuExec.Fn.DTF.run_80001d54
theorem DTF.run_80001d88 : run zesuImage cutPcs 300 0x80001d88 (stateAt 0x80001d88) = some run_80001d88_leaves := _root_.ZesuExec.Fn.DTF.run_80001d88
theorem DTF.run_80001dcc : run zesuImage cutPcs 300 0x80001dcc (stateAt 0x80001dcc) = some run_80001dcc_leaves := _root_.ZesuExec.Fn.DTF.run_80001dcc
theorem DTF.run_80001df4 : run zesuImage cutPcs 300 0x80001df4 (stateAt 0x80001df4) = some run_80001df4_leaves := _root_.ZesuExec.Fn.DTF.run_80001df4
theorem DTF.run_80001e48 : run zesuImage cutPcs 300 0x80001e48 (stateAt 0x80001e48) = some run_80001e48_leaves := _root_.ZesuExec.Fn.DTF.run_80001e48
theorem DTF.run_80001eb0 : run zesuImage cutPcs 300 0x80001eb0 (stateAt 0x80001eb0) = some run_80001eb0_leaves := _root_.ZesuExec.Fn.DTF.run_80001eb0
theorem DTF.run_80001ec4 : run zesuImage cutPcs 300 0x80001ec4 (stateAt 0x80001ec4) = some run_80001ec4_leaves := _root_.ZesuExec.Fn.DTF.run_80001ec4
theorem DTF.run_80001ef8 : run zesuImage cutPcs 300 0x80001ef8 (stateAt 0x80001ef8) = some run_80001ef8_leaves := _root_.ZesuExec.Fn.DTF.run_80001ef8
theorem DTF.run_80001f54 : run zesuImage cutPcs 300 0x80001f54 (stateAt 0x80001f54) = some run_80001f54_leaves := _root_.ZesuExec.Fn.DTF.run_80001f54
theorem DTF.run_80001fac : run zesuImage cutPcs 300 0x80001fac (stateAt 0x80001fac) = some run_80001fac_leaves := _root_.ZesuExec.Fn.DTF.run_80001fac
theorem DTF.run_80002004 : run zesuImage cutPcs 300 0x80002004 (stateAt 0x80002004) = some run_80002004_leaves := _root_.ZesuExec.Fn.DTF.run_80002004
theorem DTF.run_80002064 : run zesuImage cutPcs 300 0x80002064 (stateAt 0x80002064) = some run_80002064_leaves := _root_.ZesuExec.Fn.DTF.run_80002064
theorem DTF.run_800020ac : run zesuImage cutPcs 300 0x800020ac (stateAt 0x800020ac) = some run_800020ac_leaves := _root_.ZesuExec.Fn.DTF.run_800020ac
theorem DTF.run_800020c0 : run zesuImage cutPcs 300 0x800020c0 (stateAt 0x800020c0) = some run_800020c0_leaves := _root_.ZesuExec.Fn.DTF.run_800020c0
theorem DTF.run_8000211c : run zesuImage cutPcs 300 0x8000211c (stateAt 0x8000211c) = some run_8000211c_leaves := _root_.ZesuExec.Fn.DTF.run_8000211c
theorem DTF.run_80002138 : run zesuImage cutPcs 300 0x80002138 (stateAt 0x80002138) = some run_80002138_leaves := _root_.ZesuExec.Fn.DTF.run_80002138
theorem DTF.run_80002180 : run zesuImage cutPcs 300 0x80002180 (stateAt 0x80002180) = some run_80002180_leaves := _root_.ZesuExec.Fn.DTF.run_80002180
theorem DTF.run_800021b0 : run zesuImage cutPcs 300 0x800021b0 (stateAt 0x800021b0) = some run_800021b0_leaves := _root_.ZesuExec.Fn.DTF.run_800021b0
theorem DTF.run_800021f4 : run zesuImage cutPcs 300 0x800021f4 (stateAt 0x800021f4) = some run_800021f4_leaves := _root_.ZesuExec.Fn.DTF.run_800021f4
theorem DTF.run_8000221c : run zesuImage cutPcs 300 0x8000221c (stateAt 0x8000221c) = some run_8000221c_leaves := _root_.ZesuExec.Fn.DTF.run_8000221c
theorem DTF.run_80002274 : run zesuImage cutPcs 300 0x80002274 (stateAt 0x80002274) = some run_80002274_leaves := _root_.ZesuExec.Fn.DTF.run_80002274
theorem DTF.run_800022e4 : run zesuImage cutPcs 300 0x800022e4 (stateAt 0x800022e4) = some run_800022e4_leaves := _root_.ZesuExec.Fn.DTF.run_800022e4
theorem DTF.run_800022f0 : run zesuImage cutPcs 300 0x800022f0 (stateAt 0x800022f0) = some run_800022f0_leaves := _root_.ZesuExec.Fn.DTF.run_800022f0
theorem DTF.run_8000230c : run zesuImage cutPcs 300 0x8000230c (stateAt 0x8000230c) = some run_8000230c_leaves := _root_.ZesuExec.Fn.DTF.run_8000230c
theorem DTF.run_80002350 : run zesuImage cutPcs 300 0x80002350 (stateAt 0x80002350) = some run_80002350_leaves := _root_.ZesuExec.Fn.DTF.run_80002350
theorem DTF.run_80002378 : run zesuImage cutPcs 300 0x80002378 (stateAt 0x80002378) = some run_80002378_leaves := _root_.ZesuExec.Fn.DTF.run_80002378
theorem DTF.run_800023cc : run zesuImage cutPcs 300 0x800023cc (stateAt 0x800023cc) = some run_800023cc_leaves := _root_.ZesuExec.Fn.DTF.run_800023cc
theorem DTF.run_8000241c : run zesuImage cutPcs 300 0x8000241c (stateAt 0x8000241c) = some run_8000241c_leaves := _root_.ZesuExec.Fn.DTF.run_8000241c
theorem DTF.run_80002420 : run zesuImage cutPcs 300 0x80002420 (stateAt 0x80002420) = some run_80002420_leaves := _root_.ZesuExec.Fn.DTF.run_80002420
theorem DTF.run_80002434 : run zesuImage cutPcs 300 0x80002434 (stateAt 0x80002434) = some run_80002434_leaves := _root_.ZesuExec.Fn.DTF.run_80002434
theorem DTF.run_800024d0 : run zesuImage cutPcs 300 0x800024d0 (stateAt 0x800024d0) = some run_800024d0_leaves := _root_.ZesuExec.Fn.DTF.run_800024d0
theorem DTF.run_800024ec : run zesuImage cutPcs 300 0x800024ec (stateAt 0x800024ec) = some run_800024ec_leaves := _root_.ZesuExec.Fn.DTF.run_800024ec
theorem DTF.run_8000252c : run zesuImage cutPcs 300 0x8000252c (stateAt 0x8000252c) = some run_8000252c_leaves := _root_.ZesuExec.Fn.DTF.run_8000252c
theorem DTF.run_80002574 : run zesuImage cutPcs 300 0x80002574 (stateAt 0x80002574) = some run_80002574_leaves := _root_.ZesuExec.Fn.DTF.run_80002574
theorem DTF.run_80002600 : run zesuImage cutPcs 300 0x80002600 (stateAt 0x80002600) = some run_80002600_leaves := _root_.ZesuExec.Fn.DTF.run_80002600
theorem DTF.run_80002654 : run zesuImage cutPcs 300 0x80002654 (stateAt 0x80002654) = some run_80002654_leaves := _root_.ZesuExec.Fn.DTF.run_80002654
theorem DTF.run_80002690 : run zesuImage cutPcs 300 0x80002690 (stateAt 0x80002690) = some run_80002690_leaves := _root_.ZesuExec.Fn.DTF.run_80002690
theorem DTF.run_800026d4 : run zesuImage cutPcs 300 0x800026d4 (stateAt 0x800026d4) = some run_800026d4_leaves := _root_.ZesuExec.Fn.DTF.run_800026d4
theorem DTF.run_80002710 : run zesuImage cutPcs 300 0x80002710 (stateAt 0x80002710) = some run_80002710_leaves := _root_.ZesuExec.Fn.DTF.run_80002710
theorem DTF.run_80002754 : run zesuImage cutPcs 300 0x80002754 (stateAt 0x80002754) = some run_80002754_leaves := _root_.ZesuExec.Fn.DTF.run_80002754
theorem DTF.run_8000279c : run zesuImage cutPcs 300 0x8000279c (stateAt 0x8000279c) = some run_8000279c_leaves := _root_.ZesuExec.Fn.DTF.run_8000279c
theorem DTF.run_80002820 : run zesuImage cutPcs 300 0x80002820 (stateAt 0x80002820) = some run_80002820_leaves := _root_.ZesuExec.Fn.DTF.run_80002820
theorem DTF.run_80002868 : run zesuImage cutPcs 300 0x80002868 (stateAt 0x80002868) = some run_80002868_leaves := _root_.ZesuExec.Fn.DTF.run_80002868
theorem DTF.run_800029a8 : run zesuImage cutPcs 300 0x800029a8 (stateAt 0x800029a8) = some run_800029a8_leaves := _root_.ZesuExec.Fn.DTF.run_800029a8
theorem DTF.run_800029c4 : run zesuImage cutPcs 300 0x800029c4 (stateAt 0x800029c4) = some run_800029c4_leaves := _root_.ZesuExec.Fn.DTF.run_800029c4
theorem DTF.run_800029c8 : run zesuImage cutPcs 300 0x800029c8 (stateAt 0x800029c8) = some run_800029c8_leaves := _root_.ZesuExec.Fn.DTF.run_800029c8
theorem DTF.run_80002a08 : run zesuImage cutPcs 300 0x80002a08 (stateAt 0x80002a08) = some run_80002a08_leaves := _root_.ZesuExec.Fn.DTF.run_80002a08
theorem DTF.run_80002a1c : run zesuImage cutPcs 300 0x80002a1c (stateAt 0x80002a1c) = some run_80002a1c_leaves := _root_.ZesuExec.Fn.DTF.run_80002a1c
theorem DTF.run_80002a38 : run zesuImage cutPcs 300 0x80002a38 (stateAt 0x80002a38) = some run_80002a38_leaves := _root_.ZesuExec.Fn.DTF.run_80002a38
theorem DTF.run_80002a6c : run zesuImage cutPcs 300 0x80002a6c (stateAt 0x80002a6c) = some run_80002a6c_leaves := _root_.ZesuExec.Fn.DTF.run_80002a6c
theorem DTF.run_80002b50 : run zesuImage cutPcs 300 0x80002b50 (stateAt 0x80002b50) = some run_80002b50_leaves := _root_.ZesuExec.Fn.DTF.run_80002b50
theorem DTF.run_80002bb4 : run zesuImage cutPcs 300 0x80002bb4 (stateAt 0x80002bb4) = some run_80002bb4_leaves := _root_.ZesuExec.Fn.DTF.run_80002bb4
theorem DTF.run_80002c68 : run zesuImage cutPcs 300 0x80002c68 (stateAt 0x80002c68) = some run_80002c68_leaves := _root_.ZesuExec.Fn.DTF.run_80002c68
theorem DTF.run_80002c94 : run zesuImage cutPcs 300 0x80002c94 (stateAt 0x80002c94) = some run_80002c94_leaves := _root_.ZesuExec.Fn.DTF.run_80002c94
theorem DTF.run_80002cfc : run zesuImage cutPcs 300 0x80002cfc (stateAt 0x80002cfc) = some run_80002cfc_leaves := _root_.ZesuExec.Fn.DTF.run_80002cfc
theorem DTF.run_80002db8 : run zesuImage cutPcs 300 0x80002db8 (stateAt 0x80002db8) = some run_80002db8_leaves := _root_.ZesuExec.Fn.DTF.run_80002db8
theorem DTF.run_80002dbc : run zesuImage cutPcs 300 0x80002dbc (stateAt 0x80002dbc) = some run_80002dbc_leaves := _root_.ZesuExec.Fn.DTF.run_80002dbc
theorem DTF.run_80002dc4 : run zesuImage cutPcs 300 0x80002dc4 (stateAt 0x80002dc4) = some run_80002dc4_leaves := _root_.ZesuExec.Fn.DTF.run_80002dc4
theorem DTF.run_80002ecc : run zesuImage cutPcs 300 0x80002ecc (stateAt 0x80002ecc) = some run_80002ecc_leaves := _root_.ZesuExec.Fn.DTF.run_80002ecc
theorem DTF.run_80002ee0 : run zesuImage cutPcs 300 0x80002ee0 (stateAt 0x80002ee0) = some run_80002ee0_leaves := _root_.ZesuExec.Fn.DTF.run_80002ee0
theorem DTF.run_80002f14 : run zesuImage cutPcs 300 0x80002f14 (stateAt 0x80002f14) = some run_80002f14_leaves := _root_.ZesuExec.Fn.DTF.run_80002f14
theorem DTF.run_80002f54 : run zesuImage cutPcs 300 0x80002f54 (stateAt 0x80002f54) = some run_80002f54_leaves := _root_.ZesuExec.Fn.DTF.run_80002f54
theorem DTF.run_80002f90 : run zesuImage cutPcs 300 0x80002f90 (stateAt 0x80002f90) = some run_80002f90_leaves := _root_.ZesuExec.Fn.DTF.run_80002f90
theorem DTF.run_80002ff0 : run zesuImage cutPcs 300 0x80002ff0 (stateAt 0x80002ff0) = some run_80002ff0_leaves := _root_.ZesuExec.Fn.DTF.run_80002ff0
theorem DTF.run_80003064 : run zesuImage cutPcs 300 0x80003064 (stateAt 0x80003064) = some run_80003064_leaves := _root_.ZesuExec.Fn.DTF.run_80003064
theorem DTF.run_800030d4 : run zesuImage cutPcs 300 0x800030d4 (stateAt 0x800030d4) = some run_800030d4_leaves := _root_.ZesuExec.Fn.DTF.run_800030d4

-- `leaf_auto`'s `simp` on the 161-row cut table exceeds the default recursion depth (a runtime
-- exception `zesu_auto` cannot catch); 647 items take 262 s.
set_option maxRecDepth 20000 in
zesu_auto DTF

end ZesuExec.Fn.DTF
