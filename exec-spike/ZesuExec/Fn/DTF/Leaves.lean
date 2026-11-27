import ZesuExec.Fn.DTF.Vc
import ZesuExec.Fn.DTF.Ret

/-!
# DTF items closed by hand (programme plan S7 step 4), in `zmap next` order

The cut lemmas of the 70 cut points reached only by jumps and branches whose state has no extra
region, by `cut_plain` (`Lemmas.lean`); each instance checks by `decide` that the cut is not the
entry, has no call site, no extra region and a well-formed shape.

The cut lemmas of the 76 return sites of `decodeItem`, `alloc`, `remap` and TX, by `cut_ret`
(`Ret.lean`); each instance checks by `decide` the return site's shape against its call site
(`RetCheck`) and that the return address is even.

The entry's cut lemma (`cut_entry`) and the three hand-placed cuts with region 4: the jump-table
word (`cut_table`) and the two buffer slots (`cut_slot`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem DTF.cut_80000588 : CutOK DTF.plan DTF.plan.cuts[2]! :=
  cut_plain (table[2]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800005dc : CutOK DTF.plan DTF.plan.cuts[4]! :=
  cut_plain (table[4]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000634 : CutOK DTF.plan DTF.plan.cuts[6]! :=
  cut_plain (table[6]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000069c : CutOK DTF.plan DTF.plan.cuts[8]! :=
  cut_plain (table[8]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800006f4 : CutOK DTF.plan DTF.plan.cuts[10]! :=
  cut_plain (table[10]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000075c : CutOK DTF.plan DTF.plan.cuts[12]! :=
  cut_plain (table[12]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800007b4 : CutOK DTF.plan DTF.plan.cuts[14]! :=
  cut_plain (table[14]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000081c : CutOK DTF.plan DTF.plan.cuts[16]! :=
  cut_plain (table[16]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000874 : CutOK DTF.plan DTF.plan.cuts[18]! :=
  cut_plain (table[18]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800008e8 : CutOK DTF.plan DTF.plan.cuts[20]! :=
  cut_plain (table[20]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000960 : CutOK DTF.plan DTF.plan.cuts[22]! :=
  cut_plain (table[22]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800009d8 : CutOK DTF.plan DTF.plan.cuts[24]! :=
  cut_plain (table[24]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000a48 : CutOK DTF.plan DTF.plan.cuts[26]! :=
  cut_plain (table[26]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000ac4 : CutOK DTF.plan DTF.plan.cuts[28]! :=
  cut_plain (table[28]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000b4c : CutOK DTF.plan DTF.plan.cuts[30]! :=
  cut_plain (table[30]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000bc4 : CutOK DTF.plan DTF.plan.cuts[32]! :=
  cut_plain (table[32]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000c34 : CutOK DTF.plan DTF.plan.cuts[34]! :=
  cut_plain (table[34]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000cb0 : CutOK DTF.plan DTF.plan.cuts[36]! :=
  cut_plain (table[36]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000d38 : CutOK DTF.plan DTF.plan.cuts[38]! :=
  cut_plain (table[38]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000db0 : CutOK DTF.plan DTF.plan.cuts[40]! :=
  cut_plain (table[40]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000e20 : CutOK DTF.plan DTF.plan.cuts[42]! :=
  cut_plain (table[42]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000e9c : CutOK DTF.plan DTF.plan.cuts[44]! :=
  cut_plain (table[44]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000f24 : CutOK DTF.plan DTF.plan.cuts[46]! :=
  cut_plain (table[46]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000f9c : CutOK DTF.plan DTF.plan.cuts[48]! :=
  cut_plain (table[48]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000100c : CutOK DTF.plan DTF.plan.cuts[50]! :=
  cut_plain (table[50]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001084 : CutOK DTF.plan DTF.plan.cuts[52]! :=
  cut_plain (table[52]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800010fc : CutOK DTF.plan DTF.plan.cuts[54]! :=
  cut_plain (table[54]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800011f0 : CutOK DTF.plan DTF.plan.cuts[57]! :=
  cut_plain (table[57]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800011f8 : CutOK DTF.plan DTF.plan.cuts[58]! :=
  cut_plain (table[58]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001254 : CutOK DTF.plan DTF.plan.cuts[59]! :=
  cut_plain (table[59]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000134c : CutOK DTF.plan DTF.plan.cuts[61]! :=
  cut_plain (table[61]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800013fc : CutOK DTF.plan DTF.plan.cuts[63]! :=
  cut_plain (table[63]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001400 : CutOK DTF.plan DTF.plan.cuts[64]! :=
  cut_plain (table[64]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800014bc : CutOK DTF.plan DTF.plan.cuts[66]! :=
  cut_plain (table[66]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800015b0 : CutOK DTF.plan DTF.plan.cuts[68]! :=
  cut_plain (table[68]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800016a4 : CutOK DTF.plan DTF.plan.cuts[70]! :=
  cut_plain (table[70]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001828 : CutOK DTF.plan DTF.plan.cuts[76]! :=
  cut_plain (table[76]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001ae8 : CutOK DTF.plan DTF.plan.cuts[86]! :=
  cut_plain (table[86]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001b60 : CutOK DTF.plan DTF.plan.cuts[88]! :=
  cut_plain (table[88]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001c24 : CutOK DTF.plan DTF.plan.cuts[90]! :=
  cut_plain (table[90]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001dcc : CutOK DTF.plan DTF.plan.cuts[97]! :=
  cut_plain (table[97]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001e48 : CutOK DTF.plan DTF.plan.cuts[99]! :=
  cut_plain (table[99]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001f54 : CutOK DTF.plan DTF.plan.cuts[103]! :=
  cut_plain (table[103]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002004 : CutOK DTF.plan DTF.plan.cuts[105]! :=
  cut_plain (table[105]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800020ac : CutOK DTF.plan DTF.plan.cuts[107]! :=
  cut_plain (table[107]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800021f4 : CutOK DTF.plan DTF.plan.cuts[113]! :=
  cut_plain (table[113]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002274 : CutOK DTF.plan DTF.plan.cuts[115]! :=
  cut_plain (table[115]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800022e4 : CutOK DTF.plan DTF.plan.cuts[116]! :=
  cut_plain (table[116]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800022f0 : CutOK DTF.plan DTF.plan.cuts[117]! :=
  cut_plain (table[117]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002350 : CutOK DTF.plan DTF.plan.cuts[119]! :=
  cut_plain (table[119]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800023cc : CutOK DTF.plan DTF.plan.cuts[121]! :=
  cut_plain (table[121]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000241c : CutOK DTF.plan DTF.plan.cuts[122]! :=
  cut_plain (table[122]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002420 : CutOK DTF.plan DTF.plan.cuts[123]! :=
  cut_plain (table[123]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800024d0 : CutOK DTF.plan DTF.plan.cuts[125]! :=
  cut_plain (table[125]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002574 : CutOK DTF.plan DTF.plan.cuts[128]! :=
  cut_plain (table[128]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002690 : CutOK DTF.plan DTF.plan.cuts[131]! :=
  cut_plain (table[131]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002710 : CutOK DTF.plan DTF.plan.cuts[133]! :=
  cut_plain (table[133]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000279c : CutOK DTF.plan DTF.plan.cuts[135]! :=
  cut_plain (table[135]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002868 : CutOK DTF.plan DTF.plan.cuts[137]! :=
  cut_plain (table[137]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800029c4 : CutOK DTF.plan DTF.plan.cuts[139]! :=
  cut_plain (table[139]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800029c8 : CutOK DTF.plan DTF.plan.cuts[140]! :=
  cut_plain (table[140]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002a1c : CutOK DTF.plan DTF.plan.cuts[142]! :=
  cut_plain (table[142]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002bb4 : CutOK DTF.plan DTF.plan.cuts[146]! :=
  cut_plain (table[146]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002cfc : CutOK DTF.plan DTF.plan.cuts[149]! :=
  cut_plain (table[149]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002db8 : CutOK DTF.plan DTF.plan.cuts[150]! :=
  cut_plain (table[150]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002dbc : CutOK DTF.plan DTF.plan.cuts[151]! :=
  cut_plain (table[151]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002dc4 : CutOK DTF.plan DTF.plan.cuts[152]! :=
  cut_plain (table[152]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002ecc : CutOK DTF.plan DTF.plan.cuts[153]! :=
  cut_plain (table[153]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002ff0 : CutOK DTF.plan DTF.plan.cuts[158]! :=
  cut_plain (table[158]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800030d4 : CutOK DTF.plan DTF.plan.cuts[160]! :=
  cut_plain (table[160]!) (by decide) (by decide) (by decide) (by decide)

/-! ## Return sites (`cut_ret`) -/

theorem DTF.cut_8000059c : CutOK DTF.plan DTF.plan.cuts[3]! :=
  cut_ret (table[3]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800005f0 : CutOK DTF.plan DTF.plan.cuts[5]! :=
  cut_ret (table[5]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000065c : CutOK DTF.plan DTF.plan.cuts[7]! :=
  cut_ret (table[7]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800006b0 : CutOK DTF.plan DTF.plan.cuts[9]! :=
  cut_ret (table[9]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000071c : CutOK DTF.plan DTF.plan.cuts[11]! :=
  cut_ret (table[11]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000770 : CutOK DTF.plan DTF.plan.cuts[13]! :=
  cut_ret (table[13]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800007dc : CutOK DTF.plan DTF.plan.cuts[15]! :=
  cut_ret (table[15]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000830 : CutOK DTF.plan DTF.plan.cuts[17]! :=
  cut_ret (table[17]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000089c : CutOK DTF.plan DTF.plan.cuts[19]! :=
  cut_ret (table[19]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000910 : CutOK DTF.plan DTF.plan.cuts[21]! :=
  cut_ret (table[21]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000994 : CutOK DTF.plan DTF.plan.cuts[23]! :=
  cut_ret (table[23]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000a00 : CutOK DTF.plan DTF.plan.cuts[25]! :=
  cut_ret (table[25]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000a70 : CutOK DTF.plan DTF.plan.cuts[27]! :=
  cut_ret (table[27]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000af8 : CutOK DTF.plan DTF.plan.cuts[29]! :=
  cut_ret (table[29]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000b80 : CutOK DTF.plan DTF.plan.cuts[31]! :=
  cut_ret (table[31]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000bec : CutOK DTF.plan DTF.plan.cuts[33]! :=
  cut_ret (table[33]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000c5c : CutOK DTF.plan DTF.plan.cuts[35]! :=
  cut_ret (table[35]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000ce4 : CutOK DTF.plan DTF.plan.cuts[37]! :=
  cut_ret (table[37]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000d6c : CutOK DTF.plan DTF.plan.cuts[39]! :=
  cut_ret (table[39]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000dd8 : CutOK DTF.plan DTF.plan.cuts[41]! :=
  cut_ret (table[41]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000e48 : CutOK DTF.plan DTF.plan.cuts[43]! :=
  cut_ret (table[43]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000ed0 : CutOK DTF.plan DTF.plan.cuts[45]! :=
  cut_ret (table[45]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000f58 : CutOK DTF.plan DTF.plan.cuts[47]! :=
  cut_ret (table[47]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000fc4 : CutOK DTF.plan DTF.plan.cuts[49]! :=
  cut_ret (table[49]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001034 : CutOK DTF.plan DTF.plan.cuts[51]! :=
  cut_ret (table[51]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800010b8 : CutOK DTF.plan DTF.plan.cuts[53]! :=
  cut_ret (table[53]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001124 : CutOK DTF.plan DTF.plan.cuts[55]! :=
  cut_ret (table[55]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800011b4 : CutOK DTF.plan DTF.plan.cuts[56]! :=
  cut_ret (table[56]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800012f0 : CutOK DTF.plan DTF.plan.cuts[60]! :=
  cut_ret (table[60]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800013c8 : CutOK DTF.plan DTF.plan.cuts[62]! :=
  cut_ret (table[62]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001468 : CutOK DTF.plan DTF.plan.cuts[65]! :=
  cut_ret (table[65]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000155c : CutOK DTF.plan DTF.plan.cuts[67]! :=
  cut_ret (table[67]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001650 : CutOK DTF.plan DTF.plan.cuts[69]! :=
  cut_ret (table[69]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001708 : CutOK DTF.plan DTF.plan.cuts[71]! :=
  cut_ret (table[71]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001748 : CutOK DTF.plan DTF.plan.cuts[72]! :=
  cut_ret (table[72]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800017a0 : CutOK DTF.plan DTF.plan.cuts[73]! :=
  cut_ret (table[73]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800017d8 : CutOK DTF.plan DTF.plan.cuts[75]! :=
  cut_ret (table[75]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800018a4 : CutOK DTF.plan DTF.plan.cuts[77]! :=
  cut_ret (table[77]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800018fc : CutOK DTF.plan DTF.plan.cuts[78]! :=
  cut_ret (table[78]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001940 : CutOK DTF.plan DTF.plan.cuts[79]! :=
  cut_ret (table[79]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001998 : CutOK DTF.plan DTF.plan.cuts[80]! :=
  cut_ret (table[80]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800019dc : CutOK DTF.plan DTF.plan.cuts[81]! :=
  cut_ret (table[81]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001a34 : CutOK DTF.plan DTF.plan.cuts[82]! :=
  cut_ret (table[82]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001aa4 : CutOK DTF.plan DTF.plan.cuts[85]! :=
  cut_ret (table[85]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001b10 : CutOK DTF.plan DTF.plan.cuts[87]! :=
  cut_ret (table[87]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001bcc : CutOK DTF.plan DTF.plan.cuts[89]! :=
  cut_ret (table[89]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001ccc : CutOK DTF.plan DTF.plan.cuts[93]! :=
  cut_ret (table[93]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001d88 : CutOK DTF.plan DTF.plan.cuts[96]! :=
  cut_ret (table[96]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001df4 : CutOK DTF.plan DTF.plan.cuts[98]! :=
  cut_ret (table[98]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001ef8 : CutOK DTF.plan DTF.plan.cuts[102]! :=
  cut_ret (table[102]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001fac : CutOK DTF.plan DTF.plan.cuts[104]! :=
  cut_ret (table[104]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002064 : CutOK DTF.plan DTF.plan.cuts[106]! :=
  cut_ret (table[106]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800020c0 : CutOK DTF.plan DTF.plan.cuts[108]! :=
  cut_ret (table[108]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800021b0 : CutOK DTF.plan DTF.plan.cuts[112]! :=
  cut_ret (table[112]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000221c : CutOK DTF.plan DTF.plan.cuts[114]! :=
  cut_ret (table[114]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000230c : CutOK DTF.plan DTF.plan.cuts[118]! :=
  cut_ret (table[118]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002378 : CutOK DTF.plan DTF.plan.cuts[120]! :=
  cut_ret (table[120]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800024ec : CutOK DTF.plan DTF.plan.cuts[126]! :=
  cut_ret (table[126]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_8000252c : CutOK DTF.plan DTF.plan.cuts[127]! :=
  cut_ret (table[127]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002600 : CutOK DTF.plan DTF.plan.cuts[129]! :=
  cut_ret (table[129]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002654 : CutOK DTF.plan DTF.plan.cuts[130]! :=
  cut_ret (table[130]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800026d4 : CutOK DTF.plan DTF.plan.cuts[132]! :=
  cut_ret (table[132]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002754 : CutOK DTF.plan DTF.plan.cuts[134]! :=
  cut_ret (table[134]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002820 : CutOK DTF.plan DTF.plan.cuts[136]! :=
  cut_ret (table[136]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800029a8 : CutOK DTF.plan DTF.plan.cuts[138]! :=
  cut_ret (table[138]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002a08 : CutOK DTF.plan DTF.plan.cuts[141]! :=
  cut_ret (table[141]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002b50 : CutOK DTF.plan DTF.plan.cuts[145]! :=
  cut_ret (table[145]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002c68 : CutOK DTF.plan DTF.plan.cuts[147]! :=
  cut_ret (table[147]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002c94 : CutOK DTF.plan DTF.plan.cuts[148]! :=
  cut_ret (table[148]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002f54 : CutOK DTF.plan DTF.plan.cuts[156]! :=
  cut_ret (table[156]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002f90 : CutOK DTF.plan DTF.plan.cuts[157]! :=
  cut_ret (table[157]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80003064 : CutOK DTF.plan DTF.plan.cuts[159]! :=
  cut_ret (table[159]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001a70 : CutOK DTF.plan DTF.plan.cuts[84]! :=
  cut_ret (table[84]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001c98 : CutOK DTF.plan DTF.plan.cuts[92]! :=
  cut_ret (table[92]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001d54 : CutOK DTF.plan DTF.plan.cuts[95]! :=
  cut_ret (table[95]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001ec4 : CutOK DTF.plan DTF.plan.cuts[101]! :=
  cut_ret (table[101]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_800017c4 : CutOK DTF.plan DTF.plan.cuts[74]! :=
  cut_ret (table[74]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001a5c : CutOK DTF.plan DTF.plan.cuts[83]! :=
  cut_ret (table[83]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001c84 : CutOK DTF.plan DTF.plan.cuts[91]! :=
  cut_ret (table[91]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001d40 : CutOK DTF.plan DTF.plan.cuts[94]! :=
  cut_ret (table[94]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80001eb0 : CutOK DTF.plan DTF.plan.cuts[100]! :=
  cut_ret (table[100]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002a38 : CutOK DTF.plan DTF.plan.cuts[143]! :=
  cut_ret (table[143]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002ee0 : CutOK DTF.plan DTF.plan.cuts[154]! :=
  cut_ret (table[154]!) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## The entry and the cuts with region 4 -/

theorem DTF.cut_8000050c : CutOK DTF.plan DTF.plan.cuts[0]! :=
  cut_entry (table[0]!) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80000574 : CutOK DTF.plan DTF.plan.cuts[1]! :=
  cut_table (table[1]!) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002138 : CutOK DTF.plan DTF.plan.cuts[110]! :=
  cut_slot (table[110]!) 32 (by decide) (by decide) (by decide) (by decide) (by decide)
theorem DTF.cut_80002434 : CutOK DTF.plan DTF.plan.cuts[124]! :=
  cut_slot (table[124]!) 0x90 (by decide) (by decide) (by decide) (by decide) (by decide)

end ZesuExec.Fn.DTF
