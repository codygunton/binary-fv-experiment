import ZesuExec.Fn.DTF.Vc
import ZesuExec.Fn.DTF.Lemmas

/-!
# DTF items closed by hand (programme plan S7 step 4), in `zmap next` order

The cut lemmas of the 70 cut points reached only by jumps and branches whose state has no extra
region, by `cut_plain` (`Lemmas.lean`); each instance checks by `decide` that the cut is not the
entry, has no call site, no extra region and a well-formed shape.
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

end ZesuExec.Fn.DTF
