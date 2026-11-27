import ZesuExec.Fn.TX.Store

/-!
# TX assembled (programme plan S6 step 7)

`zesu_assemble TX` collects the cut lemmas and leaf theorems of `Vc.lean`, `Ret.lean`,
`Store.lean` and the leaf modules; the items still missing are the fields of `TX.Open`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

zesu_assemble TX

end ZesuExec.Fn.TX
