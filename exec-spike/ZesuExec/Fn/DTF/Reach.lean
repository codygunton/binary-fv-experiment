import ZesuExec.Fn.DTF.Leaves

/-!
# DTF assembly (programme plan S7 step 3)

`zesu_assemble DTF`: `DTF.Open` holds every cut lemma and leaf neither `zesu_auto` nor
`Leaves.lean` proved; `DTF.reach_from : DTF.Open → ∀ c ∈ DTF.plan.cuts, ∀ σ m, c.A σ m → Reaches …`
is conditional on `DTF.Open` and, through `σ.hTX`, on TX's contract.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Vc

zesu_assemble DTF

end ZesuExec.Fn.DTF
