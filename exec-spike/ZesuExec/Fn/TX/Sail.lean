import ZesuExec.Fn.TX.Proof
import ZesuExec.Sail.Run

/-! # TX at the Sail level: `sail_reaches` applied to `tx_spec` -/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.SailLink

theorem tx_sail (A : AllocAssumptions zesuImage) (g : Params)
    {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre A g m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post A g m m') s :=
  sail_reaches h (tx_spec A g m hpc hpre)

end ZesuExec.Fn.TX
