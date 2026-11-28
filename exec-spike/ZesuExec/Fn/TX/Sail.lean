import ZesuExec.Fn.TX.Proof
import ZesuExec.Sail.Run

/-! # TX at the Sail level: `sail_reaches` applied to `tx_spec` -/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.SailLink

theorem tx_sail (g : Params)
    {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre Alloc.contract g m) :
    SailReaches zesuImage bound
      (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post Alloc.contract g m m') s :=
  sail_reaches h (tx_spec g m hpc hpre)

end ZesuExec.Fn.TX
