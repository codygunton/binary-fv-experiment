import ZesuExec.Fn.F3.Proof
import ZesuExec.Sail.Run

/-! # F3 at the Sail level: `sail_reaches` applied to `f3_spec` -/

namespace ZesuExec.Fn.F3
open ZesuExec ZesuExec.SailLink

theorem f3_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post m m') s :=
  sail_reaches h (f3_spec m hpc hpre)

end ZesuExec.Fn.F3
