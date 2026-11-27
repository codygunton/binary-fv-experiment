import ZesuExec.Fn.F2.Proof
import ZesuExec.Sail.Run

/-! # F2 at the Sail level: `sail_reaches` applied to `f2_spec` -/

namespace ZesuExec.Fn.F2
open ZesuExec ZesuExec.SailLink

theorem f2_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post m m') s :=
  sail_reaches h (f2_spec m hpc hpre)

end ZesuExec.Fn.F2
