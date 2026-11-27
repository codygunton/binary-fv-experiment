import ZesuExec.Fn.F0.Proof
import ZesuExec.Sail.Run

/-! # F0 at the Sail level: `sail_reaches` applied to `f0_spec` -/

namespace ZesuExec.Fn.F0
open ZesuExec ZesuExec.SailLink

theorem f0_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post m m') s :=
  sail_reaches h (f0_spec m hpc hpre)

end ZesuExec.Fn.F0
