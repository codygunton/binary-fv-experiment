import ZesuExec.Fn.F6.Proof
import ZesuExec.Sail.Run

/-! # F6 at the Sail level: `sail_reaches` applied to `f6_spec` -/

namespace ZesuExec.Fn.F6
open ZesuExec ZesuExec.SailLink

theorem f6_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailReaches zesuImage 2178 (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post m m') s :=
  sail_reaches h (f6_spec m hpc hpre)

end ZesuExec.Fn.F6
