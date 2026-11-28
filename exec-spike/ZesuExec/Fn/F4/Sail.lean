import ZesuExec.Fn.F4.Proof
import ZesuExec.Sail.Run

/-! # F4 at the Sail level: `sail_reaches` applied to `f4_spec` -/

namespace ZesuExec.Fn.F4
open ZesuExec ZesuExec.SailLink

theorem f4_sail (L : List (Word × Nat)) (items : List Byte)
    {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre Alloc.contract L items m) :
    SailReaches zesuImage bound
      (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post Alloc.contract L items m m') s :=
  sail_reaches h (f4_spec L items m hpc hpre)

end ZesuExec.Fn.F4
