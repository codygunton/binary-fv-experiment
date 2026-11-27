import ZesuExec.Fn.F5.Proof
import ZesuExec.Sail.Run

/-! # F5 at the Sail level: `sail_reaches` applied to `f5_spec` -/

namespace ZesuExec.Fn.F5
open ZesuExec ZesuExec.SailLink

theorem f5_sail (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (items : List Byte)
    {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre A L items m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post A L items m m') s :=
  sail_reaches h (f5_spec A L items m hpc hpre)

end ZesuExec.Fn.F5
