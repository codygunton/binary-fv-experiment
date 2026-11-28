import ZesuExec.Fn.Memset.Proof
import ZesuExec.Sail.Run

/-! # `memset` at the Sail level, and a machine satisfying its precondition -/

namespace ZesuExec.Fn.Memset
open ZesuExec ZesuExec.SailLink

theorem memset_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : Pre m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ Post m m') s :=
  sail_reaches h (memset_spec m hpc hpre)

/-- `memset(0xa0100000, 0x5a, 16)` with the 16 bytes present. -/
def nvMachine : Machine where
  regs := fun i => if i.val = 1 then 0x80000000 else if i.val = 10 then 0xa0100000
    else if i.val = 11 then 0x5a else if i.val = 12 then 16 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun x => if 0xa0100000 ≤ x.toNat ∧ x.toNat < 0xa0100010 then some 0 else none

theorem pre_nonvacuous : ∃ m : Machine, m.pc.toNat = entry ∧ Pre m :=
  ⟨nvMachine, by decide +kernel, by decide +kernel, Or.inr (by decide +kernel)⟩

end ZesuExec.Fn.Memset
