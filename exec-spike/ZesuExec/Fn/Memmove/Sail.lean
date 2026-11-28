import ZesuExec.Fn.Memmove.Proof
import ZesuExec.Sail.Run

/-! # `memmove` at the Sail level: `sail_reaches` applied to `memmove_spec` -/

namespace ZesuExec.Fn.Memmove
open ZesuExec ZesuExec.SailLink

theorem memmove_sail {m : Machine} {s : BinaryFv.RiscV.State} (h : Rel zesuImage m s)
    (hpc : m.pc.toNat = entry) (hpre : MemcpyPre m) :
    SailReaches zesuImage bound (fun s' => ∃ m', Rel zesuImage m' s' ∧ MemcpyPost m m') s :=
  sail_reaches h (memmove_spec m hpc hpre)

/-- A machine at `memmove`'s entry that satisfies the precondition: an 8-byte move inside a
present RAM window, the staging word present. -/
def nvMachine : Machine where
  regs := fun i => if i.val = 1 then 0x80000000 else if i.val = 10 then 0xa0100004
    else if i.val = 11 then 0xa0100000 else if i.val = 12 then 8 else 0
  pc := BitVec.ofNat 64 entry
  mem := fun x => if (0xa0100000 ≤ x.toNat ∧ x.toNat < 0xa0100010) ∨
      (Layout.extraParams ≤ x.toNat ∧ x.toNat < Layout.extraParams + 8) then some 0 else none

theorem pre_nonvacuous : ∃ m : Machine, m.pc.toNat = entry ∧ MemcpyPre m :=
  ⟨nvMachine, by decide +kernel, show ziskMemcpyDomain nvMachine = true by decide +kernel⟩

end ZesuExec.Fn.Memmove
