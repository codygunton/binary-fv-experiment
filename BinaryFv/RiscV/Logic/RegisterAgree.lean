import BinaryFv.RiscV.Model.State

/-!
# Agreement on a set of registers

`Agree P base t` says `t` and `base` hold the same value in every register satisfying `P`. Machine
loops instantiate `P` with the complement of the write set of the loop body, giving the usual
"stable registers are preserved" relation.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- `t` agrees with `base` on every register satisfying `P`. -/
def Agree (P : Register → Prop) (base t : State) : Prop :=
  ∀ r : Register, P r → t.regs.get? r = base.regs.get? r

theorem Agree.refl {P : Register → Prop} (s : State) : Agree P s s := fun _ _ => rfl

theorem Agree.trans {P : Register → Prop} {s t u : State}
    (hst : Agree P s t) (htu : Agree P t u) : Agree P s u :=
  fun r hr => (htu r hr).trans (hst r hr)

/-- Agreement on a larger register set implies agreement on a smaller one. -/
theorem Agree.weaken {P Q : Register → Prop} {s t : State}
    (imp : ∀ r, Q r → P r) (h : Agree P s t) : Agree Q s t :=
  fun r hr => h r (imp r hr)

end BinaryFv.RiscV
