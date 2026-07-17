import BinaryFv.RiscV.Logic.RegisterAgree
import BinaryFv.RiscV.Step.Context

/-!
# Abstract step premises

The premises a machine-loop contract assumes rather than discharges: that the configured machine's
fetch path is enabled at every body pc, and that the Zicfilp landing-pad update is a no-op at the
return. Both are stated over all states agreeing with a base state off the loop's write set, so that
they survive each step.

Each is parameterized by the register set `P` the loop preserves and by the address set `Pcs` of the
function's fetch addresses. Which registers and which addresses those are is a target fact.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- For any state agreeing with `base` off the write set and positioned at one of the function's
fetch addresses, the generated base-fetch path is enabled. -/
def AbstractPlatform (P : Register → Prop) (Pcs : BitVec 64 → Prop) (base : State) : Prop :=
  ∀ (t : State) (pc : BitVec 64), Agree P base t → t.regs.get? PC = some pc → Pcs pc →
    FetchBasePlatform t pc ∧ FetchMemoryNoMMIO t pc ∧ InterruptDisabled t ∧ LandingPadNotExpected t

/-- The abstract platform survives to an `Agree`-equal state. -/
theorem AbstractPlatform.mono {P : Register → Prop} {Pcs : BitVec 64 → Prop} {s s' : State}
    (h : Agree P s s') (hp : AbstractPlatform P Pcs s) : AbstractPlatform P Pcs s' :=
  fun t pc hst hPC hbody => hp t pc (Agree.trans h hst) hPC hbody

/-- The Zicfilp landing-pad update for a return through link register `r` is a no-op.

`R` is a parameter rather than a fixed `x1`: a leaf helper returning through `ra` fixes `R` to `x1`,
while a caller that returns through several link registers quantifies over them. Collapsing this to
a single `∀ rs1` would silently strengthen the leaf's assumed premise. -/
def AbstractElp (P : Register → Prop) (R : regidx → Prop) (base : State) : Prop :=
  ∀ (t : State) (r : regidx), R r → Agree P base t → Runs (update_elp_state r) t t ()

/-- The abstract Zicfilp update survives to an `Agree`-equal state. -/
theorem AbstractElp.mono {P : Register → Prop} {R : regidx → Prop} {s s' : State}
    (h : Agree P s s') (he : AbstractElp P R s) : AbstractElp P R s' :=
  fun t r hr hst => he t r hr (Agree.trans h hst)

end BinaryFv.RiscV
