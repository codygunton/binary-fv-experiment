import BinaryFv.RiscV.Model.State
import BinaryFv.RiscV.Logic.RegisterAgree

/-!
# Inert platform state for normal execution, and the register set a call must not disturb
-/

namespace BinaryFv.RiscV

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register

/-- Inert platform state for normal direct execution; ABI and memory predicates remain separate. -/
def NormalExecutionState (state : State) : Prop :=
  state.regs.get? hart_state = some (HartState.HART_ACTIVE ()) ∧
    state.regs.get? cur_privilege = some Privilege.Machine ∧
      state.regs.get? satp = some (0 : BitVec 64) ∧
        state.regs.get? mideleg = some (0 : BitVec 64) ∧
          state.regs.get? mie = some (0 : BitVec 64) ∧
            state.regs.get? mip = some (0 : BitVec 64) ∧
              state.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64) ∧
                state.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64) ∧
                  state.regs.get? mcountinhibit = some (0 : BitVec 32) ∧
                    state.regs.get? minstretcfg = some (0 : BitVec 64) ∧
                      state.regs.get? elp = some
                        (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED) ∧
                        match state.regs.get? misa with
                        | some misaBits => Sail.BitVec.access misaBits 12 = 1#1
                        | none => False

/-! ## The registers a retiring `ret` reads

`Step/ControlFlow.lean`'s `tryStepRetRetires` is the lemma that turns a compiled function's final
`ret` into a retirement, and each of its premises bottoms out in register reads. Walking them down —
rather than reading the signature — gives the list below. `NormalExecutionState` already covers
twelve registers (`hart_state` for `hartRead`, `mcountinhibit` for `inhibitRead`, `minstretcfg` for
`configRead`, `elp` for `notExpected`, `misa` for the `Zca` read, `misa`/`mip`/`mie`/`mideleg` for
`InterruptDisabled`, `cur_privilege`/`pmpcfg_n`/`pmpaddr_n` for `FetchBasePlatform`, `satp` for the
translation). Five more are reached only through the premises:

| register | premise that reaches it |
| --- | --- |
| `mstatus` | `InterruptDisabled` **and** `FetchBasePlatform` |
| `sig_meip` | `InterruptDisabled` (`Logic/Framing.lean`) |
| `pma_regions` | `FetchBasePlatform` → `FetchPmaAllows`, at its **value**: the premise evaluates `matching_pma_region` on it |
| `mseccfg` | the `decode` premise (`ext_decode` gates on it) and `helpElp` (`update_elp_state` consults `Ext_Zicfilp`, which reads `mseccfg` at Machine privilege) |
| `htif_tohost_base` | `noMMIO`. `FetchMemoryNoMMIO` is a run of `within_mmio_readable`, which dispatches to `within_clint`/`within_sig`/`within_htif_readable`; the first two read **no** register and depend on `pc` alone, and the third reads exactly this one. `Platform/FetchMmio.lean`'s `fetchMemoryNoMMIO_of_agree` proves that, so the dispatch needs no clause of its own |

`minstret` is deliberately **not** in that list even though `retiredRead` reads it, and the reason is
in `RetiredCounterPresent` below.
-/

/-- The twelve registers `NormalExecutionState` reads. -/
def normalRegisters : Register → Prop := fun r =>
  r = hart_state ∨ r = cur_privilege ∨ r = satp ∨ r = mideleg ∨ r = mie ∨ r = mip ∨
    r = pmpcfg_n ∨ r = pmpaddr_n ∨ r = mcountinhibit ∨ r = minstretcfg ∨ r = elp ∨ r = misa

/--
**The registers a callee owes its caller unchanged**: the link register, the twelve
`NormalExecutionState` pins, and the five platform registers a single `ret`'s own premises reach.

`x1` is here because the sentinel bridge's `linkIsSentinel` is a fact about the value `ret` reads out
of the link register. The rest are here because the retirement's premises read them.

`PC` and `nextPC` are deliberately absent — a call changes them, and the pc the exit fetch happens at
comes from the trace rather than from preservation. `minstret` is absent for a sharper reason: see
`RetiredCounterPresent`.
-/
def platformPreserved : Register → Prop := fun r =>
  r = x1 ∨
    r = hart_state ∨ r = cur_privilege ∨ r = satp ∨ r = mideleg ∨ r = mie ∨ r = mip ∨
      r = pmpcfg_n ∨ r = pmpaddr_n ∨ r = mcountinhibit ∨ r = minstretcfg ∨ r = elp ∨ r = misa ∨
        r = mstatus ∨ r = sig_meip ∨ r = pma_regions ∨ r = mseccfg ∨ r = htif_tohost_base

/--
**The retired-instruction counter is readable.** `tryStepRetRetires`' `retiredRead` premise reads
`minstret`, so the exit state must carry it — but as *presence*, which is why it cannot be folded
into `platformPreserved`.

The machine writes `minstret` on every retirement: `tryStepControlFlowAfterRetired` is literally
`writeReg minstret (retired + 1)`. So "the callee left `minstret` alone" is **false of every routine
that retires a single instruction**, and a false conjunct in a postcondition consumed through an
assumed hypothesis makes the consumer vacuous — strictly worse than a missing clause. The counter
therefore gets the weaker claim that is true.
-/
def RetiredCounterPresent (state : State) : Prop :=
  ∃ retired, state.regs.get? minstret = some retired

theorem normalRegisters_platformPreserved : ∀ r, normalRegisters r → platformPreserved r := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [platformPreserved]

/-- **`NormalExecutionState` transports across any step that preserves the twelve platform
registers.** This is what carries the predicate from a state where it is established to the exit
state a callee-frame clause speaks about. -/
theorem normalExecutionState_of_agree {before after : State}
    (agree : Agree normalRegisters before after) (h : NormalExecutionState before) :
    NormalExecutionState after := by
  obtain ⟨hhart, hpriv, hsatp, hmideleg, hmie, hmip, hpmpcfg, hpmpaddr, hinhibit, hcfg, help,
    hmisa⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?misa⟩
  case misa =>
    rw [agree misa (by simp [normalRegisters])]
    exact hmisa
  all_goals
    first
      | (rw [agree hart_state (by simp [normalRegisters])]; exact hhart)
      | (rw [agree cur_privilege (by simp [normalRegisters])]; exact hpriv)
      | (rw [agree satp (by simp [normalRegisters])]; exact hsatp)
      | (rw [agree mideleg (by simp [normalRegisters])]; exact hmideleg)
      | (rw [agree mie (by simp [normalRegisters])]; exact hmie)
      | (rw [agree mip (by simp [normalRegisters])]; exact hmip)
      | (rw [agree pmpcfg_n (by simp [normalRegisters])]; exact hpmpcfg)
      | (rw [agree pmpaddr_n (by simp [normalRegisters])]; exact hpmpaddr)
      | (rw [agree mcountinhibit (by simp [normalRegisters])]; exact hinhibit)
      | (rw [agree minstretcfg (by simp [normalRegisters])]; exact hcfg)
      | (rw [agree elp (by simp [normalRegisters])]; exact help)

/-! ### What the one `Agree platformPreserved` clause hands back

One named lemma per register beyond `NormalExecutionState`'s twelve, so a consumer cites the register
it needs rather than an index into an eighteen-fold disjunction — and so a register quietly dropped
from `platformPreserved` breaks a theorem whose *name* says which one. -/

theorem platformPreserved_link {before after : State}
    (agree : Agree platformPreserved before after) :
    after.regs.get? x1 = before.regs.get? x1 :=
  agree x1 (by simp [platformPreserved])

theorem platformPreserved_mstatus {before after : State}
    (agree : Agree platformPreserved before after) :
    after.regs.get? mstatus = before.regs.get? mstatus :=
  agree mstatus (by simp [platformPreserved])

theorem platformPreserved_sigMeip {before after : State}
    (agree : Agree platformPreserved before after) :
    after.regs.get? sig_meip = before.regs.get? sig_meip :=
  agree sig_meip (by simp [platformPreserved])

theorem platformPreserved_pmaRegions {before after : State}
    (agree : Agree platformPreserved before after) :
    after.regs.get? pma_regions = before.regs.get? pma_regions :=
  agree pma_regions (by simp [platformPreserved])

theorem platformPreserved_mseccfg {before after : State}
    (agree : Agree platformPreserved before after) :
    after.regs.get? mseccfg = before.regs.get? mseccfg :=
  agree mseccfg (by simp [platformPreserved])

theorem platformPreserved_htifBase {before after : State}
    (agree : Agree platformPreserved before after) :
    after.regs.get? htif_tohost_base = before.regs.get? htif_tohost_base :=
  agree htif_tohost_base (by simp [platformPreserved])

/-- **The clause carries `NormalExecutionState` across the call**, which is the half of the old
absolute clause that survives: preservation plus a normal entry state gives a normal exit state. -/
theorem normalExecutionState_of_platformPreserved {before after : State}
    (agree : Agree platformPreserved before after) (h : NormalExecutionState before) :
    NormalExecutionState after :=
  normalExecutionState_of_agree (agree.weaken normalRegisters_platformPreserved) h

end BinaryFv.RiscV
