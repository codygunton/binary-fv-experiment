import BinaryFv.RiscV.Elfling.SequentialSplice
import BinaryFv.RiscV.Logic.MemoryWriteFrame
import BinaryFv.RiscV.Step.RegisterWrite

/-!
# `Seg`: one accumulator for a straight-line run of retired instructions

## The scaffolding this removes

Every per-instruction step lemma in the tree concludes

```
∃ retired, Runs (try_step k false) state (afterRegisterWrite state pc retired dest value) false
```

and the successor state mentions the `∃`-bound `retired`. A successor that cannot be *named* cannot
appear in a statement, so a composition must destructure the existential, `let`-bind the post-state,
and then re-fold that `let` at every later use -- the `obtain ⟨rN, hN⟩` / `let sN := …` /
`simpa [sN] using runN` ritual, 452 occurrences repo-wide.

`Seg` makes the successor opaque. Every combinator here concludes `∃ next, Seg … next …`, so the
caller writes `obtain ⟨next, seg⟩ := …` and never names a post-state definition again. What the
caller would have re-derived by unfolding is instead read off the fields.

## What it accumulates, and why each accumulator is needed

* `trace` and `confined` are the two obligations a Level 2 composition has to produce anyway.
* `writes` is the register frame (`WritesOnlyRegs`): "this segment touched nothing outside `W`",
  which answers every *preservation* question by one membership check (`Seg.get`).
* `mem` is the memory frame (`WritesOnlyWithin` over a `Region`). It is **not**
  `cur.mem = base.mem`: about eight of the composed instructions in this tree are stores, and the
  equality form is false of every one of them. `Seg.memEq` recovers the equality for the
  register-only case, where the region is empty.
* `regs` is a *positive* accumulator (`RegsHold`), a last-write-wins association list. The write
  frame alone cannot answer "what is in `x10`?" three instructions after `x10` was written -- it
  says only which registers were left alone. Values written inside the segment have to be carried.

## Why the frames compose at a *fixed* `W` and `M`

`WritesOnlyRegs.trans_same` and `WritesOnlyWithin.trans_same` both compose at one
fixed set, and each step widens into it first (`Seg.stepOf`'s `widen`). Letting the set grow one
`Or` per instruction makes the `Decidable` instance for a membership goal exceed
`synthInstance.maxSize` at roughly eight steps -- i.e. exactly where a segment combinator starts to
pay. Fixing the set keeps every membership check the same size at any depth.
-/

namespace BinaryFv.RiscV

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.Binary.Elfling (FunctionInstanceId)
open BinaryFv.RiscV.Elfling (ConfinedPrefix)

/-! ## The positive register accumulator -/

/-- A register paired with a value of *that register's* type.

`Sigma` rather than a pair because `RegisterType` is a family: `PC` holds a `BitVec 64`,
`hart_state` holds a `HartState`, and a homogeneous list could not hold both. -/
abbrev RegVal := (r : Register) × RegisterType r

/-- The registers of `s` whose values a segment has recorded. Order is irrelevant to the
statement; combinators push new writes on the front, so the list reads last-write-first. -/
def RegsHold (s : State) (kv : List RegVal) : Prop :=
  ∀ p ∈ kv, s.regs.get? p.1 = some p.2

/-- The side condition for carrying `kv` across a step: none of the recorded registers is one the
step writes.

`@[reducible]` for the same reason `RegSet.only` is: this is discharged by `decide` at every call
site, and typeclass synthesis unfolds at `.instances` transparency only. The `Decidable` instance is
`List.decidableBAll` over the recorded registers, so it costs one `Register` disequality per
recorded register per step and never looks at the recorded *values*. -/
@[reducible] def RegsOutside (V : RegSet) (kv : List RegVal) : Prop :=
  ∀ p ∈ kv, ¬ V p.1

namespace RegsHold

theorem nil (s : State) : RegsHold s [] := by
  intro p hp
  cases hp

theorem cons {s : State} {kv : List RegVal} (r : Register) (v : RegisterType r)
    (hv : s.regs.get? r = some v) (rest : RegsHold s kv) : RegsHold s (⟨r, v⟩ :: kv) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h
  · exact hv
  · exact rest p h

theorem append {s : State} {kv1 kv2 : List RegVal}
    (h1 : RegsHold s kv1) (h2 : RegsHold s kv2) : RegsHold s (kv1 ++ kv2) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · exact h2 p h

/-- One recorded value, read back by naming the register and the value.

Both are explicit: with the value implicit, `seg.regs _ (by simp)` leaves the value as a
metavariable and the membership proof cannot be elaborated. -/
theorem get {s : State} {kv : List RegVal} (h : RegsHold s kv) (r : Register)
    (v : RegisterType r) (hp : (⟨r, v⟩ : RegVal) ∈ kv) : s.regs.get? r = some v :=
  h ⟨r, v⟩ hp

/-- **Carrying the accumulator across a step.** Every recorded register lies outside the step's
write set, so the write frame transports the whole list at once. -/
theorem through {V : RegSet} {s t : State} {kv : List RegVal}
    (h : RegsHold s kv) (w : WritesOnlyRegs V s t) (out : RegsOutside V kv) : RegsHold t kv :=
  fun p hp => (w p.1 (out p hp)).trans (h p hp)

end RegsHold

/-! ## Memory frames for steps that touch no memory -/

/-- A step that leaves memory pointwise alone is confined to any region, including the empty one.
This is what every register-writing instruction supplies for `Seg`'s `mem` field. -/
theorem writesOnlyWithin_of_mem_eq {M : Region} {s t : State} (h : t.mem = s.mem) :
    WritesOnlyWithin M s t := fun _ _ => by rw [h]

/-- Confinement to the empty region *is* memory equality: `Std.ExtHashMap` is extensional, so the
pointwise statement upgrades. This is how a caller that still wants `after.mem = before.mem` --
`CodeIntact` transport, for one -- gets it out of the general region-valued field. -/
theorem mem_eq_of_writesOnlyWithin_empty {M : Region} {s t : State}
    (h : WritesOnlyWithin M s t) (empty : ∀ address, ¬ M address) : t.mem = s.mem :=
  Std.ExtHashMap.ext_getElem?_iff.mpr (fun address => h address (empty address))

/-- The empty region: what a segment of register-only instructions is confined to. -/
@[reducible] def noMemory : Region := fun _ => False

theorem noMemory_empty : ∀ address, ¬ noMemory address := fun _ h => h

/-! ## The segment itself -/

/--
`Seg own exit childSummary W M kv fromStep len base cur pc` -- `len` retired instructions carried
the machine from `base` to `cur`, which sits at `pc`.

The state `cur` is meant to be an *opaque* local: every combinator below concludes
`∃ next, Seg … next …`, and the caller obtains it without ever writing down a post-state
definition. Everything a caller can learn about it comes from the fields.
-/
structure Seg (own exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (W : RegSet) (M : Region) (kv : List RegVal) (fromStep len : Nat)
    (base cur : State) (pc : BitVec 64) : Prop where
  /-- `len` consecutive `try_step`s retired normally from `base` to `cur`. -/
  trace : Trace fromStep len base cur
  /-- Those steps stayed inside the parent region and off every exit. -/
  confined : ConfinedPrefix own exit childSummary fromStep len base cur
  /-- The register frame: nothing outside `W` moved. -/
  writes : WritesOnlyRegs W base cur
  /-- The memory frame: nothing outside `M` was stored to. -/
  mem : WritesOnlyWithin M base cur
  /-- The retired counter is still readable, which the next step's premises need. -/
  retired : RetiredCounterPresent cur
  /-- Where the machine is now. -/
  atPc : cur.regs.get? PC = some pc
  /-- The values written inside the segment that later instructions read back. -/
  regs : RegsHold cur kv

namespace Seg

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
  {W : RegSet} {M : Region} {kv : List RegVal} {a n : Nat} {base cur : State} {pc : BitVec 64}

/-- The empty segment. `W` and `M` are the sets the *whole* segment will be composed at, chosen
once here; see the module docstring on why they are fixed rather than accumulated. -/
theorem nil (own exit : BitVec 64 → Prop)
    (childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop)
    (W : RegSet) (M : Region) (a : Nat) {base : State} {pc : BitVec 64}
    (retiredPresent : RetiredCounterPresent base) (atPc : base.regs.get? PC = some pc) :
    Seg own exit childSummary W M [] a 0 base base pc where
  trace := Trace.refl a base
  confined := ConfinedPrefix.nil
  writes := WritesOnlyRegs.refl W base
  mem := fun _ _ => rfl
  retired := retiredPresent
  atPc := atPc
  regs := RegsHold.nil base

/-! ### Reading a segment -/

/-- **A register the segment did not write reads through to `base`.** One membership check, whatever
the register and however long the segment. -/
theorem get (seg : Seg own exit childSummary W M kv a n base cur pc) (r : Register) (hr : ¬ W r) :
    cur.regs.get? r = base.regs.get? r := seg.writes r hr

/-- **A register the segment did write reads back its recorded value.** `r` and `v` are explicit:
with `v` implicit the membership argument elaborates against a metavariable and fails. -/
theorem reg (seg : Seg own exit childSummary W M kv a n base cur pc) (r : Register)
    (v : RegisterType r) (hp : (⟨r, v⟩ : RegVal) ∈ kv) : cur.regs.get? r = some v :=
  seg.regs.get r v hp

/-- Agreement on any preserved set disjoint from the segment's write set. -/
theorem agree (seg : Seg own exit childSummary W M kv a n base cur pc) {P : RegSet}
    (disjoint : RegSet.Disjoint P W) : Agree P base cur := seg.writes.agree disjoint

/-- Memory equality, for a segment confined to an empty region. -/
theorem memEq (seg : Seg own exit childSummary W M kv a n base cur pc)
    (empty : ∀ address, ¬ M address) : cur.mem = base.mem :=
  mem_eq_of_writesOnlyWithin_empty seg.mem empty

/-- Record a value the caller proved by other means -- typically `seg.get` composed with a fact
about `base`. Used to seed the accumulator with an incoming register the segment will need later. -/
theorem know (seg : Seg own exit childSummary W M kv a n base cur pc) (r : Register)
    (v : RegisterType r) (hv : cur.regs.get? r = some v) :
    Seg own exit childSummary W M (⟨r, v⟩ :: kv) a n base cur pc :=
  { seg with regs := seg.regs.cons r v hv }

/-- **Drop recorded values a later step is about to invalidate.**

A register written *twice* inside one segment -- the wrapper prologue materializes `a1` at
`0x102cc` and reloads it at `0x102d4`, four instructions later -- leaves the first value recorded
after the instruction that consumed it has retired. `stepOf`'s `keep` obligation then rightly
rejects the second write, since the accumulator would otherwise carry a value the step destroys.
Nothing else can be done about it from the caller's side: `step` always conses what it wrote, and
`RegsHold` is a conjunction, so the stale entry has to come off before the clobbering step.

`sub` is the sublist condition and is `by simp` at every concrete list. -/
theorem forget (seg : Seg own exit childSummary W M kv a n base cur pc) {kv' : List RegVal}
    (sub : ∀ p ∈ kv', p ∈ kv) : Seg own exit childSummary W M kv' a n base cur pc :=
  { seg with regs := fun p hp => seg.regs p (sub p hp) }

/-! ### Extending a segment -/

/--
**The transformer-agnostic step.** One retired instruction, described by a family `after` indexed by
the `∃`-bound retired counter, extends the segment by one.

Everything the caller supplies is stated `∀ retired`, so the counter never escapes into the
conclusion: the successor is existential, and the caller obtains an opaque `next`.

`V` is the step's own write set -- small, per-instruction -- widened into the segment's fixed `W` by
`widen`. `kv'` is what the step *learns* (usually the one register it wrote); `keep` is the promise
that it clobbered nothing already recorded.
-/
theorem stepOf {V : RegSet} {kv' : List RegVal} {nextPc : BitVec 64}
    (seg : Seg own exit childSummary W M kv a n base cur pc)
    (inRegion : own pc) (notExit : ¬ exit pc)
    (after : BitVec 64 → State)
    (run : ∃ retired, Runs (try_step (a + n) false) cur (after retired) false)
    (stepWrites : ∀ retired, WritesOnlyRegs V cur (after retired))
    (stepMem : ∀ retired, WritesOnlyWithin M cur (after retired))
    (stepRetired : ∀ retired, RetiredCounterPresent (after retired))
    (stepPc : ∀ retired, (after retired).regs.get? PC = some nextPc)
    (learn : ∀ retired, RegsHold (after retired) kv')
    (widen : ∀ r, V r → W r)
    (keep : RegsOutside V kv) :
    ∃ next, Seg own exit childSummary W M (kv' ++ kv) a (n + 1) base next nextPc := by
  obtain ⟨retired, run⟩ := run
  exact ⟨after retired,
    { trace := seg.trace.snoc run
      confined := seg.confined.trans (ConfinedPrefix.ownStep seg.atPc inRegion notExit run)
      writes := seg.writes.trans_same ((stepWrites retired).mono widen)
      mem := WritesOnlyWithin.trans_same seg.mem (stepMem retired)
      retired := stepRetired retired
      atPc := stepPc retired
      regs := (learn retired).append (seg.regs.through (stepWrites retired) keep) }⟩

end Seg

/-! ## The `afterRegisterWrite` frame facts a step needs

`afterRegisterWrite_{writes, mem, retired_present, pc}` already exist in `RegisterWriteStep`. The
destination read does not, and it is the one `Seg.step` cannot do without: the whole point of the
positive accumulator is to carry the value the instruction just wrote.
-/

/-- **The value a register-writing retirement left in its destination.**

The two disequalities are the postlude's own writes: `tick_pc` overwrites `PC` and the retirement
overwrites `minstret` *after* the execute wrote `destination`, so an instruction targeting either
would not see its own value survive. Both are `by decide` at any concrete destination. -/
theorem afterRegisterWrite_destination (state : State) (pc retired : BitVec 64)
    (destination : Register) (value : RegisterType destination)
    (notPc : destination ≠ PC) (notRetired : destination ≠ minstret) :
    (afterRegisterWrite state pc retired destination value).regs.get? destination = some value := by
  simp [afterRegisterWrite, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    coreControlFlowNextState, tryStepControlFlowAfterIncrement, Std.ExtDHashMap.get?_insert,
    notPc.symm, notRetired.symm]

/-! ## The jump-retirement frame facts a step needs

`jumpRetirement_writes` in `Step/ControlFlow.lean` covers the register frame. `Seg.stepJump` also
needs where the jump landed and that the counter survived, and so does every caller that today
re-derives them by unfolding four post-state definitions against `Std.ExtDHashMap.get?_insert`.
-/

/-- **Where a jump retirement leaves `PC`**: at the target, because `tick_pc` copies `nextPC` and
`controlFlowJumpState` put the target there. -/
theorem jumpRetirement_pc (state : State) (pc target retired : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target)
      target retired).regs.get? PC = some target := by
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

/-- A jump retirement leaves the retired counter readable, at `retired + 1`. -/
theorem jumpRetirement_retired_present (state : State) (pc target retired : BitVec 64) :
    RetiredCounterPresent (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target) target retired) :=
  ⟨Sail.BitVec.addInt retired 1, by
    simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩

/-- A jump retirement writes no memory. -/
theorem jumpRetirement_mem (state : State) (pc target retired : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement state) pc target)
      target retired).mem = state.mem := rfl

theorem fallThroughRetirement_pc (state : State) (pc target retired : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      target retired).regs.get? PC = some target := by
  simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
    Std.ExtDHashMap.get?_insert]

theorem fallThroughRetirement_retired_present (state : State) (pc target retired : BitVec 64) :
    RetiredCounterPresent (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc) target retired) :=
  ⟨Sail.BitVec.addInt retired 1, by
    simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩

theorem fallThroughRetirement_mem (state : State) (pc target retired : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) pc)
      target retired).mem = state.mem := rfl

/-! ## The two step shapes this tree actually composes -/

namespace Seg

variable {own exit : BitVec 64 → Prop}
  {childSummary : FunctionInstanceId → Nat → Nat → State → State → Prop}
  {W : RegSet} {M : Region} {kv : List RegVal} {a n : Nat} {base cur : State} {pc : BitVec 64}

/--
**A register-writing fall-through instruction.** The `∃ retired, Runs … (afterRegisterWrite …) …`
that every step lemma in the tree concludes, consumed directly.

`nextPc` is explicit rather than implicit-with-`advance := by decide`: as an implicit it is a
metavariable when the default argument elaborates, and `decide` refuses ("expected type must not
contain metavariables").

`bookkeeping` is `∀ r, stepBookkeeping r → W r` and not the more natural
`∀ r, RegSet.union stepBookkeeping (RegSet.only dest) r → W r`, because the latter is not closed
under `by decide` (it quantifies over all 176 registers with a hypothesis `W` cannot evaluate).
Hoisted this way it is proved once per segment by `rintro … <;> decide`.
-/
theorem step (seg : Seg own exit childSummary W M kv a n base cur pc)
    (inRegion : own pc) (notExit : ¬ exit pc)
    (dest : Register) (value : RegisterType dest) (nextPc : BitVec 64)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired dest value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (bookkeeping : ∀ r, stepBookkeeping r → W r) (destination : W dest)
    (destNotPc : dest ≠ PC) (destNotRetired : dest ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only dest)) kv) :
    ∃ next,
      Seg own exit childSummary W M (⟨dest, value⟩ :: kv) a (n + 1) base next nextPc :=
  seg.stepOf inRegion notExit
    (fun retired => afterRegisterWrite cur pc retired dest value) run
    (fun retired => afterRegisterWrite_writes cur pc retired dest value)
    (fun retired => writesOnlyWithin_of_mem_eq (afterRegisterWrite_mem cur pc retired dest value))
    (fun retired => afterRegisterWrite_retired_present cur pc retired dest value)
    (fun retired => advance ▸ afterRegisterWrite_pc cur pc retired dest value)
    (fun retired =>
      RegsHold.cons dest value
        (afterRegisterWrite_destination cur pc retired dest value destNotPc destNotRetired)
        (RegsHold.nil _))
    (fun r hr => hr.elim (bookkeeping r) (fun h => h ▸ destination))
    keep

/-- `step` retaining the concrete post-register-write shape for a caller that must transport a
machine fact through this particular instruction.  The segment itself remains opaque to later
composition. -/
theorem stepWitness (seg : Seg own exit childSummary W M kv a n base cur pc)
    (inRegion : own pc) (notExit : ¬ exit pc)
    (dest : Register) (value : RegisterType dest) (nextPc : BitVec 64)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (afterRegisterWrite cur pc retired dest value) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (bookkeeping : ∀ r, stepBookkeeping r → W r) (destination : W dest)
    (destNotPc : dest ≠ PC) (destNotRetired : dest ≠ minstret)
    (keep : RegsOutside (RegSet.union stepBookkeeping (RegSet.only dest)) kv) :
    ∃ retired next, next = afterRegisterWrite cur pc retired dest value ∧
      Seg own exit childSummary W M (⟨dest, value⟩ :: kv) a (n + 1) base next nextPc := by
  obtain ⟨retired, hrun⟩ := run
  refine ⟨retired, _, rfl, ?_⟩
  refine
    { trace := seg.trace.snoc hrun
      confined := seg.confined.trans (ConfinedPrefix.ownStep seg.atPc inRegion notExit hrun)
      writes := seg.writes.trans_same ((afterRegisterWrite_writes cur pc retired dest value).mono
        (fun r hr => hr.elim (bookkeeping r) (fun h => h ▸ destination)))
      mem := WritesOnlyWithin.trans_same seg.mem
        (writesOnlyWithin_of_mem_eq (afterRegisterWrite_mem cur pc retired dest value))
      retired := afterRegisterWrite_retired_present cur pc retired dest value
      atPc := advance ▸ afterRegisterWrite_pc cur pc retired dest value
      regs := (RegsHold.cons dest value
        (afterRegisterWrite_destination cur pc retired dest value destNotPc destNotRetired)
        (RegsHold.nil _)).append
        (seg.regs.through (afterRegisterWrite_writes cur pc retired dest value) keep) }

/-- **A jump.** `Seg.step` hardcodes `pc + 4`; a taken branch, a `jal` or a `ret` retires into
`tryStepControlFlowAfterRetired (controlFlowJumpState …)` and lands at an arbitrary `target`, so it
needs its own row. It writes no architectural register -- the target goes to `nextPC`, which
`stepBookkeeping` already contains -- so it learns nothing and needs no `destination` premise. -/
theorem stepJump (seg : Seg own exit childSummary W M kv a n base cur pc) (target : BitVec 64)
    (inRegion : own pc) (notExit : ¬ exit pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (controlFlowJumpState (tryStepControlFlowAfterIncrement cur) pc target) target retired)
      false)
    (bookkeeping : ∀ r, stepBookkeeping r → W r)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next, Seg own exit childSummary W M kv a (n + 1) base next target :=
  seg.stepOf (kv' := []) inRegion notExit
    (fun retired => tryStepControlFlowAfterRetired
      (controlFlowJumpState (tryStepControlFlowAfterIncrement cur) pc target) target retired) run
    (fun retired => jumpRetirement_writes cur pc target retired)
    (fun retired => writesOnlyWithin_of_mem_eq (jumpRetirement_mem cur pc target retired))
    (fun retired => jumpRetirement_retired_present cur pc target retired)
    (fun retired => jumpRetirement_pc cur pc target retired)
    (fun _ => RegsHold.nil _)
    bookkeeping keep

/-- A comparison or branch-not-taken retirement that advances through the base control-flow path. -/
theorem stepFallThrough (seg : Seg own exit childSummary W M kv a n base cur pc)
    (target : BitVec 64) (inRegion : own pc) (notExit : ¬ exit pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc) target retired) false)
    (bookkeeping : ∀ r, stepBookkeeping r → W r)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next, Seg own exit childSummary W M kv a (n + 1) base next target :=
  seg.stepOf (kv' := []) inRegion notExit
    (fun retired => tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc) target retired) run
    (fun retired => fallThroughRetirement_writes cur pc target retired)
    (fun retired => writesOnlyWithin_of_mem_eq (fallThroughRetirement_mem cur pc target retired))
    (fun retired => fallThroughRetirement_retired_present cur pc target retired)
    (fun retired => fallThroughRetirement_pc cur pc target retired)
    (fun _ => RegsHold.nil _) bookkeeping keep

/-- A fall-through store.  The class-specific proof supplies `run`; this adapter records the
store's established register and memory frames without exposing its successor state. -/
theorem stepStore {width : Nat} (seg : Seg own exit childSummary W M kv a n base cur pc)
    (address : Nat) (value : BitVec (8 * width)) (nextPc : BitVec 64)
    (inRegion : own pc) (notExit : ¬ exit pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          address value)
        (Sail.BitVec.addInt pc 4) retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (inside : ∀ other, address ≤ other → other < address + width → M other)
    (bookkeeping : ∀ r, stepBookkeeping r → W r)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ next, Seg own exit childSummary W M kv a (n + 1) base next nextPc :=
  seg.stepOf (kv' := []) inRegion notExit
    (fun retired => tryStepControlFlowAfterRetired
      (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
        address value)
      (Sail.BitVec.addInt pc 4) retired) run
    (fun retired => storeRetirement_writes cur pc (Sail.BitVec.addInt pc 4) retired address value)
    (fun retired other outside =>
      storeRetirement_mem_writes cur pc (Sail.BitVec.addInt pc 4) retired address value other
        (fun written => outside (inside other written.1 written.2)))
    (fun retired => ⟨Sail.BitVec.addInt retired 1, by
      simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩)
    (fun retired => advance ▸ by
      simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
        afterWriteBytes_regs, Std.ExtDHashMap.get?_insert])
    (fun _ => RegsHold.nil _) bookkeeping keep

/-- `stepStore` with the concrete retirement witness retained for a caller that must state a
byte-level consequence of this particular store.  The segment successor remains opaque to later
composition, while the equality exposes exactly one post-store shape. -/
theorem stepStoreWitness {width : Nat} (seg : Seg own exit childSummary W M kv a n base cur pc)
    (address : Nat) (value : BitVec (8 * width)) (nextPc : BitVec 64)
    (inRegion : own pc) (notExit : ¬ exit pc)
    (run : ∃ retired, Runs (try_step (a + n) false) cur
      (tryStepControlFlowAfterRetired
        (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          address value)
        (Sail.BitVec.addInt pc 4) retired) false)
    (advance : Sail.BitVec.addInt pc 4 = nextPc)
    (inside : ∀ other, address ≤ other → other < address + width → M other)
    (bookkeeping : ∀ r, stepBookkeeping r → W r)
    (keep : RegsOutside stepBookkeeping kv) :
    ∃ retired next,
      next = tryStepControlFlowAfterRetired
        (afterWriteBytes (coreControlFlowNextState (tryStepControlFlowAfterIncrement cur) pc)
          address value)
        (Sail.BitVec.addInt pc 4) retired ∧
      Seg own exit childSummary W M kv a (n + 1) base next nextPc := by
  obtain ⟨retired, hrun⟩ := run
  refine ⟨retired, _, rfl, ?_⟩
  refine
    { trace := seg.trace.snoc hrun
      confined := seg.confined.trans (ConfinedPrefix.ownStep seg.atPc inRegion notExit hrun)
      writes := seg.writes.trans_same ((storeRetirement_writes cur pc (Sail.BitVec.addInt pc 4)
        retired address value).mono bookkeeping)
      mem := WritesOnlyWithin.trans_same seg.mem (fun other outside =>
        storeRetirement_mem_writes cur pc (Sail.BitVec.addInt pc 4) retired address value other
          (fun written => outside (inside other written.1 written.2)))
      retired := ⟨Sail.BitVec.addInt retired 1, by
        simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick]⟩
      atPc := advance ▸ by
        simp [tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
          afterWriteBytes_regs, Std.ExtDHashMap.get?_insert]
      regs := seg.regs.through
        (storeRetirement_writes cur pc (Sail.BitVec.addInt pc 4) retired address value) keep }

end Seg

/-! ## Regressions

The positive and negative checks below pin the control-flow distinction introduced by
`stepFallThrough`: the postlude copies its explicit fall-through target to `PC`, and cannot produce
a different literal target.
-/

example (state : State) (retired : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x1000#64))
      (0x1004#64) retired).regs.get? PC = some (0x1004#64) :=
  fallThroughRetirement_pc state (0x1000#64) (0x1004#64) retired

example (state : State) (retired : BitVec 64) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (0x1000#64))
      (0x1004#64) retired).regs.get? PC ≠ some (0x1008#64) := by
  rw [fallThroughRetirement_pc]
  decide

/-! The two facts a call site silently depends on, kept as examples for the same reason
`regSet_only_union_decide` is kept in `RegisterAgree.lean`: if either breaks, what fails downstream
is a `by decide` argument in an unrelated file, reported against a goal that does not name the
cause.
-/

/-- `RegsOutside`'s `@[reducible]` is load-bearing. Typeclass synthesis unfolds at `.instances`
transparency only, so as a plain `def` this is `failed to synthesize Decidable` at every `keep`
argument of every step.

The recorded *value* is a free variable here on purpose: the decision looks only at `p.1`, so it
costs one `Register` disequality per recorded register whatever the values are. That matters
because values accumulated inside a real segment are symbolic (`BitVec.ofNat 64 (args.bytes.size +
…)` and the like), and a check that had to evaluate them would be useless. `of_decide_eq_true rfl`
rather than `by decide` only because the tactic refuses a goal with free variables. -/
example (v : BitVec 64) :
    RegsOutside (RegSet.union stepBookkeeping (RegSet.only x10)) [⟨x2, v⟩, ⟨x18, v⟩] :=
  of_decide_eq_true rfl

/-- `RegsOutside` is a real check and not vacuously true: a recorded register that the step writes
is rejected. Without this the accumulator would carry stale values across the write that killed
them. -/
example (v : BitVec 64) : ¬ RegsOutside stepBookkeeping [⟨PC, v⟩] := of_decide_eq_false rfl

end BinaryFv.RiscV
