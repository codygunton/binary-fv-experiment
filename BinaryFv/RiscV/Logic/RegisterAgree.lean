import BinaryFv.RiscV.Model.State

/-!
# Agreement on a set of registers, and the write sets that produce it

`Agree P base t` says `t` and `base` hold the same value in every register satisfying `P`. Machine
loops instantiate `P` with the complement of the write set of the loop body, giving the usual
"stable registers are preserved" relation.

`WritesOnlyRegs` below is that write set, made explicit. It is the register-side counterpart of
`BinaryFv.Zesu.Contracts.WritesOnlyWithin`, which states the same thing about `.mem` over a
`Region`, and it is stated in the same orientation and argument order so the two read alike.

The point of stating the write set rather than the preserved set is that the write set is a property
of the *step* and does not depend on which registers a later proof happens to care about. A step
lemma proves its write set once; every observation of a register outside that set is then a
membership check, whatever register it is. Stating the preserved set instead fixes that choice up
front, and any register omitted from it has to be re-derived by hand at each use --
`platformPreserved` holds `x1` and seventeen CSRs and no other general-purpose register, which is
why reads of `x2`, `x8`-`x13` and `x18` through a step are currently re-proved inline.
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

/-! ## Write sets -/

/-- A set of registers, as a predicate.

`Register → Prop` rather than `List Register` for three reasons. `Agree`, `platformPreserved`,
`decoderPreserved` and `MemcpyProof.NonW` are already this type, so `WritesOnlyRegs.agree` below
relates a preserved set and a write set without a coercion. An `Or`-chain destructures directly
under `rintro (rfl | rfl)`, where `r ∈ [a, b]` is `List.Mem` and needs a `List.mem_cons`
normalisation first. And a write set containing a *parameter* -- `destination` in
`afterRegisterWrite`, `linkReg` in `callLinkState` -- has no list form that `decide` can evaluate,
whereas `RegSet.union closed (RegSet.only destination)` keeps the closed and open halves separate so
`RegSet.Disjoint.union` can split the obligation along them. -/
abbrev RegSet := Register → Prop

/-- The write set of a step that writes exactly `w`.

`@[reducible]` is load-bearing rather than decoration: typeclass synthesis unfolds at `.instances`
transparency only, so a plain `def` here makes `by decide` on a membership goal fail with `failed to
synthesize Decidable` at every call site. `regSet_only_union_decide` below pins that. -/
@[reducible] def RegSet.only (w : Register) : RegSet := fun r => r = w

/-- The write set of two steps run in sequence. See `RegSet.only` on `@[reducible]`. -/
@[reducible] def RegSet.union (a b : RegSet) : RegSet := fun r => a r ∨ b r

/-- Every register the step writes lies inside `written`; equivalently, every register outside
`written` reads the same after as before.

This is permission, not requirement: a step that writes nothing satisfies it for any `written`, and
`WritesOnlyRegs.mono` widens. The orientation is `after = before`, matching
`Contracts.WritesOnlyWithin` on the memory side and `writeReg_read_unchanged` in
`BinaryFv.RiscV.Logic.Framing`, which every transformer's write-set lemma reduces to. -/
def WritesOnlyRegs (written : RegSet) (before after : State) : Prop :=
  ∀ r : Register, ¬ written r → after.regs.get? r = before.regs.get? r

namespace WritesOnlyRegs

theorem refl (W : RegSet) (s : State) : WritesOnlyRegs W s s := fun _ _ => rfl

/-- Composition at one fixed write set, and the form a multi-step trace should use.

Widen each step into the function's write set first, with `mono`, and compose here. The alternative
-- composing with `trans` and letting the set grow -- builds an `Or`-chain one step per instruction,
and at roughly eight steps the `Decidable` instance for a membership goal exceeds
`synthInstance.maxSize` and aborts before the kernel sees it. Composing at a fixed set keeps the
decided predicate the same size at any trace depth.

This mirrors `Contracts.Ownership.writesOnlyWithin_trans`, which composes at a fixed `Region` for
the same reason. -/
theorem trans_same {W : RegSet} {s t u : State}
    (first : WritesOnlyRegs W s t) (second : WritesOnlyRegs W t u) : WritesOnlyRegs W s u :=
  fun r h => (second r h).trans (first r h)

/-- Composition at differing write sets, forming their union.

No disjointness hypothesis, deliberately: `controlFlowJumpState` writes `nextPC` twice, so the two
sets it composes coincide, and a rule that required disjointness could not state it. Prefer
`trans_same` for traces; see its docstring. -/
theorem trans {A B : RegSet} {s t u : State}
    (first : WritesOnlyRegs A s t) (second : WritesOnlyRegs B t u) :
    WritesOnlyRegs (RegSet.union A B) s u :=
  fun r h => (second r (fun hb => h (Or.inr hb))).trans (first r (fun ha => h (Or.inl ha)))

/-- Widening the write set weakens the claim: what a caller does to fit a precise per-step set into
the coarser set its whole function writes. The dual of `Agree.weaken`, and the counterpart of
`Contracts.Ownership.writesOnlyWithin_mono`. -/
theorem mono {W V : RegSet} {s t : State}
    (sub : ∀ r, W r → V r) (h : WritesOnlyRegs W s t) : WritesOnlyRegs V s t :=
  fun r hv => h r (fun hw => hv (sub r hw))

/-- Transport across a state known only through its register file, which is what a memory store
leaves behind: `writeBytes_preserves_regs` gives `regs` equality and nothing else. -/
theorem congr_regs {W : RegSet} {s t t' : State}
    (h : WritesOnlyRegs W s t) (regs : t'.regs = t.regs) : WritesOnlyRegs W s t' :=
  fun r hr => by rw [regs]; exact h r hr

/-- One observation costs one membership check.

This is the declaration the write set exists to provide. Where a proof currently unfolds five step
definitions plus `Std.ExtDHashMap.get?_insert` to read one register, it reads
`(someStep_writes ..).get x2 (by decide)`. -/
theorem get {W : RegSet} {s t : State} (h : WritesOnlyRegs W s t) (r : Register) (hr : ¬ W r) :
    t.regs.get? r = s.regs.get? r := h r hr

end WritesOnlyRegs

/-! ## From a write set to agreement -/

/-- No register `P` preserves is one the step writes. -/
def RegSet.Disjoint (P W : RegSet) : Prop := ∀ r, P r → ¬ W r

/-- The bridge from a step's write set to agreement on any preserved set disjoint from it.

Both relations are stated `after = before`, so this is a term with no `Eq.symm` in it. That is the
reason the orientations had to agree; with `WritesOnlyRegs` stated the other way every use of this
lemma would carry a symmetry step.

`Disjoint P W` is proved once per preserved predicate -- there are four in the repository -- rather
than decided per observation. `platformPreserved` is a plain `def`, so `¬ platformPreserved x2` is
not `Decidable` and `by decide` on it fails; the disjointness lemma case-splits its eighteen
disjuncts instead, each closed by `decide` against the `@[reducible]` write set. -/
theorem WritesOnlyRegs.agree {W P : RegSet} {s t : State}
    (h : WritesOnlyRegs W s t) (disjoint : RegSet.Disjoint P W) : Agree P s t :=
  fun r hp => h r (disjoint r hp)

/-- Splits disjointness from a composed write set into its parts. This is what makes a write set
containing a parameter usable: `Disjoint P (union closed (only destination))` reduces to a fact
about the closed part, proved once, and the single disequality `¬ P destination`. -/
theorem RegSet.Disjoint.union {P A B : RegSet}
    (ha : RegSet.Disjoint P A) (hb : RegSet.Disjoint P B) :
    RegSet.Disjoint P (RegSet.union A B) :=
  fun r hp h => h.elim (ha r hp) (hb r hp)

/-- Disjointness from a one-register write set is one disequality. -/
theorem RegSet.Disjoint.only {P : RegSet} {w : Register} (h : ¬ P w) :
    RegSet.Disjoint P (RegSet.only w) :=
  fun _ hp he => h (he ▸ hp)

/-- A smaller preserved set inherits disjointness from a larger one. This is how
`decoderPreserved` and `normalRegisters` get their disjointness facts from `platformPreserved`'s
without repeating its case split. -/
theorem RegSet.Disjoint.weaken {P Q W : RegSet}
    (imp : ∀ r, Q r → P r) (h : RegSet.Disjoint P W) : RegSet.Disjoint Q W :=
  fun r hq => h r (imp r hq)

/-- Disjointness from a wider write set covers a narrower one. -/
theorem RegSet.Disjoint.subset {P W V : RegSet}
    (sub : ∀ r, W r → V r) (h : RegSet.Disjoint P V) : RegSet.Disjoint P W :=
  fun r hp hw => h r hp (sub r hw)

/-- Regression for the `@[reducible]` attributes on `RegSet.only` and `RegSet.union`.

Dropping either makes typeclass synthesis unable to build the `Decidable` instance, and every
`(by decide)` membership argument in every downstream step lemma fails with `failed to synthesize
Decidable` -- an error that names the goal and not the missing attribute. Keep this example. -/
example : ¬ (RegSet.union (RegSet.only PC) (RegSet.only x13)) x2 := by decide

end BinaryFv.RiscV
