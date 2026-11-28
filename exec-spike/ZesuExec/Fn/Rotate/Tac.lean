import ZesuExec.Fn.Rotate.Cuts
import ZesuExec.Fn.Rotate.Attr
import ZesuExec.Vc.Tactics

/-!
# `std.mem.rotate` copies: the leaf tactics every copy uses

Proof scripts for this family's hand-written leaves, not automation of the framework: they name
the hypotheses the scripts introduce (`hpre`, `hR`, `hc`, `hm'`, …) and the copy's `cfg` and
`mE` (the word `-E`), and unfold the copy's `@[rot_simp]` definitions. Each fails unless it
closes its goal (or, for the `*prep` ones, leaves the goal in the stated form).

* `iprep`, `oprep`, `eprep`: open a leaf goal of an inner loop head, an outer loop head, the
  entry: name the assertion's parts, the register facts as `hR` (normalised `mh.reg r = …`), the
  leaf's conditions as `Nat` facts `hc`, the slice bounds.
* `rgoal`: `m'.reg r = v` from the leaf's symbolic value of `r` and `hR`.
* `wgoal`: a word equation or a `Nat` goal through `toNat` and `omega`.
* `regs_tac`: `RegsAre m' L` for a literal `L`, register by register.
-/

namespace ZesuExec.Fn.Rotate

set_option hygiene false in
macro "wgoal" : tactic => `(tactic| (
  try apply BitVec.eq_of_toNat_eq
  (simp [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, mE, cfg, Ph.lo, Ph.L])
    <;> omega))

set_option hygiene false in
macro "rgoal" : tactic => `(tactic| (
  rw [reg_at hm' _]
  simp (disch := decide) only [SState.reg, Sym.eval, BinOp.eval, envI, envO, envE, env0, entryEnv,
    Env.base, Env.setVars, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceEqDiff, if_false,
    Fin.reduceOfNat, Fin.isValue, BitVec.ofInt_ofNat, hR, add_big, mul_big, add_neg', mE]))

set_option hygiene false in
macro "regs_tac" : tactic => `(tactic| (
  simp only [rot_simp, List.cons_append, List.nil_append, RegsAre]
  and_intros <;> first | trivial | (rgoal <;> wgoal)))

set_option hygiene false in
/-- The leaf's conditions as `Nat` facts. -/
macro "conds_tac" : tactic => `(tactic| (
  try simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq, forall_eq_or_imp, SBool.eval,
    List.not_mem_nil, false_implies, implies_true, and_true] at hc
  try simp [Sym.eval, BinOp.eval, envI, envO, env0, entryEnv, Env.base, hR, BitVec.toNat_eq,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, mE] at hc
  try simp (disch := omega) only [Nat.mod_eq_of_lt, wsub_mod] at hc))

set_option hygiene false in
macro "iprep" : tactic => `(tactic| (
  leaf_intro
  intro m mh hA hc
  obtain ⟨hpre, hpc, hcom, i, k, hi2, hk, hs, hlo, hhi, hRr⟩ := hA
  have hfit : (ptr m).toNat + cfg.E * len m < 2 ^ 64 := pre_hfit hpre
  have hram := pre_ram hpre
  have hal : amt m ≤ len m := hpre.2.2.2.1
  have hi2' := hi2
  have hk' := hk
  have hR := And.intro hlo (And.intro hhi hRr)
  simp only [rot_simp, List.cons_append, List.nil_append, RegsAre, Fin.reduceOfNat, Ph.lo, Ph.L,
    cfg, and_true, Nat.zero_add, Layout.ramLo, Layout.ramHi, Nat.reducePow] at hR hfit hi2' hk' hram
  conds_tac))

set_option hygiene false in
macro "oprep" : tactic => `(tactic| (
  leaf_intro
  intro m mh hA hc
  obtain ⟨hpre, hpc, hcom, i, hi2, hs, hRr⟩ := hA
  have hfit : (ptr m).toNat + cfg.E * len m < 2 ^ 64 := pre_hfit hpre
  have hram := pre_ram hpre
  have hal : amt m ≤ len m := hpre.2.2.2.1
  have hi2' := hi2
  have hR := hRr
  simp only [rot_simp, List.cons_append, List.nil_append, RegsAre, Fin.reduceOfNat, Ph.lo, Ph.L,
    cfg, and_true, Nat.zero_add, Layout.ramLo, Layout.ramHi, Nat.reducePow] at hR hfit hi2' hram
  conds_tac))

/-- The entry machine's argument registers. -/
theorem entry_regs (m : Machine) : m.reg 10 = ptr m ∧ m.reg 11 = w (len m) ∧ m.reg 12 = w (amt m) :=
  ⟨rfl, by simp [len], by simp [amt]⟩

set_option hygiene false in
macro "eprep" : tactic => `(tactic| (
  leaf_intro
  intro m mh hA hc
  obtain ⟨rfl, hpc, hpre⟩ := hA
  have hfit : (ptr mh).toNat + cfg.E * len mh < 2 ^ 64 := pre_hfit hpre
  have hram := pre_ram hpre
  have hal : amt mh ≤ len mh := hpre.2.2.2.1
  have hR := entry_regs mh
  simp only [cfg, Layout.ramLo, Layout.ramHi, Nat.reducePow] at hfit hram
  conds_tac))

set_option hygiene false in
/-- A budget inequality: the copy's budget definitions unfolded, the loop counters read off the
cut's machine (`hR`) and, when the goal mentions it, the leaf's machine (`hm'`), then `omega`. -/
macro "bud" : tactic => `(tactic| (
  try dsimp only
  simp only [rot_simp, ix, kx]
  try simp (disch := decide) only [reg_of_lt hm']
  try simp (disch := decide) only [SState.reg, Sym.eval, BinOp.eval, envI, envO, envE, env0,
    entryEnv, Env.base, Env.setVars, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceEqDiff,
    if_false, Fin.reduceOfNat, Fin.isValue, BitVec.ofInt_ofNat, hR, add_big, mul_big, add_neg', mE]
  simp (disch := omega) only [ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, toNat_sub_ptr,
    Nat.reducePow, wsub_mod, BitVec.toNat_add]
  omega))

set_option hygiene false in
/-- After an inner leaf's run: `hst` (the byte swap's `Common` and slice), `he` the exit pc. -/
macro "istep" : tactic => `(tactic| (
  dsimp only at hm' he hso
  have hst := inner_step hpre hcom hi2 hk hs hlo hhi hm' rfl rfl hso (by decide)
  simp only [ExitOk] at he))

set_option hygiene false in
/-- After an outer leaf's run (no store). -/
macro "ostep" : tactic => `(tactic| (
  dsimp only at hm' he hso
  have hst := outer_step hpre hcom hs hm' hso (by decide)
  simp only [ExitOk] at he))

set_option hygiene false in
/-- After the entry run (the prologue's stores). -/
macro "estep" : tactic => `(tactic| (
  dsimp only at hm' he hso
  have hst := entry_step hpre hm' hso rfl rfl rfl rfl (by decide)
  simp only [ExitOk] at he))

end ZesuExec.Fn.Rotate
