import ZesuExec.Sym.Env
import ZesuExec.Vc.SimpAttr

/-!
# Region layouts and `region_tac` (programme plan S4 step 3)

A `Layout` is a list of `(base, size)` intervals that do not wrap and are pairwise disjoint.
For an `Env` whose regions are a layout's:

* `Layout.apart`: bytes of two different regions have different addresses;
* `Layout.wf`: `Env.WF` reduces to the per-region size, alignment and range facts;
* `Layout.inWritable_iff`: `InWritable` as an interval fact;
* `Layout.sameOutside_frame`: under `SameOutside (InWritable env S)`, bytes of an interval apart
  from every writable region of `S` are unchanged.

`region_tac` applies these and closes what remains by unfolding the literal region lists to
linear arithmetic on `BitVec.toNat` and `omega`. It proves the goal or fails.
-/

namespace ZesuExec.Vc
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- No interval wraps and any two are disjoint. -/
def Layout.Ok : List (Word × Nat) → Prop
  | [] => True
  | p :: ps => p.1.toNat + p.2 ≤ 2 ^ 64 ∧
      (∀ q ∈ ps, p.1.toNat + p.2 ≤ q.1.toNat ∨ q.1.toNat + q.2 ≤ p.1.toNat) ∧ Layout.Ok ps

structure Layout where
  regs : List (Word × Nat)
  ok : Layout.Ok regs

namespace Layout

def base (L : Layout) (r : Nat) : Word := (L.regs.getD r (0, 0)).1
def size (L : Layout) (r : Nat) : Nat := (L.regs.getD r (0, 0)).2

theorem nowrap_of : ∀ {ps : List (Word × Nat)}, Layout.Ok ps → ∀ r,
    ((ps.getD r (0, 0)).1.toNat + (ps.getD r (0, 0)).2 ≤ 2 ^ 64)
  | [], _, r => by simp
  | p :: ps, ⟨h, _, hs⟩, r => by
    cases r with
    | zero => simpa using h
    | succ r => simpa using nowrap_of hs r

theorem disj_of : ∀ {ps : List (Word × Nat)}, Layout.Ok ps → ∀ r r', r ≠ r' →
    0 < (ps.getD r (0, 0)).2 → 0 < (ps.getD r' (0, 0)).2 →
    (ps.getD r (0, 0)).1.toNat + (ps.getD r (0, 0)).2 ≤ (ps.getD r' (0, 0)).1.toNat ∨
    (ps.getD r' (0, 0)).1.toNat + (ps.getD r' (0, 0)).2 ≤ (ps.getD r (0, 0)).1.toNat
  | [], _, r, r', _, h, _ => by simp at h
  | p :: ps, ⟨_, hd, hs⟩, r, r', hne, h, h' => by
    cases r with
    | zero =>
      cases r' with
      | zero => exact absurd rfl hne
      | succ r' =>
        have hr' : r' < ps.length := by
          rcases Nat.lt_or_ge r' ps.length with h | h
          · exact h
          · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at h'
        simpa [List.getD_eq_getElem?_getD, hr'] using hd _ (List.getElem_mem hr')
    | succ r =>
      cases r' with
      | zero =>
        have hr : r < ps.length := by
          rcases Nat.lt_or_ge r ps.length with h' | h'
          · exact h'
          · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at h
        have := hd _ (List.getElem_mem hr)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
          List.getElem?_eq_getElem hr, Option.getD_some]
        omega
      | succ r' =>
        simpa using disj_of hs r r' (fun e => hne (by rw [e])) (by simpa using h) (by simpa using h')

/-- Bytes of two different regions have different addresses. -/
theorem apart (L : Layout) {r r' j j' : Nat} (hne : r ≠ r') (hj : j < L.size r)
    (hj' : j' < L.size r') : (L.base r).toNat + j ≠ (L.base r').toNat + j' := by
  have := disj_of L.ok r r' hne (by unfold size at hj; omega) (by unfold size at hj'; omega)
  unfold base; unfold size at hj hj'; omega

theorem env_base {env : Env} {L : Layout} (h : env.regions = L.regs) (r : Nat) :
    env.base r = L.base r := by simp [Env.base, base, h]

theorem env_size {env : Env} {L : Layout} (h : env.regions = L.regs) (r : Nat) :
    env.size r = L.size r := by simp [Env.size, size, h]

/-- `Env.WF` for an `Env` on a layout: only the per-region facts remain. -/
theorem wf (L : Layout) {env : Env} {S : SState} (henv : env.regions = L.regs)
    (hlen : L.regs.length = S.regions.length)
    (hsize : ∀ r R s, S.regions[r]? = some R → R.size = some s → L.size r = s)
    (halign : ∀ r R, S.regions[r]? = some R → (L.base r).toNat % R.align = 0)
    (hrange : ∀ r R, S.regions[r]? = some R →
      (if R.writable then writable (L.base r).toNat (L.size r)
       else readable (L.base r).toNat (L.size r)) = true) :
    Env.WF env S where
  len := henv ▸ hlen
  disjoint r r' j j' hne hj hj' := by
    rw [env_size henv] at hj hj'; rw [env_base henv, env_base henv]
    exact apart L hne hj hj'
  size r R s h hs := by rw [env_size henv]; exact hsize r R s h hs
  align r R h := by rw [env_base henv]; exact halign r R h
  range r R h := by rw [env_base henv, env_size henv]; exact hrange r R h

theorem toNat_base_add (L : Layout) {r j : Nat} (hj : j < L.size r) :
    (L.base r + BitVec.ofNat 64 j).toNat = (L.base r).toNat + j := by
  have := nowrap_of L.ok r
  unfold base; unfold size at hj
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]

/-- `InWritable` as an interval fact. -/
theorem inWritable_iff (L : Layout) {env : Env} {S : SState} (henv : env.regions = L.regs)
    {a : Word} :
    InWritable env S a ↔ ∃ r R, S.regions[r]? = some R ∧ R.writable = true ∧
      (L.base r).toNat ≤ a.toNat ∧ a.toNat < (L.base r).toNat + L.size r := by
  constructor
  · rintro ⟨r, R, j, hR, hw, hj, rfl⟩
    rw [env_size henv] at hj; rw [env_base henv, toNat_base_add L hj]
    exact ⟨r, R, hR, hw, by omega, by omega⟩
  · rintro ⟨r, R, hR, hw, hlo, hhi⟩
    refine ⟨r, R, a.toNat - (L.base r).toNat, hR, hw, by rw [env_size henv]; omega, ?_⟩
    rw [env_base henv]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_base_add L (by omega)]; omega

/-- Bytes of an interval apart from every writable region are unchanged. -/
theorem sameOutside_frame (L : Layout) {env : Env} {S : SState} {m m' : Machine}
    (henv : env.regions = L.regs) (hso : SameOutside (InWritable env S) m m') {a : Word} {n : Nat}
    (hwrap : a.toNat + n ≤ 2 ^ 64)
    (hout : ∀ r R, S.regions[r]? = some R → R.writable = true →
      (L.base r).toNat + L.size r ≤ a.toNat ∨ a.toNat + n ≤ (L.base r).toNat) :
    ∀ t < n, m'.mem (a + BitVec.ofNat 64 t) = m.mem (a + BitVec.ofNat 64 t) := by
  intro t ht
  apply hso
  rw [inWritable_iff L henv]
  rintro ⟨r, R, hR, hw, hlo, hhi⟩
  have e : (a + BitVec.ofNat 64 t).toNat = a.toNat + t := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  have := hout r R hR hw
  omega

/-- An address of the interval is not in any writable region. -/
theorem not_inWritable (L : Layout) {env : Env} {S : SState} (henv : env.regions = L.regs)
    {a : Word}
    (hout : ∀ r R, S.regions[r]? = some R → R.writable = true →
      a.toNat < (L.base r).toNat ∨ (L.base r).toNat + L.size r ≤ a.toNat) :
    ¬ InWritable env S a := by
  rw [inWritable_iff L henv]
  rintro ⟨r, R, hR, hw, hlo, hhi⟩
  have := hout r R hR hw
  omega

/-! The same with the list and its `Ok` proof as the last argument, so the goals `refine`
leaves for the other hypotheses do not mention the proof's metavariable (which would stop
`simp at *` from rewriting the hypotheses). -/

theorem wf_of {env : Env} {S : SState} (regs : List (Word × Nat)) (henv : env.regions = regs)
    (hlen : regs.length = S.regions.length)
    (hsize : ∀ r R s, S.regions[r]? = some R → R.size = some s → (regs.getD r (0, 0)).2 = s)
    (halign : ∀ r R, S.regions[r]? = some R → (regs.getD r (0, 0)).1.toNat % R.align = 0)
    (hrange : ∀ r R, S.regions[r]? = some R →
      (if R.writable then writable (regs.getD r (0, 0)).1.toNat (regs.getD r (0, 0)).2
       else readable (regs.getD r (0, 0)).1.toNat (regs.getD r (0, 0)).2) = true)
    (hok : Layout.Ok regs) : Env.WF env S :=
  wf ⟨regs, hok⟩ henv hlen hsize halign hrange

theorem not_inWritable_of {env : Env} {S : SState} (regs : List (Word × Nat))
    (henv : env.regions = regs) {a : Word}
    (hout : ∀ r R, S.regions[r]? = some R → R.writable = true →
      a.toNat < (regs.getD r (0, 0)).1.toNat ∨
        (regs.getD r (0, 0)).1.toNat + (regs.getD r (0, 0)).2 ≤ a.toNat)
    (hok : Layout.Ok regs) : ¬ InWritable env S a :=
  not_inWritable ⟨regs, hok⟩ henv hout

theorem sameOutside_frame_of {env : Env} {S : SState} {m m' : Machine}
    (regs : List (Word × Nat)) (henv : env.regions = regs)
    (hso : SameOutside (InWritable env S) m m') {a : Word} {n : Nat} (t : Nat) (ht : t < n)
    (hwrap : a.toNat + n ≤ 2 ^ 64)
    (hout : ∀ r R, S.regions[r]? = some R → R.writable = true →
      (regs.getD r (0, 0)).1.toNat + (regs.getD r (0, 0)).2 ≤ a.toNat ∨
        a.toNat + n ≤ (regs.getD r (0, 0)).1.toNat)
    (hok : Layout.Ok regs) : m'.mem (a + BitVec.ofNat 64 t) = m.mem (a + BitVec.ofNat 64 t) :=
  sameOutside_frame ⟨regs, hok⟩ henv hso hwrap hout t ht

end Layout

/-- Unfold the literal layout and region lists of the goal to `toNat` arithmetic. -/
syntax "region_arith" : tactic
macro_rules
  | `(tactic| region_arith) => `(tactic| (
      try simp only [Layout.Ok, Layout.base, Layout.size, List.mem_cons, List.mem_nil_iff,
        or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, true_and,
        List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ,
        Machine.writable, Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi,
        Layout.rodataLo, Layout.rodataHi, Layout.inputLo, Layout.inputHi, Bool.and_eq_true,
        Bool.or_eq_true, decide_eq_true_eq, zesu_simp] at *
      try (intro r)
      try (rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r)
      all_goals intros
      all_goals (try simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, reduceCtorEq, Nat.zero_add, List.getD_cons_zero,
        List.getD_cons_succ] at *)
      all_goals (try subst_vars)
      all_goals (try simp_all [Machine.writable, Machine.readable, Machine.inRange,
        Layout.ramLo, Layout.ramHi, Layout.rodataLo, Layout.rodataHi, Layout.inputLo,
        Layout.inputHi])
      all_goals omega))

/-- `Env.WF` on a layout, `¬ InWritable`, or unchanged bytes under `SameOutside`. The layout is
the `Env`'s region list; its disjointness and the region facts are proved by `region_arith`
from the hypotheses. Fails if anything remains. -/
syntax "region_tac" : tactic
macro_rules
  | `(tactic| region_tac) => `(tactic| first
      | (guard_target =~ Env.WF _ _
         refine Layout.wf_of _ rfl ?_ ?_ ?_ ?_ ?_ <;> region_arith; done)
      | (guard_target =~ ¬ InWritable _ _ _
         refine Layout.not_inWritable_of _ rfl ?_ ?_ <;> region_arith; done)
      | (guard_target =~ Machine.mem _ _ = Machine.mem _ _
         refine Layout.sameOutside_frame_of _ rfl (by assumption) _ (by assumption) ?_ ?_ ?_
          <;> region_arith; done))

end ZesuExec.Vc
