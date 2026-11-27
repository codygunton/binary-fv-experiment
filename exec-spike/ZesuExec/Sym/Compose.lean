import ZesuExec.Sym.Sound

/-!
# Composing runs: environment extension, register havoc, new regions, `run_reaches`

A function proof chains several `run`s: at a cut (a call return or a loop head) the next run
starts from the previous leaf's state with some registers replaced by fresh variables
(`SState.havoc`) and possibly a new region (`SState.addRegion`). The environment grows
accordingly (`Env.setVars`, `Env.addRegion`); `Match.ext` moves a `Match` to the larger
environment when the state only mentions the old variables and regions (`SState.wfB`).
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

/-! ## Variables and regions a symbolic value mentions -/

/-- `s` mentions only variables below `K` and regions below `R`. -/
def Sym.wfB (K R : Nat) : Sym → Bool
  | .lit _ => true
  | .var i => i < K
  | .ptr r _ => r < R
  | .init r _ _ => r < R
  | .initx r _ idx _ _ => r < R && Sym.wfB K R idx
  | .bin _ a b => Sym.wfB K R a && Sym.wfB K R b
  | .sext _ a => Sym.wfB K R a
  | .bytes a _ _ => Sym.wfB K R a
  | .cat lo hi _ => Sym.wfB K R lo && Sym.wfB K R hi

def Write.wfB (K R : Nat) (w : Write) : Bool := w.r < R && w.v.wfB K R

def SState.wfB (K : Nat) (S : SState) : Bool :=
  S.regs.all (Sym.wfB K S.regions.length) && S.mem.all (Write.wfB K S.regions.length) &&
    S.known.all (Write.wfB K S.regions.length)

/-- `env'` agrees with `env` on variables below `K` and on regions below `R`. -/
structure Env.Ext (env env' : Env) (K R : Nat) : Prop where
  vars : ∀ i < K, env'.vars i = env.vars i
  base : ∀ r < R, env'.base r = env.base r
  size : ∀ r < R, env'.size r = env.size r
  mem0 : ∀ r < R, ∀ j, env'.mem0 r j = env.mem0 r j

theorem Sym.eval_ext {env env' : Env} {K R : Nat} (he : Env.Ext env env' K R) :
    ∀ s : Sym, s.wfB K R = true → s.eval env' = s.eval env
  | .lit _, _ => rfl
  | .var i, h => he.vars i (by simpa [Sym.wfB] using h)
  | .ptr r _, h => by simp [Sym.eval, he.base r (by simpa [Sym.wfB] using h)]
  | .init r off n, h => by
    simp only [Sym.wfB, decide_eq_true_eq] at h
    have hb : env'.byte0 r = env.byte0 r := funext fun j => he.mem0 r h j
    simp only [Sym.eval, hb]
  | .initx r off idx sc n, h => by
    simp only [Sym.wfB, Bool.and_eq_true, decide_eq_true_eq] at h
    have hb : env'.byte0 r = env.byte0 r := funext fun j => he.mem0 r h.1 j
    simp only [Sym.eval, hb, Sym.eval_ext he idx h.2]
  | .bin op a b, h => by
    simp only [Sym.wfB, Bool.and_eq_true] at h
    simp only [Sym.eval, Sym.eval_ext he a h.1, Sym.eval_ext he b h.2]
  | .sext _ a, h => by simp only [Sym.eval, Sym.eval_ext he a (by simpa [Sym.wfB] using h)]
  | .bytes a _ _, h => by simp only [Sym.eval, Sym.eval_ext he a (by simpa [Sym.wfB] using h)]
  | .cat lo hi _, h => by
    simp only [Sym.wfB, Bool.and_eq_true] at h
    simp only [Sym.eval, Sym.eval_ext he lo h.1, Sym.eval_ext he hi h.2]

theorem memByte_ext {env env' : Env} {K R : Nat} (he : Env.Ext env env' K R) {ws : List Write}
    (hws : ws.all (Write.wfB K R) = true) {r j : Nat} (hr : r < R) :
    memByte env' ws r j = memByte env ws r j := by
  unfold memByte
  cases h : ws.find? (·.covers r j) with
  | none => simp [Env.byte0, he.mem0 r hr]
  | some w =>
    have hw := List.all_eq_true.mp hws w (List.mem_of_find?_eq_some h)
    simp only [Write.wfB, Bool.and_eq_true] at hw
    simp [Sym.eval_ext he w.v hw.2]

theorem Match.ext {env env' : Env} {S : SState} {m : Machine} {K : Nat} (hm : Match env S m)
    (hwfB : S.wfB K = true) (he : Env.Ext env env' K S.regions.length) : Match env' S m := by
  simp only [SState.wfB, Bool.and_eq_true] at hwfB
  obtain ⟨⟨hregs, hmem⟩, hknown⟩ := hwfB
  refine ⟨hm.regsLen, fun i => ?_, fun r j hr hj => ?_, fun k hk t ht => ?_⟩
  · rw [← hm.regs i]
    apply Sym.eval_ext he
    unfold SState.reg
    split
    · rfl
    · rw [List.getD_eq_getElem?_getD]
      cases hx : S.regs[i.val]? with
      | none => rfl
      | some s => exact List.all_eq_true.mp hregs s (List.mem_of_getElem? hx)
  · rw [he.base r hr, memByte_ext he hmem hr]
    exact hm.mem r j hr (by rwa [← he.size r hr])
  · have hw := List.all_eq_true.mp hknown k hk
    simp only [Write.wfB, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [Env.byte0, he.mem0 k.r hw.1, Sym.eval_ext he k.v hw.2]
    exact hm.known k hk t ht

theorem Env.WF.ext {env env' : Env} {S : SState} (hwf : Env.WF env S)
    (he : Env.Ext env env' 0 S.regions.length) (hlen : env'.regions.length = S.regions.length) :
    Env.WF env' S where
  len := hlen
  disjoint r r' j j' hne hj hj' := by
    have hr : r < S.regions.length := by
      rcases Nat.lt_or_ge r S.regions.length with h | h
      · exact h
      · simp [Env.size, List.getD_eq_getElem?_getD, List.getElem?_eq_none (hlen ▸ h)] at hj
    have hr' : r' < S.regions.length := by
      rcases Nat.lt_or_ge r' S.regions.length with h | h
      · exact h
      · simp [Env.size, List.getD_eq_getElem?_getD, List.getElem?_eq_none (hlen ▸ h)] at hj'
    rw [he.base r hr, he.base r' hr']
    rw [he.size r hr] at hj; rw [he.size r' hr'] at hj'
    exact hwf.disjoint r r' j j' hne hj hj'
  size r R s hR hs := by
    have hr := (List.getElem?_eq_some_iff.mp hR).1
    rw [he.size r hr]; exact hwf.size r R s hR hs
  align r R hR := by
    have hr := (List.getElem?_eq_some_iff.mp hR).1
    rw [he.base r hr]; exact hwf.align r R hR
  range r R hR := by
    have hr := (List.getElem?_eq_some_iff.mp hR).1
    rw [he.base r hr, he.size r hr]; exact hwf.range r R hR

/-! ## Fresh variables -/

/-- Variables from `F` on are `f (i - F)`. -/
def Env.setVars (env : Env) (F : Nat) (f : Nat → Word) : Env :=
  { env with vars := fun i => if F ≤ i then f (i - F) else env.vars i }

theorem Env.setVars_ext (env : Env) (F : Nat) (f : Nat → Word) (R : Nat) :
    Env.Ext env (env.setVars F f) F R :=
  ⟨fun i hi => by simp [Env.setVars, Nat.not_le.mpr hi], fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- Registers in `H` become `var (F + i)`. -/
def SState.havoc (S : SState) (H : List Nat) (F : Nat) : SState :=
  { S with regs := S.regs.mapIdx fun i s => if H.contains i then .var (F + i) else s }

theorem SState.havoc_reg (S : SState) (H : List Nat) (F : Nat) (hl : S.regs.length = 32)
    (i : Fin 32) (h0 : i.val ≠ 0) :
    (S.havoc H F).reg i.val = if H.contains i.val then .var (F + i.val) else S.reg i.val := by
  unfold SState.havoc SState.reg
  simp only [h0, if_false, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  have : i.val < S.regs.length := by rw [hl]; exact i.isLt
  rw [List.getElem?_eq_getElem this]
  simp only [Option.map_some, Option.getD_some]

/-- After a call (or at a loop head): the registers in `H` take the values of `m₂`, the others
and every region's bytes are those of `m`. -/
theorem Match.havoc {env : Env} {S : SState} {m m₂ : Machine} {H : List Nat} {F : Nat}
    (hm : Match env S m) (hwfB : S.wfB F = true) (h0 : ¬ H.contains 0)
    (hkeep : ∀ i : Fin 32, ¬ H.contains i.val → m₂.reg i = m.reg i)
    (hmem : ∀ r j, r < S.regions.length → j < env.size r →
      m₂.mem (env.base r + BitVec.ofNat 64 j) = m.mem (env.base r + BitVec.ofNat 64 j)) :
    Match (env.setVars F fun i => m₂.reg (Fin.ofNat 32 i)) (S.havoc H F) m₂ := by
  have hm' := hm.ext hwfB (Env.setVars_ext env F (fun i => m₂.reg (Fin.ofNat 32 i)) S.regions.length)
  refine ⟨by simp [SState.havoc, hm.regsLen], fun i => ?_, fun r j hr hj => ?_, hm'.known⟩
  · by_cases hi0 : i.val = 0
    · have := hm'.regs i
      simp only [SState.reg, SState.havoc, hi0, if_true] at this ⊢
      rw [this, Machine.reg, Machine.reg, if_pos hi0, if_pos hi0]
    · rw [SState.havoc_reg S H F hm.regsLen i hi0]
      split
      · next hh => simp [Sym.eval, Env.setVars]
      · next hh => rw [hm'.regs i, hkeep i hh]
  · rw [show (env.setVars F _).base r = env.base r from rfl, hmem r j hr hj]
    exact hm'.mem r j hr hj

/-! ## New regions -/

/-- Append a region with base `b`, size `n` and initial bytes `bytes`. -/
def Env.addRegion (env : Env) (b : Word) (n : Nat) (bytes : Nat → Byte) : Env :=
  { env with
    regions := env.regions ++ [(b, n)]
    mem0 := fun r j => if r = env.regions.length then bytes j else env.mem0 r j }

def SState.addRegion (S : SState) (R : Region) : SState := { S with regions := S.regions ++ [R] }

theorem Env.addRegion_ext (env : Env) (b : Word) (n : Nat) (bytes : Nat → Byte) (K : Nat) :
    Env.Ext env (env.addRegion b n bytes) K env.regions.length where
  vars _ _ := rfl
  base r hr := by
    simp [Env.base, Env.addRegion, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  size r hr := by
    simp [Env.size, Env.addRegion, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  mem0 r hr j := by simp [Env.addRegion, Nat.ne_of_lt hr]

theorem Env.addRegion_base (env : Env) (b : Word) (n : Nat) (bytes : Nat → Byte) :
    (env.addRegion b n bytes).base env.regions.length = b := by
  simp [Env.base, Env.addRegion, List.getD_eq_getElem?_getD]

theorem Env.addRegion_size (env : Env) (b : Word) (n : Nat) (bytes : Nat → Byte) :
    (env.addRegion b n bytes).size env.regions.length = n := by
  simp [Env.size, Env.addRegion, List.getD_eq_getElem?_getD]

/-- A new region whose bytes are present in `m` keeps `Match`. -/
theorem Match.addRegion {env : Env} {S : SState} {m : Machine} {K : Nat} (hm : Match env S m)
    (hwfB : S.wfB K = true) (hlen : env.regions.length = S.regions.length) (R : Region)
    (b : Word) (n : Nat)
    (hpres : ∀ j < n, (m.mem (b + BitVec.ofNat 64 j)).isSome) :
    Match (env.addRegion b n fun j => (m.mem (b + BitVec.ofNat 64 j)).getD 0)
      (S.addRegion R) m := by
  have he := Env.addRegion_ext env b n (fun j => (m.mem (b + BitVec.ofNat 64 j)).getD 0) K
  rw [hlen] at he
  have hm' := hm.ext hwfB he
  refine ⟨hm.regsLen, hm'.regs, fun r j hr hj => ?_, hm'.known⟩
  simp only [SState.addRegion, List.length_append, List.length_singleton] at hr
  rcases Nat.lt_or_ge r S.regions.length with h | h
  · exact hm'.mem r j h hj
  · have hr' : r = env.regions.length := by omega
    subst hr'
    rw [Env.addRegion_size] at hj
    rw [Env.addRegion_base]
    have hnone : ∀ w ∈ S.mem, w.covers env.regions.length j = false := by
      intro w hw
      simp only [SState.wfB, Bool.and_eq_true] at hwfB
      have := List.all_eq_true.mp hwfB.1.2 w hw
      simp only [Write.wfB, Bool.and_eq_true, decide_eq_true_eq] at this
      simp [Write.covers]; intro h; omega
    have hfind : S.mem.find? (·.covers env.regions.length j) = none :=
      List.find?_eq_none.mpr fun w hw => by simp [hnone w hw]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hpres j hj)
    simp [SState.addRegion, memByte, hfind, Env.byte0, Env.addRegion, hx]

/-- `WF` for a state with one more region, disjoint from the others and well placed. -/
theorem Env.WF.addRegion {env : Env} {S : SState} (hwf : Env.WF env S) (R : Region) (b : Word)
    (n : Nat) (bytes : Nat → Byte)
    (hdisj : ∀ r < S.regions.length, (env.base r).toNat + env.size r ≤ b.toNat ∨
      b.toNat + n ≤ (env.base r).toNat)
    (hsize : ∀ s, R.size = some s → n = s) (halign : b.toNat % R.align = 0)
    (hrange : (if R.writable then writable b.toNat n else readable b.toNat n) = true) :
    Env.WF (env.addRegion b n bytes) (S.addRegion R) := by
  have hlen := hwf.len
  have he := Env.addRegion_ext env b n bytes 0
  rw [hlen] at he
  have hbase : (env.addRegion b n bytes).base S.regions.length = b := by
    rw [← hlen]; exact Env.addRegion_base env b n bytes
  have hsz : (env.addRegion b n bytes).size S.regions.length = n := by
    rw [← hlen]; exact Env.addRegion_size env b n bytes
  have hout : ∀ r, S.regions.length < r → (env.addRegion b n bytes).size r = 0 := by
    intro r hr
    simp [Env.size, Env.addRegion, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show (env.regions ++ [(b, n)]).length ≤ r by simp; omega)]
  have idx : ∀ r j, j < (env.addRegion b n bytes).size r → r < S.regions.length ∨ r = S.regions.length := by
    intro r j hj
    rcases Nat.lt_trichotomy r S.regions.length with h | h | h
    · exact .inl h
    · exact .inr h
    · rw [hout r h] at hj; omega
  refine ⟨by simp [Env.addRegion, SState.addRegion, hlen], ?_, ?_, ?_, ?_⟩
  · intro r r' j j' hne hj hj'
    rcases idx r j hj with h | rfl <;> rcases idx r' j' hj' with h' | rfl
    · rw [he.base r h, he.base r' h']
      rw [he.size r h] at hj; rw [he.size r' h'] at hj'
      exact hwf.disjoint r r' j j' hne hj hj'
    · rw [he.base r h, hbase]; rw [he.size r h] at hj; rw [hsz] at hj'
      rcases hdisj r h with d | d <;> omega
    · rw [he.base r' h', hbase]; rw [he.size r' h'] at hj'; rw [hsz] at hj
      rcases hdisj r' h' with d | d <;> omega
    · exact absurd rfl hne
  · intro r R' s hR hs
    simp only [SState.addRegion] at hR
    rcases Nat.lt_or_ge r S.regions.length with h | h
    · rw [List.getElem?_append_left h] at hR; rw [he.size r h]; exact hwf.size r R' s hR hs
    · rw [List.getElem?_append_right h] at hR
      have h1 := (List.getElem?_eq_some_iff.mp hR).1
      simp at h1
      have : r = S.regions.length := by omega
      subst this
      simp at hR; subst hR; rw [hsz]; exact hsize s hs
  · intro r R' hR
    simp only [SState.addRegion] at hR
    rcases Nat.lt_or_ge r S.regions.length with h | h
    · rw [List.getElem?_append_left h] at hR; rw [he.base r h]; exact hwf.align r R' hR
    · rw [List.getElem?_append_right h] at hR
      have h1 := (List.getElem?_eq_some_iff.mp hR).1
      simp at h1
      have : r = S.regions.length := by omega
      subst this
      simp at hR; subst hR; rw [hbase]; exact halign
  · intro r R' hR
    simp only [SState.addRegion] at hR
    rcases Nat.lt_or_ge r S.regions.length with h | h
    · rw [List.getElem?_append_left h] at hR; rw [he.base r h, he.size r h]; exact hwf.range r R' hR
    · rw [List.getElem?_append_right h] at hR
      have h1 := (List.getElem?_eq_some_iff.mp hR).1
      simp at h1
      have : r = S.regions.length := by omega
      subst this
      simp at hR; subst hR; rw [hbase, hsz]; exact hrange

/-! ## A run as a `Reaches` step -/

/-- Each leaf whose conditions hold must meet its obligations and continue to `Q` within the
remaining budget. -/
theorem run_reaches {img : Image} {cuts : List Nat} {fuel pc : Nat} {S : SState}
    {ls : List Leaf} {env : Env} {m : Machine} {b : Nat} {Q : Machine → Prop}
    (h : run img cuts fuel pc S = some ls) (hwf : Env.WF env S) (hm : Match env S m)
    (hpc : m.pc.toNat = pc) (hro : RodataLoaded img m)
    (hleaf : ∀ l ∈ ls, (∀ c ∈ l.conds, c.eval env = true) →
      (∀ o ∈ l.obligs, o.holds env) ∧ l.S.steps - S.steps ≤ b ∧
      ∀ m', Match env l.S m' → ExitOk env l.exit m' → SameOutside (InWritable env S) m m' →
        Reaches img (b - (l.S.steps - S.steps)) Q m') :
    Reaches img b Q m := by
  obtain ⟨l, hl, hc, hr⟩ := run_sound h hwf hm hpc hro
  obtain ⟨hob, hb, hk⟩ := hleaf l hl hc
  obtain ⟨m', hrun, hm', hex, hfr⟩ := hr hob
  obtain ⟨k, m'', hk', hrun', hQ⟩ := hk m' hm' hex hfr
  exact ⟨_, m'', by omega, hrun.trans hrun', hQ⟩

end ZesuExec.Sym
