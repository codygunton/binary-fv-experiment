import ZesuExec.Sym.Compose

/-!
# Join cuts: `generalise` (programme plan S5 probe 1)

Where several paths meet, one symbolic state stands for all of them: `generalise F Ss K` keeps
a register where every state of `Ss` holds the same term and that term is *clean* (it mentions
only variables below `K` and initial bytes only of regions no state writes); any other register
`i` becomes the fresh variable `var (F + i)`. A memory write is kept when it is clean and, in
every state, it is the newest write of each byte it covers (`visibleB`); a known fact when
every state has it and it is clean. The bytes of a written ("dirty") region that no kept write
covers are the region's initial bytes in the new environment: there the environment reads them
off the machine.

`Match.generalise_to`: from `Match env S m` for one `S ∈ Ss`, the generalised state matches `m`
under any `env'` that agrees with `env` on the variables below `K`, on the regions and on the
initial bytes of clean regions, reads `var (F + i)` as register `i` of `m` and the initial
bytes of dirty regions off `m`. `Match.generalise` is the plan's existential form, with
`K = F` and `env' = genEnv F Ss env m`.
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

/-- Some state of `Ss` writes region `r`. -/
def dirtyB (Ss : List SState) (r : Nat) : Bool := Ss.any fun S => S.mem.any (·.r == r)

/-- `s` mentions only variables below `K`, and initial bytes only of regions below `R` that are
not dirty (`d r = false`). -/
def Sym.cleanB (K R : Nat) (d : Nat → Bool) : Sym → Bool
  | .lit _ => true
  | .var i => decide (i < K)
  | .ptr _ _ => true
  | .init r _ _ => decide (r < R) && !d r
  | .initx r _ idx _ _ => decide (r < R) && !d r && Sym.cleanB K R d idx
  | .bin _ a b => Sym.cleanB K R d a && Sym.cleanB K R d b
  | .sext _ a => Sym.cleanB K R d a
  | .bytes a _ _ => Sym.cleanB K R d a
  | .cat lo hi _ => Sym.cleanB K R d lo && Sym.cleanB K R d hi

/-- `w` is the newest write of each byte it covers in `S`. -/
def visibleB (S : SState) (w : Write) : Bool :=
  (List.range w.n).all fun t => S.mem.find? (·.covers w.r (w.off + t)) == some w

/-- Register `i` of the join of `Ss` (head `S₀`). -/
def genReg (F K R : Nat) (d : Nat → Bool) (Ss : List SState) (S₀ : SState) (i : Nat) : Sym :=
  if i = 0 then .lit 0
  else if Ss.all (fun S => S.reg i == S₀.reg i) && (S₀.reg i).cleanB K R d then S₀.reg i
  else .var (F + i)

/-- One state for all of `Ss`; fresh variables `var (F + i)`, kept terms over variables below
`K` (by default `F`). -/
def generalise (F : Nat) (Ss : List SState) (K : Nat := F) : SState :=
  let S₀ := Ss.headD default
  let R := S₀.regions.length
  let d := dirtyB Ss
  { regs := (List.range 32).map (genReg F K R d Ss S₀)
    mem := S₀.mem.filter fun w => Ss.all (visibleB · w) && w.v.cleanB K R d
    known := S₀.known.filter fun w =>
      Ss.all (fun S => S.known.contains w) && decide (w.r < R) && !d w.r && w.v.cleanB K R d
    regions := S₀.regions
    steps := 0 }

/-- The plan's environment for `generalise F Ss`: `var (F + i)` is register `i` of `m`, the
initial bytes of dirty regions are `m`'s bytes, all else is `env`. -/
def genEnv (F : Nat) (Ss : List SState) (env : Env) (m : Machine) : Env where
  vars i := if F ≤ i then m.reg (Fin.ofNat 32 (i - F)) else env.vars i
  regions := env.regions
  mem0 r j := if dirtyB Ss r then (m.mem (env.base r + BitVec.ofNat 64 j)).getD 0 else env.mem0 r j

theorem Sym.eval_clean {env env' : Env} {K R : Nat} {d : Nat → Bool}
    (hv : ∀ i < K, env'.vars i = env.vars i) (hr : env'.regions = env.regions)
    (hc : ∀ r < R, d r = false → ∀ j, env'.mem0 r j = env.mem0 r j) :
    ∀ s : Sym, s.cleanB K R d = true → s.eval env' = s.eval env
  | .lit _, _ => rfl
  | .var i, h => hv i (by simpa [Sym.cleanB] using h)
  | .ptr r _, _ => by simp only [Sym.eval, Env.base, hr]
  | .init r off n, h => by
    simp only [Sym.cleanB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    have hb : env'.byte0 r = env.byte0 r := funext fun j => hc r h.1 h.2 j
    simp only [Sym.eval, hb]
  | .initx r off idx sc n, h => by
    simp only [Sym.cleanB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    have hb : env'.byte0 r = env.byte0 r := funext fun j => hc r h.1.1 h.1.2 j
    simp only [Sym.eval, hb, Sym.eval_clean hv hr hc idx h.2]
  | .bin op a b, h => by
    simp only [Sym.cleanB, Bool.and_eq_true] at h
    simp only [Sym.eval, Sym.eval_clean hv hr hc a h.1, Sym.eval_clean hv hr hc b h.2]
  | .sext _ a, h => by
    simp only [Sym.eval, Sym.eval_clean hv hr hc a (by simpa [Sym.cleanB] using h)]
  | .bytes a _ _, h => by
    simp only [Sym.eval, Sym.eval_clean hv hr hc a (by simpa [Sym.cleanB] using h)]
  | .cat lo hi _, h => by
    simp only [Sym.cleanB, Bool.and_eq_true] at h
    simp only [Sym.eval, Sym.eval_clean hv hr hc lo h.1, Sym.eval_clean hv hr hc hi h.2]

/-- `Env.WF` depends only on the regions. -/
theorem Env.WF.congr_regions {env env' : Env} {S S' : SState} (hwf : Env.WF env S)
    (hr : env'.regions = env.regions) (hS : S'.regions = S.regions) : Env.WF env' S' := by
  have hb : ∀ r, env'.base r = env.base r := fun r => by simp only [Env.base, hr]
  have hs : ∀ r, env'.size r = env.size r := fun r => by simp only [Env.size, hr]
  refine ⟨by rw [hr, hS]; exact hwf.len, fun r r' j j' h hj hj' => ?_, fun r R s hR h => ?_,
    fun r R hR => ?_, fun r R hR => ?_⟩
  · rw [hb, hb]; rw [hs] at hj hj'; exact hwf.disjoint r r' j j' h hj hj'
  · rw [hs]; rw [hS] at hR; exact hwf.size r R s hR h
  · rw [hb]; rw [hS] at hR; exact hwf.align r R hR
  · rw [hb, hs]; rw [hS] at hR; exact hwf.range r R hR

theorem generalise_regions {F K : Nat} {Ss : List SState} {S : SState} (hS : S ∈ Ss)
    (hR : ∀ S' ∈ Ss, S'.regions = S.regions) : (generalise F Ss K).regions = S.regions := by
  cases Ss with
  | nil => cases hS
  | cons S₀ _ => exact hR S₀ (List.mem_cons_self ..)

theorem genReg_getD (F K R : Nat) (d : Nat → Bool) (Ss : List SState) (S₀ : SState) (i : Fin 32) :
    ((List.range 32).map (genReg F K R d Ss S₀)).getD i.val (.lit 0) = genReg F K R d Ss S₀ i.val := by
  simp [List.getD_eq_getElem?_getD]

/-- The join matches `m` under any environment that agrees with `env` below `K`, on the regions
and on clean initial bytes, and reads fresh variables and dirty initial bytes off `m`. -/
theorem Match.generalise_to {F K : Nat} {Ss : List SState} {S : SState} {env env' : Env}
    {m : Machine} (hS : S ∈ Ss) (hR : ∀ S' ∈ Ss, S'.regions = S.regions) (hm : Match env S m)
    (hv : ∀ i < K, env'.vars i = env.vars i) (hF : ∀ i : Fin 32, env'.vars (F + i.val) = m.reg i)
    (hr : env'.regions = env.regions)
    (hc : ∀ r < S.regions.length, dirtyB Ss r = false → ∀ j, env'.mem0 r j = env.mem0 r j)
    (hd : ∀ r j, dirtyB Ss r = true → j < env.size r →
      env'.mem0 r j = (m.mem (env.base r + BitVec.ofNat 64 j)).getD 0) :
    Match env' (generalise F Ss K) m := by
  obtain ⟨S₀, rest, rfl⟩ : ∃ S₀ rest, Ss = S₀ :: rest := by
    cases Ss with
    | nil => cases hS
    | cons a l => exact ⟨a, l, rfl⟩
  have hR0 : S₀.regions = S.regions := hR S₀ (List.mem_cons_self ..)
  have hc' : ∀ r < S₀.regions.length, dirtyB (S₀ :: rest) r = false →
      ∀ j, env'.mem0 r j = env.mem0 r j := fun r h => hc r (hR0 ▸ h)
  have hb : ∀ r, env'.base r = env.base r := fun r => by simp only [Env.base, hr]
  have hs : ∀ r, env'.size r = env.size r := fun r => by simp only [Env.size, hr]
  have hclean := @Sym.eval_clean env env' K S₀.regions.length (dirtyB (S₀ :: rest)) hv hr hc'
  refine ⟨by simp [generalise], fun i => ?_, fun r j hr' hj => ?_, fun k hk t ht => ?_⟩
  · -- registers
    have hreg : (generalise F (S₀ :: rest) K).reg i.val =
        genReg F K S₀.regions.length (dirtyB (S₀ :: rest)) (S₀ :: rest) S₀ i.val := by
      unfold SState.reg
      split
      · simp [genReg, *]
      · exact genReg_getD ..
    rw [hreg]
    unfold genReg
    split
    · rename_i h0
      have := hm.regs i
      simp only [SState.reg, h0, if_true] at this
      rw [← this]; rfl
    · split
      · rename_i h0 hk
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
        rw [hclean _ hk.2, ← hk.1 S hS]
        exact hm.regs i
      · rw [Sym.eval_var, hF]
  · -- memory
    simp only [generalise, List.headD_cons] at hr'
    rw [hb]; rw [hs] at hj
    rw [hm.mem r j (hR0 ▸ hr') hj]
    congr 1
    unfold memByte
    cases hf : (generalise F (S₀ :: rest) K).mem.find? (·.covers r j) with
    | some w =>
      have hw := List.mem_of_find?_eq_some hf
      have hcov := List.find?_some hf
      simp only [generalise, List.headD_cons, List.mem_filter, Bool.and_eq_true,
        List.all_eq_true] at hw
      have hvis := hw.2.1 S hS
      simp only [visibleB, List.all_eq_true, List.mem_range, beq_iff_eq] at hvis
      simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcov
      have hfS := hvis (j - w.off) (by omega)
      rw [show w.off + (j - w.off) = j by omega, hcov.1.1] at hfS
      rw [hfS]; simp only
      rw [hclean _ hw.2.2]
    | none =>
      simp only
      cases hdr : dirtyB (S₀ :: rest) r with
      | true =>
        simp only [Env.byte0]; rw [hd r j hdr hj, hm.mem r j (hR0 ▸ hr') hj]; rfl
      | false =>
        have hnone : S.mem.find? (·.covers r j) = none := by
          refine List.find?_eq_none.mpr fun w hw hcov => ?_
          have : dirtyB (S₀ :: rest) r = true := by
            simp only [dirtyB, List.any_eq_true]
            exact ⟨S, hS, w, hw, by simp [Write.covers] at hcov; simp [hcov.1.1]⟩
          rw [hdr] at this; cases this
        rw [hnone]; simp only [Env.byte0]
        exact (hc' r hr' hdr j).symm
  · -- known facts
    simp only [generalise, List.headD_cons, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_iff_mem] at hk
    obtain ⟨-, ⟨⟨hkS, hkr⟩, hkd⟩, hkv⟩ := hk
    rw [Env.byte0, hc' k.r hkr hkd, hclean _ hkv]
    exact hm.known k (hkS S hS) t ht

theorem Env.WF.generalise {F K : Nat} {Ss : List SState} {S : SState} {env env' : Env}
    (hS : S ∈ Ss) (hR : ∀ S' ∈ Ss, S'.regions = S.regions) (hwf : Env.WF env S)
    (hr : env'.regions = env.regions) : Env.WF env' (generalise F Ss K) :=
  hwf.congr_regions hr (generalise_regions hS hR)

/-- Programme plan S5 probe 1: a state of `Ss` that matches `m` makes the join of `Ss` match `m`
under an environment that extends `env` below `F` and has `env`'s regions. -/
theorem Match.generalise {F : Nat} {Ss : List SState} {S : SState} {env : Env} {m : Machine}
    (hS : S ∈ Ss) (hR : ∀ S' ∈ Ss, S'.regions = S.regions) (hm : Match env S m)
    (hwf : Env.WF env S) :
    ∃ env', Env.Ext env env' F 0 ∧ env'.regions = env.regions ∧
      Match env' (generalise F Ss) m ∧ Env.WF env' (generalise F Ss) := by
  have hv : ∀ i < F, (genEnv F Ss env m).vars i = env.vars i := fun i hi => by
    simp [genEnv, Nat.not_le.mpr hi]
  refine ⟨genEnv F Ss env m, ⟨hv, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩, rfl,
    Match.generalise_to hS hR hm hv (fun i => ?_) rfl (fun r _ hd j => ?_) (fun r j hd _ => ?_),
    Env.WF.generalise hS hR hwf rfl⟩
  · simp [genEnv]
  · simp [genEnv, hd]
  · simp [genEnv, hd]

end ZesuExec.Sym
