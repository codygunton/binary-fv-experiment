import ZesuExec.Fn.F1.Proof
import ZesuExec.Vc.Tactics

/-!
# F1 in the obligation framework (programme plan S4 benchmark; conditional)

Plan `F1`: the map's cut points, the entry and the four call return sites: after `remap` (F0,
`0x800cb4f8`), after `alloc` (`0x800cb55c`), after `memcpy` (`0x800cb588`), after `free`
(`0x800cb5a8`). `σ` = `Sig`: the allocator assumptions, the allocator list, the items and the
entry machine.

Cut states: the entry state `S0`; after `remap` the spike's `S1` (one path reaches it, so its
`Env` is the entry `Env` plus the returned registers, a function of the machine). The other
three return sites are reached on two paths (capacity 0, or after `remap`); their states are
`genS` of the spike's two path states: a register or a write is kept where both agree and
mention only entry variables, everything else is a fresh variable `F + i` that the cut's `Env`
reads off the machine. Their assertions are the hypotheses of the spike's stage lemmas for either
path (`stage2a`/`stage2b`, `stage3a`/`stage3b`, `stage4b`), stated with an existential `Env`.
Budgets: 197 at the entry, 148 after `remap`, `103`/`78` after `alloc`, `18`/`67` after
`memcpy` (capacity 0 / positive), 17 after `free`.

The hand proofs below reuse the spike's stage-0 and stage-1 arguments. The `CutOK` of the three
join cuts needs the matching of a path state against its `genS` (programme plan S5 probe 1) and
stays open with the leaves of their runs; `f1_spec` keeps its spike proof (`Fn/F1/Proof.lean`).
-/

namespace ZesuExec.Fn.F1
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Joined states -/

/-- A term over entry variables (`var i`, `i < 32`), literals, region pointers and initial bytes. -/
def entryOnly : Sym → Bool
  | .lit _ => true
  | .var i => i < 32
  | .ptr _ _ => true
  | .init _ _ _ => true
  | .initx _ _ i _ _ => entryOnly i
  | .bin _ a b => entryOnly a && entryOnly b
  | .sext _ a => entryOnly a
  | .bytes a _ _ => entryOnly a
  | .cat a b _ => entryOnly a && entryOnly b

/-- Keep what `a` and `b` share over entry variables; other registers become `var (F + i)`;
other writes are dropped (their bytes are the machine's at the cut). -/
def genS (F : Nat) (a b : SState) : SState where
  regs := (List.range 32).map fun i =>
    if i = 0 then .lit 0
    else if a.reg i == b.reg i && entryOnly (a.reg i) then a.reg i else .var (F + i)
  mem := a.mem.filter fun w => b.mem.contains w && entryOnly w.v
  known := a.known.filter fun w => b.known.contains w && entryOnly w.v
  regions := a.regions
  steps := 0

def SJ2 : SState := genS 500 S2a S2b
def SJ3 : SState := genS 600 S3a S3b
def SJ4 : SState := genS 700 S4b S4b

/-! ## Parameters, environments, assertions -/

structure Sig where
  A : AllocAssumptions zesuImage
  L : List (Word × Nat)
  items : List Byte
  m : Machine

/-- Capacity and request of the entry machine. -/
abbrev capOf (m : Machine) : Nat := (wordAt m (m.reg 10 + 16)).toNat
abbrev reqOf (m : Machine) : Nat := (m.reg 12).toNat

/-- After `remap`: the entry `Env` and `var (100 + i)` = register `i` at the return. -/
def envR (g : Sig) (mh : Machine) : Env := (env0 g.m).setVars 100 fun i => mh.reg (Fin.ofNat 32 i)

/-- At a join: entry variables from the entry machine, `var (F + i)` = register `i` at the cut,
the entry regions, frame bytes from the machine at the cut, header and allocator bytes from
the entry. -/
def envJ (F : Nat) (g : Sig) (mh : Machine) : Env where
  vars := fun i => if i < 32 then g.m.reg (Fin.ofNat 32 i) else mh.reg (Fin.ofNat 32 (i - F))
  regions := (shape g.m).map (·.1)
  mem0 := fun r j =>
    let b := (((shape g.m).map (·.1)).getD r (0, 0)).1 + BitVec.ofNat 64 j
    ((if r = 0 then mh.mem b else g.m.mem b)).getD 0

def AE (g : Sig) (m : Machine) : Prop := m = g.m ∧ m.pc.toNat = entry ∧ Pre g.A g.L g.items m

/-- The hypotheses of `stage1`. -/
def AR (g : Sig) (m2 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ Match (envR g m2) S1 m2 ∧ Env.WF (envR g m2) S1 ∧
  m2.pc.toNat = 0x800cb4f8 ∧ Inv g.A g.L g.m m2 ∧ 0 < capOf g.m ∧ capOf g.m < reqOf g.m ∧
  (envR g m2).vars 120 = 0 ∧ (envR g m2).vars 122 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧
  g.A.Heap g.L m2 ∧ ScratchSame g.m m2 ∧ BytesAt m2 (wordAt g.m (g.m.reg 10)) g.items

/-- The hypotheses of `stage2a` (capacity 0) or `stage2b` (after `remap`). -/
def AJ2 (g : Sig) (m2 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ m2.pc.toNat = 0x800cb55c ∧ Inv g.A g.L g.m m2 ∧
  capOf g.m < reqOf g.m ∧ BytesAt m2 (wordAt g.m (g.m.reg 10)) g.items ∧ ScratchSame g.m m2 ∧
  AllocOut g.A g.L (grown (reqOf g.m) * elemBytes) m2 ∧
  ((capOf g.m = 0 ∧ ∃ env, EnvOk g.m env ∧ Match env S2a m2 ∧ Env.WF env S2a ∧
      env.vars 210 = m2.reg 10 ∧ env.vars 222 = BitVec.ofNat 64 (grown (reqOf g.m))) ∨
   (0 < capOf g.m ∧ ∃ env, EnvOk g.m env ∧ Match env S2b m2 ∧ Env.WF env S2b ∧
      env.vars 310 = m2.reg 10 ∧ env.vars 122 = BitVec.ofNat 64 (grown (reqOf g.m))))

/-- What `stage3a` and `stage3b` share, for the new buffer `p'`. -/
def Copied (g : Sig) (m4 : Machine) (p' : Word) : Prop :=
  0 < p'.toNat ∧ RamRange p' (grown (reqOf g.m) * elemBytes) ∧ BytesAt m4 p' g.items ∧
  BytesAt m4 (BitVec.ofNat 64 Layout.extraParams)
    (wordBytes (BitVec.ofNat 64 ((wordAt g.m (g.m.reg 10 + 8)).toNat * elemBytes))) ∧
  g.A.Heap (g.L ++ [(p', grown (reqOf g.m) * elemBytes)]) m4 ∧
  (∀ a, g.A.Priv (g.L ++ [(p', grown (reqOf g.m) * elemBytes)]) a → g.A.Priv g.L a) ∧
  (∀ a, InRange p' (grown (reqOf g.m) * elemBytes) a → g.A.Priv g.L a)

/-- The hypotheses of `stage3a` (capacity 0) or `stage3b` (after `remap`). -/
def AJ3 (g : Sig) (m4 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ m4.pc.toNat = 0x800cb588 ∧ Inv g.A g.L g.m m4 ∧
  capOf g.m < reqOf g.m ∧
  ((capOf g.m = 0 ∧ ∃ env p', EnvOk g.m env ∧ Match env S3a m4 ∧ Env.WF env S3a ∧
      env.vars 210 = p' ∧ env.vars 222 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧ Copied g m4 p') ∨
   (0 < capOf g.m ∧ ∃ env p', EnvOk g.m env ∧ Match env S3b m4 ∧ Env.WF env S3b ∧
      env.vars 310 = p' ∧ env.vars 122 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧ Copied g m4 p'))

/-- The hypotheses of `stage4b`. -/
def AJ4 (g : Sig) (m4 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ m4.pc.toNat = 0x800cb5a8 ∧ Inv g.A g.L g.m m4 ∧
  0 < capOf g.m ∧ capOf g.m < reqOf g.m ∧
  ∃ env p', EnvOk g.m env ∧ Match env S4b m4 ∧ Env.WF env S4b ∧ env.vars 310 = p' ∧
    env.vars 122 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧ 0 < p'.toNat ∧
    RamRange p' (grown (reqOf g.m) * elemBytes) ∧ BytesAt m4 p' g.items ∧
    BytesAt m4 (BitVec.ofNat 64 Layout.extraParams)
      (wordBytes (BitVec.ofNat 64 ((wordAt g.m (g.m.reg 10 + 8)).toNat * elemBytes))) ∧
    g.A.Heap ((g.L.erase (wordAt g.m (g.m.reg 10), capOf g.m * elemBytes)) ++
      [(p', grown (reqOf g.m) * elemBytes)]) m4 ∧
    (∀ a, g.A.Priv ((g.L.erase (wordAt g.m (g.m.reg 10), capOf g.m * elemBytes)) ++
      [(p', grown (reqOf g.m) * elemBytes)]) a →
        g.A.Priv g.L a ∨ InRange (wordAt g.m (g.m.reg 10)) (capOf g.m * elemBytes) a) ∧
    (∀ a, InRange p' (grown (reqOf g.m) * elemBytes) a → g.A.Priv g.L a)

def cE : Cut Sig := ⟨entry, S0, AE, fun _ m => env0 m, fun _ _ => bound⟩
def cR : Cut Sig := ⟨0x800cb4f8, S1, AR, envR, fun _ _ => 148⟩
def cJ2 : Cut Sig :=
  ⟨0x800cb55c, SJ2, AJ2, envJ 500, fun g _ => if capOf g.m = 0 then 103 else 78⟩
def cJ3 : Cut Sig :=
  ⟨0x800cb588, SJ3, AJ3, envJ 600, fun g _ => if capOf g.m = 0 then 18 else 67⟩
def cJ4 : Cut Sig := ⟨0x800cb5a8, SJ4, AJ4, envJ 700, fun _ _ => 17⟩

/-! ## Runs, with the plan's cut points -/

def cutPcs : List Nat := [entry, 0x800cb4f8, 0x800cb55c, 0x800cb588, 0x800cb5a8]

sym_run runE := run zesuImage cutPcs 400 entry S0
sym_run runR := run zesuImage cutPcs 400 0x800cb4f8 S1
sym_run runJ2 := run zesuImage cutPcs 400 0x800cb55c SJ2
sym_run runJ3 := run zesuImage cutPcs 400 0x800cb588 SJ3
sym_run runJ4 := run zesuImage cutPcs 400 0x800cb5a8 SJ4

/-! ## Callees -/

def remapC : Callee Sig zesuImage where
  entry := F0.entry
  bound := F0.bound
  Pre := fun _ => F0.Pre
  Post := fun _ m m' => F0.Post m m' ∧ Preserved m m'
  spec := fun _ m hpc hpre => Reaches.preserve (F0.f0_spec m hpc hpre)

def allocC : Callee Sig zesuImage where
  entry := allocEntry
  bound := 53
  Pre := fun g m => g.A.Heap g.L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧
    (m.reg 12).toNat ≤ 3 ∧ StackOk m 16 ∧ RetAligned m ∧ CalleeFrameFree (g.A.Priv g.L) m
  Post := fun g m m' => (Returns m m' ∧
      SameOutside (fun a => g.A.Priv g.L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
      ((m'.reg 10 = 0 ∧ g.A.Heap g.L m') ∨
       (m'.reg 10 ≠ 0 ∧ g.A.Heap (g.L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
        RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
        (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → g.A.Priv g.L a) ∧
        (∀ a, g.A.Priv (g.L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → g.A.Priv g.L a)))) ∧
    Preserved m m'
  spec := fun g m hpc hpre => Reaches.preserve (g.A.alloc_spec g.L m hpc hpre)

/-- `free` of a block of some allocator list `L'` (the list after `alloc`). -/
def freeC : Callee Sig zesuImage where
  entry := freeEntry
  bound := 42
  Pre := fun g m => ∃ L', g.A.Heap L' m ∧ (m.reg 11, (m.reg 12).toNat) ∈ L' ∧
    0 < (m.reg 12).toNat ∧ (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 3 ∧ StackOk m 16 ∧
    RetAligned m ∧ CalleeFrameFree (g.A.Priv L') m
  Post := fun g m m' => ∃ L', g.A.Heap L' m ∧ (Returns m m' ∧
      SameOutside (fun a => g.A.Priv L' a ∨ InRange (m.reg 11) (m.reg 12).toNat a ∨
        InRange (m.reg 2 - 16) 16 a) m m' ∧
      g.A.Heap (L'.erase (m.reg 11, (m.reg 12).toNat)) m' ∧
      (∀ a, g.A.Priv (L'.erase (m.reg 11, (m.reg 12).toNat)) a →
        g.A.Priv L' a ∨ InRange (m.reg 11) (m.reg 12).toNat a)) ∧ Preserved m m'
  spec := fun g m hpc ⟨L', hpre⟩ =>
    (Reaches.preserve (g.A.free_spec L' m hpc hpre)).mono (Nat.le_refl _)
      fun _ h => ⟨L', hpre.1, h⟩

def vcPlan : Plan Sig zesuImage where
  cuts := [cE, cR, cJ2, cJ3, cJ4]
  fuel := 400
  leaves := fun pc =>
    if pc = entry then runE_leaves else if pc = 0x800cb4f8 then runR_leaves
    else if pc = 0x800cb55c then runJ2_leaves else if pc = 0x800cb588 then runJ3_leaves
    else if pc = 0x800cb5a8 then runJ4_leaves else []
  callee := fun r =>
    if r = 0x800cb4f8 then some remapC else if r = 0x800cb55c then some allocC
    else if r = 0x800cb588 then some (Callee.memcpy Sig zesuImage)
    else if r = 0x800cb5a8 then some freeC else none
  Post := fun g => Post g.A g.L g.items g.m

zesu_plan F1 := vcPlan

zesu_auto F1

/-! ## Items `zesu_auto` left open, by hand -/

/-- A leaf's run keeps every present byte and every byte below RAM: it writes only inside the
writable regions of its start state, which lie in RAM and stay present. -/
theorem preserved_of_leaf {env : Env} {S S' : SState} {m m' : Machine} (hwf : Env.WF env S)
    (hm' : Match env S' m') (hreg : S.regions.length ≤ S'.regions.length)
    (hso : SameOutside (InWritable env S) m m') : Preserved m m' := by
  refine ⟨fun a ha => ?_, fun a ha => hso a ?_⟩
  · by_cases hw : InWritable env S a
    · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
      have hr : r < S.regions.length := (List.getElem?_eq_some_iff.mp hR).1
      rw [hm'.mem r j (by omega) hj]; rfl
    · rw [hso a hw]; exact ha
  · rintro ⟨r, R, j, hR, hwR, hj, rfl⟩
    have := hwf.range r R hR
    simp only [hwR, if_true, Machine.writable, Machine.inRange, Bool.and_eq_true,
      decide_eq_true_eq, Layout.ramLo, Layout.ramHi] at this
    have e : (env.base r + BitVec.ofNat 64 j).toNat = (env.base r).toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e] at ha; unfold Layout.ramLo at ha; omega

theorem F1.cut_800cb40c : CutOK F1.plan F1.plan.cuts[0]! := by
  show CutOK F1.plan cE
  rintro g m ⟨rfl, hpc, hpre⟩
  have E := Entry.of_pre hpre
  exact ⟨E.wf, E.match, E.ro, hpc⟩

theorem F1.cut_800cb4f8 : CutOK F1.plan F1.plan.cuts[1]! := by
  show CutOK F1.plan cR
  rintro g m2 ⟨E, hm, hwf, hpc, hinv, -⟩
  exact ⟨hwf, hm, hinv.ro E, hpc⟩

/-- Entry leaf 0: no growth, return 0. -/
theorem F1.leaf_800cb40c_0 :
    LeafGoal F1.plan F1.plan.cuts[0]! ((F1.plan.leaves 0x800cb40c)[0]!) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  sym_simp at hc
  simp only [E.cap] at hc
  refine ⟨fun o ho => ?_, by decide, fun mf hm hex hfr => ?_⟩
  · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, entryEnv] using E.ra
  show Post A L items m mf
  have hret : Returns m mf := returns_leaf hm (envOk0 m).vars (by decide)
    (by simp [SState.reg, Sym.eval, entryEnv, Env.base, shape, BitVec.sub_add_cancel]) hex
  have hfr' : SameOutside (Allowed A L m) m mf := SameOutside.mono hfr fun a ha => by
    rcases E.inWritable ha with h | h
    · exact .inr (.inl (frame_sub_stack (by have := E.sp.1; unfold Layout.ramLo at this; omega) h))
    · exact .inl h
  have hle : (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by
    simp [BitVec.ult, entryEnv] at hc ⊢; omega
  refine ⟨hret, hfr', ?_⟩
  simp only [hle, if_true]
  refine ⟨by rw [← hm.regs 10]; rfl, E.header_same (envOk0 m) hm (by decide) (by decide),
    A.heap_frame L m mf E.heap fun a hp => hfr a fun hw => ?_, fun j hj => hfr _ fun hw => ?_⟩
  · exact E.ownNotPriv (E.inWritable hw) hp
  · exact E.scratchNotOwn hj (E.inWritable hw)

/-- Entry leaf 1: the grown byte count is not a multiple of 32 only above `2^32`. -/
theorem F1.leaf_800cb40c_1 :
    LeafGoal F1.plan F1.plan.cuts[0]! ((F1.plan.leaves 0x800cb40c)[1]!) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  exfalso
  sym_simp at hc
  simp only [E.cap] at hc
  simp only [entryEnv, Fin.ofNat] at hc
  simp at hc
  simp only [g_or' _ hreq, grown_shl5 _ hreq] at hc
  exact grown_bytes_ne _ hreq hc.2.2.2

theorem F1.leaf_800cb40c_3 :
    LeafGoal F1.plan F1.plan.cuts[0]! ((F1.plan.leaves 0x800cb40c)[3]!) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  exfalso; f1_overflow

theorem F1.leaf_800cb40c_7 :
    LeafGoal F1.plan F1.plan.cuts[0]! ((F1.plan.leaves 0x800cb40c)[7]!) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  exfalso; f1_overflow

/-- Entry leaf 4: capacity > 0, call `remap` (F0), which returns null; its return establishes
the hypotheses of `stage1`. -/
theorem F1.leaf_800cb40c_4 :
    LeafGoal F1.plan F1.plan.cuts[0]! ((F1.plan.leaves 0x800cb40c)[4]!) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  have hc2 := hc
  sym_simp at hc2; simp only [E.cap] at hc2; simp only [entryEnv, Fin.ofNat] at hc2; simp at hc2
  have hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat := by
    have := hc2.2.1
    refine Nat.pos_of_ne_zero fun h => this ?_
    apply BitVec.eq_of_toNat_eq; simpa using h
  have hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat := by
    have := hc2.1; simp [BitVec.ult] at this; simpa using this
  refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr => ?_⟩
  have hp : Preserved m mc := preserved_of_leaf E.wf hmc (by decide) hfr
  have own : ∀ a, InWritable (env0 m) S0 a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 (envOk0 m) (by decide) h
  have h22 : mc.reg 22 = BitVec.ofNat 64 (grown (m.reg 12).toNat) := by
    rw [Match.reg_eq hmc 22 22 rfl]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    exact g_or' _ hreq
  have h20 : mc.reg 20 = 0 := by
    rw [Match.reg_eq hmc 20 20 rfl]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    simp only [g_or' _ hreq, grown_srl59 _ hreq] <;> rfl
  have g2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [Match.reg_eq hmc 2 2 rfl]; show (env0 m).base 0 + BitVec.ofInt 64 0 = _
    rw [(envOk0 m).base0]; simp
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb4f8 := by rw [Match.reg_eq hmc 1 1 rfl]; rfl
  have hinv1 : Inv A L m mc := Inv.refl.step hfr (fun a h => E.inWritable' (envOk0 m) (by decide) h) hp
  have hpre : F0.Pre mc := ⟨hinv1.ro E, E.calleeStack hp g2, by unfold RetAligned; rw [g1]; decide⟩
  refine ⟨remapC, rfl, by simpa [F0.entry] using hex, hpre, fun m2 hpost => ?_⟩
  obtain ⟨⟨hret, ha0, hfrR⟩, hp2⟩ := hpost
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [g2]; bv_omega
  rw [hcf] at hfrR
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := 100) (a0 := some (.lit 0)) hmc (E.wf.congr (by decide))
    (by decide) hret (fun s h => by cases h; rw [ha0]; rfl)
    (fun r j hr hj => hfrR _ (E.calleeApart (envOk0 m) r j (by simpa using hr) hj))
  have hsame : ∀ x, ¬ InRange (m.reg 2 - 128) 16 x →
      ¬ (InRange (m.reg 2 - 112) 112 x ∨ InRange (m.reg 10) 24 x) → m2.mem x = m.mem x :=
    fun x h1 h2 => (hfrR x h1).trans (hfr x fun hw => h2 (own x hw))
  have hpc2 : m2.pc.toNat = 0x800cb4f8 := by rw [hret.1, g1]; decide
  refine ⟨cR, by simp [F1.plan, vcPlan], rfl, hpc2, ⟨E, hm2, hwf2, hpc2, ?_, hc0, hlt,
    by simp [envR, Env.setVars]; rw [hret.2 20 (by decide), h20]; rfl,
    by simp [envR, Env.setVars]; rw [hret.2 22 (by decide), h22], ?_, ?_, ?_⟩,
    by show 9 + 148 ≤ 197 - (40 - 0); decide⟩
  · refine hinv1.step hfrR (fun a h => .inr (.inl ?_)) hp2
    have h128 := sp128 E
    simp only [InRange, h128] at h ⊢; omega
  · refine A.heap_frame L m m2 E.heap fun a ha => hsame a (fun h => ?_) (fun h => E.ownNotPriv h ha)
    exact E.priv a (.inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩))) ha
  · intro j hj
    have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
      simp [Layout.extraParams]; omega
    refine hsame _ (fun h => ?_) (E.scratchNotOwn hj)
    have d := E.d6; have h128 := sp128 E
    simp only [InRange] at h; rw [hs, h128] at h
    simp only [Apart, h128, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at d h
    omega
  · intro i hi
    obtain ⟨hc, hin⟩ := E.itemsOld hi
    obtain ⟨-, h2⟩ := E.oldSafe hc hin
    rw [hsame _ h2 (E.oldNotOwn hc hin)]; exact E.items i hi

/-- After `remap`, leaves 0 and 2: infeasible (the grown size is not 0; `remap` returned null). -/
theorem F1.leaf_800cb4f8_0 :
    LeafGoal F1.plan F1.plan.cuts[1]! ((F1.plan.leaves 0x800cb4f8)[0]!) := by
  leaf_intro
  intro g m2 hA hc
  obtain ⟨A, L, items, m⟩ := g
  obtain ⟨E, -, -, -, -, -, -, -, hv122, -⟩ := hA
  dsimp only at hc ⊢
  have hreq := E.req
  exfalso
  have h2 : (SBool.eq (.bin .sll (.var 122) (.lit 5)) (.lit 0)).eval (envR ⟨A, L, items, m⟩ m2) = true :=
    hc _ (by simp)
  simp only [SBool.eval, beq_iff_eq] at h2
  have h := congrArg BitVec.toNat h2
  rw [sll5_eval (i := 122) hv122 hreq] at h
  simp only [Sym.eval_lit, grown, elemBytes, BitVec.toNat_ofNat, Nat.zero_mod] at h; omega

theorem F1.leaf_800cb4f8_2 :
    LeafGoal F1.plan F1.plan.cuts[1]! ((F1.plan.leaves 0x800cb4f8)[2]!) := by
  leaf_intro
  intro g m2 hA hc
  obtain ⟨A, L, items, m⟩ := g
  obtain ⟨-, -, -, -, -, -, -, hv120, -⟩ := hA
  dsimp only at hc ⊢
  exfalso; sym_simp at hc; simp only [bne_iff_ne, ne_eq, hv120] at hc; exact hc rfl

/-- `alloc_step` split for `ExitGoal`: the callee's precondition, and what every result of
`alloc` gives at the return site. -/
theorem alloc_call {A : AllocAssumptions zesuImage} {L : List (Word × Nat)} {items : List Byte}
    {m : Machine} (E : Entry A L items m) {env : Env} {S Sl : SState} {mk mc : Machine} {F : Nat}
    (he : EnvOk m env) (hS : S.regions = [frameR, headerR, allocObjR])
    (hSl : Sl.regions = [frameR, headerR, allocObjR]) (hmc : Match env Sl mc) (hwf : Env.WF env S)
    (hfr : SameOutside (InWritable env S) mk mc) (hp : Preserved mk mc)
    (hinv : Inv A L m mk) (hheap : A.Heap L mk) (hscr : ScratchSame m mk)
    (hitems : BytesAt mk (wordAt m (m.reg 10)) items) (hwfB : Sl.wfB F = true)
    (r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes) (r12 : Sl.reg 12 = .lit 0)
    (r1 : Sl.reg 1 = .lit 0x800cb55c) (r2 : Sl.reg 2 = .ptr 0 0) :
    allocC.Pre ⟨A, L, items, m⟩ mc ∧ ∀ m2, allocC.Post ⟨A, L, items, m⟩ mc m2 →
      Match (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) m2 ∧
      Env.WF (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) ∧
      m2.pc.toNat = 0x800cb55c ∧ Inv A L m m2 ∧ ScratchSame m m2 ∧
      BytesAt m2 (wordAt m (m.reg 10)) items ∧
      AllocOut A L (grown (m.reg 12).toNat * elemBytes) m2 ∧ Returns mc m2 := by
  have own : ∀ a, InWritable env S a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he hS h
  have g2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [← hmc.regs 2]; show Sym.eval env (Sl.reg 2) = _; rw [r2]
    show env.base 0 + BitVec.ofInt 64 0 = _; rw [he.base0]; simp
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb55c := by
    rw [← hmc.regs 1]; show Sym.eval env (Sl.reg 1) = _; rw [r1]; rfl
  have g12 : mc.reg 12 = 0 := by
    rw [← hmc.regs 12]; show Sym.eval env (Sl.reg 12) = _; rw [r12]; rfl
  have hheapc : A.Heap L mc := A.heap_frame L mk mc hheap fun a ha => hfr a fun hw =>
    E.ownNotPriv (own a hw) ha
  have hreq := E.req
  refine ⟨⟨hheapc, ?_, ?_, by rw [g12]; decide, E.calleeStack (hinv.2.trans hp) g2,
    by unfold RetAligned; rw [g1]; decide, E.calleeFree (fun _ h => h) g2⟩, fun m2 hpost => ?_⟩
  · show 0 < (mc.reg 11).toNat; rw [r11]; simp only [grown, elemBytes]; omega
  · show (mc.reg 11).toNat < 2 ^ 63; rw [r11]; simp only [grown, elemBytes]; omega
  obtain ⟨⟨hret, hfrA, hout⟩, hp2⟩ := hpost
  rw [r11] at hout
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [g2]; bv_omega
  rw [hcf] at hfrA
  have hframe : ∀ r j, r < Sl.regions.length → j < env.size r →
      m2.mem (env.base r + BitVec.ofNat 64 j) = mc.mem (env.base r + BitVec.ofNat 64 j) := by
    intro r j hr hj
    have hr3 : r < 3 := by rw [hSl] at hr; simpa using hr
    refine hfrA _ fun h => ?_
    rcases h with h | h
    · exact E.regionNotPriv he hr3 hj h
    · exact E.calleeApart he r j hr3 hj h
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := F) (a0 := none) hmc (hwf.congr (hSl.trans hS.symm)) hwfB
    hret (fun s h => by simp at h) hframe
  have hinv2 : Inv A L m m2 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he hS h) hp).step hfrA ?_ hp2
    intro a h
    rcases h with h | h
    · exact .inr (.inr (.inr (.inl h)))
    · refine .inr (.inl ?_)
      have h128 := sp128 E
      simp only [InRange, h128] at h ⊢; omega
  have hpc2 : m2.pc.toNat = 0x800cb55c := by rw [hret.1, g1]; decide
  have hsame : ∀ x, ¬ A.Priv L x → ¬ InRange (m.reg 2 - 128) 16 x → ¬ (InRange (m.reg 2 - 112) 112 x ∨
      InRange (m.reg 10) 24 x) → m2.mem x = mk.mem x := fun x h1 h2 h3 =>
    (hfrA x fun h => h.elim h1 h2).trans (hfr x fun hw => h3 (own x hw))
  refine ⟨hm2, hwf2, hpc2, hinv2, fun j hj => ?_, fun i hi => ?_, hout, hret⟩
  · have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
      simp [Layout.extraParams]; omega
    have hin : InRange (BitVec.ofNat 64 Layout.extraParams) 8
        (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j) := by
      simp only [InRange]; rw [hs]; simp [Layout.extraParams]; omega
    rw [hsame _ (E.priv _ (.inr (.inr (.inr hin)))) (fun h => by
        have d := E.d6; have h128 := sp128 E
        simp only [InRange] at h; rw [hs, h128] at h
        simp only [Apart, h128, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
          Nat.reducePow] at d h; omega)
      (fun h => E.scratchNotOwn hj h)]
    exact hscr j hj
  · obtain ⟨hc, hin⟩ := E.itemsOld hi
    obtain ⟨h1, h2⟩ := E.oldSafe hc hin
    rw [hsame _ h1 h2 (E.oldNotOwn hc hin)]; exact hitems i hi

/-- Entry leaf 2: capacity 0, call `alloc`; its return establishes the `stage2a` side of the
assertion after `alloc`. -/
theorem F1.leaf_800cb40c_2 :
    LeafGoal F1.plan F1.plan.cuts[0]! ((F1.plan.leaves 0x800cb40c)[2]!) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  have hc2 := hc
  sym_simp at hc2; simp only [E.cap] at hc2; simp only [entryEnv, Fin.ofNat] at hc2; simp at hc2
  have hc0 : (wordAt m (m.reg 10 + 16)).toNat = 0 := by simp [hc2.2.1]
  have hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat := by
    have := hc2.1; simp [BitVec.ult] at this; simpa using this
  refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr => ?_⟩
  have hp : Preserved m mc := preserved_of_leaf E.wf hmc (by decide) hfr
  have h22 : mc.reg 22 = BitVec.ofNat 64 (grown (m.reg 12).toNat) := by
    rw [Match.reg_eq hmc 22 22 rfl]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    exact g_or' _ hreq
  have h11 : mc.reg 11 = BitVec.ofNat 64 (grown (m.reg 12).toNat * elemBytes) := by
    rw [Match.reg_eq hmc 11 11 rfl]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    simp only [g_or' _ hreq, grown_shl5 _ hreq]
  have r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes := by
    rw [h11, BitVec.toNat_ofNat]; simp only [grown, elemBytes]; omega
  obtain ⟨hpreA, hpostA⟩ := alloc_call (F := 200) E (envOk0 m) (by decide) (by decide) hmc E.wf
    hfr hp Inv.refl E.heap (fun _ _ => rfl) E.items (by decide) r11 rfl rfl rfl
  refine ⟨allocC, rfl, by simpa using hex, hpreA, fun m2 hpost => ?_⟩
  obtain ⟨hm2, hwf2, hpc2, hinv2, hscr2, hitems2, hout, hret⟩ := hpostA m2 hpost
  refine ⟨cJ2, by simp [F1.plan, vcPlan], rfl, hpc2, ⟨E, hpc2, hinv2, hlt, hitems2, hscr2, hout,
    .inl ⟨hc0, _, (envOk0 m).setVars (by decide) _, hm2, hwf2, by simp [Env.setVars],
      by simp [Env.setVars]; rw [hret.2 22 (by decide), h22]⟩⟩, ?_⟩
  show 53 + (if capOf m = 0 then 103 else 78) ≤ 197 - (41 - 0)
  simp only [capOf, hc0, if_true]; decide

/-- After `remap`, leaf 1: call `alloc`; its return establishes the `stage2b` side of the
assertion after `alloc`. -/
theorem F1.leaf_800cb4f8_1 :
    LeafGoal F1.plan F1.plan.cuts[1]! ((F1.plan.leaves 0x800cb4f8)[1]!) := by
  leaf_intro
  intro g m2 hA hc
  obtain ⟨A, L, items, m⟩ := g
  obtain ⟨E, hm, hwf, hpc, hinv, hc0, hlt, -, hv122, hheap, hscr, hitems⟩ := hA
  dsimp only at hc ⊢
  have hreq := E.req
  have he : EnvOk m (envR ⟨A, L, items, m⟩ m2) := (envOk0 m).setVars (by decide) _
  refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr => ?_⟩
  have hp : Preserved m2 mc := preserved_of_leaf hwf hmc (by decide) hfr
  obtain ⟨hpreA, hpostA⟩ := alloc_call (F := 300) E he (by decide) (by decide) hmc hwf hfr hp hinv
    hheap hscr hitems (by decide) (by rw [← hmc.regs 11]; exact sll5_eval hv122 hreq) rfl rfl rfl
  refine ⟨allocC, rfl, by simpa using hex, hpreA, fun m3 hpost => ?_⟩
  obtain ⟨hm3, hwf3, hpc3, hinv3, hscr3, hitems3, hout, -⟩ := hpostA m3 hpost
  refine ⟨cJ2, by simp [F1.plan, vcPlan], rfl, hpc3, ⟨E, hpc3, hinv3, hlt, hitems3, hscr3, hout,
    .inr ⟨hc0, _, he.setVars (by decide) _, hm3, hwf3, by simp [Env.setVars],
      by simp [Env.setVars]; exact hv122⟩⟩, ?_⟩
  show 53 + (if capOf m = 0 then 103 else 78) ≤ 148 - (17 - 0)
  simp only [capOf, Nat.pos_iff_ne_zero.mp hc0, if_false]; decide

zesu_assemble F1

end ZesuExec.Fn.F1
