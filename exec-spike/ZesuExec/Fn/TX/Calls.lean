import ZesuExec.Fn.TX.Keys

/-!
# TX: leaves that only set up a `decodeItem` call (programme plan S6 step 6)

`0x800000c4` (the entry item) and `0x8000018c` (a key item) write no memory and change only
argument registers: the loop assertion carries over to the call site (`os_congr`, `ie_congr`),
`f2_pre` gives `decodeItem`'s precondition, and the return cut's assertion is the site and `Post`.
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- A leaf of an `envB` cut that writes nothing leaves memory as it was. -/
theorem mem_same_nowrite {σ : Sig} {m m' : Machine} {S S' : SState} (hc : Common σ m)
    (hS : S.regions = baseRegions) (hm' : Match (envB σ m) S' m') (hS' : S'.regions = baseRegions)
    (hmem : S'.mem = []) (hfr : SameOutside (InWritable (envB σ m) S) m m') : m'.mem = m.mem := by
  funext a
  by_cases hw : InWritable (envB σ m) S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    have hr : r < 5 := by
      have := (List.getElem?_eq_some_iff.mp hR).1; rw [hS] at this; simpa [baseRegions] using this
    exact region_same hm' (by rw [hS']; simpa [baseRegions] using hr) (by rw [hmem]; rfl)
      (fun j hj => mem0_entry (common_present hc r j hr hj)) j hj
  · exact hfr a hw

/-- `OuterState` depends on memory and the saved registers only. -/
theorem os_congr {σ : Sig} {m m' : Machine} {o : Obs} {L : List (Word × Nat)}
    (h : OuterState σ m o L) (hmem : m'.mem = m.mem)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 24, 25, 27] : List (Fin 32)), m'.reg i = m.reg i) :
    OuterState σ m' o L := by
  obtain ⟨rm, pcm, mm⟩ := m
  obtain ⟨r', pc', mm'⟩ := m'
  simp only at hmem; subst hmem
  obtain ⟨⟨hpc, hpre, hro, h2, h8, h9, h18, h19, hsv, hst, hres, hrest, hscr, hfr⟩, hok,
    ⟨h20, h21, hi, hmag⟩, ⟨h24, h25, h27⟩, hel, hlive⟩ := h
  refine ⟨⟨hpc, hpre, hro, ?_, ?_, ?_, ?_, ?_, hsv, hst, hres, hrest, hscr, hfr⟩, hok,
    ⟨?_, ?_, hi, hmag⟩, ⟨?_, ?_, ?_⟩, hel,
    ⟨σ.A.heap_frame' _ _ _ hlive.1 (fun _ _ => rfl) ⟨fun _ h => h, fun _ _ => rfl⟩, hlive.2⟩⟩
  all_goals first
    | (rw [hr 2 (by decide)]; exact h2) | (rw [hr 8 (by decide)]; exact h8)
    | (rw [hr 9 (by decide)]; exact h9) | (rw [hr 18 (by decide)]; exact h18)
    | (rw [hr 19 (by decide)]; exact h19) | (rw [hr 20 (by decide)]; exact h20)
    | (rw [hr 21 (by decide)]; exact h21) | (rw [hr 24 (by decide)]; exact h24)
    | (rw [hr 25 (by decide)]; exact h25) | (rw [hr 27 (by decide)]; exact h27)

/-- The saved registers of a leaf state that keeps them. -/
theorem regs_keep {σ : Sig} {m m' : Machine} {S S' : SState} (hm : Match (envB σ m) S m)
    (hm' : Match (envB σ m) S' m') (is : List (Fin 32)) (hs : ∀ i ∈ is, S'.reg i.val = S.reg i.val) :
    ∀ i ∈ is, m'.reg i = m.reg i := fun i hi => by
  rw [Match.reg_eq hm' i i.val rfl, hs i hi, ← Match.reg_eq hm i i.val rfl]

theorem nil_obligs {l : Leaf} {env : Env} (h : l.obligs = []) : ∀ o ∈ l.obligs, o.holds env := by
  rw [h]; intro o ho; cases ho

theorem TX.leaf_800000c4_0 :
    LeafGoal TX.plan TX.plan.cuts[2]! ((TX.plan.leaves 0x800000c4)[0]!) := by
  show LeafGoal TX.plan cut0c4 (run0c4_leaves[0]!)
  rintro σ m ⟨hpc, o, L, hs⟩ -
  have hsteps : (run0c4_leaves[0]!).S.steps - cut0c4.S.steps = 5 := by decide
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run0c4_leaves[0]!).exit = .call 0x800d6960 0x800000d8 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d6960 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  have hc := hs.1
  have hpre := hc.2.1
  obtain ⟨hwf, hm, -⟩ := body_cut hc
  have hmem := mem_same_nowrite hc rfl hm' (by decide) (by decide) hfr
  have hr := regs_keep hm hm' [2, 8, 9, 18, 19, 20, 21, 24, 25, 27] (by decide)
  have hs' := os_congr hs hmem hr
  have reg : ∀ (i : Fin 32) (s : Sym), (run0c4_leaves[0]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run0c4_leaves[0]!).S.reg 1 = .lit 0x800000d8)
  have r10 := reg 10 _ (by decide : (run0c4_leaves[0]!).S.reg 10 = .ptr 0 0x98)
  have r11 := reg 11 _ (by decide : (run0c4_leaves[0]!).S.reg 11 = .var 20)
  have r12 := reg 12 _ (by decide : (run0c4_leaves[0]!).S.reg 12 = .var 21)
  simp only [Sym.eval, Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero, Sig.sl, w,
    frameBytes] at r1 r10 r11 r12
  rw [show σ.S - 576#64 + BitVec.ofInt 64 0x98 = σ.sl 0x1a8 by simp only [Sig.sl, w]; bv_omega]
    at r10
  have r11' : m'.reg 11 = curPtr σ o := r11.trans hs.2.2.1.1
  have r12' : m'.reg 12 = w (o.p - o.i) := r12.trans hs.2.2.1.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hle := hs.2.1.2.1
  have hi := hs.2.2.1.2.2.1
  have hsite : Site0d4 σ m' := ⟨o, L, hs', r1, fun t ht => by
    simp only [List.length_cons, List.length_nil] at ht
    obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    · exact r10
    · exact r11'
    · exact r12'⟩
  have hpre2 : F2.Pre m' := f2_pre hs'.1 r10 (by decide) (by decide) (by decide)
    (off := o.h + o.i) r11' (by rw [r12']; simp only [w, BitVec.toNat_ofNat]; omega)
    (by unfold RetAligned; rw [r1]; decide)
  refine ⟨f2C, (), rfl, hex, hpre2, fun m'' hpost => ⟨cut0d8, by simp [TX.plan, vcPlan], rfl,
    ?_, ⟨m', (), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by decide))
    show F2.bound + (32 * outerLeft m'' + 220) ≤ bOuter m - _
    rw [hsteps]; unfold bOuter outerLeft at *; rw [h21]; unfold F2.bound; omega

/-- The keys loop's facts depend on memory and the saved registers only. -/
theorem ie_congr {σ : Sig} {m m' : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    (h : InEntry σ m o k L ∧ KeysOk σ m o k ∧ KList σ m k k.keys.length) (hmem : m'.mem = m.mem)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 26, 27] : List (Fin 32)),
      m'.reg i = m.reg i) :
    InEntry σ m' o k L ∧ KeysOk σ m' o k ∧ KList σ m' k k.keys.length := by
  obtain ⟨rm, pcm, mm⟩ := m
  obtain ⟨r', pc', mm'⟩ := m'
  simp only at hmem; subst hmem
  obtain ⟨⟨⟨hpc, hpre, hro, h2, h8, h9, h18, h19, hsv, hst, hres, hrest, hscr, hfr⟩, hok,
    ⟨h20, h21, hi, hmag⟩, hel, hlive, ⟨hd, hle, h26⟩, had, hkl, h27⟩,
    ⟨hkw, h23, h22, h24⟩, hK⟩ := h
  refine ⟨⟨⟨hpc, hpre, hro, ?_, ?_, ?_, ?_, ?_, hsv, hst, hres, hrest, hscr, hfr⟩, hok,
    ⟨?_, ?_, hi, hmag⟩, hel,
    ⟨σ.A.heap_frame' _ _ _ hlive.1 (fun _ _ => rfl) ⟨fun _ h => h, fun _ _ => rfl⟩, hlive.2⟩,
    ⟨hd, hle, ?_⟩, had, hkl, ?_⟩, ⟨hkw, ?_, ?_, ?_⟩, hK⟩
  all_goals first
    | (rw [hr 2 (by decide)]; exact h2) | (rw [hr 8 (by decide)]; exact h8)
    | (rw [hr 9 (by decide)]; exact h9) | (rw [hr 18 (by decide)]; exact h18)
    | (rw [hr 19 (by decide)]; exact h19) | (rw [hr 20 (by decide)]; exact h20)
    | (rw [hr 21 (by decide)]; exact h21) | (rw [hr 22 (by decide)]; exact h22)
    | (rw [hr 23 (by decide)]; exact h23) | (rw [hr 24 (by decide)]; exact h24)
    | (rw [hr 26 (by decide)]; exact h26) | (rw [hr 27 (by decide)]; exact h27)

theorem TX.leaf_8000018c_0 :
    LeafGoal TX.plan TX.plan.cuts[6]! ((TX.plan.leaves 0x8000018c)[0]!) := by
  show LeafGoal TX.plan cut18c (run18c_leaves[0]!)
  rintro σ m ⟨hpc, o, k, L, hie, hko, hK, hj⟩ -
  have hsteps : (run18c_leaves[0]!).S.steps - cut18c.S.steps = 5 := by decide
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run18c_leaves[0]!).exit = .call 0x800d6960 0x800001a0 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800d6960 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  have hc := hie.1
  have hpre := hc.2.1
  obtain ⟨hwf, hm, -⟩ := body_cut hc
  have hmem := mem_same_nowrite hc rfl hm' (by decide) (by decide) hfr
  have hr := regs_keep hm hm' [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 26, 27] (by decide)
  obtain ⟨hie', hko', hK'⟩ := ie_congr ⟨hie, hko, hK⟩ hmem hr
  have reg : ∀ (i : Fin 32) (s : Sym), (run18c_leaves[0]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run18c_leaves[0]!).S.reg 1 = .lit 0x800001a0)
  have r10 := reg 10 _ (by decide : (run18c_leaves[0]!).S.reg 10 = .ptr 0 0x140)
  have r11 := reg 11 _ (by decide : (run18c_leaves[0]!).S.reg 11 = .var 23)
  have r12 := reg 12 _ (by decide : (run18c_leaves[0]!).S.reg 12 = .var 22)
  simp only [Sym.eval, Env.base, envB, entryEnv, shapeOf, List.getD_cons_zero, Sig.sl, w,
    frameBytes] at r1 r10 r11 r12
  rw [show σ.S - 576#64 + BitVec.ofInt 64 0x140 = σ.sl 0x100 by simp only [Sig.sl, w]; bv_omega]
    at r10
  have r11' : m'.reg 11 = keyPtr σ o k := r11.trans hko.2.1
  have r12' : m'.reg 12 = w (k.kl - k.j) := r12.trans hko.2.2.1
  have hl64 : σ.len < 2 ^ 64 := (wordAt σ.m (σ.rest + 8)).isLt
  have hle := hie.2.1.2.1
  have hi := hie.2.2.1.2.2.1
  have hel := hie.2.2.2.2.2.1.2.1
  have hal := hie.2.2.2.2.2.2.1.2.1
  have hkb := hie.2.2.2.2.2.2.2.1.2
  have hsite : Site19c σ m' := ⟨o, k, L, hie', hko', hK', hj, r1, fun t ht => by
    simp only [List.length_cons, List.length_nil] at ht
    obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    · exact r10
    · exact r11'
    · exact r12'⟩
  have hpre2 : F2.Pre m' := f2_pre hie'.1 r10 (by decide) (by decide) (by decide)
    (off := o.h + o.i + k.eh + (k.ah + 20) + k.kh + k.j)
    (by rw [r11']; simp only [keyPtr, kplPtr, aftPtr, entPtr, curPtr, w]; bv_omega)
    (by rw [r12']; simp only [w, BitVec.toNat_ofNat]; omega)
    (by unfold RetAligned; rw [r1]; decide)
  refine ⟨f2C, (), rfl, hex, hpre2, fun m'' hpost => ⟨cut1a0, by simp [TX.plan, vcPlan], rfl,
    ?_, ⟨m', (), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1, r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by decide))
    have h22 : m''.reg 22 = m.reg 22 := (hpost.1.1.2 22 (by decide)).trans (hr 22 (by decide))
    have h26 : m''.reg 26 = m.reg 26 := (hpost.1.1.2 26 (by decide)).trans (hr 26 (by decide))
    show F2.bound + (32 * (afterEntry m'' + keysLeft m'') + 658) ≤ bKeys m - _
    rw [hsteps]; unfold bKeys afterEntry keysLeft at *; rw [h21, h22, h26]; unfold F2.bound; omega

end ZesuExec.Fn.TX
