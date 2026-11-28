import ZesuExec.Fn.TX.Leaves3

/-!
# TX: growing the entries list (programme plan S6 step 6, third hand)

After `toOwnedSlice` of the keys (`0x8000025c`) a full entries list grows: `remap` (F0, always
null), then `alloc` (`0x800003d4`), `memcpy` (`0x80000400`), `free` of the old buffer
(`0x8000042c`), and the entry store `0x80000460`. The new block's bytes are the allocator's
(`live_of_heap`: `arena_split` and the live list's disjointness).
-/

namespace ZesuExec.Fn.TX
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Live lists from the allocator's heap -/

/-- TX's live list from the allocator's heap: blocks outside `g.L` lie in `Priv g.L`. -/
theorem live_of_heap {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hpre : Pre σ.A σ.g σ.m)
    (hh : σ.A.Heap L m) (hperm : L.Perm (σ.g.L ++ X)) (hpos : ∀ b ∈ X, 0 < b.2) :
    Live σ m L X := by
  have hok := σ.A.live_ok L m hh
  have hp := hok.1
  rw [hperm.pairwise_iff (fun h => h.symm), List.pairwise_append] at hp
  have hheap0 : σ.A.Heap σ.g.L σ.m := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hh, hperm, fun b hb => ⟨hpos b hb,
    (hok.2 b (hperm.symm.subset (List.mem_append_right _ hb))).1, fun a ha => ?_⟩⟩
  have hL : b ∈ L := hperm.symm.subset (List.mem_append_right _ hb)
  have harena := (σ.A.arena_split L m a hh).mpr (.inr ⟨b, hL, ha⟩)
  rcases (σ.A.arena_split σ.g.L σ.m a hheap0).mp harena with h' | ⟨c, hc, hin⟩
  · exact h'
  · have := hp.2.2 c hc b hb
    simp only [InRange] at ha hin; omega

/-- A block of TX's live list is present. -/
theorem live_present {σ : Sig} {m : Machine} {L X : List (Word × Nat)} (hlive : Live σ m L X)
    {b : Word × Nat} (hb : b ∈ X) : Present m b.1 b.2 :=
  ((σ.A.live_ok L m hlive.1).2 b (hlive.2.1.symm.subset (List.mem_append_right _ hb))).2

theorem heap_same {σ : Sig} {m m' : Machine} {L : List (Word × Nat)} (h : σ.A.Heap L m)
    (hmem : m'.mem = m.mem) : σ.A.Heap L m' :=
  σ.A.heap_frame' L m m' h (fun a _ => by rw [hmem])
    ⟨fun a h => by rw [hmem]; exact h, fun a _ => by rw [hmem]⟩

theorem common_same {σ : Sig} {m m' : Machine} (hc : Common σ m) (hmem : m'.mem = m.mem)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19] : List (Fin 32)), m'.reg i = m.reg i) : Common σ m' :=
  common_keep hc hr ⟨fun a h => by rw [hmem]; exact h, fun a _ => by rw [hmem]⟩
    (R := fun _ => False) (fun a _ => by rw [hmem]) fun _ h => h.elim

/-! ## The callee frame of `alloc`/`free` -/

/-- The 16 bytes below `sp` an allocator callee uses: TX's stack, none of `EntryDone`'s slots. -/
theorem cframe_R {σ : Sig} {mc : Machine} (hc : Common σ mc) {a : Word}
    (h : InRange (mc.reg 2 - 16) 16 a) :
    InRange (σ.sl stackBytes) stackBytes a ∧
      ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20)] : List (Nat × Nat)),
        ¬ InRange (σ.sl kn.1) kn.2 a := by
  have hpre := hc.2.1
  rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
  refine ⟨sl_in_stack hpre (by decide) (by decide) h, fun kn hkn hin => ?_⟩
  have hk : kn.1 ≤ 576 ∧ kn.2 ≤ kn.1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
    rcases hkn with rfl | rfl | rfl | rfl <;> decide
  have h1 := sl_toNat hpre (k := 592) (by decide)
  have h2 := sl_toNat hpre (k := kn.1) (by unfold stackBytes; omega)
  have := (entry_nums hpre).1; unfold Layout.ramLo at this
  simp only [InRange, h1, h2] at h hin; omega

/-- A frame word `S - j` (`8 ≤ j ≤ 576`) is outside the callee frame and the allocator's memory. -/
theorem frame_out {σ : Sig} {mc : Machine} (hc : Common σ mc) {L X : List (Word × Nat)}
    (hlive : Live σ mc L X) {j t : Nat} (hj : 8 ≤ j) (hj' : j ≤ 576) (ht : t < 8) :
    ¬ σ.A.Priv L (σ.sl j + BitVec.ofNat 64 t) ∧
      ¬ InRange (mc.reg 2 - 16) 16 (σ.sl j + BitVec.ofNat 64 t) := by
  have hpre := hc.2.1
  have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  have hin : InRange (σ.sl j) 8 (σ.sl j + BitVec.ofNat 64 t) := in_self (by rw [h3]; omega) ht
  refine ⟨fun hp => stack_not_priv hpre (sl_in_stack hpre (by unfold stackBytes; omega) hj hin)
    (priv_sub hpre hlive hp), fun h => ?_⟩
  rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at h
  have h1 := sl_toNat hpre (k := 592) (by decide)
  simp only [InRange, h1, h3] at h hin; omega

/-! ## `memcpy`'s precondition -/

theorem memcpy_pre {m : Machine} (hra : RetAligned m) (hscr : Present m scratch 8)
    (h : 0 < (m.reg 12).toNat → RamRange (m.reg 11) (m.reg 12).toNat ∧
      Present m (m.reg 11) (m.reg 12).toNat ∧ RamRange (m.reg 10) (m.reg 12).toNat ∧
      Present m (m.reg 10) (m.reg 12).toNat) : MemcpyPre m := by
  unfold MemcpyPre ziskMemcpyDomain
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hra, by decide⟩, ?_⟩, ?_⟩
  · unfold Machine.present
    exact readBytes_isSome_of fun t ht => by
      have := hscr t ht
      rwa [show scratch + BitVec.ofNat 64 t = BitVec.ofNat 64 (Layout.extraParams + t) by
        simp only [scratch]; bv_omega] at this
  · rcases Nat.eq_zero_or_pos (m.reg 12).toNat with h0 | h0
    · exact .inl h0
    · obtain ⟨r1, p1, r0, p0⟩ := h h0
      unfold RamRange at r1 r0
      refine .inr ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simp only [Machine.readable, Machine.inRange, Layout.ramLo, Layout.ramHi, Layout.rodataLo,
          Layout.rodataHi, Layout.inputLo, Layout.inputHi, Bool.or_eq_true, Bool.and_eq_true,
          decide_eq_true_eq] at r1 ⊢; omega
      · unfold Machine.present
        exact readBytes_isSome_of fun t ht => by rw [ofNat_toNat_add]; exact p1 t ht
      · simp only [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi,
          Bool.and_eq_true, decide_eq_true_eq] at r0 ⊢; omega
      · unfold Machine.present
        exact readBytes_isSome_of fun t ht => by rw [ofNat_toNat_add]; exact p0 t ht

/-! ## `0x800003d4`: after `alloc`, `memcpy` of the old entries -/

theorem w_40 (n : Nat) : w (32 * n) + w (8 * n) = w (entrySize * n) := by
  simp only [w, entrySize, ← BitVec.ofNat_add]; congr 1; omega

theorem TX.leaf_800003d4_0 :
    LeafGoal TX.plan TX.plan.cuts[12]! ((TX.plan.leaves 0x800003d4)[0]!) := by
  show LeafGoal TX.plan cut3d4 (run3d4_leaves[0]!)
  have hcs : (run3d4_leaves[0]!).conds = [SBool.ne (Sym.var 10) (Sym.lit 0)] := by decide
  have hsteps : (run3d4_leaves[0]!).S.steps - cut3d4.S.steps = 9 := by decide
  intro σ m hA hc
  have hcm := A3d4_common hA
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run3d4_leaves[0]!).exit = .call 0x800e06c0 0x80000400 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x800e06c0 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  obtain ⟨-, hm, -⟩ := body_cut hcm
  have hmem := mem_same_nowrite hcm rfl hm' (by decide) (by decide) hfr
  have hS : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 25, 26, 27, 10] : List (Fin 32)),
      (run3d4_leaves[0]!).S.reg i.val = SBody.reg i.val := by decide
  have hr := regs_keep hm hm' _ hS
  have reg : ∀ (i : Fin 32) (s : Sym), (run3d4_leaves[0]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run3d4_leaves[0]!).S.reg 1 = .lit 0x80000400)
  have r11 := reg 11 _ (by decide : (run3d4_leaves[0]!).S.reg 11 = .var 22)
  have r12 := reg 12 _ (by decide : (run3d4_leaves[0]!).S.reg 12 =
    .bin .add (.init 0 64 8) (.init 0 72 8))
  have r24 := reg 24 _ (by decide : (run3d4_leaves[0]!).S.reg 24 = .var 10)
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.var 10) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  have hne : m.reg 10 ≠ 0 := by
    intro h0
    have hv : (envB σ m).vars 10 = 0 := h0
    simp only [SBool.eval, Sym.eval, hv] at h1
    exact absurd h1 (by decide)
  change ∃ (mc : Machine) (L : List (Word × Nat)), Site3d0 σ L mc ∧ allocC.Post σ L mc m at hA
  obtain ⟨mc, L, ⟨o, k, kp', hED, hG, h27, r22, ha⟩, ⟨hret, hso, hcase⟩, -⟩ := hA
  have hc0 := hED.1
  have hlive := hED.2.2.2.2.1
  have hEL := hED.2.2.2.1
  have hn32 : o.done.length < 2 ^ 32 := by have := hEL.2.1; have := hEL.2.2.2.2.1; omega
  have hgc := grownCap_lt hn32
  have hge := grownCap_ge o.done.length
  have h11 : mc.reg 11 = w (entrySize * grownCap o.done.length) := ha.arg 1 (by simp)
  have h11n : (mc.reg 11).toNat = entrySize * grownCap o.done.length := by
    rw [h11]; simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  obtain ⟨p'', hp''⟩ : ∃ p, m.reg 10 = p := ⟨_, rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n, n = entrySize * grownCap o.done.length := ⟨_, rfl⟩
  rw [← hn'] at h11n
  rw [hp''] at hne hcase
  have hn'0 : 0 < n' := by simp only [hn', entrySize, grownCap]; omega
  obtain ⟨hheap, hram, hpr, -, -⟩ : σ.A.Heap (L ++ [(p'', n')]) m ∧ RamRange p'' n' ∧
      Present m p'' n' ∧ True ∧ True := by
    rcases hcase with ⟨h0, -⟩ | ⟨-, hh, hr', hp', -, -⟩
    · exact absurd h0 hne
    · rw [h11n] at hh hr' hp'; exact ⟨hh, hr', hp', trivial, trivial⟩
  -- the registers the call keeps
  have rk : ∀ i ∈ ([20, 21, 22, 23, 25, 26, 27] : List (Fin 32)), m'.reg i = mc.reg i :=
    fun i hi => (hr i (by simp at hi ⊢; omega)).trans (hret.2 i (by
      simp only [calleeSaved]; simp at hi ⊢; omega))
  have hso' : SameOutside (fun a => σ.A.Priv L a ∨ InRange (mc.reg 2 - 16) 16 a) mc m' :=
    fun a ha => by rw [hmem]; exact hso a ha
  have hcm' : Common σ m' := common_same hcm hmem fun i hi => hr i (by simp at hi ⊢; omega)
  have hheap' := heap_same hheap hmem
  have hlive' : Live σ m' (L ++ [(p'', n')]) (EX o ++ KD k kp' ++ [(p'', n')]) :=
    live_of_heap hpre hheap' (by
      have := hlive.2.1.append_right [(p'', n')]
      simpa using this) fun b hb => by
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at hb hlive ⊢
        rcases hb with hb | rfl
        · exact (hlive.2.2 b (by simpa using hb)).1
        · exact hn'0
  have hED' : EntryDone σ m' o k (L ++ [(p'', n')]) kp' [(p'', n')] :=
    ed_congr' hED hcm' hlive' (fun i hi => rk i (by simp at hi ⊢; omega))
      (edsame_of hpre hlive hso' fun a h => by
        rcases h with h | h
        · exact .inr (.inr (.inl h))
        · exact .inl (cframe_R hc0 h))
  have hG' : Growing σ m' o k kp' := growing_keep hG (fun i hi => rk i (by simp at hi ⊢; omega))
    fun j hj t ht => hso' _ fun h => by
      have hk : 8 ≤ j ∧ j ≤ 576 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      obtain ⟨n1, n2⟩ := frame_out hc0 hlive hk.1 hk.2 ht
      rcases h with h | h
      · exact n1 h
      · exact n2 h
  have hmm : ∀ a n, m.load a n = m'.load a n := fun a n =>
    load_congr (m := m') (m' := m) fun t _ => by rw [hmem]
  have e64 := frame_init hpre (m := m) (k := 0x200) (by decide) (by decide)
    ((hmm _ _).trans hG'.2.2.2.1)
  have e72 := frame_init hpre (m := m) (k := 0x1f8) (by decide) (by decide)
    ((hmm _ _).trans hG'.2.2.2.2.1)
  simp only [show 576 - 0x200 = 64 from rfl, show 576 - 0x1f8 = 72 from rfl] at e64 e72
  rw [show (Sym.bin BinOp.add (Sym.init 0 64 8) (Sym.init 0 72 8)).eval (envB σ m) =
    (Sym.init 0 64 8).eval (envB σ m) + (Sym.init 0 72 8).eval (envB σ m) from rfl, e64, e72,
    w_40] at r12
  have r10 : m'.reg 10 = p'' := (hr 10 (by simp)).trans hp''
  have e11 : m'.reg 11 = o.ep := r11.trans ((envB_var σ m 22).trans
    ((hr 22 (by simp)).symm.trans ((rk 22 (by simp)).trans r22)))
  have hlen : (m'.reg 12).toNat = entrySize * o.done.length := by
    rw [r12]; simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  have hsite : Site3fc σ m' := by
   subst hn'
   exact ⟨o, k, L ++ [(p'', _)], kp', p'',
    ⟨hED', hG', by rw [rk 22 (by simp)]; exact r22, (r24.trans (envB_var σ m 10)).trans hp'',
      Nat.pos_of_ne_zero fun h => hne (BitVec.eq_of_toNat_eq h),
      fun j hj => by rw [hmem]; exact hpr j hj⟩,
    by rw [rk 27 (by simp)]; exact h27,
    by simp only [Sym.eval] at r1; exact r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
      · exact r10
      · exact e11
      · exact r12⟩
  have hpre2 : MemcpyPre m' := memcpy_pre (by unfold RetAligned; simp only [Sym.eval] at r1; rw [r1]; decide)
    hcm'.2.2.2.2.2.2.2.2.2.2.2.2.1 fun h0 => by
      rw [hlen] at h0 ⊢
      have hec : 0 < o.ec.toNat := by rw [← hG.1]; simp only [entrySize] at h0; omega
      have hb : (o.ep, entrySize * o.ec.toNat) ∈ EX o ++ KD k kp' ++ [(p'', n')] := by
        simp [EX, hec]
      have hle : entrySize * o.done.length ≤ n' := by rw [hn']; exact Nat.mul_le_mul_left _ hge
      have hpe := live_present hlive' hb
      have hpn := live_present hlive' (b := (p'', n')) (by simp)
      have hre := hEL.2.2.2.2.2.1 hec
      rw [hG.1] at hle ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e11]; exact hre
      · rw [e11]; exact hpe
      · rw [r10]; unfold RamRange at hram ⊢; omega
      · rw [r10]; exact fun j hj => hpn j (by omega)
  refine ⟨memcpyC, (), rfl, hex, hpre2, fun m'' hpost => ⟨cut400, by simp [TX.plan, vcPlan],
    rfl, ?_, ⟨m', (), hsite, hpost⟩, ?_⟩⟩
  · rw [memcpy_eq hpost.1]; show (m'.reg 1 &&& ~~~(1 : Word)).toNat = _
    simp only [Sym.eval] at r1; rw [r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (memcpy_reg hpost.1 21).trans (hr 21 (by simp))
    have h26 : m''.reg 26 = m.reg 26 := (memcpy_reg hpost.1 26).trans (hr 26 (by simp))
    show 3 + bTail m'' 377 ≤ bTail m 389 - _
    rw [hsteps]; unfold bTail afterEntry; rw [h21, h26]; omega

/-! ## `0x80000400`: after `memcpy`, `free` of the old buffer -/

/-- The 16 bytes below `sp` are stack, apart from the allocator's memory. -/
theorem callee_frame {σ : Sig} {m : Machine} (hc : Common σ m) {L X : List (Word × Nat)}
    (hlive : Live σ m L X) : StackOk m 16 ∧ CalleeFrameFree (σ.A.Priv L) m := by
  have hpre := hc.2.1
  obtain ⟨hlo, hhi, h16, -⟩ := entry_nums hpre
  have hsp : (m.reg 2).toNat = σ.S.toNat - 576 := by
    rw [hc.2.2.2.1]; exact sl_toNat hpre (by decide)
  refine ⟨⟨by rw [hsp]; omega, by rw [hsp]; unfold Layout.ramLo at *; omega, by rw [hsp]; omega,
    fun j hj => ?_⟩, fun a h hp => stack_not_priv hpre (cframe_R hc h).1 (priv_sub hpre hlive hp)⟩
  rw [show m.reg 2 - BitVec.ofNat 64 16 = σ.sl 592 from sp_sub hc 16]
  exact stack_present' hc (k := 592) (j := j) (by omega) (by decide)

theorem shl5 {x : Word} (hx : x.toNat < 2 ^ 40) :
    x <<< ((5#64).toNat % 64) = w (32 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, show (5#64).toNat % 64 = 5 from rfl, Nat.shiftLeft_eq]
  simp only [w, BitVec.toNat_ofNat]
  omega

theorem shl3 {x : Word} (hx : x.toNat < 2 ^ 40) :
    x <<< ((3#64).toNat % 64) = w (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, show (3#64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq]
  simp only [w, BitVec.toNat_ofNat]
  omega

theorem shl40 {x : Word} (hx : x.toNat < 2 ^ 40) :
    x <<< ((5#64).toNat % 64) + x <<< ((3#64).toNat % 64) = w (entrySize * x.toNat) := by
  rw [shl5 hx, shl3 hx, w_40]

/-- `Allocated` on a machine with the same memory and the registers it reads. -/
theorem alloc_same {σ : Sig} {m m' : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    {kp' p'' : Word} (h : Allocated σ m o k L kp' p'') (hmem : m'.mem = m.mem)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (Fin 32)),
      m'.reg i = m.reg i) : Allocated σ m' o k L kp' p'' := by
  obtain ⟨hED, hG, r22, r24, hp0, hpres⟩ := h
  have hm : ∀ a, m'.mem a = m.mem a := fun a => by rw [hmem]
  refine ⟨ed_congr hED (common_same hED.1 hmem fun i hi => hr i (by simp at hi ⊢; omega))
      (heap_same hED.2.2.2.2.1.1 hmem) (fun i hi => hr i (by simp at hi ⊢; omega))
      ⟨fun t _ => hm _, fun _ _ t _ => hm _, fun _ _ t _ => hm _⟩,
    growing_keep hG (fun i hi => hr i (by simp at hi ⊢; omega)) (fun _ _ t _ => hm _),
    (hr 22 (by simp)).trans r22, (hr 24 (by simp)).trans r24, hp0,
    fun j hj => by rw [hm]; exact hpres j hj⟩

/-- After `memcpy` into the new block: `Copied`, `s11` still the old capacity. -/
theorem ret400_copied {σ : Sig} {m : Machine} (h : ARet memcpyC (unit Site3fc) σ m) :
    ∃ o k L kp' p'', Copied σ m o k L kp' p'' ∧ m.reg 27 = o.ec := by
  obtain ⟨hcm, -, -⟩ := ret_400 h
  obtain ⟨mc, _, ⟨o, k, L, kp', p'', ⟨hED, hG, r22, r24, hp0, hpres⟩, h27c, ha⟩, hmc, -⟩ := h
  have hpre := hcm.2.1
  have hreg := memcpy_reg hmc
  have hlive := hED.2.2.2.2.1
  have hEL := hED.2.2.2.1
  have hn32 : o.done.length < 2 ^ 32 := by have := hEL.2.1; have := hEL.2.2.2.2.1; omega
  have hgc := grownCap_lt hn32
  have hge := grownCap_ge o.done.length
  have h10 : mc.reg 10 = p'' := ha.arg 0 (by simp)
  have h11 : mc.reg 11 = o.ep := ha.arg 1 (by simp)
  have h12 : mc.reg 12 = w (entrySize * o.done.length) := ha.arg 2 (by simp)
  have hlen : (mc.reg 12).toNat = entrySize * o.done.length := by
    rw [h12]; simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  have hnb : (p'', entrySize * grownCap o.done.length) ∈
      EX o ++ KD k kp' ++ [(p'', entrySize * grownCap o.done.length)] := by simp
  have hramN := (hlive.2.2 _ hnb).2.1
  have hprivN := (hlive.2.2 _ hnb).2.2
  dsimp only at hramN hprivN
  have hdst : ∀ a, InRange (mc.reg 10) (mc.reg 12).toNat a →
      InRange p'' (entrySize * grownCap o.done.length) a := fun a h => by
    rw [h10, hlen] at h
    have : entrySize * o.done.length ≤ entrySize * grownCap o.done.length :=
      Nat.mul_le_mul_left _ hge
    simp only [InRange] at h ⊢; omega
  have hso : SameOutside (fun a => InRange p'' (entrySize * grownCap o.done.length) a ∨
      InRange scratch 8 a) mc m :=
    fun a ha' => memcpy_out hmc (fun h => ha' (.inl (hdst a h))) (fun h => ha' (.inr h))
  have hheap : σ.A.Heap L m := σ.A.heap_frame' L mc m hlive.1 (fun a ha' => hso a fun h =>
    h.elim (fun h => σ.A.priv_not_live L a ha' ⟨_, hlive.2.1.symm.subset
        (List.mem_append_right _ hnb), h⟩)
      (fun hs => owned_not_priv hpre (.inr (.inr (.inr hs))) (priv_sub hpre hlive ha')))
    (memcpy_preserved hmc)
  have hED' := ed_congr hED hcm hheap (fun i _ => hreg i)
    (edsame_of hpre hlive hso fun a h => h.elim
      (fun h => .inr (.inr (.inr ⟨(p'', entrySize * grownCap o.done.length),
        List.mem_singleton_self _, h⟩)))
      (fun h => .inr (.inl h)))
  have hG' := growing_keep hG (fun i _ => hreg i) fun j hj t ht => hso _ fun hs => by
    have hk : j ≤ 576 ∧ 8 ≤ j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
    have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
    have hst := sl_in_stack hpre (k := j) (n := 8) (by unfold stackBytes; omega) hk.2
      (in_self (by rw [h3]; omega) ht)
    rcases hs with hs | hs
    · exact stack_not_priv hpre hst (hprivN _ hs)
    · exact scratch_not_stack hpre hs hst
  refine ⟨o, k, L, kp', p'', ⟨⟨hED', hG', (hreg 22).trans r22, (hreg 24).trans r24, hp0,
    Present.of_preserved hpres (memcpy_preserved hmc)⟩, fun i hi => ?_⟩, (hreg 27).trans h27c⟩
  -- the copied bytes
  obtain ⟨-, hle', -, -, -, hram', hil, hbytes, hz⟩ := hEL
  have hl := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
  rw [hl] at hi
  have hec : 0 < o.ec.toNat := by rw [← hG.1]; simp only [entrySize] at hi; omega
  have hob : (o.ep, entrySize * o.ec.toNat) ∈ EX o ++ KD k kp' := by simp [EX, hec]
  have hramE := hram' hec
  have hap := live_apart hlive hob (List.mem_singleton_self _)
  have hpos : 0 < entrySize * grownCap o.done.length := by
    simp only [entrySize, grownCap]; omega
  have hlt : i < entrySize * o.ec.toNat := by rw [← hG.1]; exact hi
  unfold RamRange Layout.ramHi at hramN hramE
  have hsrc : ¬ InRange (BitVec.ofNat 64 Layout.extraParams) 8 (mc.reg 11 + BitVec.ofNat 64 i) := by
    rw [h11]; intro hs
    exact owned_not_priv hpre (.inr (.inr (.inr hs)))
      ((hlive.2.2 _ (List.mem_append_left _ hob)).2.2 _
        (in_self (by dsimp only; omega) hlt))
  have hne : mc.reg 10 ≠ mc.reg 11 := by
    rw [h10, h11]; intro he; rw [he] at hap; simp only at hap; omega
  have hdfit : (mc.reg 10).toNat + (mc.reg 12).toNat ≤ 2 ^ 64 := by
    rw [h10, hlen]; have := Nat.mul_le_mul_left entrySize hge; omega
  have hsfit : (mc.reg 11).toNat + (mc.reg 12).toNat ≤ 2 ^ 64 := by
    rw [h11, hlen, hG.1]; omega
  rw [← h10, memcpy_dst hmc (by rw [hlen]; exact hi) hne hdfit hsfit hsrc, h11]
  exact hbytes i (by rw [hl]; exact hi)

theorem TX.leaf_80000400_1 :
    LeafGoal TX.plan TX.plan.cuts[13]! ((TX.plan.leaves 0x80000400)[1]!) := by
  show LeafGoal TX.plan cut400 (run400_leaves[1]!)
  have hcs : (run400_leaves[1]!).conds = [SBool.ne (Sym.var 27) (Sym.lit 0)] := by decide
  have hsteps : (run400_leaves[1]!).S.steps - cut400.S.steps = 11 := by decide
  intro σ m hA hc
  obtain ⟨hcm, -, hsp⟩ := ret_400 hA
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run400_leaves[1]!).exit = .call 0x80041f38 0x8000042c := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x80041f38 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SSpill) m m' at hfr
  obtain ⟨-, hm, -⟩ := spill_cut hcm hsp
  have hmem := mem_same_nowrite hcm rfl hm' (by decide) (by decide) hfr
  have hS : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (Fin 32)),
      (run400_leaves[1]!).S.reg i.val = SSpill.reg i.val := by decide
  have hr := regs_keep hm hm' _ hS
  have reg : ∀ (i : Fin 32) (s : Sym), (run400_leaves[1]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run400_leaves[1]!).S.reg 1 = .lit 0x8000042c)
  have r10 := reg 10 _ (by decide : (run400_leaves[1]!).S.reg 10 = .init 0 40 8)
  have r11 := reg 11 _ (by decide : (run400_leaves[1]!).S.reg 11 = .var 22)
  have r12 := reg 12 _ (by decide : (run400_leaves[1]!).S.reg 12 =
    .bin .add (.bin .sll (.var 27) (.lit 5)) (.bin .sll (.var 27) (.lit 3)))
  have r13 := reg 13 _ (by decide : (run400_leaves[1]!).S.reg 13 = .lit 3)
  have r14 := reg 14 _ (by decide : (run400_leaves[1]!).S.reg 14 = .var 19)
  have h1 : SBool.eval (envB σ m) (SBool.ne (Sym.var 27) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; exact List.mem_singleton.mpr rfl)
  obtain ⟨o, k, L, kp', p'', ⟨hAl, hcopy⟩, h27⟩ := ret400_copied hA
  have hAl' := alloc_same hAl hmem hr
  have hcopy' : BytesAt m' p'' (entriesBytes o.done o.is) := fun i hi => by
    rw [hmem]; exact hcopy i hi
  have hED := hAl.1
  have hEL := hED.2.2.2.1
  have hlive := hED.2.2.2.2.1
  have hec : 0 < o.ec.toNat := by
    rcases Nat.eq_zero_or_pos o.ec.toNat with h0 | h0
    · exfalso
      have hv : (envB σ m).vars 27 = 0 := h27.trans (BitVec.eq_of_toNat_eq (by simpa using h0))
      simp only [SBool.eval, Sym.eval, hv] at h1
      exact absurd h1 (by decide)
    · exact h0
  have hc32 := hEL.2.2.2.2.1
  have e10 : m'.reg 10 = wordAt σ.m σ.ao := by
    rw [r10]; exact frame_init hpre (k := 0x218) (by decide) (by decide) hAl.2.1.2.2.2.2.2.2.2.1
  have e11 : m'.reg 11 = o.ep :=
    r11.trans ((envB_var σ m 22).trans hAl.2.2.1)
  have e12 : m'.reg 12 = w (entrySize * o.ec.toNat) := by
    rw [r12, ← shl40 (x := o.ec) (by omega), ← h27]; rfl
  have e19 : m'.reg 14 = σ.m.reg 1 := r14.trans ((envB_var σ m 19).trans hcm.2.2.2.2.2.2.2.1)
  have hn12 : (m'.reg 12).toNat = entrySize * o.ec.toNat := by
    rw [e12]; simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  have hcm' : Common σ m' := hAl'.1.1
  have hlive' := hAl'.1.2.2.2.2.1
  have hsite : Site428 σ L m' := ⟨o, k, kp', p'', ⟨hAl', hcopy'⟩, hec,
    by simp only [Sym.eval] at r1; exact r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
      · exact e10
      · exact e11
      · exact e12
      · simp only [Sym.eval] at r13; exact r13
      · exact e19⟩
  obtain ⟨hstk, hcf⟩ := callee_frame hcm' hlive'
  have hpre2 : freePre σ.A L m' := ⟨hlive'.1, by
      rw [e11, hn12]; exact hlive'.2.1.symm.subset (List.mem_append_right _ (by simp [EX, hec])),
    by rw [hn12]; simp only [entrySize]; omega, by rw [hn12]; simp only [entrySize]; omega,
    by simp only [Sym.eval] at r13; rw [r13]; decide, hstk,
    by unfold RetAligned; simp only [Sym.eval] at r1; rw [r1]; decide, hcf⟩
  refine ⟨freeC, L, rfl, hex, hpre2, fun m'' hpost => ⟨cut42c, by simp [TX.plan, vcPlan],
    rfl, ?_, .inr ⟨m', L, hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1]; simp only [Sym.eval] at r1; rw [r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by simp))
    have h26 : m''.reg 26 = m.reg 26 := (hpost.1.1.2 26 (by decide)).trans (hr 26 (by simp))
    show 42 + bTail m'' 324 ≤ bTail m 377 - _
    rw [hsteps]; unfold bTail afterEntry; rw [h21, h26]; omega

/-! ## The grown list before its header is written -/

/-- `EList` without the header at `S-0x1c0`. -/
def ELNoHdr (σ : Sig) (m : Machine) (o : Obs) : Prop :=
  o.done.length ≤ o.ec.toNat ∧ 0 < o.ep.toNat ∧
  (o.ec.toNat = 0 → o.ep = 8) ∧ o.ec.toNat < 2 ^ 32 ∧
  (0 < o.ec.toNat → RamRange o.ep (entrySize * o.ec.toNat)) ∧
  o.is.length = o.done.length ∧ BytesAt m o.ep (entriesBytes o.done o.is) ∧
  ∀ x ∈ List.zip o.done o.is, x.2.padding.length = 4 ∧ x.1.address.length = 20 ∧
    (∀ y ∈ x.1.keys, y.length = keySize) ∧
    (x.1.keys ≠ [] → RamRange x.2.keysPtr (keySize * x.1.keys.length)) ∧
    BytesAt m x.2.keysPtr x.1.keys.flatten

/-- `EntryDone` without the entries header and copy B, with live blocks `X` besides TX's. -/
def Grown (σ : Sig) (m : Machine) (o : Obs) (k : Kobs) (L : List (Word × Nat)) (kp' : Word)
    (X : List (Word × Nat)) : Prop :=
  Common σ m ∧ OuterOk σ m o ∧ OuterRegs σ m o ∧ ELNoHdr σ m o ∧
  Live σ m L (EX o ++ KD k kp' ++ X) ∧ EntryOk σ m o k ∧ AddrOk σ m o k ∧ KeysListOk σ o k ∧
  KeysWalked (kpl σ o k) k.kl k.keys ∧
  (k.keys ≠ [] → RamRange kp' (keySize * k.keys.length)) ∧ BytesAt m kp' k.keys.flatten ∧
  (∀ y ∈ k.keys, y.length = keySize)

theorem live_perm {σ : Sig} {m : Machine} {L X X' : List (Word × Nat)} (h : Live σ m L X)
    (hp : X.Perm X') : Live σ m L X' :=
  ⟨h.1, h.2.1.trans (List.Perm.append_left _ hp), fun b hb => h.2.2 b (hp.symm.subset hb)⟩

/-- `OuterOk` on a machine that keeps `rest`'s bytes. -/
theorem outer_bytes {σ : Sig} {mc m : Machine} {o : Obs} (hok : OuterOk σ mc o)
    (hrest : ∀ t < 16, m.mem (σ.rest + BitVec.ofNat 64 t) = mc.mem (σ.rest + BitVec.ofNat 64 t)) :
    OuterOk σ m o := by
  refine ⟨hok.1, hok.2.1, ?_, ?_, hok.2.2.2.2⟩
  · rw [load_congr fun t ht => hrest t (by omega)]; exact hok.2.2.1
  · rw [load_congr (m := mc) fun t ht => by
      rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact hrest _ (by omega)]
    exact hok.2.2.2.1

/-- `ELNoHdr` on a machine that keeps the bytes of TX's blocks. -/
theorem elnohdr_keep {σ : Sig} {mc m : Machine} {o : Obs} (h : ELNoHdr σ mc o)
    (hblk : ∀ b ∈ EX o, ∀ t < b.2,
      m.mem (b.1 + BitVec.ofNat 64 t) = mc.mem (b.1 + BitVec.ofNat 64 t)) : ELNoHdr σ m o := by
  obtain ⟨hle', hp0, hc0, hc32, hram', hil, hbytes, hz⟩ := h
  refine ⟨hle', hp0, hc0, hc32, hram', hil, ?_, fun x hx => ?_⟩
  · rcases Nat.eq_zero_or_pos o.ec.toNat with he | he
    · have : o.done = [] := List.eq_nil_of_length_eq_zero (by omega)
      have : o.is = [] := List.eq_nil_of_length_eq_zero (by rw [hil, this]; rfl)
      intro i hi; simp [entriesBytes, *] at hi
    · have hlen := entriesBytes_length o.done o.is hil fun x hx => ⟨(hz x hx).1, (hz x hx).2.1⟩
      refine bytes_congr hbytes fun t ht => hblk (o.ep, entrySize * o.ec.toNat)
        (by simp [EX, he]) t ?_
      rw [hlen] at ht
      exact Nat.lt_of_lt_of_le ht (Nat.mul_le_mul_left _ hle')
  · obtain ⟨hpad, haddr, hkl', hkram, hkb'⟩ := hz x hx
    refine ⟨hpad, haddr, hkl', hkram, ?_⟩
    by_cases hk : x.1.keys = []
    · rw [hk]; intro i hi; simp at hi
    · exact bytes_congr hkb' fun t ht => hblk _ (by
        simp only [EX, List.mem_append]; exact .inr (mem_keysBlocks hx hk)) t
        (by rw [flatten_length _ hkl'] at ht; exact ht)

/-- `Grown` carries over to a machine that keeps its bytes and registers. -/
theorem grown_keep {σ : Sig} {mc m : Machine} {o : Obs} {k : Kobs}
    {L X L' X' : List (Word × Nat)} {kp' : Word} (h : Grown σ mc o k L kp' X) (hcm : Common σ m)
    (hl : Live σ m L' (EX o ++ KD k kp' ++ X'))
    (hr : ∀ i ∈ ([20, 21, 26] : List (Fin 32)), m.reg i = mc.reg i)
    (hrest : ∀ t < 16, m.mem (σ.rest + BitVec.ofNat 64 t) = mc.mem (σ.rest + BitVec.ofNat 64 t))
    (hslot : ∀ kn ∈ ([(0x1f0, 8), (0x158, 20)] : List (Nat × Nat)), ∀ t < kn.2,
      m.mem (σ.sl kn.1 + BitVec.ofNat 64 t) = mc.mem (σ.sl kn.1 + BitVec.ofNat 64 t))
    (hblk : ∀ b ∈ EX o ++ KD k kp', ∀ t < b.2,
      m.mem (b.1 + BitVec.ofNat 64 t) = mc.mem (b.1 + BitVec.ofNat 64 t)) :
    Grown σ m o k L' kp' X' := by
  obtain ⟨-, hok, ⟨r20, r21, hi, hmag⟩, hEL, -, ⟨hd, hle, r26⟩, ⟨had, hal, hA⟩, hkl, hkw,
    hram, hkb, hkeys⟩ := h
  have l0 := hslot (0x1f0, 8) (by simp)
  have l2 := hslot (0x158, 20) (by simp)
  have h20 : ∀ t < (itemPayload (ent σ o k) k.ah 20).length, t < 20 := fun t ht => by
    simp only [itemPayload, List.length_take] at ht; omega
  refine ⟨hcm, outer_bytes hok hrest,
    ⟨(hr 20 (by decide)).trans r20, (hr 21 (by decide)).trans r21, hi,
      (load_congr fun t ht => l0 t ht).trans hmag⟩,
    elnohdr_keep hEL fun b hb => hblk b (List.mem_append_left _ hb),
    hl, ⟨hd, hle, (hr 26 (by decide)).trans r26⟩,
    ⟨had, hal, bytes_congr hA fun t ht => l2 t (h20 t ht)⟩, hkl, hkw, hram, ?_, hkeys⟩
  by_cases hk : k.keys = []
  · rw [hk]; intro i hi; simp at hi
  · exact bytes_congr hkb fun t ht => hblk (kp', keySize * k.keys.length)
      (by simp [KD, hk]) t (by rw [flatten_length _ hkeys] at ht; exact ht)

/-- The grown list `{p'', c'}` once the old entries are copied; the old buffer (if any) is
still live. -/
theorem grown_of_copied {σ : Sig} {m : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)}
    {kp' p'' : Word} (h : Copied σ m o k L kp' p'') :
    Grown σ m { o with ep := p'', ec := w (grownCap o.done.length) } k L kp'
      (if 0 < o.ec.toNat then [(o.ep, entrySize * o.ec.toNat)] else []) := by
  obtain ⟨⟨hED, hG, -, -, hp0, -⟩, hcopy⟩ := h
  obtain ⟨hc, hok, hOR, hEL, hlive, hEO, hAO, hKLO, hkw, hram, hkb, hkeys, -⟩ := hED
  obtain ⟨-, hle', -, -, hc32, -, hil, -, hz⟩ := hEL
  have hn32 : o.done.length < 2 ^ 32 := by omega
  have hgc := grownCap_lt hn32
  have hge := grownCap_ge o.done.length
  have hcn : (w (grownCap o.done.length)).toNat = grownCap o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have hpos : 0 < grownCap o.done.length := by unfold grownCap; omega
  have hnb : (p'', entrySize * grownCap o.done.length) ∈
      EX o ++ KD k kp' ++ [(p'', entrySize * grownCap o.done.length)] := by simp
  have hramN := (hlive.2.2 _ hnb).2.1
  dsimp only at hramN
  have hEX : EX { o with ep := p'', ec := w (grownCap o.done.length) } =
      [(p'', entrySize * grownCap o.done.length)] ++ keysBlocks o.done o.is := by
    simp only [EX, hcn, if_pos hpos]
  have hEXo : EX o = (if 0 < o.ec.toNat then [(o.ep, entrySize * o.ec.toNat)] else []) ++
      keysBlocks o.done o.is := rfl
  refine ⟨hc, hok, hOR, ⟨by rw [hcn]; exact hge, hp0, fun h0 => by rw [hcn] at h0; omega, ?_,
    fun _ => by rw [hcn]; exact hramN, hil, hcopy, hz⟩, live_perm hlive ?_, hEO, hAO, hKLO, hkw,
    hram, hkb, hkeys⟩
  · rw [hcn]; unfold RamRange Layout.ramHi at hramN; simp only [entrySize] at hramN; omega
  · rw [hEX, hEXo, List.perm_iff_count]; intro a; simp only [List.count_append]; omega

/-- Freeing a live block `a` of `L ~ g.L ++ (Y ++ [a])` leaves `g.L ++ Y`. -/
theorem erase_perm {σ : Sig} {m : Machine} {L Y : List (Word × Nat)} {a : Word × Nat}
    (hlive : Live σ m L (Y ++ [a])) (ha : 0 < a.2) : (L.erase a).Perm (σ.g.L ++ Y) := by
  have hpw := (σ.A.live_ok L m hlive.1).1
  rw [hlive.2.1.pairwise_iff (fun h => h.symm),
    show σ.g.L ++ (Y ++ [a]) = (σ.g.L ++ Y) ++ [a] by simp, List.pairwise_append] at hpw
  have hnot : a ∉ σ.g.L ++ Y := fun hin => by
    have := hpw.2.2 a hin a (List.mem_singleton_self _); omega
  refine (hlive.2.1.erase a).trans ?_
  rw [show σ.g.L ++ (Y ++ [a]) = (σ.g.L ++ Y) ++ [a] by simp, List.erase_append_right _ hnot]
  simp

/-- At `0x8000042c`: the grown list is in place but its header is the old one. -/
theorem at42c {σ : Sig} {m : Machine} (h : A42c σ m) :
    ∃ o k L kp' p'', Grown σ m { o with ep := p'', ec := w (grownCap o.done.length) } k L kp' [] ∧
      Growing σ m o k kp' ∧ m.reg 24 = p'' ∧
      BytesAt m (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20) := by
  have hcm := A42c_common h
  rcases h with ⟨-, o, k, L, kp', p'', hcop, hec⟩ | h
  · have hG := grown_of_copied hcop
    rw [if_neg (by omega)] at hG
    exact ⟨o, k, L, kp', p'', hG, hcop.1.2.1, hcop.1.2.2.2.1,
      hcop.1.1.2.2.2.2.2.2.2.2.2.2.2.2⟩
  change ∃ (mc : Machine) (L : List (Word × Nat)), Site428 σ L mc ∧ freeC.Post σ L mc m at h
  obtain ⟨mc, L, ⟨o, k, kp', p'', hcop, hec, ha⟩, ⟨hret, hso, hheap, -⟩, -⟩ := h
  have G := grown_of_copied hcop
  rw [if_pos hec] at G
  have hc0 := hcop.1.1.1
  have hpre := hc0.2.1
  have hEL := hcop.1.1.2.2.2.1
  have hlive := G.2.2.2.2.1
  have h11 : mc.reg 11 = o.ep := ha.arg 1 (by simp)
  have h12' : mc.reg 12 = w (entrySize * o.ec.toNat) := ha.arg 2 (by simp)
  have h12 : (mc.reg 12).toNat = entrySize * o.ec.toNat := by
    rw [h12']; have := hEL.2.2.2.2.1; simp only [w, BitVec.toNat_ofNat, entrySize] at *; omega
  rw [h11, h12] at hso hheap
  have hpos : 0 < entrySize * o.ec.toNat := by simp only [entrySize]; omega
  have hY : ∀ a, InRange o.ep (entrySize * o.ec.toNat) a → σ.A.Priv σ.g.L a := fun a h =>
    (hlive.2.2 _ (List.mem_append_right _ (List.mem_singleton_self _))).2.2 a h
  have hs := edsame_of hpre hlive hso fun a h => by
    rcases h with h | h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨_, List.mem_singleton_self _, h⟩))
    · exact .inl (cframe_R hc0 h)
  have hl : Live σ m (L.erase (o.ep, entrySize * o.ec.toNat))
      (EX { o with ep := p'', ec := w (grownCap o.done.length) } ++ KD k kp' ++ []) :=
    live_of_heap hpre hheap (by simpa using erase_perm hlive hpos) fun b hb =>
      (hlive.2.2 b (List.mem_append_left _ (by simpa using hb))).1
  have rk : ∀ i ∈ ([20, 21, 23, 24, 25, 26] : List (Fin 32)), m.reg i = mc.reg i :=
    fun i hi => hret.2 i (by simp only [calleeSaved]; simp at hi ⊢; omega)
  refine ⟨o, k, L.erase (o.ep, entrySize * o.ec.toNat), kp', p'',
    grown_keep G hcm hl (fun i hi => rk i (by simp at hi ⊢; omega)) hs.rest
      (fun kn hkn => hs.slot kn (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
        rcases hkn with rfl | rfl <;> simp)) hs.blk,
    growing_keep hcop.1.2.1 (fun i hi => rk i (by simp at hi ⊢; omega)) fun j hj t ht =>
      hso _ fun h => ?_, (rk 24 (by simp)).trans hcop.1.2.2.2.1,
    bytes_congr hcop.1.1.2.2.2.2.2.2.2.2.2.2.2.2 fun t ht => hs.slot (0xa0, 20) (by simp) t (by
      simp only [itemPayload, List.length_take] at ht; omega)⟩
  have hk : 8 ≤ j ∧ j ≤ 576 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨n1, n2⟩ := frame_out hc0 hcop.1.1.2.2.2.2.1 hk.1 hk.2 ht
  rcases h with h | h | h
  · exact n1 h
  · have h3 := sl_toNat hpre (k := j) (by unfold stackBytes; omega)
    have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
    exact stack_not_priv hpre (sl_in_stack hpre (k := j) (n := 8) (by unfold stackBytes; omega)
      hk.1 (in_self (by rw [h3]; omega) ht)) (hY _ h)
  · exact n2 h

/-! ## Leaves that write frame words -/

/-- A leaf over the base regions whose writes are frame words changes only those words. -/
theorem frame_leaf_so {σ : Sig} {m m' : Machine} {S S' : SState} (hc : Common σ m)
    (hS : S.regions = baseRegions) (hm' : Match (envB σ m) S' m')
    (hS' : S'.regions = baseRegions) (hfr : SameOutside (InWritable (envB σ m) S) m m')
    (hall : S'.mem.all (fun w => w.r == 0) = true) :
    SameOutside (fun a => ∃ wr ∈ S'.mem, InRange (σ.sl 576 + w wr.off) wr.n a) m m' := by
  have hpre := hc.2.1
  have h576 := sl_toNat hpre (k := 576) (by decide)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  intro a ha
  by_cases hw : InWritable (envB σ m) S a
  · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
    have hr5 : r < 5 := by
      have := (List.getElem?_eq_some_iff.mp hR).1; rw [hS] at this
      simpa [baseRegions] using this
    refine byte_keep hm' (by rw [hS']; simpa [baseRegions] using hr5) hj (fun wr hwr => ?_)
      (mem0_entry (common_present hc r j hr5 hj))
    have h0 := List.all_eq_true.mp hall wr hwr
    simp only [beq_iff_eq] at h0
    cases hcv : wr.covers r j
    · rfl
    · exfalso
      simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcv
      obtain ⟨⟨hr0, h1⟩, h2⟩ := hcv
      rw [h0] at hr0; subst hr0
      have hb : (envB σ m).base 0 = σ.sl 576 := rfl
      have hs : (envB σ m).size 0 = 576 := rfl
      rw [hs] at hj
      apply ha
      refine ⟨wr, hwr, ?_⟩
      rw [hb]
      simp only [InRange, w]
      rw [toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
      omega
  · exact hfr a hw

/-- A frame range inside another. -/
theorem fr_in {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {off n k n' : Nat} {a : Word} (hk : k ≤ 576)
    (h1 : 576 - k ≤ off) (h2 : off + n ≤ 576 - k + n') (ho : off ≤ 576)
    (h : InRange (σ.sl 576 + w off) n a) :
    InRange (σ.sl k) n' a := by
  have h576 := sl_toNat hpre (k := 576) (by decide)
  have hk' := sl_toNat hpre (k := k) (by unfold stackBytes; omega)
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  have hhi := (entry_nums hpre).2.1; unfold Layout.ramHi at hhi
  simp only [InRange, w] at h ⊢
  rw [toNat_add_ofNat (by omega)] at h
  rw [hk']; omega

/-- `rest`'s bytes survive a change of `Rcls` bytes only. -/
theorem rest_bytes {σ : Sig} {mc m : Machine} (hpre : Pre σ.A σ.g σ.m) {R : Word → Prop}
    (hso : SameOutside R mc m) (hR : ∀ a, R a → Rcls σ a) :
    ∀ t < 16, m.mem (σ.rest + BitVec.ofNat 64 t) = mc.mem (σ.rest + BitVec.ofNat 64 t) := by
  have hfit := pre_fit hpre ((σ.rest, 16), restR) (by simp [shapeFull])
  have h2 := sl_toNat hpre (k := stackBytes) (Nat.le_refl _)
  have d9 : Apart (σ.sl stackBytes) stackBytes σ.rest 16 :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have d33 : Apart scratch 8 σ.rest 16 :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at d9 d33
  intro t ht
  refine hso _ fun hr => ?_
  have hin : InRange σ.rest 16 (σ.rest + BitVec.ofNat 64 t) := by
    simp only [InRange]; rw [toNat_add_ofNat (by simp at hfit; omega)]; omega
  rcases hR _ hr with h | h | h
  · simp only [InRange] at h hin
    rw [h2] at h d9; omega
  · simp only [InRange] at h hin
    simp only [scratch, Layout.extraParams, BitVec.toNat_ofNat] at h d33; omega
  · exact owned_not_priv hpre (.inr (.inl hin)) h

/-- `AEntryStore` from the grown list, its new header and the store's registers. -/
theorem aes_of {σ : Sig} {m : Machine} {o : Obs} {k : Kobs} {L : List (Word × Nat)} {kp' : Word}
    (hpc : m.pc.toNat = c460) (h : Grown σ m o k L kp' []) (hC : Consts m)
    (hH : F1.HeaderIs m (σ.sl 0x1c0) o.ep (w (o.done.length + 1)) o.ec)
    (hroom : o.done.length + 1 ≤ o.ec.toNat)
    (hB : BytesAt m (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20))
    (h10 : m.reg 10 = o.ep + w (entrySize * o.done.length)) (h14 : m.reg 14 = kp')
    (h15 : m.reg 15 = w k.keys.length) : AEntryStore σ m := by
  obtain ⟨hc, hok, hOR, hEL, hlive, hEO, hAO, hKLO, hkw, hram, hkb, hkeys⟩ := h
  rw [List.append_nil] at hlive
  exact ⟨hpc, o, k, L, kp', hc, hok, hOR, hC, ⟨hH, hEL⟩, hroom, hlive, hEO, hAO, hKLO, hkw,
    hram, hkb, hkeys, hB, h10, h14, h15⟩

/-! ## `0x8000042c`: the grown list's header, to the entry store -/

theorem TX.leaf_8000042c_0 :
    LeafGoal TX.plan TX.plan.cuts[14]! ((TX.plan.leaves 0x8000042c)[0]!) := by
  show LeafGoal TX.plan cut42c (run42c_leaves[0]!)
  have hsteps : (run42c_leaves[0]!).S.steps - cut42c.S.steps = 13 := by decide
  intro σ m hA _
  have hcm := A42c_common hA
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run42c_leaves[0]!).exit = .at 0x80000460 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x80000460 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  obtain ⟨hwf, hm, -⟩ := body_cut hcm
  obtain ⟨o, k, L, kp', p'', G, hG, r24, hB⟩ := at42c hA
  have hS : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 23, 26] : List (Fin 32)),
      (run42c_leaves[0]!).S.reg i.val = SBody.reg i.val := by decide
  have hr := regs_keep hm hm' _ hS
  have reg : ∀ (i : Fin 32) (s : Sym), (run42c_leaves[0]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r10 := reg 10 _ (by decide : (run42c_leaves[0]!).S.reg 10 =
    .bin .add (.var 24) (.bin .add (.init 0 64 8) (.init 0 72 8)))
  have r14 := reg 14 _ (by decide : (run42c_leaves[0]!).S.reg 14 = .init 0 56 8)
  have r15 := reg 15 _ (by decide : (run42c_leaves[0]!).S.reg 15 = .init 0 48 8)
  have c24 := reg 24 _ (by decide : (run42c_leaves[0]!).S.reg 24 = .lit 20)
  have c25 := reg 25 _ (by decide : (run42c_leaves[0]!).S.reg 25 = .lit 1)
  have c27 := reg 27 _ (by decide : (run42c_leaves[0]!).S.reg 27 = .lit 32)
  have hlive := G.2.2.2.2.1
  obtain ⟨hc', hlive', -⟩ := base_leaf hcm hlive (BaseEnv.ofB σ m) hwf rfl hm' (by decide) hfr
    (by decide) fun i hi => hr i (by simp at hi ⊢; omega)
  have hso := frame_leaf_so hcm rfl hm' (by decide) hfr (by decide)
  have hmem : (run42c_leaves[0]!).S.mem =
      [⟨0, 136, 8, .var 23⟩, ⟨0, 144, 8, .var 25⟩, ⟨0, 128, 8, .var 24⟩] := by decide
  have hW : ∀ a, (∃ wr ∈ (run42c_leaves[0]!).S.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      InRange (σ.sl 0x1c0) 24 a := by
    rintro a ⟨wr, hwr, hin⟩
    rw [hmem] at hwr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwr
    rcases hwr with rfl | rfl | rfl <;>
      exact fr_in hpre (by decide) (by decide) (by decide) (by decide) hin
  have hst : ∀ a, InRange (σ.sl 0x1c0) 24 a → InRange (σ.sl stackBytes) stackBytes a :=
    fun a h => sl_in_stack hpre (by decide) (by decide) h
  have G' := grown_keep G hc' hlive' (fun i hi => hr i (by simp at hi ⊢; omega))
    (rest_bytes hpre hso fun a h => .inl (hst a (hW a h)))
    (fun kn hkn t ht => hso _ fun h => by
      have hW' := hW _ h
      have h3 := sl_toNat hpre (k := kn.1) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
        rcases hkn with rfl | rfl <;> decide)
      have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
      rcases hkn with rfl | rfl <;>
        exact sl_apart hpre (by decide) (by decide) (by decide)
          (in_self (by dsimp only at h3 ⊢; rw [h3]; omega) ht) hW')
    (fun b hb t ht => hso _ fun h => by
      have hP := (hlive.2.2 b (List.mem_append_left _ hb))
      have hram := hP.2.1
      unfold RamRange Layout.ramHi at hram
      exact stack_not_priv hpre (hst _ (hW _ h)) (hP.2.2 _ (in_self (by omega) ht)))
  have hwf' : Env.WF (envB σ m) (run42c_leaves[0]!).S := hwf.congr (by decide)
  have fw := fun kk hk hk' => frame_word (BaseEnv.ofB σ m) hwf' hm' (by decide) (k := kk) hk hk'
  have f0 := fw 0x1c0 (by decide) (by decide)
  have f8 := fw 0x1b8 (by decide) (by decide)
  have f16 := fw 0x1b0 (by decide) (by decide)
  have v23 : (Sym.var 23).eval (envB σ m) = m.reg 23 := envB_var σ m 23
  have v24 : (Sym.var 24).eval (envB σ m) = m.reg 24 := envB_var σ m 24
  have v25 : (Sym.var 25).eval (envB σ m) = m.reg 25 := envB_var σ m 25
  rw [show readConst (run42c_leaves[0]!).S 0 (576 - 0x1c0) 8 = .var 24 by decide, v24, r24] at f0
  rw [show readConst (run42c_leaves[0]!).S 0 (576 - 0x1b8) 8 = .var 23 by decide, v23,
    hG.2.1] at f8
  rw [show readConst (run42c_leaves[0]!).S 0 (576 - 0x1b0) 8 = .var 25 by decide, v25,
    hG.2.2.1] at f16
  have hEL := G.2.2.2.1
  have hn32 : o.done.length < 2 ^ 32 := by
    have h1 := hEL.1; have h2 := hEL.2.2.2.1; dsimp only at h1 h2; omega
  have hgc := grownCap_lt hn32
  have hcn : (w (grownCap o.done.length)).toNat = grownCap o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have e64 := frame_init hpre (m := m) (k := 0x200) (by decide) (by decide) hG.2.2.2.1
  have e72 := frame_init hpre (m := m) (k := 0x1f8) (by decide) (by decide) hG.2.2.2.2.1
  have e56 := frame_init hpre (m := m) (k := 0x208) (by decide) (by decide) hG.2.2.2.2.2.2.1
  have e48 := frame_init hpre (m := m) (k := 0x210) (by decide) (by decide) hG.2.2.2.2.2.1
  simp only [show 576 - 0x200 = 64 from rfl, show 576 - 0x1f8 = 72 from rfl,
    show 576 - 0x208 = 56 from rfl, show 576 - 0x210 = 48 from rfl] at e64 e72 e56 e48
  have hB' : BytesAt m' (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20) := by
    have h3 := sl_toNat hpre (k := 0xa0) (by decide)
    have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
    refine bytes_congr hB fun t ht => hso _ fun h => sl_apart hpre (k1 := 0xa0) (n1 := 20)
      (by decide) (by decide) (by decide) (in_self (by rw [h3]; omega) ?_) (hW _ h)
    simp only [itemPayload, List.length_take] at ht; omega
  refine ExitGoal.at_cut rfl ⟨cut460, by simp [TX.plan, vcPlan], hex, aes_of hex G'
    ⟨by simp only [Sym.eval] at c24; exact c24, by simp only [Sym.eval] at c25; exact c25,
      by simp only [Sym.eval] at c27; exact c27⟩
    ⟨f0, by rw [show σ.sl 0x1c0 + 8 = σ.sl 0x1b8 by simp only [Sig.sl, w]; bv_omega]; exact f8,
      by rw [show σ.sl 0x1c0 + 16 = σ.sl 0x1b0 by simp only [Sig.sl, w]; bv_omega]; exact f16⟩
    (by dsimp only; rw [hcn]; unfold grownCap; omega)
    hB' ?_ (r14.trans e56) (r15.trans e48), ?_⟩
  · rw [r10]
    show m.reg 24 + ((Sym.init 0 64 8).eval (envB σ m) + (Sym.init 0 72 8).eval (envB σ m)) = _
    rw [e64, e72, w_40, r24]
  · show bTail m' 311 ≤ bTail m 324 - _
    rw [hsteps]; unfold bTail afterEntry; rw [hr 21 (by simp), hr 26 (by simp)]; omega

/-! ## `0x8000025c`: after `toOwnedSlice` of the keys -/

/-- A stack range of `n` bytes at `S - k` that misses `EntryDone`'s slots. -/
theorem slots_free {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k n : Nat} {a : Word} (hk : k ≤ 704)
    (hn : n ≤ k)
    (hd : ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20)] : List (Nat × Nat)),
      k + kn.2 ≤ kn.1 ∨ kn.1 + n ≤ k) (h : InRange (σ.sl k) n a) :
    InRange (σ.sl stackBytes) stackBytes a ∧
      ∀ kn ∈ ([(0x1f0, 8), (0x1c0, 24), (0x158, 20), (0xa0, 20)] : List (Nat × Nat)),
        ¬ InRange (σ.sl kn.1) kn.2 a :=
  ⟨sl_in_stack hpre hk hn h, fun kn hkn hin => sl_apart hpre hk (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
    rcases hkn with rfl | rfl | rfl | rfl <;> decide) (hd kn hkn) h hin⟩

/-- After `toOwnedSlice` of the keys without error: the finished entry's keys slice
`{kp', |keys|}` in the result slot `S-0xb8`, the entries list as before. -/
theorem ret25c {σ : Sig} {m : Machine} (h : ARet f4C Site258 σ m)
    (he : (Sym.init 0 408 2).eval (envB σ m) = 0) :
    ∃ o k L kp', Grown σ m o k L kp' [] ∧
      F1.HeaderIs m (σ.sl 0x1c0) o.ep (w o.done.length) o.ec ∧
      m.load (σ.sl 0xb8) 8 = some kp' ∧ m.load (σ.sl 0xb0) 8 = some (w k.keys.length) ∧
      m.reg 27 = 32 := by
  have hcm := (ret_25c h).1
  have hpre := hcm.2.1
  obtain ⟨mc, x, ⟨o, k, hIE, hx, hkw, hKL, ha⟩, hpost, -⟩ := h
  rcases x with ⟨L, items⟩
  have hx' : items = k.keys.flatten := hx
  subst hx'
  have hIE : InEntry σ mc o k L := hIE
  obtain ⟨hret, hso, hcase⟩ : ToOwned.Post F4.elemBytes σ.A L k.keys.flatten F4.emptyPtr mc m :=
    hpost
  obtain ⟨hc0, hok, ⟨r20, r21, hi, hmag⟩, hEL, hlive, ⟨hd, hle, r26⟩, hAO, hKLO, r27⟩ := hIE
  obtain ⟨⟨hH0, hH8, hH16⟩, hkle, -, -, hkc32, -, hlens, -⟩ := hKL
  have hres : mc.reg 10 = σ.sl 0xb8 := ha.arg 0 (by simp)
  have hhdr : mc.reg 11 = σ.sl 0x118 := ha.arg 1 (by simp)
  simp only [ToOwned.listPtr, ToOwned.listLen, ToOwned.listCap, hhdr, hres, f4w hH0, f4w hH8,
    f4w hH16, show mc.reg 2 - 112 = σ.sl 688 from sp_sub hc0 112] at hso hcase
  have hn : (w k.keys.length).toNat = k.keys.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have e32 : k.kc.toNat * F4.elemBytes = keySize * k.kc.toNat := by
    simp only [F4.elemBytes, keySize]; omega
  rw [hn, e32] at hcase
  have hs := edsame_of (k := { k with keys := [] }) (kp' := 0) (Y := KX k) hpre
    (by simpa [KD] using hlive) hso fun a h => by
      rcases h with h | h | h | h | h | ⟨hc1, h⟩
      · exact .inl (slots_free hpre (by decide) (by decide) (by decide) h)
      · exact .inl (slots_free hpre (by decide) (by decide) (by decide) h)
      · exact .inl (slots_free hpre (by decide) (by decide) (by decide) h)
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · refine .inr (.inr (.inr ⟨(k.kq, keySize * k.kc.toNat), by simp [KX, hc1], ?_⟩))
        rw [e32] at h; exact h
  have hrk : ∀ i ∈ ([20, 21, 26, 27] : List (Fin 32)), m.reg i = mc.reg i :=
    fun i hi => hret.2 i (by simp only [calleeSaved]; simp at hi ⊢; omega)
  have hOK := outer_bytes hok hs.rest
  have hOR : OuterRegs σ m o := ⟨(hrk 20 (by simp)).trans r20, (hrk 21 (by simp)).trans r21, hi,
    (load_congr fun t ht => hs.slot (0x1f0, 8) (by simp) t ht).trans hmag⟩
  have hNH : ELNoHdr σ m o := elnohdr_keep (hEL.2 : ELNoHdr σ mc o) fun b hb =>
    hs.blk b (by simpa [KD] using hb)
  have hEO : EntryOk σ m o k := ⟨hd, hle, (hrk 26 (by simp)).trans r26⟩
  have hAO' : AddrOk σ m o k := ⟨hAO.1, hAO.2.1, bytes_congr hAO.2.2 fun t ht =>
    hs.slot (0x158, 20) (by simp) t (by simp only [itemPayload, List.length_take] at ht; omega)⟩
  have hH := hdr_congr hEL.1 fun t ht => hs.slot (0x1c0, 24) (by simp) t ht
  have h27 : m.reg 27 = 32 := (hrk 27 (by simp)).trans r27
  have hb0 : σ.sl 0xb0 = σ.sl 0xb8 + 8 := by simp only [Sig.sl, w]; bv_omega
  split at hcase
  · rename_i h0
    have hk0 : k.keys = [] := List.eq_nil_of_length_eq_zero h0
    obtain ⟨-, ⟨hr0, hr8, -, -⟩, hheap, -⟩ := hcase
    have hKD : KD k k.kq = [] := by simp [KD, hk0]
    have hl : Live σ m (if 0 < k.kc.toNat then L.erase (k.kq, keySize * k.kc.toNat) else L)
        (EX o ++ KD k k.kq ++ []) := by
      rw [hKD]
      by_cases hc : 0 < k.kc.toNat
      · rw [if_pos hc] at hheap ⊢
        have hKX : KX k = [(k.kq, keySize * k.kc.toNat)] := by simp [KX, hc]
        rw [hKX] at hlive
        exact live_of_heap hpre hheap (by simpa using erase_perm hlive (by
          simp only [keySize]; omega)) fun b hb =>
            (hlive.2.2 b (List.mem_append_left _ (by simpa using hb))).1
      · rw [if_neg hc] at hheap ⊢
        have hKX : KX k = [] := by simp [KX, hc]
        rw [hKX] at hlive
        exact ⟨hheap, by simpa using hlive.2.1, fun b hb => hlive.2.2 b (by simpa using hb)⟩
    refine ⟨o, k, _, k.kq, ⟨hcm, hOK, hOR, hNH, hl, hEO, hAO', hKLO, hkw,
      fun h => absurd hk0 h, by rw [hk0]; intro i hi; simp at hi, hlens⟩, hH, hr0, ?_, h27⟩
    rw [hb0, hr8, hk0]; rfl
  · rename_i h0
    rcases hcase with ⟨p', -, hram', hbytes', -, ⟨hr0, hr8, -, -⟩, hheap, -⟩ |
      ⟨-, ⟨-, herr, -⟩, -, -⟩
    · have hc : 0 < k.kc.toNat := by omega
      have hKX : KX k = [(k.kq, keySize * k.kc.toNat)] := by simp [KX, hc]
      rw [hKX] at hlive
      have hk0 : k.keys ≠ [] := fun h => h0 (by rw [h]; rfl)
      have e32' : k.keys.length * F4.elemBytes = keySize * k.keys.length := by
        simp only [F4.elemBytes, keySize]; omega
      rw [e32'] at hheap hram'
      have hKD : KD k p' = [(p', keySize * k.keys.length)] := by simp [KD, hk0]
      have hl : Live σ m (L.erase (k.kq, keySize * k.kc.toNat) ++ [(p', keySize * k.keys.length)])
          (EX o ++ KD k p' ++ []) := by
        rw [hKD]
        refine live_of_heap hpre hheap (by
          simpa using (erase_perm hlive (by simp only [keySize]; omega)).append_right
            [(p', keySize * k.keys.length)]) fun b hb => ?_
        simp only [List.append_nil, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact (hlive.2.2 b (List.mem_append_left _ hb)).1
        · show 0 < keySize * k.keys.length
          have : 0 < k.keys.length := List.length_pos_iff.mpr hk0
          simp only [keySize]; omega
      exact ⟨o, k, _, p', ⟨hcm, hOK, hOR, hNH, hl, hEO, hAO', hKLO, hkw, fun _ => hram',
        hbytes', hlens⟩, hH, hr0, by rw [hb0]; exact hr8, h27⟩
    · exfalso
      have := frame_init_n hpre (k := 0xb8) (off := 16) (n := 2) (by decide) (by decide)
        (v := 2) herr
      rw [show 576 - 0xb8 + 16 = 408 from rfl, he] at this
      exact absurd this (by decide)

/-- An initial frame byte of an `envB` leaf. -/
theorem frame_byte0 {σ : Sig} {m : Machine} (hc : Common σ m) {j : Nat} (hj : j < 576) :
    some ((envB σ m).byte0 0 j) = m.mem (σ.sl 576 + BitVec.ofNat 64 j) :=
  mem0_entry (common_present hc 0 j (by decide) hj)

/-- A frame word the leaf copied from another frame word. -/
theorem leaf_copy {σ : Sig} {m m' : Machine} {S' : SState} (hc : Common σ m)
    (hwf : Env.WF (envB σ m) S') (hm' : Match (envB σ m) S' m') (hS' : S'.regions = baseRegions)
    {d s n : Nat} (hn : n ≤ 8) (hd : d + n ≤ 576) (hs : s + n ≤ 576)
    (hv : ∀ u < n, byteOf ((readConst S' 0 d n).eval (envB σ m)) u = (envB σ m).byte0 0 (s + u)) :
    ∀ u < n, m'.mem (σ.sl (576 - d) + BitVec.ofNat 64 u) =
      m.mem (σ.sl 576 + BitVec.ofNat 64 (s + u)) := fun u hu => by
  rw [leaf_bytes (BaseEnv.ofB σ m) hwf hm' hS' hn hd u hu, hv u hu]
  exact frame_byte0 hc (by omega)

theorem TX.leaf_8000025c_1 :
    LeafGoal TX.plan TX.plan.cuts[10]! ((TX.plan.leaves 0x8000025c)[1]!) := by
  show LeafGoal TX.plan cut25c (run25c_leaves[1]!)
  have hcs : (run25c_leaves[1]!).conds = [SBool.eq (Sym.init 0 408 2) (Sym.lit 0),
      SBool.ltu (Sym.init 0 136 8) (Sym.init 0 144 8)] := by decide
  have hsteps : (run25c_leaves[1]!).S.steps - cut25c.S.steps = 23 := by decide
  intro σ m hA hc
  have hcm := (ret_25c hA).1
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run25c_leaves[1]!).exit = .at 0x80000460 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x80000460 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 408 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m) (SBool.ltu (Sym.init 0 136 8) (Sym.init 0 144 8)) = true :=
    hc _ (by rw [hcs]; simp)
  have he : (Sym.init 0 408 2).eval (envB σ m) = 0 := by
    simpa [SBool.eval, Sym.eval] using h1
  obtain ⟨o, k, L, kp', G, hH, hb8, hb0, -⟩ := ret25c hA he
  obtain ⟨hwf, hm, -⟩ := body_cut hcm
  have hS : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 26] : List (Fin 32)),
      (run25c_leaves[1]!).S.reg i.val = SBody.reg i.val := by decide
  have hr := regs_keep hm hm' _ hS
  have reg : ∀ (i : Fin 32) (s : Sym), (run25c_leaves[1]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r10 := reg 10 _ (by decide : (run25c_leaves[1]!).S.reg 10 =
    .bin .add (.init 0 128 8) (.bin .add (.bin .sll (.init 0 136 8) (.lit 5))
      (.bin .sll (.init 0 136 8) (.lit 3))))
  have r14 := reg 14 _ (by decide : (run25c_leaves[1]!).S.reg 14 = .init 0 392 8)
  have r15 := reg 15 _ (by decide : (run25c_leaves[1]!).S.reg 15 = .init 0 400 8)
  have c24 := reg 24 _ (by decide : (run25c_leaves[1]!).S.reg 24 = .lit 20)
  have c25 := reg 25 _ (by decide : (run25c_leaves[1]!).S.reg 25 = .lit 1)
  have c27 := reg 27 _ (by decide : (run25c_leaves[1]!).S.reg 27 = .lit 32)
  -- the frame words the leaf reads
  have e128 := frame_init hpre (m := m) (k := 0x1c0) (by decide) (by decide) hH.1
  have e136 := frame_init hpre (m := m) (k := 0x1b8) (by decide) (by decide)
    (by rw [show σ.sl 0x1b8 = σ.sl 0x1c0 + 8 by simp only [Sig.sl, w]; bv_omega]; exact hH.2.1)
  have e144 := frame_init hpre (m := m) (k := 0x1b0) (by decide) (by decide)
    (by rw [show σ.sl 0x1b0 = σ.sl 0x1c0 + 16 by simp only [Sig.sl, w]; bv_omega]; exact hH.2.2)
  have e392 := frame_init hpre (m := m) (k := 0xb8) (by decide) (by decide) hb8
  have e400 := frame_init hpre (m := m) (k := 0xb0) (by decide) (by decide) hb0
  simp only [show 576 - 0x1c0 = 128 from rfl, show 576 - 0x1b8 = 136 from rfl,
    show 576 - 0x1b0 = 144 from rfl, show 576 - 0xb8 = 392 from rfl,
    show 576 - 0xb0 = 400 from rfl] at e128 e136 e144 e392 e400
  have hNH := G.2.2.2.1
  have hn32 : o.done.length < 2 ^ 32 := by have := hNH.1; have := hNH.2.2.2.1; omega
  have hnn : (w o.done.length).toNat = o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have hroom : o.done.length + 1 ≤ o.ec.toNat := by
    simp only [SBool.eval, e136, e144] at h2
    simp only [BitVec.ult, decide_eq_true_eq, hnn] at h2; omega
  -- what the leaf writes
  have hlive := G.2.2.2.2.1
  obtain ⟨hc', hlive', -⟩ := base_leaf hcm hlive (BaseEnv.ofB σ m) hwf rfl hm' (by decide) hfr
    (by decide) fun i hi => hr i (by simp at hi ⊢; omega)
  have hso := frame_leaf_so hcm rfl hm' (by decide) hfr (by decide)
  have hmem : (run25c_leaves[1]!).S.mem =
      [⟨0, 136, 8, .bin .add (.init 0 136 8) (.lit 1)⟩, ⟨0, 432, 4, .sext 32 (.init 0 248 4)⟩,
        ⟨0, 424, 8, .init 0 240 8⟩, ⟨0, 416, 8, .init 0 232 8⟩] := by decide
  have hW : ∀ a, (∃ wr ∈ (run25c_leaves[1]!).S.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      InRange (σ.sl 0x1b8) 8 a ∨ InRange (σ.sl 0xa0) 20 a := by
    rintro a ⟨wr, hwr, hin⟩
    rw [hmem] at hwr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwr
    rcases hwr with rfl | rfl | rfl | rfl
    · exact .inl (fr_in hpre (by decide) (by decide) (by decide) (by decide) hin)
    all_goals exact .inr (fr_in hpre (by decide) (by decide) (by decide) (by decide) hin)
  have hst : ∀ a, (InRange (σ.sl 0x1b8) 8 a ∨ InRange (σ.sl 0xa0) 20 a) →
      InRange (σ.sl stackBytes) stackBytes a := fun a h => by
    rcases h with h | h
    · exact sl_in_stack hpre (by decide) (by decide) h
    · exact sl_in_stack hpre (by decide) (by decide) h
  have G' := grown_keep G hc' hlive' (fun i hi => hr i (by simp at hi ⊢; omega))
    (rest_bytes hpre hso fun a h => .inl (hst a (hW a h)))
    (fun kn hkn t ht => hso _ fun h => by
      have h3 := sl_toNat hpre (k := kn.1) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
        rcases hkn with rfl | rfl <;> decide)
      have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
      have hin := in_self (a := σ.sl kn.1) (n := kn.2) (t := t) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
        rcases hkn with rfl | rfl <;> (dsimp only at h3 ⊢; rw [h3]; omega)) ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
      rcases hW _ h with hw | hw <;> rcases hkn with rfl | rfl <;>
        exact sl_apart hpre (by decide) (by decide) (by decide) hin hw)
    (fun b hb t ht => hso _ fun h => by
      have hP := (hlive.2.2 b (List.mem_append_left _ hb))
      have hram := hP.2.1
      unfold RamRange Layout.ramHi at hram
      exact stack_not_priv hpre (hst _ (hW _ h)) (hP.2.2 _ (in_self (by omega) ht)))
  -- the header with the new length
  have hwf' : Env.WF (envB σ m) (run25c_leaves[1]!).S := hwf.congr (by decide)
  have f8 := frame_word (BaseEnv.ofB σ m) hwf' hm' (by decide) (k := 0x1b8) (by decide) (by decide)
  rw [show readConst (run25c_leaves[1]!).S 0 (576 - 0x1b8) 8 = .bin .add (.init 0 136 8) (.lit 1)
    by decide] at f8
  have hso8 : ∀ t < 24, t < 8 ∨ 16 ≤ t →
      m'.mem (σ.sl 0x1c0 + BitVec.ofNat 64 t) = m.mem (σ.sl 0x1c0 + BitVec.ofNat 64 t) :=
    fun t ht ht' => hso _ fun h => by
      have h3 := sl_toNat hpre (k := 0x1c0) (by decide)
      have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
      have hin := in_self (a := σ.sl 0x1c0) (n := 24) (by rw [h3]; omega) ht
      have h1b8 := sl_toNat hpre (k := 0x1b8) (by decide)
      have h0a0 := sl_toNat hpre (k := 0xa0) (by decide)
      rcases hW _ h with hw | hw
      · simp only [InRange, h3, h1b8] at hw; rw [toNat_add_ofNat (by omega)] at hw; omega
      · exact sl_apart hpre (by decide) (by decide) (by decide) hin hw
  have hH' : F1.HeaderIs m' (σ.sl 0x1c0) o.ep (w (o.done.length + 1)) o.ec := by
    refine ⟨(load_congr fun t ht => hso8 t (by omega) (.inl ht)).trans hH.1, ?_, ?_⟩
    · rw [show σ.sl 0x1c0 + 8 = σ.sl 0x1b8 by simp only [Sig.sl, w]; bv_omega, f8]
      show some ((Sym.init 0 136 8).eval (envB σ m) + 1#64) = _
      rw [e136]; simp only [w, BitVec.ofNat_add]
    · rw [load_congr (m := m) fun t ht => by
        rw [show σ.sl 0x1c0 + 16 + BitVec.ofNat 64 t = σ.sl 0x1c0 + BitVec.ofNat 64 (16 + t) by
          bv_omega]
        exact hso8 _ (by omega) (.inr (by omega))]
      exact hH.2.2
  -- copy B from copy A
  have hA := G.2.2.2.2.2.2.1.2.2
  have cp := fun d s n hn hd hs hv => leaf_copy (S' := (run25c_leaves[1]!).S) hcm hwf' hm'
    (by decide) (d := d) (s := s) (n := n) hn hd hs hv
  have c0 := cp 416 232 8 (by decide) (by decide) (by decide) fun u hu => by
    rw [show readConst (run25c_leaves[1]!).S 0 416 8 = .init 0 232 8 by decide]
    exact byteOf_byteList (by decide) hu
  have c1 := cp 424 240 8 (by decide) (by decide) (by decide) fun u hu => by
    rw [show readConst (run25c_leaves[1]!).S 0 424 8 = .init 0 240 8 by decide]
    exact byteOf_byteList (by decide) hu
  have c2 := cp 432 248 4 (by decide) (by decide) (by decide) fun u hu => by
    rw [show readConst (run25c_leaves[1]!).S 0 432 4 = .bytes (.sext 32 (.init 0 248 4)) 0 4 by
      decide]
    show byteOf (ofBytesLE (byteList (byteOf ((((Sym.init 0 248 4).eval (envB σ m)).setWidth 32
      ).signExtend 64)) 0 4)) u = _
    rw [byteOf_byteList (by decide) hu, Nat.zero_add, byteOf_sext32 _ hu]
    exact byteOf_byteList (by decide) hu
  have hB : BytesAt m' (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20) := fun i hi => by
    have hi20 : i < 20 := by simp only [itemPayload, List.length_take] at hi; omega
    rw [← hA i hi]
    rcases Nat.lt_or_ge i 8 with h8 | h8
    · have := c0 i h8
      rw [show σ.sl (576 - 416) = σ.sl 0xa0 from rfl,
        show σ.sl 576 + BitVec.ofNat 64 (232 + i) = σ.sl 0x158 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega] at this
      exact this
    rcases Nat.lt_or_ge i 16 with h16 | h16
    · have := c1 (i - 8) (by omega)
      rw [show σ.sl (576 - 424) + BitVec.ofNat 64 (i - 8) = σ.sl 0xa0 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega,
        show σ.sl 576 + BitVec.ofNat 64 (240 + (i - 8)) = σ.sl 0x158 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega] at this
      exact this
    · have := c2 (i - 16) (by omega)
      rw [show σ.sl (576 - 432) + BitVec.ofNat 64 (i - 16) = σ.sl 0xa0 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega,
        show σ.sl 576 + BitVec.ofNat 64 (248 + (i - 16)) = σ.sl 0x158 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega] at this
      exact this
  refine ExitGoal.at_cut rfl ⟨cut460, by simp [TX.plan, vcPlan], hex, aes_of hex G'
    ⟨by simp only [Sym.eval] at c24; exact c24, by simp only [Sym.eval] at c25; exact c25,
      by simp only [Sym.eval] at c27; exact c27⟩
    hH' hroom hB ?_ (r14.trans e392) (r15.trans e400), ?_⟩
  · rw [r10]
    show (Sym.init 0 128 8).eval (envB σ m) +
      (((Sym.init 0 136 8).eval (envB σ m)) <<< ((5#64).toNat % 64) +
        ((Sym.init 0 136 8).eval (envB σ m)) <<< ((3#64).toNat % 64)) = _
    rw [e128, e136, shl40 (by rw [hnn]; omega), hnn]
  · show bTail m' 311 ≤ bTail m 539 - _
    rw [hsteps]; unfold bTail afterEntry; rw [hr 21 (by simp), hr 26 (by simp)]; omega

/-! ## `0x8000025c`: a full list grows -/

def nS : Sym := .bin .add (.init 0 136 8) (.lit 1)
def xS : Sym := .bin .add (.bin .add (.bin .srl nS (.lit 1)) nS) (.lit 1)
/-- The leaves' new capacity `c'` over the length word at `S-0x1b8`. -/
def growS : Sym := .bin .or (.bin .sub (.lit 0) (.bin .sltu xS nS)) xS

theorem growS_eval {env : Env} (hx : ((Sym.init 0 136 8).eval env).toNat < 2 ^ 32) :
    growS.eval env = w (grownCap ((Sym.init 0 136 8).eval env).toNat) := by
  have h := grow_val hx
  simp only [growS, xS, nS, Sym.eval_bin, BinOp.eval, Sym.eval_lit] at h ⊢
  simp only [BitVec.ult, decide_eq_true_eq]
  exact h

/-- The allocator context word `ao[0]`. -/
theorem ctx_eval {σ : Sig} {m : Machine} (hc : Common σ m) :
    (Sym.init 3 0 8).eval (envB σ m) = wordAt σ.m σ.ao := by
  have hpre := hc.2.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpre.2.2.2.2.2.2.2.2.1
  have hram : RamRange σ.ao 16 := hpre.2.2.2.2.2.2.1
  unfold RamRange Layout.ramHi at hram
  rw [show wordAt σ.m σ.ao = v by simp [wordAt, hv]]
  apply init_eval_load (regs := shapeOf σ) (r := 3) (by simp [shapeOf])
  · rw [show ((shapeOf σ)[3]'(by simp [shapeOf])).1 + BitVec.ofNat 64 0 = σ.ao by simp [shapeOf],
      load_congr (m := σ.m) (m' := m) fun t ht => ao_same hc (by omega)]
    exact hv
  · show σ.ao.toNat + 0 + 8 < 2 ^ 64; omega

/-- A written frame range misses a frame range it does not meet. -/
theorem wr_miss {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {off n k len : Nat} {a : Word}
    (ho : off + n ≤ 576) (hk : k ≤ 576) (hd : off + n ≤ 576 - k ∨ 576 - k + len ≤ off)
    (hw : InRange (σ.sl 576 + w off) n a) (ha : InRange (σ.sl k) len a) : False :=
  sl_apart hpre (k1 := 576 - off) (n1 := n) (k2 := k) (n2 := len) (by unfold stackBytes; omega)
    (by unfold stackBytes; omega) (by omega)
    (fr_in hpre (by omega) (by omega) (by omega) (by omega) hw) ha

/-- The leaves of `0x8000025c` that grow a full list: the finished entry (copy B written) and
the growth spills. -/
theorem grow25c {σ : Sig} {m m' : Machine} {S' : SState} (hA : ARet f4C Site258 σ m)
    (he : (Sym.init 0 408 2).eval (envB σ m) = 0)
    (hge : ((Sym.init 0 144 8).eval (envB σ m)).toNat ≤
      ((Sym.init 0 136 8).eval (envB σ m)).toNat)
    (hm' : Match (envB σ m) S' m') (hS' : S'.regions = baseRegions)
    (hfr : SameOutside (InWritable (envB σ m) SBody) m m')
    (hall : S'.mem.all (fun w => w.r == 0) = true)
    (hno : S'.mem.all (fun w => w.r != 0 || decide (w.off + w.n ≤ 472)) = true)
    (hkeep : ∀ wr ∈ S'.mem, wr.off + wr.n ≤ 472 ∧ (wr.off + wr.n ≤ 80 ∨
      (88 ≤ wr.off ∧ wr.off + wr.n ≤ 128) ∨ (152 ≤ wr.off ∧ wr.off + wr.n ≤ 232) ∨ 252 ≤ wr.off))
    (hcp : readConst S' 0 416 8 = .init 0 232 8 ∧ readConst S' 0 424 8 = .init 0 240 8 ∧
      readConst S' 0 432 4 = .bytes (.sext 32 (.init 0 248 4)) 0 4)
    (hsp : readConst S' 0 64 8 = .bin .sll (.init 0 136 8) (.lit 5) ∧
      readConst S' 0 72 8 = .bin .sll (.init 0 136 8) (.lit 3) ∧
      readConst S' 0 48 8 = .init 0 400 8 ∧ readConst S' 0 56 8 = .init 0 392 8 ∧
      readConst S' 0 40 8 = .init 3 0 8 ∧ readConst S' 0 32 8 = .lit vtable)
    (hr : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 26] : List (Fin 32)), S'.reg i.val = SBody.reg i.val)
    (h23 : S'.reg 23 = nS) (h25 : S'.reg 25 = growS) (h27 : S'.reg 27 = .init 0 144 8) :
    ∃ o k L kp', EntryDone σ m' o k L kp' [] ∧ Growing σ m' o k kp' ∧ m'.reg 27 = o.ec ∧
      (Sym.init 0 128 8).eval (envB σ m) = o.ep ∧ (Sym.init 0 144 8).eval (envB σ m) = o.ec ∧
      growS.eval (envB σ m) = w (grownCap o.done.length) ∧ o.done.length < 2 ^ 32 := by
  have hcm := (ret_25c hA).1
  have hpre := hcm.2.1
  obtain ⟨o, k, L, kp', G, hH, hb8, hb0, -⟩ := ret25c hA he
  obtain ⟨hwf, hm, -⟩ := body_cut hcm
  have hrk := regs_keep hm hm' _ hr
  have reg : ∀ (i : Fin 32) (s : Sym), S'.reg i.val = s → m'.reg i = s.eval (envB σ m) :=
    fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have e128 := frame_init hpre (m := m) (k := 0x1c0) (by decide) (by decide) hH.1
  have e136 := frame_init hpre (m := m) (k := 0x1b8) (by decide) (by decide)
    (by rw [show σ.sl 0x1b8 = σ.sl 0x1c0 + 8 by simp only [Sig.sl, w]; bv_omega]; exact hH.2.1)
  have e144 := frame_init hpre (m := m) (k := 0x1b0) (by decide) (by decide)
    (by rw [show σ.sl 0x1b0 = σ.sl 0x1c0 + 16 by simp only [Sig.sl, w]; bv_omega]; exact hH.2.2)
  have e392 := frame_init hpre (m := m) (k := 0xb8) (by decide) (by decide) hb8
  have e400 := frame_init hpre (m := m) (k := 0xb0) (by decide) (by decide) hb0
  simp only [show 576 - 0x1c0 = 128 from rfl, show 576 - 0x1b8 = 136 from rfl,
    show 576 - 0x1b0 = 144 from rfl, show 576 - 0xb8 = 392 from rfl,
    show 576 - 0xb0 = 400 from rfl] at e128 e136 e144 e392 e400
  have hNH := G.2.2.2.1
  have hn32 : o.done.length < 2 ^ 32 := by have := hNH.1; have := hNH.2.2.2.1; omega
  have hnn : (w o.done.length).toNat = o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have hec : o.done.length = o.ec.toNat := by
    rw [e136, e144, hnn] at hge; have := hNH.1; omega
  have hlive := G.2.2.2.2.1
  obtain ⟨hc', hlive', -⟩ := base_leaf hcm hlive (BaseEnv.ofB σ m) hwf rfl hm' hS' hfr hno
    fun i hi => hrk i (by simp at hi ⊢; omega)
  have hso := frame_leaf_so hcm rfl hm' hS' hfr hall
  have hWst : ∀ a, (∃ wr ∈ S'.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      InRange (σ.sl stackBytes) stackBytes a := by
    rintro a ⟨wr, hwr, hin⟩
    have := (hkeep wr hwr).1
    exact sl_in_stack hpre (k := 576 - wr.off) (n := wr.n) (by unfold stackBytes; omega)
      (by omega) (fr_in hpre (by omega) (by omega) (by omega) (by omega) hin)
  have hWk : ∀ j len, (j = 80 ∧ len = 8 ∨ j = 128 ∧ len = 24 ∨ j = 232 ∧ len = 20) → ∀ a,
      (∃ wr ∈ S'.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      ¬ InRange (σ.sl (576 - j)) len a := by
    rintro j len hj a ⟨wr, hwr, hin⟩ ha
    obtain ⟨h1, h2⟩ := hkeep wr hwr
    exact wr_miss hpre (k := 576 - j) (by omega) (by omega) (by omega) hin ha
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  have inS : ∀ {kk len t : Nat}, kk ≤ 576 → len ≤ kk → t < len →
      InRange (σ.sl kk) len (σ.sl kk + BitVec.ofNat 64 t) := fun {kk len t} hk hl ht => by
    have h3 := sl_toNat hpre (k := kk) (by unfold stackBytes; omega)
    exact in_self (by rw [h3]; omega) ht
  have G' := grown_keep G hc' hlive' (fun i hi => hrk i (by simp at hi ⊢; omega))
    (rest_bytes hpre hso fun a h => .inl (hWst a h))
    (fun kn hkn t ht => hso _ fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
      rcases hkn with rfl | rfl
      · exact hWk 80 8 (by simp) _ h (inS (by decide) (by decide) ht)
      · exact hWk 232 20 (by simp) _ h (inS (by decide) (by decide) ht))
    (fun b hb t ht => hso _ fun h => by
      have hP := (hlive.2.2 b (List.mem_append_left _ hb))
      have hram := hP.2.1
      unfold RamRange Layout.ramHi at hram
      exact stack_not_priv hpre (hWst _ h) (hP.2.2 _ (in_self (by omega) ht)))
  have hH' := hdr_congr hH fun t ht => hso _ fun h =>
    hWk 128 24 (by simp) _ h (inS (by decide) (by decide) ht)
  -- copy B from copy A
  have hwf' : Env.WF (envB σ m) S' := hwf.congr (by rw [hS']; rfl)
  have hA := G.2.2.2.2.2.2.1.2.2
  obtain ⟨cp0, cp1, cp2⟩ := hcp
  have cp := fun d s n hn hd hs hv => leaf_copy (S' := S') hcm hwf' hm' hS' (d := d) (s := s)
    (n := n) hn hd hs hv
  have c0 := cp 416 232 8 (by decide) (by decide) (by decide) fun u hu => by
    rw [cp0]; exact byteOf_byteList (by decide) hu
  have c1 := cp 424 240 8 (by decide) (by decide) (by decide) fun u hu => by
    rw [cp1]; exact byteOf_byteList (by decide) hu
  have c2 := cp 432 248 4 (by decide) (by decide) (by decide) fun u hu => by
    rw [cp2]
    show byteOf (ofBytesLE (byteList (byteOf ((((Sym.init 0 248 4).eval (envB σ m)).setWidth 32
      ).signExtend 64)) 0 4)) u = _
    rw [byteOf_byteList (by decide) hu, Nat.zero_add, byteOf_sext32 _ hu]
    exact byteOf_byteList (by decide) hu
  have hB : BytesAt m' (σ.sl 0xa0) (itemPayload (ent σ o k) k.ah 20) := fun i hi => by
    have hi20 : i < 20 := by simp only [itemPayload, List.length_take] at hi; omega
    rw [← hA i hi]
    rcases Nat.lt_or_ge i 8 with h8 | h8
    · have := c0 i h8
      rw [show σ.sl (576 - 416) = σ.sl 0xa0 from rfl,
        show σ.sl 576 + BitVec.ofNat 64 (232 + i) = σ.sl 0x158 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega] at this
      exact this
    rcases Nat.lt_or_ge i 16 with h16 | h16
    · have := c1 (i - 8) (by omega)
      rw [show σ.sl (576 - 424) + BitVec.ofNat 64 (i - 8) = σ.sl 0xa0 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega,
        show σ.sl 576 + BitVec.ofNat 64 (240 + (i - 8)) = σ.sl 0x158 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega] at this
      exact this
    · have := c2 (i - 16) (by omega)
      rw [show σ.sl (576 - 432) + BitVec.ofNat 64 (i - 16) = σ.sl 0xa0 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega,
        show σ.sl 576 + BitVec.ofNat 64 (248 + (i - 16)) = σ.sl 0x158 + BitVec.ofNat 64 i by
          simp only [Sig.sl, w]; bv_omega] at this
      exact this
  -- the growth spills
  have fw := fun kk hk hk' => frame_word (BaseEnv.ofB σ m) hwf' hm' hS' (k := kk) hk hk'
  obtain ⟨s64, s72, s48, s56, s40, s32⟩ := hsp
  have hx40 : ((Sym.init 0 136 8).eval (envB σ m)).toNat < 2 ^ 40 := by rw [e136, hnn]; omega
  have f200 := fw 0x200 (by decide) (by decide)
  rw [show 576 - 0x200 = 64 from rfl, s64] at f200
  have f1f8 := fw 0x1f8 (by decide) (by decide)
  rw [show 576 - 0x1f8 = 72 from rfl, s72] at f1f8
  have f210 := fw 0x210 (by decide) (by decide)
  rw [show 576 - 0x210 = 48 from rfl, s48, e400] at f210
  have f208 := fw 0x208 (by decide) (by decide)
  rw [show 576 - 0x208 = 56 from rfl, s56, e392] at f208
  have f218 := fw 0x218 (by decide) (by decide)
  rw [show 576 - 0x218 = 40 from rfl, s40, ctx_eval hcm] at f218
  have f220 := fw 0x220 (by decide) (by decide)
  rw [show 576 - 0x220 = 32 from rfl, s32] at f220
  have hgr : growS.eval (envB σ m) = w (grownCap o.done.length) := by
    rw [growS_eval (by rw [e136, hnn]; exact hn32), e136, hnn]
  have hG : Growing σ m' o k kp' := by
    refine ⟨hec, ?_, by rw [reg 25 _ h25, hgr], ?_, ?_, f210, f208, f218, f220⟩
    · rw [reg 23 _ h23]
      show (Sym.init 0 136 8).eval (envB σ m) + 1#64 = _
      rw [e136]; simp only [w, BitVec.ofNat_add]
    · rw [f200]; congr 1
      show ((Sym.init 0 136 8).eval (envB σ m)) <<< ((5#64).toNat % 64) = _
      rw [shl5 hx40, e136, hnn]
    · rw [f1f8]; congr 1
      show ((Sym.init 0 136 8).eval (envB σ m)) <<< ((3#64).toNat % 64) = _
      rw [shl3 hx40, e136, hnn]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := G'
  exact ⟨o, k, _, kp', ⟨g1, g2, g3, ⟨hH', g4⟩, g5, g6, g7, g8, g9, g10, g11, g12, hB⟩, hG,
    (reg 27 _ h27).trans e144, e128, e144, hgr, hn32⟩

theorem TX.leaf_8000025c_4 :
    LeafGoal TX.plan TX.plan.cuts[10]! ((TX.plan.leaves 0x8000025c)[4]!) := by
  show LeafGoal TX.plan cut25c (run25c_leaves[4]!)
  have hsteps : (run25c_leaves[4]!).S.steps - cut25c.S.steps = 50 := by decide
  have hcs : (run25c_leaves[4]!).conds = [SBool.eq (Sym.init 0 408 2) (Sym.lit 0),
      SBool.geu (Sym.init 0 136 8) (Sym.init 0 144 8), SBool.eq (Sym.init 0 144 8) (Sym.lit 0),
      SBool.eq (Sym.bin .mulhu growS (Sym.lit 40)) (Sym.lit 0),
      SBool.ne (Sym.bin .add (Sym.bin .sll growS (Sym.lit 5)) (Sym.bin .sll growS (Sym.lit 3)))
        (Sym.lit 0)] := by decide
  intro σ m hA hc
  have hcm := (ret_25c hA).1
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run25c_leaves[4]!).exit = .call 0x80042494 0x800003d4 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x80042494 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 408 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m) (SBool.geu (Sym.init 0 136 8) (Sym.init 0 144 8)) = true :=
    hc _ (by rw [hcs]; simp)
  have he : (Sym.init 0 408 2).eval (envB σ m) = 0 := by simpa [SBool.eval, Sym.eval] using h1
  have hge : ((Sym.init 0 144 8).eval (envB σ m)).toNat ≤
      ((Sym.init 0 136 8).eval (envB σ m)).toNat := by
    have : ¬ (((Sym.init 0 136 8).eval (envB σ m)).toNat <
      ((Sym.init 0 144 8).eval (envB σ m)).toNat) := by simpa [SBool.eval, BitVec.ult] using h2
    omega
  obtain ⟨o, k, L, kp', hED, hG, h27, e128, e144, hgr, hn32⟩ := grow25c hA he hge hm' (by decide)
    hfr (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨-, hm, -⟩ := body_cut hcm
  have hr := regs_keep hm hm' _ (by decide : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 26] : List (Fin 32)),
    (run25c_leaves[4]!).S.reg i.val = SBody.reg i.val)
  have reg : ∀ (i : Fin 32) (s : Sym), (run25c_leaves[4]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run25c_leaves[4]!).S.reg 1 = .lit 0x800003d4)
  have r10 := reg 10 _ (by decide : (run25c_leaves[4]!).S.reg 10 = .init 3 0 8)
  have r11 := reg 11 _ (by decide : (run25c_leaves[4]!).S.reg 11 =
    .bin .add (.bin .sll growS (.lit 5)) (.bin .sll growS (.lit 3)))
  have r12 := reg 12 _ (by decide : (run25c_leaves[4]!).S.reg 12 = .lit 3)
  have r13 := reg 13 _ (by decide : (run25c_leaves[4]!).S.reg 13 = .var 19)
  have r22 := reg 22 _ (by decide : (run25c_leaves[4]!).S.reg 22 = .init 0 128 8)
  have hgc := grownCap_lt hn32
  have hc40 : (w (grownCap o.done.length)).toNat = grownCap o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have e11 : m'.reg 11 = w (entrySize * grownCap o.done.length) := by
    rw [r11]
    show growS.eval (envB σ m) <<< ((5#64).toNat % 64) + growS.eval (envB σ m) <<< ((3#64).toNat % 64) = _
    rw [hgr, shl40 (by rw [hc40]; omega), hc40]
  have hn11 : (m'.reg 11).toNat = entrySize * grownCap o.done.length := by
    rw [e11]; simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  have hpos : 0 < grownCap o.done.length := by unfold grownCap; omega
  have hcm' := hED.1
  have hsite : Site3d0 σ L m' := ⟨o, k, kp', hED, hG, h27, r22.trans e128,
    by simp only [Sym.eval] at r1; exact r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
      · exact r10.trans (ctx_eval hcm)
      · exact e11
      · simp only [Sym.eval] at r12; exact r12
      · exact r13.trans ((envB_var σ m 19).trans hcm.2.2.2.2.2.2.2.1)⟩
  obtain ⟨hstk, hcf⟩ := callee_frame hcm' hED.2.2.2.2.1
  have hpre2 : allocPre σ.A L m' := ⟨hED.2.2.2.2.1.1,
    by rw [hn11]; simp only [entrySize]; omega, by rw [hn11]; simp only [entrySize]; omega,
    by simp only [Sym.eval] at r12; rw [r12]; decide, hstk,
    by unfold RetAligned; simp only [Sym.eval] at r1; rw [r1]; decide, hcf⟩
  refine ⟨allocC, L, rfl, hex, hpre2, fun m'' hpost => ⟨cut3d4, by simp [TX.plan, vcPlan],
    rfl, ?_, ⟨m', L, hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1]; simp only [Sym.eval] at r1; rw [r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by simp))
    have h26 : m''.reg 26 = m.reg 26 := (hpost.1.1.2 26 (by decide)).trans (hr 26 (by simp))
    show 53 + bTail m'' 389 ≤ bTail m 539 - _
    rw [hsteps]; unfold bTail afterEntry; rw [h21, h26]; omega

theorem TX.leaf_8000025c_5 :
    LeafGoal TX.plan TX.plan.cuts[10]! ((TX.plan.leaves 0x8000025c)[5]!) := by
  show LeafGoal TX.plan cut25c (run25c_leaves[5]!)
  have hsteps : (run25c_leaves[5]!).S.steps - cut25c.S.steps = 52 := by decide
  have hcs : (run25c_leaves[5]!).conds = [SBool.eq (Sym.init 0 408 2) (Sym.lit 0),
      SBool.geu (Sym.init 0 136 8) (Sym.init 0 144 8), SBool.ne (Sym.init 0 144 8) (Sym.lit 0),
      SBool.eq (Sym.bin .mulhu growS (Sym.lit 40)) (Sym.lit 0)] := by decide
  intro σ m hA hc
  have hcm := (ret_25c hA).1
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run25c_leaves[5]!).exit = .call 0x8004218c 0x80000340 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x8004218c at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SBody) m m' at hfr
  have h1 : SBool.eval (envB σ m) (SBool.eq (Sym.init 0 408 2) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h2 : SBool.eval (envB σ m) (SBool.geu (Sym.init 0 136 8) (Sym.init 0 144 8)) = true :=
    hc _ (by rw [hcs]; simp)
  have h3 : SBool.eval (envB σ m) (SBool.ne (Sym.init 0 144 8) (Sym.lit 0)) = true :=
    hc _ (by rw [hcs]; simp)
  have h4 : SBool.eval (envB σ m) (SBool.eq (Sym.bin .mulhu growS (Sym.lit 40)) (Sym.lit 0)) =
    true := hc _ (by rw [hcs]; simp)
  have he : (Sym.init 0 408 2).eval (envB σ m) = 0 := by simpa [SBool.eval, Sym.eval] using h1
  have hge : ((Sym.init 0 144 8).eval (envB σ m)).toNat ≤
      ((Sym.init 0 136 8).eval (envB σ m)).toNat := by
    have : ¬ (((Sym.init 0 136 8).eval (envB σ m)).toNat <
      ((Sym.init 0 144 8).eval (envB σ m)).toNat) := by simpa [SBool.eval, BitVec.ult] using h2
    omega
  obtain ⟨o, k, L, kp', hED, hG, h27, e128, e144, hgr, hn32⟩ := grow25c hA he hge hm' (by decide)
    hfr (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨hwf, hm, -⟩ := body_cut hcm
  have hr := regs_keep hm hm' _ (by decide : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 26] : List (Fin 32)),
    (run25c_leaves[5]!).S.reg i.val = SBody.reg i.val)
  have reg : ∀ (i : Fin 32) (s : Sym), (run25c_leaves[5]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run25c_leaves[5]!).S.reg 1 = .lit 0x80000340)
  have r10 := reg 10 _ (by decide : (run25c_leaves[5]!).S.reg 10 = .init 3 0 8)
  have r11 := reg 11 _ (by decide : (run25c_leaves[5]!).S.reg 11 = .init 0 128 8)
  have r12 := reg 12 _ (by decide : (run25c_leaves[5]!).S.reg 12 =
    .bin .add (.bin .sll (.init 0 144 8) (.lit 5)) (.bin .sll (.init 0 144 8) (.lit 3)))
  have r13 := reg 13 _ (by decide : (run25c_leaves[5]!).S.reg 13 = .lit 3)
  have r14 := reg 14 _ (by decide : (run25c_leaves[5]!).S.reg 14 =
    .bin .add (.bin .sll growS (.lit 5)) (.bin .sll growS (.lit 3)))
  have r15 := reg 15 _ (by decide : (run25c_leaves[5]!).S.reg 15 = .var 19)
  have r22 := reg 22 _ (by decide : (run25c_leaves[5]!).S.reg 22 =
    .bin .mulhu growS (.lit 40))
  have hgc := grownCap_lt hn32
  have hc40 : (w (grownCap o.done.length)).toNat = grownCap o.done.length := by
    simp only [w, BitVec.toNat_ofNat]; omega
  have hgx : (growS.eval (envB σ m)).toNat < 2 ^ 40 := by rw [hgr, hc40]; omega
  have hEL := hED.2.2.2.1
  have hec0 : 0 < o.ec.toNat := by
    simp only [SBool.eval, e144, bne_iff_ne, ne_eq] at h3
    exact Nat.pos_of_ne_zero fun h0 => h3 (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hwf' : Env.WF (envB σ m) (run25c_leaves[5]!).S := hwf.congr (by decide)
  have fw := fun kk hk hk' => frame_word (BaseEnv.ofB σ m) hwf' hm' (by decide) (k := kk) hk hk'
  have f228 := fw 0x228 (by decide) (by decide)
  rw [show 576 - 0x228 = 24 from rfl,
    show readConst (run25c_leaves[5]!).S 0 24 8 = .init 0 128 8 by decide, e128] at f228
  have f230 := fw 0x230 (by decide) (by decide)
  rw [show 576 - 0x230 = 16 from rfl,
    show readConst (run25c_leaves[5]!).S 0 16 8 = .bin .sll growS (.lit 3) by decide] at f230
  have f238 := fw 0x238 (by decide) (by decide)
  rw [show 576 - 0x238 = 8 from rfl,
    show readConst (run25c_leaves[5]!).S 0 8 8 = .bin .sll growS (.lit 5) by decide] at f238
  have f240 := fw 0x240 (by decide) (by decide)
  rw [show 576 - 0x240 = 0 from rfl, show readConst (run25c_leaves[5]!).S 0 0 8 =
    .bin .add (.bin .sll growS (.lit 5)) (.bin .sll growS (.lit 3)) by decide] at f240
  have e40 : (Sym.bin .add (.bin .sll growS (.lit 5)) (.bin .sll growS (.lit 3))).eval
      (envB σ m) = w (entrySize * grownCap o.done.length) := by
    show growS.eval (envB σ m) <<< ((5#64).toNat % 64) + growS.eval (envB σ m) <<< ((3#64).toNat % 64) = _
    rw [shl40 hgx, hgr, hc40]
  have hsite : Site33c σ m' := ⟨o, k, L, kp', hED, hG, h27, hec0, by
      rw [r22]; simpa [SBool.eval] using h4, f228,
    by rw [f230]; congr 1; show growS.eval (envB σ m) <<< ((3#64).toNat % 64) = _
       rw [shl3 hgx, hgr, hc40],
    by rw [f238]; congr 1; show growS.eval (envB σ m) <<< ((5#64).toNat % 64) = _
       rw [shl5 hgx, hgr, hc40],
    by rw [f240, e40],
    by simp only [Sym.eval] at r1; exact r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 :=
        by omega
      · exact r10.trans (ctx_eval hcm)
      · exact r11.trans e128
      · refine r12.trans ?_
        show (Sym.init 0 144 8).eval (envB σ m) <<< ((5#64).toNat % 64) +
          (Sym.init 0 144 8).eval (envB σ m) <<< ((3#64).toNat % 64) = _
        rw [e144, shl40 (by have := hEL.2.2.2.2.1; omega)]; rfl
      · simp only [Sym.eval] at r13; exact r13
      · exact r14.trans e40
      · exact r15.trans ((envB_var σ m 19).trans hcm.2.2.2.2.2.2.2.1)⟩
  have hcm' := hED.1
  obtain ⟨hstk, -⟩ := callee_frame hcm' hED.2.2.2.2.1
  have hpre2 : F0.Pre m' := ⟨hcm'.2.2.1, hstk,
    by unfold RetAligned; simp only [Sym.eval] at r1; rw [r1]; decide⟩
  refine ⟨remapC, (), rfl, hex, hpre2, fun m'' hpost => ⟨cut340, by simp [TX.plan, vcPlan],
    rfl, ?_, ⟨m', (), hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1]; simp only [Sym.eval] at r1; rw [r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by simp))
    have h26 : m''.reg 26 = m.reg 26 := (hpost.1.1.2 26 (by decide)).trans (hr 26 (by simp))
    show 9 + bTail m'' 478 ≤ bTail m 539 - _
    rw [hsteps]; unfold bTail afterEntry; rw [h21, h26]; omega

/-! ## `0x80000340`: `remap` returned null, `alloc` -/

/-- A frame word survives a call that writes only its 16-byte callee frame. -/
theorem cframe_keep {σ : Sig} {mc m : Machine} (hc : Common σ mc)
    (hso : SameOutside (InRange (mc.reg 2 - 16) 16) mc m) {j : Nat} (hj : 8 ≤ j) (hj' : j ≤ 576)
    {v : Word} (h : mc.load (σ.sl j) 8 = some v) : m.load (σ.sl j) 8 = some v :=
  frame_keep hc.2.1 hso hj' hj (fun a ha hin => by
    rw [show mc.reg 2 - 16 = σ.sl 592 from sp_sub hc 16] at ha
    exact sl_apart hc.2.1 (k1 := 592) (n1 := 16) (k2 := j) (n2 := 8) (by decide)
      (by unfold stackBytes; omega) (by omega) ha hin) h

/-- A frame word a leaf rewrote with its own value. -/
theorem fw_same {σ : Sig} {m m' : Machine} {S' : SState} (hc : Common σ m)
    (hwf : Env.WF (envB σ m) S') (hm' : Match (envB σ m) S' m') (hS' : S'.regions = baseRegions)
    {j : Nat} (hj : 8 ≤ j) (hj' : j ≤ 576) (hv : readConst S' 0 (576 - j) 8 = .init 0 (576 - j) 8)
    {v : Word} (h : m.load (σ.sl j) 8 = some v) : m'.load (σ.sl j) 8 = some v := by
  rw [frame_word (BaseEnv.ofB σ m) hwf hm' hS' hj hj', hv, frame_init hc.2.1 hj hj' h]

/-- `EntryDone`'s bytes survive a leaf that writes frame words apart from its slots. -/
theorem edsame_frame {σ : Sig} {m m' : Machine} {S' : SState} {o : Obs} {k : Kobs} {kp' : Word}
    {L X : List (Word × Nat)} (hc : Common σ m) (hlive : Live σ m L (EX o ++ KD k kp' ++ X))
    (hso : SameOutside (fun a => ∃ wr ∈ S'.mem, InRange (σ.sl 576 + w wr.off) wr.n a) m m')
    (hkeep : ∀ wr ∈ S'.mem, wr.off + wr.n ≤ 472 ∧ (wr.off + wr.n ≤ 80 ∨
      (88 ≤ wr.off ∧ wr.off + wr.n ≤ 128) ∨ (152 ≤ wr.off ∧ wr.off + wr.n ≤ 232) ∨
      (252 ≤ wr.off ∧ wr.off + wr.n ≤ 416) ∨ 436 ≤ wr.off)) :
    EDSame σ o k kp' m m' := by
  have hpre := hc.2.1
  have hWst : ∀ a, (∃ wr ∈ S'.mem, InRange (σ.sl 576 + w wr.off) wr.n a) →
      InRange (σ.sl stackBytes) stackBytes a := by
    rintro a ⟨wr, hwr, hin⟩
    have := (hkeep wr hwr).1
    exact sl_in_stack hpre (k := 576 - wr.off) (n := wr.n) (by unfold stackBytes; omega)
      (by omega) (fr_in hpre (by omega) (by omega) (by omega) (by omega) hin)
  refine edsame_of hpre hlive hso fun a ⟨wr, hwr, hin⟩ => .inl ⟨hWst a ⟨wr, hwr, hin⟩,
    fun kn hkn ha => ?_⟩
  obtain ⟨h1, h2⟩ := hkeep wr hwr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hkn
  rcases hkn with rfl | rfl | rfl | rfl <;>
    exact wr_miss hpre (by omega) (by decide) (by dsimp only; omega) hin ha

theorem TX.leaf_80000340_2 :
    LeafGoal TX.plan TX.plan.cuts[11]! ((TX.plan.leaves 0x80000340)[2]!) := by
  show LeafGoal TX.plan cut340 (run340_leaves[2]!)
  have hsteps : (run340_leaves[2]!).S.steps - cut340.S.steps = 29 := by decide
  intro σ m hA _
  obtain ⟨hcm, -, hsp⟩ := ret_340 hA
  have hpre := hcm.2.1
  refine ⟨nil_obligs (by decide), by budget_auto, ?_⟩
  intro m' hm' hex hfr
  have hx : (run340_leaves[2]!).exit = .call 0x80042494 0x800003d4 := by decide
  rw [hx] at hex ⊢
  change m'.pc.toNat = 0x80042494 at hex
  change Match (envB σ m) _ m' at hm'
  change SameOutside (InWritable (envB σ m) SSpill) m m' at hfr
  obtain ⟨hwf, hm, -⟩ := spill_cut hcm hsp
  obtain ⟨mc, _, ⟨o, k, L, kp', hED, hG, h27, -, -, l228, l230, l238, l240, -⟩,
    ⟨hret, -, hso⟩, hpres⟩ := hA
  have hc0 := hED.1
  have hlive := hED.2.2.2.2.1
  have hEL := hED.2.2.2.1
  -- after `remap`: only its frame changed
  have rk : ∀ i ∈ ([20, 21, 23, 25, 26, 27] : List (Fin 32)), m.reg i = mc.reg i :=
    fun i hi => hret.2 i (by simp only [calleeSaved]; simp at hi ⊢; omega)
  have hheap : σ.A.Heap L m := σ.A.heap_frame' L mc m hlive.1 (fun a ha => hso a fun h =>
    stack_not_priv hpre (cframe_R hc0 h).1 (priv_sub hpre hlive ha)) hpres
  have hEDm := ed_congr hED hcm hheap (fun i hi => rk i (by simp at hi ⊢; omega))
    (edsame_of (Y := []) hpre (by simpa using hlive) hso fun a h => .inl (cframe_R hc0 h))
  have ck := fun {j : Nat} (hj : 8 ≤ j) (hj' : j ≤ 576) {v : Word} (h : mc.load (σ.sl j) 8 = some v) =>
    cframe_keep hc0 hso hj hj' h
  obtain ⟨g0, g23, g25, g200, g1f8, g210, g208, g218, g220⟩ := hG
  -- the leaf: spills rewritten with their values, the flag byte
  have hS : ∀ i ∈ ([2, 8, 9, 18, 19, 20, 21, 23, 25, 26, 27] : List (Fin 32)),
      (run340_leaves[2]!).S.reg i.val = SSpill.reg i.val := by decide
  have hr := regs_keep hm hm' _ hS
  have reg : ∀ (i : Fin 32) (s : Sym), (run340_leaves[2]!).S.reg i.val = s →
      m'.reg i = s.eval (envB σ m) := fun i s h => by rw [Match.reg_eq hm' i i.val rfl, h]
  have r1 := reg 1 _ (by decide : (run340_leaves[2]!).S.reg 1 = .lit 0x800003d4)
  have r10 := reg 10 _ (by decide : (run340_leaves[2]!).S.reg 10 = .init 0 40 8)
  have r11 := reg 11 _ (by decide : (run340_leaves[2]!).S.reg 11 =
    .bin .add (.init 0 8 8) (.init 0 16 8))
  have r12 := reg 12 _ (by decide : (run340_leaves[2]!).S.reg 12 = .lit 3)
  have r13 := reg 13 _ (by decide : (run340_leaves[2]!).S.reg 13 = .var 19)
  have r22 := reg 22 _ (by decide : (run340_leaves[2]!).S.reg 22 = .init 0 24 8)
  obtain ⟨hc', hlive', -⟩ := base_leaf hcm hEDm.2.2.2.2.1 (BaseEnv.ofB σ m) hwf rfl hm'
    (by decide) hfr (by decide) fun i hi => hr i (by simp at hi ⊢; omega)
  have hso' := frame_leaf_so hcm rfl hm' (by decide) hfr (by decide)
  have hED' := ed_congr hEDm hc' hlive'.1 (fun i hi => hr i (by simp at hi ⊢; omega))
    (edsame_frame hcm hEDm.2.2.2.2.1 hso' (by decide))
  have hwf' : Env.WF (envB σ m) (run340_leaves[2]!).S := hwf.congr (by decide)
  have fs := fun {j : Nat} (hj : 8 ≤ j) (hj' : j ≤ 576)
    (hv : readConst (run340_leaves[2]!).S 0 (576 - j) 8 = .init 0 (576 - j) 8) {v : Word}
    (h : m.load (σ.sl j) 8 = some v) => fw_same hcm hwf' hm' (by decide) hj hj' hv h
  have hG' : Growing σ m' o k kp' := ⟨g0, (hr 23 (by simp)).trans ((rk 23 (by simp)).trans g23),
    (hr 25 (by simp)).trans ((rk 25 (by simp)).trans g25),
    fs (by decide) (by decide) (by decide) (ck (by decide) (by decide) g200),
    fs (by decide) (by decide) (by decide) (ck (by decide) (by decide) g1f8),
    fs (by decide) (by decide) (by decide) (ck (by decide) (by decide) g210),
    fs (by decide) (by decide) (by decide) (ck (by decide) (by decide) g208),
    fs (by decide) (by decide) (by decide) (ck (by decide) (by decide) g218),
    by rw [frame_word (BaseEnv.ofB σ m) hwf' hm' (by decide) (k := 0x220) (by decide) (by decide),
      show readConst (run340_leaves[2]!).S 0 (576 - 0x220) 8 = .lit vtable by decide]; rfl⟩
  have hn32 : o.done.length < 2 ^ 32 := by have := hEL.2.1; have := hEL.2.2.2.2.1; omega
  have hgc := grownCap_lt hn32
  have e40 := frame_init hpre (k := 0x218) (by decide) (by decide) (ck (by decide) (by decide) g218)
  have e24 := frame_init hpre (k := 0x228) (by decide) (by decide) (ck (by decide) (by decide) l228)
  have e16 := frame_init hpre (k := 0x230) (by decide) (by decide) (ck (by decide) (by decide) l230)
  have e8 := frame_init hpre (k := 0x238) (by decide) (by decide) (ck (by decide) (by decide) l238)
  simp only [show 576 - 0x218 = 40 from rfl, show 576 - 0x228 = 24 from rfl,
    show 576 - 0x230 = 16 from rfl, show 576 - 0x238 = 8 from rfl] at e40 e24 e16 e8
  have e11 : m'.reg 11 = w (entrySize * grownCap o.done.length) := by
    rw [r11]
    show (Sym.init 0 8 8).eval (envB σ m) + (Sym.init 0 16 8).eval (envB σ m) = _
    rw [e8, e16, w_40]
  have hn11 : (m'.reg 11).toNat = entrySize * grownCap o.done.length := by
    rw [e11]; simp only [w, BitVec.toNat_ofNat, entrySize]; omega
  have hsite : Site3d0 σ L m' := ⟨o, k, kp', hED', hG',
    (hr 27 (by simp)).trans ((rk 27 (by simp)).trans h27), r22.trans e24,
    by simp only [Sym.eval] at r1; exact r1, fun t ht => by
      simp only [List.length_cons, List.length_nil] at ht
      obtain rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
      · exact r10.trans e40
      · exact e11
      · simp only [Sym.eval] at r12; exact r12
      · exact r13.trans ((envB_var σ m 19).trans hcm.2.2.2.2.2.2.2.1)⟩
  obtain ⟨hstk, hcf⟩ := callee_frame hc' hED'.2.2.2.2.1
  have hpre2 : allocPre σ.A L m' := ⟨hED'.2.2.2.2.1.1,
    by rw [hn11]; simp only [entrySize, grownCap]; omega,
    by rw [hn11]; simp only [entrySize]; omega,
    by simp only [Sym.eval] at r12; rw [r12]; decide, hstk,
    by unfold RetAligned; simp only [Sym.eval] at r1; rw [r1]; decide, hcf⟩
  refine ⟨allocC, L, rfl, hex, hpre2, fun m'' hpost => ⟨cut3d4, by simp [TX.plan, vcPlan],
    rfl, ?_, ⟨m', L, hsite, hpost⟩, ?_⟩⟩
  · rw [hpost.1.1.1]; simp only [Sym.eval] at r1; rw [r1]; decide
  · have h21 : m''.reg 21 = m.reg 21 := (hpost.1.1.2 21 (by decide)).trans (hr 21 (by simp))
    have h26 : m''.reg 26 = m.reg 26 := (hpost.1.1.2 26 (by decide)).trans (hr 26 (by simp))
    show 53 + bTail m'' 389 ≤ bTail m 478 - _
    rw [hsteps]; unfold bTail afterEntry; rw [h21, h26]; omega

end ZesuExec.Fn.TX
