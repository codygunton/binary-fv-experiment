import ZesuExec.Fn.TX.Leaves2

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
  refine ⟨nil_obligs (by decide), by show _ ≤ bTail m 389; unfold bTail; omega, ?_⟩
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

theorem shl40 {x : Word} (hx : x.toNat < 2 ^ 32) :
    x <<< ((5#64).toNat % 64) + x <<< ((3#64).toNat % 64) = w (entrySize * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    show (5#64).toNat % 64 = 5 from rfl, show (3#64).toNat % 64 = 3 from rfl,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp only [w, BitVec.toNat_ofNat, entrySize]
  omega

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
  refine ⟨nil_obligs (by decide), by show _ ≤ bTail m 377; unfold bTail; omega, ?_⟩
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
    rw [r12, ← shl40 hc32, ← h27]; rfl
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
  obtain ⟨hle', hp0, hc0, hc32, hram', hil, hbytes, hz⟩ := hEL
  have h20 : ∀ t < (itemPayload (ent σ o k) k.ah 20).length, t < 20 := fun t ht => by
    simp only [itemPayload, List.length_take] at ht; omega
  refine ⟨hcm, ⟨hok.1, hok.2.1, ?_, ?_, hok.2.2.2.2⟩,
    ⟨(hr 20 (by decide)).trans r20, (hr 21 (by decide)).trans r21, hi,
      (load_congr fun t ht => l0 t ht).trans hmag⟩,
    ⟨hle', hp0, hc0, hc32, hram', hil, ?_, fun x hx => ?_⟩,
    hl, ⟨hd, hle, (hr 26 (by decide)).trans r26⟩,
    ⟨had, hal, bytes_congr hA fun t ht => l2 t (h20 t ht)⟩, hkl, hkw, hram, ?_, hkeys⟩
  · rw [load_congr fun t ht => hrest t (by omega)]; exact hok.2.2.1
  · rw [load_congr (m := mc) fun t ht => by
      rw [show σ.rest + 8 + BitVec.ofNat 64 t = σ.rest + BitVec.ofNat 64 (8 + t) by bv_omega]
      exact hrest _ (by omega)]
    exact hok.2.2.2.1
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
        simp only [EX, List.mem_append]; exact .inl (.inr (mem_keysBlocks hx hk))) t
        (by rw [flatten_length _ hkl'] at ht; exact ht)
  · by_cases hk : k.keys = []
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

/-- Frame ranges `S-k` of `n` bytes and `S-k'` of `n'` bytes that do not meet. -/
theorem fr_apart {σ : Sig} (hpre : Pre σ.A σ.g σ.m) {k n k' n' : Nat} {a : Word} (hk : k ≤ 704)
    (hk' : k' ≤ 704) (hd : k' + n ≤ k ∨ k + n' ≤ k') (h : InRange (σ.sl k) n a)
    (h' : InRange (σ.sl k') n' a) : False := by
  have h1 := sl_toNat hpre (k := k) hk
  have h2 := sl_toNat hpre (k := k') hk'
  have hlo := (entry_nums hpre).1; unfold Layout.ramLo at hlo
  simp only [InRange, h1, h2] at h h'; omega

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
  refine ⟨nil_obligs (by decide), by show _ ≤ bTail m 324; unfold bTail; omega, ?_⟩
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
        exact fr_apart hpre (by decide) (by decide) (by decide)
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
    refine bytes_congr hB fun t ht => hso _ fun h => fr_apart hpre (k := 0xa0) (n := 20)
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

end ZesuExec.Fn.TX
