import ZesuExec.Fn.Alloc.AllocCuts

/-! # `alloc`: assembling `AllocPost` at a return -/

namespace ZesuExec.Fn.Alloc
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

theorem returns_of {g : Sig} {m' : Machine} (hK : Keep g m')
    (hpc : m'.pc = g.m.reg 1 &&& ~~~(1 : Word)) : Returns g.m m' :=
  ⟨hpc, fun i hi => hK i (by
    simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)⟩

/-- The return target `ra & ~1` of a leaf is the entry's and is aligned. -/
theorem ret_target {g : Sig} {m : Machine} {env : Env} (hv : env.vars 1 = m.reg 1) (hK : Keep g m) :
    (Sym.bin .and (.var 1) (.lit 18446744073709551614)).eval env = g.m.reg 1 &&& ~~~(1 : Word) := by
  simp only [Sym.eval, BinOp.eval, hv, notOne]
  rw [hK 1 (by decide)]

theorem ret_oblig {g : Sig} {m : Machine} {env : Env} (hv : env.vars 1 = m.reg 1) (hK : Keep g m)
    (hpre : AllocPre g.L g.m) :
    (Oblig.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4).holds env := by
  simp only [Oblig.holds]; rw [ret_target hv hK]; exact hpre.2.2.2.2.2.1

theorem post_null {g : Sig} {m' : Machine} (hret : Returns g.m m')
    (hso : SameOutside (fun a => Priv g.L a ∨ InRange (g.m.reg 2 - 16) 16 a) g.m m')
    (h10 : m'.reg 10 = 0) (hh : Heap g.L m') : AllocPost g.L g.m m' :=
  ⟨hret, hso, .inl ⟨h10, hh⟩⟩

theorem post_block {g : Sig} {m' : Machine} (hret : Returns g.m m')
    (hso : SameOutside (fun a => Priv g.L a ∨ InRange (g.m.reg 2 - 16) 16 a) g.m m') {q : Nat}
    (h10 : m'.reg 10 = BitVec.ofNat 64 q) (hq : heapLo ≤ q) (hqe : q + lenOf g < 2 ^ 64)
    (hh : Heap (g.L ++ [(BitVec.ofNat 64 q, lenOf g)]) m')
    (hfresh : ∀ t < lenOf g, Priv g.L (BitVec.ofNat 64 (q + t))) : AllocPost g.L g.m m' := by
  have hmem : (BitVec.ofNat 64 q, lenOf g) ∈ g.L ++ [(BitVec.ofNat 64 q, lenOf g)] := by simp
  obtain ⟨hram, hpres⟩ := (live_ok _ _ hh).2 _ hmem
  refine ⟨hret, hso, .inr ⟨?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_⟩⟩
  · rw [h10]; intro h0
    have := congrArg BitVec.toNat h0
    rw [toNat_ofNat_lt (by omega)] at this; unfold heapLo at hq; simp at this; omega
  · rw [h10]; exact hh
  · rw [h10]; exact hram
  · rw [h10]; exact hpres
  · rw [h10] at ha
    obtain ⟨t, ht, rfl⟩ := inRange_lit hqe ha
    exact hfresh t ht
  · rw [h10] at ha; exact priv_append ha

end ZesuExec.Fn.Alloc
