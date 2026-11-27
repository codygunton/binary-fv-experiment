import ZesuExec.Fn.F0.Regions

namespace ZesuExec.Fn.F0
open ZesuExec ZesuExec.Sym

sym_run run0 := run zesuImage [] 20 entry S0

theorem f0_spec : Spec zesuImage entry bound Pre Post := by
  intro m hpc ⟨hro, ⟨hal, hlo, hhi, hpres⟩, hra⟩
  have hsp : (m.reg 2 - 16).toNat = (m.reg 2).toNat - 16 := by
    have h16 : (16 : Word).toNat = 16 := rfl
    rw [BitVec.toNat_sub, h16]; unfold Layout.ramLo at hlo; omega
  have hwf : Env.WF (entryEnv m ((shape m).map (·.1))) S0 :=
    entry_wf (shape m) (by
      simp only [shape, List.mem_singleton, forall_eq, RegionOk, frame]
      refine ⟨by simp, by rw [hsp]; omega, ?_⟩
      simp [Machine.writable, Machine.inRange, hsp]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega)
      (by simp [shape])
  have hm : Match (entryEnv m ((shape m).map (·.1))) S0 m := by
    refine entry_match (fun i hi s hs => ?_) (fun r j hr hj => ?_) (by simp)
    · simp only [ov] at hs
      split at hs
      · next h2 =>
        cases hs
        have : i = 2 := Fin.ext h2
        subst this
        simp [Sym.eval, Env.base, entryEnv, shape, BitVec.sub_add_cancel]
      · simp at hs
    · simp [frame] at hr; subst hr
      simp [entryEnv, Env.size, shape] at hj
      simpa [Env.base, entryEnv, shape] using hpres j hj
  obtain ⟨l, hl, -, hr⟩ := run_sound run0 hwf hm hpc hro
  simp at hl; subst hl
  obtain ⟨m', hrun, hm', hex, hfr⟩ := hr (by simpa [Oblig.holds, Sym.eval, entryEnv] using hra)
  refine ⟨9, m', Nat.le_refl _, by simpa [S0, entryState] using hrun, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [ExitOk, Sym.eval, BinOp.eval, entryEnv] using hex
  · intro i hi
    rw [← hm'.regs i]
    simp [calleeSaved] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | rfl
        | (show (m.reg 2 - 16) + BitVec.ofInt 64 16 = m.reg 2
           simp [BitVec.sub_add_cancel])
  · rw [← hm'.regs 10]; rfl
  · refine SameOutside.mono hfr fun a ha => ?_
    obtain ⟨p, hp, -, hin⟩ := inWritable_entry ha (by
      simp [shape]; simp [Layout.ramHi] at hhi; omega)
    simp [shape] at hp; subst hp
    exact hin

end ZesuExec.Fn.F0
