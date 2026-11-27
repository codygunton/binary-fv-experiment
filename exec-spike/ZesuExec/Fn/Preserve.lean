import ZesuExec.Sym.MemLemmas

/-!
# What every machine run preserves

No step makes a present byte absent, and no step writes below RAM (stores and the `memcpy`
service write RAM only). `Reaches.preserve` adds both facts to any `Reaches` conclusion, so a
caller learns them about a callee whose contract does not state them.
-/

namespace ZesuExec.Fn
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- `m'` keeps every byte present in `m` and every byte below RAM. -/
def Preserved (m m' : Machine) : Prop :=
  (∀ a, (m.mem a).isSome → (m'.mem a).isSome) ∧ (∀ a : Word, a.toNat < Layout.ramLo → m'.mem a = m.mem a)

theorem Preserved.refl (m : Machine) : Preserved m m := ⟨fun _ h => h, fun _ _ => rfl⟩

theorem Preserved.trans {m₁ m₂ m₃ : Machine} (h₁ : Preserved m₁ m₂) (h₂ : Preserved m₂ m₃) :
    Preserved m₁ m₃ :=
  ⟨fun a h => h₂.1 a (h₁.1 a h), fun a ha => (h₂.2 a ha).trans (h₁.2 a ha)⟩

theorem Preserved.of_mem_eq {m m' : Machine} (h : m'.mem = m.mem) : Preserved m m' :=
  ⟨fun a ha => h ▸ ha, fun a _ => by rw [h]⟩

theorem readBytes_isSome_get {mem : Word → Option Byte} :
    ∀ {a n : Nat}, (readBytes mem a n).isSome → ∀ t < n, (mem (BitVec.ofNat 64 (a + t))).isSome
  | _, 0, _, t, ht => absurd ht (Nat.not_lt_zero _)
  | a, n + 1, h, t, ht => by
    simp only [readBytes] at h
    cases hb : mem (BitVec.ofNat 64 a) with
    | none => simp [hb] at h
    | some b =>
      cases hr : readBytes mem (a + 1) n with
      | none => simp [hb, hr] at h
      | some rest =>
        cases t with
        | zero => simp [hb]
        | succ t =>
          have := readBytes_isSome_get (a := a + 1) (n := n) (by rw [hr]; rfl) t (by omega)
          rwa [show a + 1 + t = a + (t + 1) by omega] at this

theorem store_preserved {m m' : Machine} {a v : Word} {n : Nat} (h : m.store a n v = some m') :
    Preserved m m' := by
  unfold Machine.store at h
  split at h
  · next hc =>
    obtain ⟨hw, _⟩ := hc
    cases h
    have hw' : Layout.ramLo ≤ a.toNat ∧ a.toNat + n ≤ Layout.ramHi := by
      simpa [writable, inRange] using hw
    have hA : a.toNat + n ≤ 2 ^ 64 := by unfold Layout.ramHi at hw'; omega
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only
      rw [writeBytes_apply hA]
      split <;> simp_all
    · simp only
      rw [writeBytes_apply hA, if_neg (by omega)]
  · simp at h

theorem setReg_mem' (m : Machine) (i : Fin 32) (v : Word) : (m.setReg i v).mem = m.mem := by
  unfold Machine.setReg; split <;> rfl

theorem jumpTo_mem {m m' : Machine} {t : Word} (h : m.jumpTo t = some m') : m'.mem = m.mem := by
  unfold Machine.jumpTo at h; split at h <;> simp at h; subst h; rfl

theorem exec_preserved {m m' : Machine} {i : Instr} (h : m.exec i = some m') : Preserved m m' := by
  cases i
  case sb | sh | sw | sd =>
    simp only [Machine.exec, Machine.storeFrom, Option.map_eq_some_iff] at h
    obtain ⟨m₁, hs, rfl⟩ := h
    exact (store_preserved hs).trans (Preserved.of_mem_eq rfl)
  case lb | lbu | lhu | lw | ld =>
    simp only [Machine.exec, Machine.loadInto, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact Preserved.of_mem_eq (by simp [Machine.advance, setReg_mem'])
  case jal | jalr =>
    simp only [Machine.exec] at h
    exact Preserved.of_mem_eq ((jumpTo_mem h).trans (setReg_mem' _ _ _))
  case beq | bne | blt | bltu | bgeu =>
    simp only [Machine.exec, Machine.branch] at h
    split at h
    · exact Preserved.of_mem_eq (jumpTo_mem h)
    · cases h; exact Preserved.of_mem_eq rfl
  all_goals
    simp only [Machine.exec, Machine.writeReg, Option.some.injEq] at h
    subst h
    exact Preserved.of_mem_eq (by simp [Machine.advance, setReg_mem'])

theorem memcpy_preserved {m m' : Machine} (h : ziskMemcpy m = some m') : Preserved m m' := by
  unfold ziskMemcpy at h
  split at h
  · next hd =>
    cases h
    simp only [ziskMemcpyDomain, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hd
    obtain ⟨-, hcopy⟩ := hd
    have hep : Layout.ramLo ≤ Layout.extraParams := by decide
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [ziskMemcpyMem]
      split
      · next hin =>
        split
        · rfl
        · rcases hcopy with h0 | ⟨⟨⟨_, hps⟩, _⟩, _⟩
          · exact absurd h0 hin.1
          · have := readBytes_isSome_get hps (x.toNat - (m.reg 10).toNat) (by omega)
            rwa [show (m.reg 11).toNat + (x.toNat - (m.reg 10).toNat) =
              (m.reg 11).toNat + x.toNat - (m.reg 10).toNat by omega] at this
      · split
        · rfl
        · simpa using hx
    · simp only [ziskMemcpyMem]
      have hx' : x.toNat < Layout.extraParams := by omega
      rw [if_neg, if_neg (by omega)]
      · simp
      · rintro ⟨h0, -, hdx, -⟩
        rcases hcopy with h | ⟨⟨-, hw⟩, -⟩
        · exact h0 h
        · simp [writable, inRange] at hw; omega
  · simp at h

theorem next_preserved {img : Image} {m m' : Machine} {c : Nat} (h : next img m = some (m', c)) :
    Preserved m m' := by
  unfold next at h
  split at h
  · cases hz : ziskMemcpy m with
    | none => simp [hz] at h
    | some m₁ => simp [hz] at h; obtain ⟨rfl, -⟩ := h; exact memcpy_preserved hz
  · cases hs : step img m with
    | none => simp [hs] at h
    | some m₁ =>
      simp [hs] at h; obtain ⟨rfl, -⟩ := h
      unfold step at hs
      split at hs
      · split at hs
        · split at hs
          · exact exec_preserved hs
          · simp at hs
        · simp at hs
      · simp at hs

theorem _root_.ZesuExec.RunsIn.preserved {img : Image} {k : Nat} {m m' : Machine} (h : RunsIn img k m m') :
    Preserved m m' := by
  induction h with
  | refl => exact Preserved.refl _
  | step hn _ ih => exact (next_preserved hn).trans ih

theorem Reaches.preserve {img : Image} {b : Nat} {Q : Machine → Prop} {m : Machine}
    (h : Reaches img b Q m) : Reaches img b (fun m' => Q m' ∧ Preserved m m') m := by
  obtain ⟨k, m', hk, hr, hq⟩ := h
  exact ⟨k, m', hk, hr, hq, hr.preserved⟩

end ZesuExec.Fn
