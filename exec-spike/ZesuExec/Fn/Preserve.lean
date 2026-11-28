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
  case lb | lbu | lhu | lw | ld | lwu | lh =>
    simp only [Machine.exec, Machine.loadInto, Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact Preserved.of_mem_eq (by simp [Machine.advance, setReg_mem'])
  case jal | jalr =>
    simp only [Machine.exec] at h
    exact Preserved.of_mem_eq ((jumpTo_mem h).trans (setReg_mem' _ _ _))
  case beq | bne | blt | bltu | bgeu | bge =>
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

/-! ## Service steps are framed (`SvcEffect.Framed`) -/
theorem mem_rangeMap {d n x : Nat} : x ∈ (List.range n).map (d + ·) ↔ d ≤ x ∧ x < d + n := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩; omega
  · intro h; exact ⟨x - d, by omega, by omega⟩

theorem present_get {mem : Word → Option Byte} {a n : Nat} (h : present mem a n = true) {t : Nat}
    (ht : t < n) : (mem (BitVec.ofNat 64 (a + t))).isSome :=
  readBytes_isSome_get (by simpa [present] using h) t ht

theorem writable_bounds {a n : Nat} (h : writable a n = true) :
    Layout.ramLo ≤ a ∧ a + n ≤ Layout.ramHi := by
  simpa [writable, inRange] using h

theorem ofNat_toNat' (x : Word) : BitVec.ofNat 64 x.toNat = x := by simp

theorem memsetEffect_framed {m : Machine} {d n : Nat} {b : Byte} {len : Nat} {e : SvcEffect}
    (h : memsetEffect m d n b len = some e) : e.Framed m := by
  unfold memsetEffect at h
  split at h
  · rename_i hc
    cases h
    refine ⟨fun x hx => ?_, fun a ha => ?_, fun x hx => ?_⟩
    · simp only [fillMem]; rw [if_neg]; rwa [mem_rangeMap] at hx
    · rw [mem_rangeMap] at ha
      simp only [Bool.or_eq_true, beq_iff_eq, dstOk, Bool.and_eq_true] at hc
      rcases hc with hc | ⟨hw, -⟩
      · omega
      · have := writable_bounds hw; simp only [Layout.ramLo, Layout.ramHi] at this ⊢; omega
    · simp only [fillMem]; split <;> simp_all
  · cases h

theorem copyMem_framed {mem : Word → Option Byte} {d s n : Nat}
    (hsrc : n = 0 ∨ present mem s n = true) :
    ∀ x : Word, (mem x).isSome → (copyMem mem d s n x).isSome := by
  intro x hx
  simp only [copyMem]
  split
  · rename_i hc
    rcases hsrc with h0 | hp
    · exact absurd h0 hc.1
    · have := present_get hp (t := x.toNat - d) (by omega)
      rwa [show s + (x.toNat - d) = s + x.toNat - d by omega] at this
  · exact hx

theorem csr813_framed {img : Image} {m : Machine} {e : SvcEffect} (h : csr813 img m = some e) :
    e.Framed m := by
  unfold csr813 at h
  split at h
  · rename_i w0 w1 _ _
    split at h
    dsimp only at h
    · split at h
      · split at h
        · rename_i hd
          cases h
          simp only [dmaMemcpyDomain, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hd
          obtain ⟨⟨hew, hep⟩, hn⟩ := hd
          have heb := writable_bounds hew
          refine ⟨fun x hx => ?_, fun a ha => ?_, fun x hx => ?_⟩
          · simp only [List.mem_append, mem_rangeMap, not_or] at hx
            simp only [dmaMemcpyMem]
            rw [if_neg (by omega), if_neg (by omega), ofNat_toNat']
          · simp only [List.mem_append, mem_rangeMap] at ha
            simp only [Layout.ramLo, Layout.ramHi, Layout.extraParams] at heb ha ⊢
            rcases ha with ha | ha
            · omega
            · rcases hn with hn | ⟨⟨⟨-, -⟩, hw⟩, -⟩
              · omega
              · have := writable_bounds hw
                simp only [Layout.ramLo, Layout.ramHi] at this; omega
          · simp only [dmaMemcpyMem]
            split
            · rename_i hc
              split
              · simp
              · rcases hn with hn | ⟨⟨⟨-, hp⟩, -⟩, -⟩
                · exact absurd hn hc.1
                · have := present_get hp (t := x.toNat - (m.reg (Decode.reg w1 15)).toNat)
                    (by omega)
                  rwa [show (m.reg (Decode.reg w0 15)).toNat +
                      (x.toNat - (m.reg (Decode.reg w1 15)).toNat) =
                      (m.reg (Decode.reg w0 15)).toNat + x.toNat -
                      (m.reg (Decode.reg w1 15)).toNat by omega] at this
            · split
              · simp
              · rw [ofNat_toNat']; exact hx
        · cases h
      · split at h
        · split at h
          · rename_i hd
            cases h
            simp only [Bool.or_eq_true, beq_iff_eq, srcOk, dstOk, Bool.and_eq_true] at hd
            refine ⟨fun x hx => ?_, fun a ha => ?_, ?_⟩
            · rw [mem_rangeMap] at hx
              simp only [copyMem]; rw [if_neg (by omega)]
            · rw [mem_rangeMap] at ha
              rcases hd with hd | ⟨-, hw, -⟩
              · omega
              · have := writable_bounds hw
                simp only [Layout.ramLo, Layout.ramHi] at this ⊢; omega
            · exact copyMem_framed (by rcases hd with hd | ⟨⟨-, hp⟩, -⟩ <;> simp_all)
          · cases h
        · cases h
    · cases h
  · cases h

theorem csr816_framed {img : Image} {m : Machine} {e : SvcEffect} (h : csr816 img m = some e) :
    e.Framed m := by
  unfold csr816 at h
  split at h
  · split at h
    · split at h
      · exact memsetEffect_framed h
      · cases h
    · split at h
      · split at h
        · split at h
          · exact memsetEffect_framed h
          · cases h
        · cases h
      · cases h
  · cases h

theorem csr805_framed {img : Image} {m : Machine} {e : SvcEffect} (h : csr805 img m = some e) :
    e.Framed m := by
  unfold csr805 at h
  split at h
  · split at h
    dsimp only at h
    · split at h
      · split at h
        · split at h
          · split at h
            · rename_i hd _ _ _ _ _ _
              cases h
              simp only [dstOk, srcOk, Bool.and_eq_true] at hd
              obtain ⟨-, -, ⟨hw, hp⟩, -⟩ := hd
              refine ⟨fun x hx => ?_, fun a ha => ?_, fun x hx => ?_⟩
              · rw [mem_rangeMap] at hx
                simp only [putBytes]; rw [if_neg (by omega)]
              · rw [mem_rangeMap] at ha
                have := writable_bounds hw
                simp only [Layout.ramLo, Layout.ramHi] at this ⊢; omega
              · simp only [putBytes]; split <;> simp_all
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem csrF12_framed {img : Image} {m : Machine} {e : SvcEffect} (h : csrF12 img m = some e) :
    e.Framed m := by
  unfold csrF12 at h
  split at h
  · split at h
    · split at h
      · cases h
        exact ⟨fun _ _ => rfl, fun _ ha => absurd ha (by simp), fun _ hx => hx⟩
      · cases h
    · cases h
  · cases h

theorem svc_framed {img : Image} {m : Machine} {e : SvcEffect} (h : svc img m = some e) :
    e.Framed m := by
  unfold svc at h
  cases h1 : csr813 img m with
  | some e1 => simp [h1] at h; subst h; exact csr813_framed h1
  | none =>
    cases h2 : csr816 img m with
    | some e2 => simp [h1, h2] at h; subst h; exact csr816_framed h2
    | none =>
      cases h3 : csr805 img m with
      | some e3 => simp [h1, h2, h3] at h; subst h; exact csr805_framed h3
      | none => simp [h1, h2, h3] at h; exact csrF12_framed h

/-- A framed service step preserves present bytes and everything below RAM. -/
theorem framed_preserved {e : SvcEffect} {m : Machine} (h : e.Framed m) :
    Preserved m (e.apply m) := by
  refine ⟨fun a ha => h.2.2 a ha, fun a ha => h.1 a fun hx => ?_⟩
  have := (h.2.1 _ hx).1; omega

theorem next_preserved {img : Image} {m m' : Machine} {c : Nat} (h : next img m = some (m', c)) :
    Preserved m m' := by
  unfold next at h
  split at h
  · cases hz : ziskMemcpy m with
    | none => simp [hz] at h
    | some m₁ => simp [hz] at h; obtain ⟨rfl, -⟩ := h; exact memcpy_preserved hz
  · cases hs : step img m with
    | none =>
      simp only [hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨e, he, rfl, -⟩ := h
      exact framed_preserved (svc_framed he)
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
