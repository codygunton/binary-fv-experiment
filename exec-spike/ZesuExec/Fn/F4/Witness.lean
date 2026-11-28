import ZesuExec.Fn.F4.Lemmas

/-!
# `ToOwned.Pre` is satisfiable

Given the allocator's assumptions `A`, a machine `m0` with the allocator state `A.Heap [] m0` and
the image's rodata loaded, and a 4 KiB window of RAM at `0xa0000000` (which contains the memcpy
staging word `Layout.extraParams = 0xa0000f00`) outside the allocator's memory `A.Priv []`, the
machine `wit m0` satisfies `Pre eb A [] []` for every element size `eb`: it is `m0` with the window
overwritten by an empty list `{items.ptr = 1, 0, 0}` at `0xa0000300`, an allocator object
`{0, vtable}` at `0xa0000400`, a 24-byte result at `0xa0000200`, and the stack below
`sp = 0xa0000100`.
-/

namespace ZesuExec.Fn.ToOwned
open ZesuExec ZesuExec.Sym ZesuExec.Machine

/-- The window `[0xa0000000, 0xa0001000)`. -/
def Win (a : Word) : Prop := 0xa0000000 ≤ a.toNat ∧ a.toNat < 0xa0001000

instance (a : Word) : Decidable (Win a) := inferInstanceAs (Decidable (_ ∧ _))

/-- The window's bytes: `items.ptr = 1` at `0xa0000300`, the vtable address at `0xa0000408`. -/
def winByte (a : Nat) : Byte :=
  if a = 0xa0000300 then 1 else if a = 0xa0000408 then 0xd8 else if a = 0xa0000409 then 0x36
  else if a = 0xa000040a then 0x11 else if a = 0xa000040b then 0x80 else 0

def witRegs (i : Fin 32) : Word :=
  if i.val = 1 then 0x80000000 else if i.val = 2 then 0xa0000100 else if i.val = 10 then 0xa0000200
  else if i.val = 11 then 0xa0000300 else if i.val = 12 then 0xa0000400 else 0

/-- The window alone (a closed machine, for evaluating loads). -/
def winMachine : Machine := ⟨witRegs, 0, fun a => some (winByte a.toNat)⟩

def wit (m0 : Machine) : Machine :=
  ⟨witRegs, 0, fun a => if Win a then some (winByte a.toNat) else m0.mem a⟩

theorem wit_load (m0 : Machine) {a : Word} {n : Nat}
    (h : ∀ t < n, Win (a + BitVec.ofNat 64 t)) : (wit m0).load a n = winMachine.load a n :=
  load_congr fun t ht => by simp [wit, winMachine, h t ht]

theorem wit_win (m0 : Machine) {a : Word} (h : Win a) : ((wit m0).mem a).isSome := by
  simp [wit, h]

theorem win_add {a : Word} {k n t : Nat} (ha : a.toNat = k) (hk : 0xa0000000 ≤ k)
    (hn : k + n ≤ 0xa0001000) (ht : t < n) : Win (a + BitVec.ofNat 64 t) := by
  unfold Win; rw [toNat_add_ofNat (by omega), ha]; omega

theorem pre_satisfiable (eb : Nat) (A : AllocAssumptions zesuImage) (m0 : Machine)
    (h0 : A.Heap [] m0) (hro : RodataLoaded zesuImage m0)
    (hwin : ∀ a, Win a → ¬ A.Priv [] a) : Pre eb A [] [] (wit m0) := by
  have r2 : (wit m0).reg 2 = 0xa0000100 := rfl
  have r10 : (wit m0).reg 10 = 0xa0000200 := rfl
  have r11 : (wit m0).reg 11 = 0xa0000300 := rfl
  have r12 : (wit m0).reg 12 = 0xa0000400 := rfl
  have lp : (wit m0).load 0xa0000300 8 = some 1 := by
    rw [wit_load m0 fun t ht => win_add (k := 0xa0000300) rfl (by decide) (by decide) ht]; decide
  have ln : (wit m0).load (0xa0000300 + 8) 8 = some 0 := by
    rw [wit_load m0 fun t ht => win_add (k := 0xa0000308) rfl (by decide) (by decide) ht]; decide
  have lc : (wit m0).load (0xa0000300 + 16) 8 = some 0 := by
    rw [wit_load m0 fun t ht => win_add (k := 0xa0000310) rfl (by decide) (by decide) ht]; decide
  have lctx : (wit m0).load 0xa0000400 8 = some 0 := by
    rw [wit_load m0 fun t ht => win_add (k := 0xa0000400) rfl (by decide) (by decide) ht]; decide
  have lvt : (wit m0).load (0xa0000400 + 8) 8 = some (BitVec.ofNat 64 vtable) := by
    rw [wit_load m0 fun t ht => win_add (k := 0xa0000408) rfl (by decide) (by decide) ht]; decide
  have hp : listPtr (wit m0) = 1 := by unfold listPtr wordAt; rw [r11, lp]; rfl
  have hn : listLen (wit m0) = 0 := by unfold listLen wordAt; rw [r11, ln]; rfl
  have hc : listCap (wit m0) = 0 := by unfold listCap wordAt; rw [r11, lc]; rfl
  have present : ∀ (a : Word) (k n : Nat), a.toNat = k → 0xa0000000 ≤ k → k + n ≤ 0xa0001000 →
      Present (wit m0) a n := fun a k n ha hk hn t ht => wit_win m0 (win_add ha hk hn ht)
  have inWin : ∀ (a : Word) (k n : Nat) (x : Word), a.toNat = k → 0xa0000000 ≤ k →
      k + n ≤ 0xa0001000 → InRange a n x → Win x := by
    intro a k n x ha hk hn hx; unfold InRange at hx; unfold Win; omega
  refine ⟨?_, ?_, by unfold RetAligned; rw [show (wit m0).reg 1 = 0x80000000 from rfl]; decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have ha := zesu_rodata_low h; unfold Layout.ramLo at ha
    have hw : ¬ Win (BitVec.ofNat 64 a) := by
      unfold Win; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    simp only [wit, hw, if_false]; exact hro a b h
  · refine ⟨by rw [r2]; decide, by rw [r2]; decide, by rw [r2]; decide, ?_⟩
    rw [r2]; exact present _ 0xa0000090 112 (by decide) (by decide) (by decide)
  · rw [r10]; unfold RamRange Layout.ramLo Layout.ramHi; decide
  · rw [r10]; decide
  · rw [r10]; exact present _ 0xa0000200 24 rfl (by decide) (by decide)
  · rw [r11]; unfold RamRange Layout.ramLo Layout.ramHi; decide
  · rw [r11]; decide
  · rw [hp, hn, hc, r11]; exact ⟨lp, ln, lc⟩
  · rw [hn, hc]; exact Nat.le_refl _
  · simp [hn]
  · rw [hp]; decide
  · intro h; rw [hc] at h; exact absurd h (by decide)
  · intro i hi; simp at hi
  · rw [r12]; unfold RamRange Layout.ramLo Layout.ramHi; decide
  · rw [r12]; decide
  · rw [r12, lctx]; rfl
  · rw [r12]; exact lvt
  · exact present _ 0xa0000f00 8 rfl (by decide) (by decide)
  · exact A.heap_frame [] m0 _ h0 (fun a ha => by
      have : ¬ Win a := fun hw => hwin a hw ha
      simp [wit, this]) (by simp)
  all_goals first
    | (simp only [Apart, r2, r10, r11, r12, scratch, Layout.extraParams]; decide)
    | skip
  · intro h; rw [hc] at h; simp at h
  intro a ha
  apply hwin
  rw [r2, r10, r11, r12] at ha
  rcases ha with h | h | h | h | h
  · exact inWin _ 0xa0000200 24 a rfl (by decide) (by decide) h
  · exact inWin _ 0xa0000300 24 a rfl (by decide) (by decide) h
  · exact inWin _ 0xa0000400 16 a rfl (by decide) (by decide) h
  · exact inWin _ 0xa0000090 112 a (by decide) (by decide) (by decide) h
  · exact inWin _ 0xa0000f00 8 a rfl (by decide) (by decide) h

end ZesuExec.Fn.ToOwned
