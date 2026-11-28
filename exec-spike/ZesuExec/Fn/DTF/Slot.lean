import ZesuExec.Fn.DTF.HashSlot

/-!
# DTF: leaves from a buffer-store cut (programme plan S7 step 4)

At `0x80002138` (`0x80002434`) region 4 is the slot `a0` of a list buffer, one of DTF's blocks.
A leaf from there stores into it, so its writes are DTF's frame below the save area, the result,
or the slot (`writesLowS`); the slot lies in a live block, so the heap and `Common` survive
(`common_slot`). Frame words no write covers keep their values (`slot_word_keep`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-- Every write of `S` is a frame word below the save area, in the result, or in the slot. -/
def writesLowS (S : SState) : Bool :=
  S.mem.all fun w =>
    (w.r == 0 && decide (w.off + w.n ≤ frameBytes - 104)) || w.r == 1 || w.r == 4

theorem writesLowS_nocover {S : SState} (h : writesLowS S = true) {j : Nat}
    (hj : frameBytes - 104 ≤ j) : S.mem.find? (·.covers 0 j) = none := by
  rw [List.find?_eq_none]
  intro w hw hcov
  simp only [writesLowS, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have := h w hw
  simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcov
  omega

/-- The store slot region. -/
abbrev slotR (n : Nat) : Region := ⟨some n, 1, true⟩

/-- An address of a writable region of a store cut's state: DTF's own, or the slot. -/
theorem inWritable_slot {sh : Shape} {σ : Sig} {m : Machine} {S : SState}
    (hpre : Pre σ.A σ.g σ.m) {n : Nat} (hS : S.regions = baseRegions ++ [slotR n])
    (hx : sh.extra = [slotR n]) (hram : RamRange (m.reg 10) n) {a : Word}
    (h : InWritable (envOf sh σ m) S a) : Owned σ a ∨ InRange (m.reg 10) n a := by
  obtain ⟨r, R, j, hR, hwr, hj, rfl⟩ := h
  rw [hS] at hR
  by_cases hr : r < 4
  · rw [List.getElem?_append_left (by simpa [baseRegions] using hr)] at hR
    exact .inl (inWritable_owned (S := { S with regions := baseRegions }) hpre rfl
      ⟨r, R, j, hR, hwr, hj, rfl⟩).1
  · rw [List.getElem?_append_right (by simp [baseRegions]; omega)] at hR
    have hr4 : r = 4 := by
      have hl : baseRegions.length = 4 := rfl
      rw [hl] at hR
      rcases hk : r - 4 with _ | k
      · omega
      · rw [hk] at hR; simp at hR
    subst hr4
    rw [env_size4 _ hx] at hj
    rw [env_base4 _ hx]
    unfold RamRange Layout.ramHi at hram
    exact .inr (inRange_self (by omega) (by simpa using hj))

/-- `Common` and the live list at the end of a leaf from a store cut: it keeps present bytes,
writes DTF's own memory or the slot, of the frame only words below the save area; the slot lies
in a live block of `L`. -/
theorem common_slot {sh : Shape} {σ : Sig} {m m' : Machine} {S S' : SState} {n : Nat}
    (hc : Common σ m) (hS : S.regions = baseRegions ++ [slotR n]) (hx : sh.extra = [slotR n])
    (hp : Preserved m m') (hm' : Match (envOf sh σ m) S' m') (h0 : 0 < S'.regions.length)
    (hso : SameOutside (InWritable (envOf sh σ m) S) m m') (hlow : writesLowS S' = true)
    (hslot : SlotOk σ m n) {L X : List (Word × Nat)} (hlive : Live σ m L X)
    (hin : ∀ a, InRange (m.reg 10) n a → InLive L a) : Common σ m' ∧ Live σ m' L X := by
  have hpre := hc.2.1
  let R : Word → Prop := fun a => InWritable (envOf sh σ m) S a ∧ ¬ InRange (σ.S - w 104) 104 a
  have hso' : SameOutside R m m' := fun a ha => by
    by_cases hw : InWritable (envOf sh σ m) S a
    · have hin' : InRange (σ.S - w 104) 104 a :=
        Classical.byContradiction fun h => ha ⟨hw, h⟩
      have h1 := S_sub_toNat hpre (k := 104) (by decide)
      have hfr := fr_toNat hpre
      have hsp := pre_sp hpre
      simp only [InRange, h1] at hin'
      have ha' : a = σ.fr + BitVec.ofNat 64 (a.toNat - σ.fr.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_add_ofNat (by unfold Layout.ramHi frameBytes stackBytes TX.stackBytes at *; omega)]
        unfold frameBytes stackBytes TX.stackBytes at *; omega
      rw [ha']
      exact frame_byte_keep' hc.avail hm' h0 (by unfold frameBytes stackBytes TX.stackBytes at *; omega)
        (writesLowS_nocover hlow (by unfold frameBytes stackBytes TX.stackBytes at *; omega))
    · exact hso a hw
  have hown := fun a (h : InWritable (envOf sh σ m) S a) => inWritable_slot hpre hS hx hslot.1 h
  have hlive' : Live σ m' L X := live_keep hlive hso' hp fun a ha hpv => by
    rcases hown a ha.1 with h | h
    · exact owned_not_priv hpre h (priv_sub hpre hlive hpv)
    · exact σ.A.priv_not_live L a hpv (hin a h)
  refine ⟨common_keep hc hp hso' (fun a ha => ⟨?_, ha.2⟩) ⟨L, X, hlive'⟩, hlive'⟩
  rcases hown a ha.1 with h | h
  · exact .inl h
  · exact .inr (hslot.2.2 a h)

/-- A frame word whose symbolic value the leaf keeps keeps its value. -/
theorem slot_word_keep {env : Env} {S S' : SState} {m m' : Machine} {σ : Sig}
    (hwf : Env.WF env S) (hm : Match env S m) (hR : S.regions[0]? = some frameR)
    (hwf' : Env.WF env S') (hm' : Match env S' m') (hR' : S'.regions[0]? = some frameR)
    (hb : env.base 0 = σ.fr) (hsz : env.size 0 = frameBytes) {o : Nat}
    (ho : o + 8 ≤ frameBytes) (h : readConst S' 0 o 8 = readConst S 0 o 8) :
    m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8 := by
  have e' := load_cst hwf' hm' hR' (off := o) (n := 8) (by rw [hsz]; exact ho)
  have e := load_cst hwf hm hR (off := o) (n := 8) (by rw [hsz]; exact ho)
  rw [hb] at e e'
  rw [e', h, ← e]

/-- A frame word as the leaf's state says. -/
theorem slot_word {env : Env} {S' : SState} {m' : Machine} {σ : Sig}
    (hwf' : Env.WF env S') (hm' : Match env S' m') (hR' : S'.regions[0]? = some frameR)
    (hb : env.base 0 = σ.fr) (hsz : env.size 0 = frameBytes) {o : Nat}
    (ho : o + 8 ≤ frameBytes) {s : Sym} (h : readConst S' 0 o 8 = s) :
    m'.load (σ.fr + w o) 8 = some (s.eval env) := by
  have e' := load_cst hwf' hm' hR' (off := o) (n := 8) (by rw [hsz]; exact ho)
  rw [hb, h] at e'
  exact e'

end ZesuExec.Fn.DTF
