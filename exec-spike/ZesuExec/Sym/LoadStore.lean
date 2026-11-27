import ZesuExec.Sym.MemLemmas
import ZesuExec.Sym.Exec

/-!
# Soundness of symbolic loads and stores (`loadSym`, `storeSym`)
-/

namespace ZesuExec.Sym
open ZesuExec.Machine

/-! ## Region facts from `Env.WF` -/

theorem Env.WF.fits {env : Env} {S : SState} (hwf : Env.WF env S) {r : Nat} {R : Region}
    (hR : S.regions[r]? = some R) : (env.base r).toNat + env.size r ≤ Layout.ramHi := by
  have h := hwf.range r R hR
  cases hw : R.writable <;> simp [hw, readable, writable, inRange, Layout.rodataLo, Layout.rodataHi,
    Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi] at h ⊢ <;> omega

theorem Env.WF.readable_of {env : Env} {S : SState} (hwf : Env.WF env S) {r : Nat} {R : Region}
    (hR : S.regions[r]? = some R) {off n : Nat} (hb : off + n ≤ env.size r) :
    readable ((env.base r).toNat + off) n = true := by
  have h := hwf.range r R hR
  cases hw : R.writable <;> simp [hw, readable, writable, inRange, Layout.rodataLo, Layout.rodataHi,
    Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi] at h ⊢ <;> omega

theorem Env.WF.writable_of {env : Env} {S : SState} (hwf : Env.WF env S) {r : Nat} {R : Region}
    (hR : S.regions[r]? = some R) (hw : R.writable = true) {off n : Nat}
    (hb : off + n ≤ env.size r) : writable ((env.base r).toNat + off) n = true := by
  have h := hwf.range r R hR
  simp [hw, writable, inRange, Layout.ramLo, Layout.ramHi] at h ⊢; omega

theorem Env.WF.writable_ram {env : Env} {S : SState} (hwf : Env.WF env S) {r : Nat} {R : Region}
    (hR : S.regions[r]? = some R) (hw : R.writable = true) :
    Layout.ramLo ≤ (env.base r).toNat ∧ (env.base r).toNat + env.size r ≤ Layout.ramHi := by
  have h := hwf.range r R hR
  simp [hw, writable, inRange] at h; exact h

theorem size_zero_of_ge {env : Env} {S : SState} (hwf : Env.WF env S) {r : Nat}
    (hr : S.regions.length ≤ r) : env.size r = 0 := by
  simp only [Env.size, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by rw [hwf.len]; exact hr)]; rfl

theorem region_of_lt {env : Env} {S : SState} (hwf : Env.WF env S) {r j : Nat}
    (hj : j < env.size r) : ∃ R, S.regions[r]? = some R := by
  rcases Nat.lt_or_ge r S.regions.length with h | h
  · exact ⟨_, List.getElem?_eq_getElem h⟩
  · rw [size_zero_of_ge hwf h] at hj; omega

theorem addr_toNat {env : Env} {S : SState} (hwf : Env.WF env S) {r j : Nat}
    (hj : j < env.size r) : (env.base r + BitVec.ofNat 64 j).toNat = (env.base r).toNat + j := by
  obtain ⟨R, hR⟩ := region_of_lt hwf hj
  have := hwf.fits hR
  exact toNat_add_ofNat (by simp [Layout.ramHi] at this; omega)

/-- Two region addresses are equal only at the same region and offset. -/
theorem addr_inj {env : Env} {S : SState} (hwf : Env.WF env S) {r r' j j' : Nat}
    (hj : j < env.size r) (hj' : j' < env.size r')
    (h : (env.base r).toNat + j = (env.base r').toNat + j') : r = r' ∧ j = j' := by
  by_cases hr : r = r'
  · subst hr; exact ⟨rfl, by omega⟩
  · exact absurd h (hwf.disjoint r r' j j' hr hj hj')

/-! ## Covering and overlapping writes -/

theorem covers_overlaps {w : Write} {r off n t : Nat} (ht : t < n) (h : w.covers r (off + t) = true) :
    w.overlaps r off n = true := by
  simp [Write.covers, Write.overlaps] at h ⊢; omega

theorem find_covers_of_find_overlaps {ws : List Write} {w : Write} {r off n t : Nat} (ht : t < n)
    (hf : ws.find? (·.overlaps r off n) = some w) (hw : w.covers r (off + t) = true) :
    ws.find? (·.covers r (off + t)) = some w := by
  induction ws with
  | nil => simp at hf
  | cons w' ws ih =>
    rw [List.find?_cons] at hf ⊢
    by_cases ho : w'.overlaps r off n = true
    · simp only [ho] at hf
      cases hf; simp [hw]
    · simp only [ho] at hf
      have hc : w'.covers r (off + t) = false := by
        cases hcv : w'.covers r (off + t)
        · rfl
        · exact absurd (covers_overlaps ht hcv) ho
      simp only [hc]
      exact ih (by simpa using hf)

theorem find_covers_none {ws : List Write} {r off n t : Nat} (ht : t < n)
    (hf : ws.find? (·.overlaps r off n) = none) : ws.find? (·.covers r (off + t)) = none := by
  rw [List.find?_eq_none] at hf ⊢
  intro w hw hc
  exact hf w hw (covers_overlaps ht (by simpa using hc))

theorem memByte_cons (env : Env) (w : Write) (ws : List Write) (r j : Nat) :
    memByte env (w :: ws) r j =
      if w.covers r j then byteOf (w.v.eval env) (j - w.off) else memByte env ws r j := by
  unfold memByte
  rw [List.find?_cons]
  cases w.covers r j <;> rfl

/-! ## Reading at a constant offset -/

theorem byteSym_eval {env : Env} {S : SState} {m : Machine} (hm : Match env S m) (r j : Nat) :
    (byteSym S r j).eval env = (memByte env S.mem r j).zeroExtend 64 := by
  unfold byteSym memByte
  cases hw : S.mem.find? (·.covers r j) with
  | some w => simp [Sym.eval, byteList, ofBytesLE]
  | none =>
    simp only
    cases hk : S.known.find? (·.covers r j) with
    | none => simp [Sym.eval, byteList, ofBytesLE]
    | some k =>
      have hkm := List.mem_of_find?_eq_some hk
      have hkc := List.find?_some hk
      simp [Write.covers] at hkc
      have h := hm.known k hkm (j - k.off) (by omega)
      rw [show k.off + (j - k.off) = j by omega, hkc.1.1] at h
      simp [Sym.eval, byteList, ofBytesLE, h]

theorem joinBytes_byteSyms_eval {env : Env} {S : SState} {m : Machine} (hm : Match env S m)
    (r : Nat) : ∀ n j, (joinBytes (byteSyms S r j n)).eval env =
      ofBytesLE (byteList (memByte env S.mem r) j n)
  | 0, _ => by simp [byteSyms, joinBytes, Sym.eval, byteList, ofBytesLE]
  | 1, j => by simp [byteSyms, joinBytes, byteList, ofBytesLE, byteSym_eval hm]
  | n + 2, j => by
    have ih := joinBytes_byteSyms_eval hm r (n + 1) (j + 1)
    rw [show byteSyms S r j (n + 2) = byteSym S r j :: byteSyms S r (j + 1) (n + 1) from rfl,
      show byteSyms S r (j + 1) (n + 1) = byteSym S r (j + 1) :: byteSyms S r (j + 2) n from rfl]
      at *
    rw [show joinBytes (byteSym S r j :: byteSym S r (j + 1) :: byteSyms S r (j + 2) n) =
      .cat (byteSym S r j) (joinBytes (byteSym S r (j + 1) :: byteSyms S r (j + 2) n)) 1 from rfl]
    simp only [Sym.eval]
    rw [ih, byteSym_eval hm]
    simp [byteList, ofBytesLE, zeroExtend_and_255]

theorem readConst_eval {env : Env} {S : SState} {m : Machine} (hm : Match env S m)
    (r off n : Nat) :
    (readConst S r off n).eval env = ofBytesLE (byteList (memByte env S.mem r) off n) := by
  unfold readConst
  cases hw : S.mem.find? (·.overlaps r off n) with
  | some w =>
    simp only
    split
    · next he =>
      obtain ⟨ho, hn⟩ := he
      rw [mkBytes_eval]
      congr 1
      apply byteList_congr
      intro t ht
      have hc : w.covers r (off + t) = true := by
        have := List.find?_some hw
        simp [Write.overlaps] at this
        simp [Write.covers, this.1.1]; omega
      simp only [memByte, find_covers_of_find_overlaps ht hw hc]
      congr 1; omega
    · exact joinBytes_byteSyms_eval hm r n off
  | none =>
    simp only
    cases hk : S.known.find? (·.overlaps r off n) with
    | some k =>
      simp only
      split
      · next he =>
        obtain ⟨ho, hn⟩ := he
        rw [mkBytes_eval]
        congr 1
        apply byteList_congr
        intro t ht
        have hkr : k.r = r := by
          have := List.find?_some hk; simp [Write.overlaps] at this; exact this.1.1
        have h := hm.known k (List.mem_of_find?_eq_some hk) t (by omega)
        simp only [memByte, find_covers_none ht hw, Nat.zero_add]
        rw [← hkr, ← ho, h]
      · exact joinBytes_byteSyms_eval hm r n off
    | none =>
      simp only [Sym.eval]
      congr 1
      apply byteList_congr
      intro t ht
      simp [memByte, find_covers_none ht hw]

/-! ## Loads -/

theorem mod_of_aligned {b off n align : Nat} (hb : b % align = 0) (ha : align % n = 0)
    (ho : off % n = 0) : (b + off) % n = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact Nat.dvd_add (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb))
    (Nat.dvd_of_mod_eq_zero ho)

theorem cstCheck_spec {R : Region} {r off n : Nat} {ob : List Oblig} {env : Env} {S : SState}
    (hwf : Env.WF env S) (hR : S.regions[r]? = some R) (hc : cstCheck R r off n = some ob)
    (hob : ∀ o ∈ ob, o.holds env) :
    off % n = 0 ∧ R.align % n = 0 ∧ off + n ≤ env.size r := by
  unfold cstCheck at hc
  split at hc
  · next ha =>
    refine ⟨ha.1, ha.2, ?_⟩
    cases hs : R.size with
    | some s =>
      rw [hs] at hc; simp only at hc
      split at hc
      · rw [hwf.size r R s hR hs]; assumption
      · simp at hc
    | none =>
      rw [hs] at hc; simp only [Option.some.injEq] at hc; subst hc
      have := hob (.inBounds r off (.lit 0) 1 n) (by simp)
      simpa [Oblig.holds, Sym.eval] using this
  · simp at hc

theorem load_cst {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S)
    (hm : Match env S m) {r off n : Nat} {R : Region} (hR : S.regions[r]? = some R)
    (hal : off % n = 0) (hra : R.align % n = 0) (hb : off + n ≤ env.size r) :
    m.load (env.base r + BitVec.ofNat 64 off) n = some ((readConst S r off n).eval env) := by
  have hfit := hwf.fits hR
  have hlt : (env.base r).toNat + off < 2 ^ 64 := by simp [Layout.ramHi] at hfit; omega
  have ha : (env.base r + BitVec.ofNat 64 off).toNat = (env.base r).toNat + off :=
    toNat_add_ofNat hlt
  unfold Machine.load
  rw [ha, if_pos ⟨mod_of_aligned (hwf.align r R hR) hra hal, hwf.readable_of hR hb⟩]
  rw [readBytes_of (f := memByte env S.mem r) (k := off), readConst_eval hm]
  · rfl
  · intro t ht
    rw [Nat.add_assoc, ofNat_toNat_add]
    exact hm.mem r (off + t) (by have := hR; exact (List.getElem?_eq_some_iff.mp hR).1) (by omega)

theorem load_idx {env : Env} {S : SState} {m : Machine} (hwf : Env.WF env S)
    (hm : Match env S m) {r off n sc : Nat} {i : Sym} {R : Region} (hR : S.regions[r]? = some R)
    (hal : off % n = 0) (hra : R.align % n = 0) (hsc : sc % n = 0)
    (hnw : S.mem.all (·.r != r) = true)
    (hb : off + sc * (i.eval env).toNat + n ≤ env.size r) (a : Word)
    (haddr : a.toNat = (env.base r).toNat + (off + sc * (i.eval env).toNat)) :
    m.load a n = some ((Sym.initx r off i sc n).eval env) := by
  have hfit := hwf.fits hR
  unfold Machine.load
  have hmod : (off + sc * (i.eval env).toNat) % n = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_add (Nat.dvd_of_mod_eq_zero hal)
      (Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero hsc) _)
  rw [haddr, if_pos ⟨mod_of_aligned (hwf.align r R hR) hra hmod,
    hwf.readable_of hR (off := off + sc * (i.eval env).toNat) (by omega)⟩]
  rw [readBytes_of (f := env.byte0 r) (k := off + sc * (i.eval env).toNat)]
  · rfl
  · intro t ht
    rw [Nat.add_assoc, ofNat_toNat_add]
    rw [hm.mem r _ (List.getElem?_eq_some_iff.mp hR).1 (by omega)]
    simp only [memByte, Option.some.injEq]
    rw [List.find?_eq_none.mpr]
    intro w hw
    have := List.all_eq_true.mp hnw w hw
    simp [Write.covers] at this ⊢
    intro h; exact absurd h this

theorem zext_or_shift (x : Byte) (y : Word) :
    x.zeroExtend 64 ||| (y <<< 8) = x.zeroExtend 64 + (y <<< 8) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  ext i hi
  simp
  intro h1 h2
  rw [BitVec.getLsbD_of_ge x i (by omega)] at h1
  contradiction

theorem roValue_spec {img : Image} {m : Machine} (hro : RoLoaded img m) :
    ∀ n a v, roValue img a n = some v → Layout.rodataLo ≤ a → a + n ≤ Layout.rodataHi →
      ∃ bs, readBytes m.mem a n = some bs ∧ ofBytesLE bs = BitVec.ofNat 64 v
  | 0, a, v, h, _, _ => by
    simp [roValue] at h; subst h; exact ⟨[], rfl, by simp [ofBytesLE]⟩
  | n + 1, a, v, h, hlo, hhi => by
    simp only [roValue, Option.bind_eq_bind] at h
    cases hb : img.rodataByte? a with
    | none => simp [hb] at h
    | some b =>
      cases hr : roValue img (a + 1) n with
      | none => simp [hb, hr] at h
      | some rest =>
        simp [hb, hr] at h; subst h
        obtain ⟨bs, hbs, hv⟩ := roValue_spec hro n (a + 1) rest hr (by omega) (by omega)
        have hm := hro a b hlo (by unfold Layout.rodataHi at *; omega) hb
        refine ⟨BitVec.ofNat 8 b :: bs, by simp [readBytes, hm, hbs], ?_⟩
        simp only [ofBytesLE, hv]
        rw [zext_or_shift]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_shiftLeft]
        omega

end ZesuExec.Sym
