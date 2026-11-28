import ZesuExec.Fn.DTF.HashStore

/-!
# DTF: tools for the `txAuthList` loop (programme plan S7 step 4)

The authorization list (arm 4's item 9) is read tuple by tuple from the list cursor `S-0x300`/
`S-0x308`; each tuple's fields from the field cursor `s6`/`s7` (`AuthTup`, `Cuts.lean`). Here:
header fit of a tuple (`auth_fits`, from `Fits`), a return site's call machine (`ret_parts`), a
`decodeItem` outcome on a payload slice (`f2_post_cur`), a field's consumed length
(`field_consumed`), and keeping the list cursor and buffer (`authOut_mono`, `authBuf_mono`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Header fit of the list's items -/

/-- The payload of the list item after `k` items has `inner` (`Fits`'s `ItemsFit`). -/
theorem inner_at {inner : List Byte → Prop} : ∀ {k n : Nat} {b : List Byte} {c : Nat},
    ItemsFit inner n b → skip k b = some c → k < n → ∀ {h p : Nat},
    F2.decode (b.drop c) = .success true h p → inner (TX.itemPayload (b.drop c) h p)
  | 0, _ + 1, b, c, hf, hs, _, h, p, hd => by
    simp only [skip, Option.some.injEq] at hs; subst hs
    simp only [List.drop_zero] at hd ⊢
    simp only [ItemsFit, hd] at hf
    exact hf.2.1 trivial
  | k + 1, n + 1, b, c, hf, hs, hk, h, p, hd => by
    simp only [skip] at hs
    split at hs
    · next l h0 p0 hd0 =>
      obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp hs
      simp only [ItemsFit, hd0] at hf
      have := inner_at hf.2.2 h' (by omega) (h := h) (p := p)
        (by rwa [TX.itemRest, List.drop_drop])
      rwa [TX.itemRest, List.drop_drop] at this
    · cases hs
  | _, 0, _, _, _, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)

/-- Arm 4 at a cut only arm 4 reaches. -/
theorem arm4 {σ : Sig} {arms : List Nat} (h : ArmOk σ arms) (ha : arms = [4]) : σ.t = 4 := by
  rcases h with h | h
  · rw [ha] at h; cases h
  · rw [ha] at h; simpa using h

/-- The `n + 1`-th tuple's header fits (`Fits`: the items of a top-level list's payload). -/
theorem auth_fits {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4) {c h p n j : Nat}
    (hl : AuthList σ c h p) (hsk : skip n (TX.itemPayload (σ.payload.drop c) h p) = some j)
    (hn : n < p) (hp : p ≤ (σ.payload.drop (c + h)).length) :
    TX.HeaderFits ((σ.payload.drop (c + h + j)).take (p - j)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := hpre
  have hf := hd.2
  unfold Fits at hf
  rw [show (σ.m.reg 12).toNat = 4 from h4] at hf
  have hi := inner_at hf hl.1 (by decide) hl.2
  have hlen : (TX.itemPayload (σ.payload.drop c) h p).length = p := by
    simp only [TX.itemPayload, List.length_take, List.length_drop] at hp ⊢
    omega
  rw [hlen] at hi
  have := fits_at hi hsk hn
  rwa [itemPayload_drop] at this

/-! ## Return sites -/

/-- The call machine and the callee's `Post` at the return site `table[i]!` (a return site only). -/
theorem ret_parts {σ : Sig} {m : Machine} {i : Nat} (hne : (table[i]!).pc ≠ entry)
    (hpl : (table[i]!).plain = false) (hA : (mkCut (table[i]!)).A σ m) :
    ∃ mc x, SiteA (siteAt i) (table[i]!).pc σ x mc ∧
      (calleeOf (siteAt i).kind).Post σ x mc m := by
  simp only [mkCut, if_neg hne, ACut] at hA
  rcases hA with ⟨h, -⟩ | ⟨s, hs, mc, x, hsite, hpost⟩
  · rw [hpl] at h; cases h
  have hs' : s = siteAt i := by
    show s = ((table[i]!).site).getD default; rw [hs]; rfl
  subst hs'
  exact ⟨mc, x, hsite, hpost⟩

/-- `decodeItem`'s outcome at `fr + ko` on `n` payload bytes from `inp + c`. -/
theorem f2_post_cur {σ : Sig} {mc m : Machine} (hc : Common σ mc) (hq : F2.Post mc m) {ko c n : Nat}
    (hout : mc.reg 10 = σ.fr + w ko) (hko : ko + 40 ≤ frameBytes) (hin : mc.reg 11 = σ.inp + w c)
    (hn : mc.reg 12 = w n) (hcn : c + n ≤ σ.len) :
    ∃ before, BytesAt m (σ.fr + w ko)
      (F2.result40 (σ.inp + w c) ((σ.payload.drop c).take n) before) := by
  have hpre := hc.2.1
  have hav := hc.avail
  have hlen := payload_len hpre
  obtain ⟨before, hbl, hbb⟩ := TX.bytes_of_present (m := mc) (a := mc.reg 10) (n := 40)
    fun i hi => by
      rw [hout, show σ.fr + w ko + BitVec.ofNat 64 i = σ.fr + BitVec.ofNat 64 (ko + i) by
        simp only [w]; rw [F1.add_add_ofNat]]
      exact stack_present hav (by omega)
  have hin' : BytesAt mc (mc.reg 11) ((σ.payload.drop c).take n) := by
    rw [hin]; exact bytesAt_take (input_bytes hav (by omega)) _
  have hl12 : (mc.reg 12).toNat = n := by
    have : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
    rw [hn]; simp only [w, BitVec.toNat_ofNat]; omega
  have hres := hq.2.2 _ before hin'
    (by rw [hl12]; simp only [List.length_take, List.length_drop, hlen]; omega) hbb hbl
  rw [hout, hin] at hres
  exact ⟨before, hres⟩

/-! ## Field items -/

/-- A one-byte item has no header. -/
theorem decode_h0 {b : List Byte} {l : Bool} {p : Nat} (hd : F2.decode b = .success l 0 p) :
    p = 1 := by
  cases b with
  | nil => simp [F2.decode] at hd
  | cons pre rest =>
    simp only [F2.decode, F2.checkedPayload] at hd
    repeat' split at hd
    all_goals (try simp only [F2.Item.success.injEq, reduceCtorEq] at hd)
    all_goals (try (obtain ⟨-, hh, hp⟩ := hd))
    all_goals first | omega | simp_all

/-- A field item of at most 32 payload bytes: its consumed length does not wrap and is positive. -/
theorem field_consumed {b : List Byte} {l : Bool} {h p : Nat} (hd : F2.decode b = .success l h p)
    (hp : p % 2 ^ 64 ≤ 32) :
    (h + p) % 2 ^ 64 = h + p % 2 ^ 64 ∧ 1 ≤ h + p % 2 ^ 64 ∧ h + p % 2 ^ 64 ≤ b.length := by
  obtain ⟨hh9, -⟩ := decode_hdr hd
  have hc := decode_consumed_le hd
  unfold TX.itemConsumed at hc
  have e : (h + p) % 2 ^ 64 = h + p % 2 ^ 64 := by omega
  refine ⟨e, ?_, by omega⟩
  rcases Nat.eq_zero_or_pos h with h0 | h0
  · subst h0; have := decode_h0 hd; subst this; decide
  · omega

/-! ## Keeping the list cursor and the buffer -/

theorem authOut_mono {σ : Sig} {m m' : Machine} {n j c h p : Nat}
    (h70 : m'.load (σ.fr + w 0x70) 8 = m.load (σ.fr + w 0x70) 8)
    (h68 : m'.load (σ.fr + w 0x68) 8 = m.load (σ.fr + w 0x68) 8)
    (h30 : m'.load (σ.fr + w 0x30) 8 = m.load (σ.fr + w 0x30) 8)
    (ho : AuthOut σ m n j c h p) : AuthOut σ m' n j c h p := by
  obtain ⟨hl, hs, hnj, l70, l68, l30⟩ := ho
  exact ⟨hl, hs, hnj, h70.trans l70, h68.trans l68, h30.trans l30⟩

theorem bufIs_mono {σ : Sig} {m m' : Machine} {n r : Nat} {bp cap : Word}
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) (hb : BufIs σ m n r bp cap) :
    BufIs σ m' n r bp cap := by
  obtain ⟨h1, h2, L, X, hlive, hx⟩ := hb
  exact ⟨h1, h2, L, X, hL L X hlive, hx⟩

theorem authBuf_mono {σ : Sig} {m m' : Machine} {n r : Nat}
    (h58 : m'.load (σ.fr + w 0x58) 8 = m.load (σ.fr + w 0x58) 8)
    (h60 : m'.load (σ.fr + w 0x60) 8 = m.load (σ.fr + w 0x60) 8)
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) (hb : AuthBuf σ m n r) : AuthBuf σ m' n r := by
  obtain ⟨bp, cap, l58, l60, hb⟩ := hb
  exact ⟨bp, cap, h58.trans l58, h60.trans l60, bufIs_mono hL hb⟩

end ZesuExec.Fn.DTF
