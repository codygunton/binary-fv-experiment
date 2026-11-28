import ZesuExec.Fn.DTF.Hash

/-!
# DTF: the `txHashList` loop's item and `ensureTotalCapacity` (programme plan S7 step 4)

At `0x800020c0` `decodeItem` has run on the `p - j` list bytes left at the cursor (`SiteX`: its
input `a1`/`a2` is `s7`/`s6`). Leaf 3 (a 32-byte string) reads the item's four words and calls
`ensureTotalCapacity(S-0x118, ao, n + 1)` (F1); `f1_pre_dtf` is F1's precondition there.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## `decodeItem`'s outcome on any input -/

/-- The outcome at `ko` of a `decodeItem` on `input` at `q` that failed or not. -/
theorem res_ok {sh : Shape} {σ : Sig} {m : Machine} {ko : Nat} {q : Word}
    {input before : List Byte} (hko : ko + 40 ≤ frameBytes)
    (hres : BytesAt m (σ.fr + w ko) (F2.result40 q input before))
    (herr : (Sym.init 0 (ko + 32) 2).eval (envOf sh σ m) = 0) : F2.decode input ≠ .error := by
  have hrl : (F2.result40 q input before).length = 40 := by simp [F2.result40]
  rw [init_frame hres (by rw [hrl]; omega), TX.result40_err] at herr
  exact (TX.err_half).mp (by simpa using herr)

/-- The words of the outcome at `ko` of a successful `decodeItem` on `input` at `q`. -/
theorem res_words {sh : Shape} {σ : Sig} {m : Machine} {ko : Nat} {q : Word}
    {input before : List Byte} (hav : Avail σ m) (hko : ko + 40 ≤ frameBytes)
    (hres : BytesAt m (σ.fr + w ko) (F2.result40 q input before))
    {l : Bool} {h p : Nat} (hd : F2.decode input = .success l h p) :
    (isL ko).eval (envOf sh σ m) = (if l then 1 else 0) ∧
    (Sym.init 0 (ko + 8) 8).eval (envOf sh σ m) = w p ∧
    (Sym.init 0 (ko + 24) 8).eval (envOf sh σ m) = w (h + p) ∧
    TX.wordAt m (σ.fr + w ko) = if input.head? = some 128 then 1 else q + w h := by
  have hrl : (F2.result40 q input before).length = 40 := by simp [F2.result40]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [isL, Sym.eval_bin, Sym.eval_lit, BinOp.eval]
    rw [init_frame hres (by rw [hrl]; omega),
      List.drop_eq_getElem_cons (by rw [hrl]; omega)]
    simp only [List.take_succ_cons, List.take_zero, F2.result40, List.getElem_map,
      List.getElem_range, F2.resultByte, hd, F2.successByte, if_neg (show ¬ (16 < 8) by decide),
      if_neg (show ¬ (16 < 16) by decide)]
    cases l <;> simp only [if_true, Bool.false_eq_true, if_false] <;> decide
  · rw [init_frame hres (by rw [hrl]; omega), result40_len]
    simp only [F2.resultByte, hd, F2.successByte]
    have e : ∀ j ∈ List.range 8, (if 8 + j < 8 then
          byteOf (if input.head? = some 128 then 1 else q + BitVec.ofNat 64 h) (8 + j)
        else if 8 + j < 16 then byteOf (BitVec.ofNat 64 p) (8 + j - 8)
        else if 8 + j = 16 then (if l = true then 1 else 0)
        else if 8 + j < 24 then before.getD (8 + j) 0
        else if 8 + j < 32 then byteOf (BitVec.ofNat 64 (h + p)) (8 + j - 24)
        else if 8 + j < 34 then 0 else before.getD (8 + j) 0) =
        byteOf (BitVec.ofNat 64 p) j := by
      intro j hj
      simp only [List.mem_range] at hj
      rw [if_neg (by omega), if_pos (by omega), show 8 + j - 8 = j by omega]
    rw [List.map_congr_left e]
    exact ofBytesLE_bytes8 _
  · rw [init_frame hres (by rw [hrl]; omega), result40_consumed]
    simp only [F2.resultByte, hd, F2.successByte]
    have e : ∀ j ∈ List.range 8, (if 24 + j < 8 then
          byteOf (if input.head? = some 128 then 1 else q + BitVec.ofNat 64 h) (24 + j)
        else if 24 + j < 16 then byteOf (BitVec.ofNat 64 p) (24 + j - 8)
        else if 24 + j = 16 then (if l = true then 1 else 0)
        else if 24 + j < 24 then before.getD (24 + j) 0
        else if 24 + j < 32 then byteOf (BitVec.ofNat 64 (h + p)) (24 + j - 24)
        else if 24 + j < 34 then 0 else before.getD (24 + j) 0) =
        byteOf (BitVec.ofNat 64 (h + p)) j := by
      intro j hj
      simp only [List.mem_range] at hj
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), show 24 + j - 24 = j by omega]
    rw [List.map_congr_left e]
    exact ofBytesLE_bytes8 _
  · have hl := frame_load hav (o := ko) (by omega)
    have hb := load_bytes hl (by omega)
    apply word_of_bytes
    intro t ht
    have h1 := hb t ht
    have h2 := hres t (by rw [hrl]; omega)
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    rw [h2]
    simp only [F2.result40, List.getElem_map, List.getElem_range, F2.resultByte, hd,
      F2.successByte, if_pos ht]

/-- A frame variable (`var (64 + o / 8)`): the frame word minus the payload base. -/
theorem var_slot {sh : Shape} {σ : Sig} {m : Machine} {i : Nat} (h : 64 ≤ i) :
    (Sym.var i).eval (envOf sh σ m) = TX.wordAt m (σ.fr + w (8 * (i - 64))) - σ.inp := by
  simp [Sym.eval, envOf, show ¬ i < 32 by omega, show ¬ i < 64 by omega]

/-- The bytes of a prefix. -/
theorem bytesAt_take {m : Machine} {a : Word} {bs : List Byte} (h : BytesAt m a bs) (k : Nat) :
    BytesAt m a (bs.take k) := fun i hi => by
  simp only [List.length_take] at hi
  rw [h i (by omega), List.getElem_take]

/-- The list payload after `j` bytes is the payload after `c + h + j`, `p - j` bytes of it. -/
theorem itemPayload_drop (b : List Byte) (c h p j : Nat) :
    (TX.itemPayload (b.drop c) h p).drop j = (b.drop (c + h + j)).take (p - j) := by
  simp only [TX.itemPayload, List.drop_take, List.drop_drop]

/-! ## The return from `decodeItem` on the cursor (`0x800020c0`) -/

/-- `Live` survives `decodeItem` (it writes its outcome and its stack only). -/
theorem f2_live {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hk : Kind.SiteFine .f2 s = true) (hsite : SiteA s r σ x mc) (hq : F2.Post mc m)
    (hp : Preserved mc m) {L X : List (Word × Nat)} (hlive : Live σ mc L X) : Live σ m L X := by
  have hc := hsite.2.1
  have hpre := hc.2.1
  have hfr := fr_toNat hpre
  have hsp := pre_sp hpre
  simp only [Kind.SiteFine, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨h2, h10⟩ := hk
  cases h10' : regFr s 10 with
  | none => simp [h10'] at h10
  | some ka =>
    simp only [h10', decide_eq_true_eq] at h10
    have r10 : mc.reg 10 = σ.fr + w ka := hsite.2.2.1.1 _ (lookup_mem (regFr_spec h10')) _ rfl
    have r2 := sp_fr hsite h2
    have e10 := fr_add_toNat hpre (k := ka) (by omega)
    have e2 := below_fr_toNat hpre
    obtain ⟨-, hso, -⟩ := hq
    unfold frameBytes stackBytes TX.stackBytes Layout.ramLo at *
    refine live_keep hlive hso hp fun a h hl => ?_
    have hP := priv_sub hpre hlive hl
    rcases h with h | h
    · rw [r10] at h
      exact (stack_R hpre (by rw [e10]; unfold stackBytes TX.stackBytes; omega)
        (by rw [e10]; omega) h).2 hP
    · rw [r2] at h
      exact (stack_R hpre (by rw [e2]; unfold stackBytes TX.stackBytes; omega)
        (by rw [e2]; omega) h).2 hP

/-- At `0x800020c0`: the loop state, and the outcome is `decodeItem`'s on the `p - j` list bytes
left at the cursor. -/
theorem hash_ret {σ : Sig} {m : Machine} (hA : (mkCut (table[108]!)).A σ m) :
    ∃ c h p n j before, HashList σ c h p ∧
      skip n (TX.itemPayload (σ.payload.drop c) h p) = some j ∧ n ≤ j ∧
      m.reg 23 = σ.inp + w (c + h + j) ∧ m.reg 22 = w (p - j) ∧ m.reg 25 = w n ∧
      ListHdr σ m 0x258 n 0 ∧ HashesOk (TX.itemPayload (σ.payload.drop c) h p) n ∧
      BytesAt m (σ.fr + w 0x2e0) (F2.result40 (σ.inp + w (c + h + j))
        ((σ.payload.drop (c + h + j)).take (p - j)) before) := by
  have hpc : (table[108]!).pc ≠ entry := by decide
  simp only [mkCut, if_neg hpc, ACut] at hA
  rcases hA with ⟨h, -⟩ | ⟨s, hs, mc, x, hsite, hpost⟩
  · exact absurd h (by decide)
  have hs' : s = siteAt 108 := by
    show s = ((table[108]!).site).getD default; rw [hs]; rfl
  subst hs'
  have hkind : (siteAt 108).kind = .f2 := by decide
  have hSF : (siteAt 108).kind.SiteFine (siteAt 108) = true := by decide
  have hSF' : Kind.SiteFine .f2 (siteAt 108) = true := by decide
  obtain ⟨hret, hcm, hkeep⟩ := ret_common hSF hsite hpost
  have hc := hsite.2.1
  have hpre := hc.2.1
  have hav := hc.avail
  have h3 : σ.t = 3 := arm3 hsite.2.2.2.1 (by decide)
  have hsx := hsite.2.2.2.2.2.2.2.2
  rw [show (table[108]!).pc = 0x800020c0 by decide] at hsx
  simp only [SiteX, if_true] at hsx
  obtain ⟨⟨c, h, p, n, j, hl, hsk, hnj, r23, r22, r25, hdr, hok⟩, a11, a12⟩ := hsx
  obtain ⟨hq, hp⟩ := hpost
  replace hq : F2.Post mc m := by rw [hkind] at hq; exact hq
  have hle := hashList_le hpre h3 hl
  have hlen := payload_len hpre
  have hjp : j ≤ p := by
    have := skip_le hsk
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  -- the header and the loop registers survive the call
  have hdr' : ListHdr σ m 0x258 n 0 := by
    obtain ⟨p0, cap, l0, l8, l16, hnr, hp0, L, X, hlive, hb⟩ := hdr
    refine ⟨p0, cap, ?_, ?_, ?_, hnr, hp0, L, X, f2_live hSF' hsite hq hp hlive, hb⟩
    · rw [hkeep 0x258 (by decide) (by decide)]; exact l0
    · rw [hkeep (0x258 + 8) (by decide) (by decide)]; exact l8
    · rw [hkeep (0x258 + 16) (by decide) (by decide)]; exact l16
  have e23 : m.reg 23 = mc.reg 23 := hret.2 23 (by decide)
  have e22 : m.reg 22 = mc.reg 22 := hret.2 22 (by decide)
  have e25 : m.reg 25 = mc.reg 25 := hret.2 25 (by decide)
  -- the outcome
  have hout : mc.reg 10 = σ.fr + w 0x2e0 := hsite.2.2.1.1 (10, .fr 0x2e0) (by decide) _ rfl
  obtain ⟨before, hbl, hbb⟩ := TX.bytes_of_present (m := mc) (a := mc.reg 10) (n := 40)
    fun i hi => by
      rw [hout, show σ.fr + w 0x2e0 + BitVec.ofNat 64 i = σ.fr + BitVec.ofNat 64 (0x2e0 + i) by
        simp only [w]; rw [F1.add_add_ofNat]]
      exact stack_present hav (by unfold frameBytes; omega)
  have hin : BytesAt mc (mc.reg 11) ((σ.payload.drop (c + h + j)).take (p - j)) := by
    rw [a11, r23]; exact bytesAt_take (input_bytes hav (by omega)) _
  have hl12 : (mc.reg 12).toNat = p - j := by
    have : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
    rw [a12, r22]; simp only [w, BitVec.toNat_ofNat]; omega
  have hres := hq.2.2 _ before hin
    (by rw [hl12]; simp only [List.length_take, List.length_drop, hlen]; omega) hbb hbl
  rw [hout, a11, r23] at hres
  exact ⟨c, h, p, n, j, before, hl, hsk, hnj, e23.trans r23, e22.trans r22, e25.trans r25, hdr',
    hok, hres⟩

/-! ## `ensureTotalCapacity` at DTF's call -/

/-- `ensureTotalCapacity`'s precondition at a call with `sp = fr`, the list header `fr + ho` below
the save area, `a1` the allocator object and `a2 = n + 1`; the items are the buffer's first `32 n`
bytes, the live list DTF's. -/
theorem f1_pre_dtf {σ : Sig} {m : Machine} (hc : Common σ m) {ho n : Nat}
    (hsp : m.reg 2 = σ.fr + w 0) (hhdr : m.reg 10 = σ.fr + w ho) (hao : m.reg 11 = σ.ao + w 0)
    (hreq : m.reg 12 = w (n + 1)) (hn : n + 1 < 2 ^ 32) (hho : ho + 24 + 128 ≤ frameBytes)
    (hho8 : ho % 8 = 0) (hh : ListHdr σ m ho n 0) (hra : RetAligned m) :
    ∃ L X items, F1.Pre σ.A L items m ∧ Live σ m L X ∧
      BufOwn X (F1.wordAt m (m.reg 10)) (F1.wordAt m (m.reg 10 + 16)) := by
  obtain ⟨p, cap, L, X, l0, l8, l16, hnr, hp0, hlive, hbuf, hb, hpres⟩ := hdr_facts hc hh
  have hpre := hc.2.1
  have hav := hc.avail
  have hS := pre_sp hpre
  have hF : σ.fr.toNat = σ.S.toNat - frameBytes := fr_toNat hpre
  have hst : (σ.S - w stackBytes).toNat = σ.S.toNat - stackBytes :=
    S_sub_toNat hpre (Nat.le_refl _)
  have e8 : σ.fr + w ho + 8 = σ.fr + w (ho + 8) := by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl]; simp only [w]; rw [F1.add_add_ofNat]
  have e16 : σ.fr + w ho + 16 = σ.fr + w (ho + 16) := by
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl]; simp only [w]; rw [F1.add_add_ofNat]
  have ep : F1.wordAt m (σ.fr + w ho) = p := by simp [F1.wordAt, l0]
  have en : F1.wordAt m (σ.fr + w ho + 8) = w n := by rw [e8]; simp [F1.wordAt, l8]
  have ec : F1.wordAt m (σ.fr + w ho + 16) = cap := by rw [e16]; simp [F1.wordAt, l16]
  have hP : ∀ a, InRange σ.res resultBytes a ∨ InRange σ.ao 16 a ∨ InRange σ.inp σ.len a ∨
      InRange (σ.S - w stackBytes) stackBytes a ∨ InRange TX.scratch 8 a →
      ¬ σ.A.Priv σ.g.L a := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, haoR, hao8, haoS, -, -, -, -, -, -, -, -, -, -, -, -, d5, -,
    -, d8, -, d10, -⟩ := hpre
  have haoR' : Layout.ramLo ≤ σ.ao.toNat ∧ σ.ao.toNat + 16 ≤ Layout.ramHi := haoR
  have hao8' : σ.ao.toNat % 8 = 0 := hao8
  have d5' : TX.Apart (σ.S - w stackBytes) stackBytes σ.ao 16 := d5
  have d8' : TX.Apart TX.scratch 8 σ.ao 16 := d8
  have d10' : TX.Apart TX.scratch 8 (σ.S - w stackBytes) stackBytes := d10
  clear haoR hao8 d5 d8 d10
  have hn' : (w n).toNat = n := by simp only [w, BitVec.toNat_ofNat]; omega
  have hreq' : (w (n + 1)).toNat = n + 1 := by simp only [w, BitVec.toNat_ofNat]; omega
  have hsb : stackBytes = 1584 := rfl
  have hfb : frameBytes = 880 := rfl
  have hfS : σ.fr.toNat + 880 = σ.S.toNat := by
    rw [hF]; simp only [hfb, stackBytes, TX.stackBytes] at hS ⊢; omega
  have eho : (σ.fr + w ho).toNat = σ.fr.toNat + ho := fr_add_toNat hc.2.1 (by omega)
  have esp : (σ.fr - 128).toNat = σ.fr.toNat - 128 := by
    have := below_fr_toNat' hc.2.1 (n := 128) (by decide)
    simpa [w] using this
  have hscr : (BitVec.ofNat 64 Layout.extraParams : Word).toNat = Layout.extraParams := rfl
  have hscr' : TX.scratch.toNat = Layout.extraParams := rfl
  have hao0 : σ.ao + w 0 = σ.ao := by simp [w]
  have hsp0 : σ.fr + w 0 = σ.fr := by simp [w]
  have hnot : ∀ a, (InRange (σ.fr + w ho) 24 a ∨ InRange (σ.fr - 128) 128 a) →
      ¬ σ.A.Priv σ.g.L a := fun a ha =>
    hP a (.inr (.inr (.inr (.inl (by
      simp only [InRange, hst, eho, esp] at ha ⊢
      simp only [hsb] at hfS ⊢; omega)))))
  refine ⟨L, X, bytesOf m p (n * 32), ?_, hlive, by rw [hhdr, ep, ec]; exact hbuf⟩
  unfold F1.Pre
  simp only [hsp, hhdr, hao, hreq, hao0, hsp0, ep, en, ec]
  unfold F1.Apart RamRange InRange
  simp only [eho, esp, hscr, hn', hreq', F1.elemBytes]
  have hbA : ∀ q k', 0 < k' → q.toNat + k' ≤ 2 ^ 64 →
      (∀ a, InRange q k' a → ¬ σ.A.Priv σ.g.L a) →
      0 < cap.toNat → p.toNat + cap.toNat * 32 ≤ q.toNat ∨ q.toNat + k' ≤ p.toNat :=
    fun q k' hk' hq hn h0 => by
      have hr := (hb h0).1
      unfold RamRange Layout.ramHi at hr
      exact apart_priv (hb h0).2.2 hn (by omega) hk' (by omega) hq
  have hlo := hS.1
  have hhi := hS.2.1
  simp only [Layout.ramLo, Layout.ramHi, hsb] at hlo hhi haoR' ⊢
  refine ⟨hc.2.2.1, ⟨?_, ?_, ?_, fun j hj => ?_⟩, hra, ⟨by omega, by omega⟩, by omega,
    ⟨l0, by rw [e8]; exact l8, by rw [e16]; exact l16⟩, by omega, bytesOf_length _ _ _, hp0,
    fun h0 => ⟨(hb h0).1, (hb h0).2.1⟩, bytesOf_at hpres, haoR', hao8', ?_, common_vtable hav,
    by omega, hc.2.2.2.2.2.2.1, hlive.1, ?_, ?_, ?_, ?_, ?_, ?_,
    fun h0 => ⟨?_, ?_, ?_, ?_⟩, fun a ha hPa => ?_⟩
  · rw [hsp, hsp0, hF]; omega
  · rw [hsp, hsp0, hF]; omega
  · rw [hsp, hsp0, hF]; omega
  · rw [hsp, hsp0]
    have := hav.stack (1584 - 880 - 128 + j) (by omega)
    rwa [show σ.S - w stackBytes + BitVec.ofNat 64 (1584 - 880 - 128 + j) =
      σ.fr - BitVec.ofNat 64 128 + BitVec.ofNat 64 j by
        apply BitVec.eq_of_toNat_eq
        simp only [Sig.fr, w, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hfb, hsb]
        omega] at this
  · rw [load_congr (m := σ.m) fun t ht => hav.ao (by omega)]; exact haoS
  -- the six `Apart`s of the call's own ranges, each from at most one of the entry's
  all_goals first
    | omega
    | (have := d5'; unfold TX.Apart at this; rw [hst] at this; omega)
    | (have := d8'; unfold TX.Apart at this; rw [hscr'] at this; omega)
    | (have := d10'; unfold TX.Apart at this; rw [hscr', hst] at this; omega)
    | skip
  -- the buffer, one of DTF's blocks, against the call's ranges
  · have := hbA (σ.fr + w ho) 24 (by decide) (by rw [eho]; omega)
      (fun a ha => hnot a (.inl ha)) h0
    rwa [eho] at this
  · exact hbA σ.ao 16 (by decide) (by omega) (fun a ha => hP a (.inr (.inl ha))) h0
  · have := hbA (σ.fr - 128) 128 (by decide) (by rw [esp]; omega)
      (fun a ha => hnot a (.inr ha)) h0
    rwa [esp] at this
  · have := hbA TX.scratch 8 (by decide) (by rw [hscr']; unfold Layout.extraParams; omega)
      (fun a ha => hP a (.inr (.inr (.inr (.inr ha))))) h0
    rwa [hscr'] at this
  -- the owned ranges are not the allocator's
  have hP' := priv_sub hc.2.1 hlive hPa
  rcases ha with h | h | h | h
  · exact hnot a (.inl (by simpa only [InRange, eho] using h)) hP'
  · exact hP a (.inr (.inl h)) hP'
  · exact hnot a (.inr (by simpa only [InRange, esp] using h)) hP'
  · exact hP a (.inr (.inr (.inr (.inr (by simpa only [InRange, hscr'] using h))))) hP'

/-! ## The item (`0x800020c0`, leaf 3) -/

/-- The payload is below `2^32` bytes (it lies in the input area or in RAM). -/
theorem len_lt32 {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : σ.len < 2 ^ 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hia, -⟩ := hpre
  have hia' : (Layout.inputLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.inputHi) ∨
      (Layout.ramLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.ramHi) := hia
  unfold Layout.inputHi Layout.ramHi at hia'
  omega

/-- At `0x800020c0` with the outcome a 32-byte string: the `n + 1`-th item decoded, `k` bytes,
its payload at `inp + c + h + j + (k - 32)`. -/
theorem hash_item {σ : Sig} {m : Machine} (hA : (mkCut (table[108]!)).A σ m)
    (herr : (Sym.init 0 (0x2e0 + 32) 2).eval (envOf (table[108]!).shape σ m) = 0)
    (hlist : (isL 0x2e0).eval (envOf (table[108]!).shape σ m) = 0)
    (hlen : (Sym.init 0 (0x2e0 + 8) 8).eval (envOf (table[108]!).shape σ m) = 32) :
    ∃ c h p n j k, HashList σ c h p ∧
      skip n (TX.itemPayload (σ.payload.drop c) h p) = some j ∧
      skip (n + 1) (TX.itemPayload (σ.payload.drop c) h p) = some (j + k) ∧ n ≤ j ∧ 32 ≤ k ∧
      j + k ≤ p ∧ c + h + p ≤ σ.len ∧
      m.reg 23 = σ.inp + w (c + h + j) ∧ m.reg 22 = w (p - j) ∧ m.reg 25 = w n ∧
      ListHdr σ m 0x258 n 0 ∧ HashesOk (TX.itemPayload (σ.payload.drop c) h p) (n + 1) ∧
      (Sym.init 0 (0x2e0 + 24) 8).eval (envOf (table[108]!).shape σ m) = w k ∧
      TX.wordAt m (σ.fr + w 0x2e0) = σ.inp + w (c + h + j + (k - 32)) := by
  obtain ⟨c, h, p, n, j, before, hl, hsk, hnj, r23, r22, r25, hdr, hok, hres⟩ := hash_ret hA
  have F := facts_of_A (d := table[108]!) (by decide) (by decide) hA
  have hpre := F.common.2.1
  have hav := F.common.avail
  have h3 : σ.t = 3 := arm3 F.arms (by decide)
  have hle := hashList_le hpre h3 hl
  have hlenP := payload_len hpre
  have hjp : j ≤ p := by
    have := skip_le hsk
    simp only [TX.itemPayload, List.length_take, List.length_drop] at this
    omega
  have hne := res_ok (by decide) hres herr
  cases hd : F2.decode ((σ.payload.drop (c + h + j)).take (p - j)) with
  | error => exact absurd hd hne
  | success l h' p' =>
  obtain ⟨hL, hP, hK, hW⟩ := res_words hav (by decide) hres hd
  have hl0 : l = false := by
    cases l
    · rfl
    · rw [hL] at hlist; exact absurd hlist (by decide)
  have hp32 : p' % 2 ^ 64 = 32 := by
    rw [hP] at hlen
    have := congrArg BitVec.toNat hlen
    simpa [w] using this
  have hp32' : p' = 32 := by have := decode_p_lt hd; omega
  obtain ⟨hh9, h128⟩ := decode_hdr hd
  have hcons := decode_consumed_le hd
  simp only [TX.itemConsumed, List.length_take, List.length_drop] at hcons
  have hcons' : (h' + p') % 2 ^ 64 = h' + 32 := by omega
  refine ⟨c, h, p, n, j, h' + 32, hl, hsk, ?_, hnj, by omega, by omega, hle, r23, r22, r25, hdr,
    hashesOk_succ hok hsk (h := h') ?_, ?_, ?_⟩
  · have := skip_snoc hsk (by rw [itemPayload_drop]; exact hd)
    rw [this]; simp only [TX.itemConsumed, hcons']
  · rw [itemPayload_drop, hd, hl0, hp32']
  · rw [hK]; apply BitVec.eq_of_toNat_eq; simp only [w, BitVec.toNat_ofNat]; omega
  · have hp0 : p' ≠ 0 := fun h0 => by rw [h0] at hp32; simp at hp32
    rw [hW, if_neg (fun h1 => hp0 (h128 h1)), show h' + 32 - 32 = h' by omega]
    simp only [w]; rw [F1.add_add_ofNat]

/-- The leaf's conditions: no error, a string, 32 payload bytes. -/
theorem hash_conds {σ : Sig} {m : Machine}
    (hc : ∀ b ∈ ((leavesAt 0x800020c0)[3]!).conds, b.eval (envOf (table[108]!).shape σ m) = true) :
    (Sym.init 0 (0x2e0 + 32) 2).eval (envOf (table[108]!).shape σ m) = 0 ∧
    (isL 0x2e0).eval (envOf (table[108]!).shape σ m) = 0 ∧
    (Sym.init 0 (0x2e0 + 8) 8).eval (envOf (table[108]!).shape σ m) = 32 := by
  have h1 := hc _ (show SBool.eq (.init 0 768 2) (.lit 0) ∈ _ by decide)
  have h2 := hc _ (show SBool.eq (isL 0x2e0) (.lit 0) ∈ _ by decide)
  have h3 := hc _ (show SBool.eq (.init 0 744 8) (.lit 32) ∈ _ by decide)
  simp only [SBool.eval, beq_iff_eq] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- A 32-byte item (`0x800020c0`, leaf 3): its four words read, `ensureTotalCapacity(n + 1)`. -/
theorem DTF.leaf_800020c0_3 :
    LeafGoal DTF.plan DTF.plan.cuts[108]! ((DTF.plan.leaves 0x800020c0)[3]!) := by
  refine leaf_call_xo (table[108]!) (table[109]!) (siteAt 109) ((leavesAt 0x800020c0)[3]!)
    F1.entry (by decide) DTF.cut_800020c0 (by decide) (by decide) ?_ (by decide) rfl rfl
    (by decide) ?_
  · intro σ m hA hc
    obtain ⟨he, hli, hln⟩ := hash_conds hc
    obtain ⟨c, h, p, n, j, k, -, -, -, -, hk32, hjk, hle, -, -, -, -, -, -, hW⟩ :=
      hash_item hA he hli hln
    have hob : ((leavesAt 0x800020c0)[3]!).obligs = [.inBounds 3 0 (.var 156) 1 8,
        .inBounds 3 8 (.var 156) 1 8, .inBounds 3 16 (.var 156) 1 8,
        .inBounds 3 24 (.var 156) 1 8] := by decide
    have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
    have hv : ((Sym.var 156).eval (envOf (table[108]!).shape σ m)).toNat =
        c + h + j + (k - 32) := by
      rw [var_slot (by decide), show 8 * (156 - 64) = 0x2e0 from rfl, hW]
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
      simp only [w, BitVec.toNat_ofNat]
      omega
    intro o ho
    rw [hob] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;>
      simp only [Oblig.holds, env_size3, hv] <;> omega
  intro σ m m' hA hc C CF
  obtain ⟨he, hli, hln⟩ := hash_conds hc
  obtain ⟨c, h, p, n, j, k, hl, hsk, hsk1, hnj, hk32, hjk, hle, r23, r22, r25, hdr, hok, hK, -⟩ :=
    hash_item hA he hli hln
  have hpre := C.F.common.2.1
  have e23 := ctx_reg C (i := 23) (i' := 23) (by decide) (by decide) (by decide)
  have e22 := ctx_reg C (i := 22) (i' := 22) (by decide) (by decide) (by decide)
  have e25 := ctx_reg C (i := 25) (i' := 25) (by decide) (by decide) (by decide)
  have e20 : m'.reg 20 = w k := by
    rw [show (20 : Fin 32) = Fin.ofNat 32 20 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x800020c0)[3]!).S.reg 20 = .init 0 (0x2e0 + 24) 8 by decide, hK]
  have e12 : m'.reg 12 = w (n + 1) := by
    rw [show (12 : Fin 32) = Fin.ofNat 32 12 from rfl, reg_eval C.hm' (by decide),
      show ((leavesAt 0x800020c0)[3]!).S.reg 12 = .bin .add (.var 25) (.lit 1) by decide]
    simp only [Sym.eval, BinOp.eval, envOf, show (25 : Nat) < 32 by decide, if_true]
    rw [show (Fin.ofNat 32 25 : Fin 32) = 25 from rfl, r25]
    simp only [w]; rw [BitVec.ofNat_add]
  have hdr' := hdr_keep C (o := 0x258) (by decide) (by decide) (by decide) (by decide) hdr
  have hitem : HashItem σ m' 0 := ⟨c, h, p, n, j, k, hl, hsk, hsk1, by omega, hk32,
    e23.trans r23, e22.trans r22, e25.trans r25, e20, hdr', hok⟩
  have hsp : m'.reg 2 = σ.fr + w 0 := CF.shape.1 (2, .fr 0) (by decide) _ rfl
  have hhdr : m'.reg 10 = σ.fr + w 0x258 := CF.shape.1 (10, .fr 0x258) (by decide) _ rfl
  have hao : m'.reg 11 = σ.ao + w 0 := CF.shape.1 (11, .ao 0) (by decide) _ rfl
  have hn : n + 1 < 2 ^ 32 := by have := len_lt32 hpre; omega
  obtain ⟨L, X, items, hpre1, hlive, hbuf⟩ := f1_pre_dtf CF.common hsp hhdr hao e12 hn
    (by decide) (by decide) hdr' CF.aligned
  have hidx : IdxOk (siteAt 109).kind σ (L, items, ⟨[], []⟩) m' := by
    rw [show (siteAt 109).kind = .f1 by decide]; exact ⟨hpre1, X, hlive, hbuf⟩
  have h25 : m'.reg 25 = w n := e25.trans r25
  have hsx : SiteX (table[109]!).pc σ (L, items, ⟨[], []⟩) m' := by
    rw [show (table[109]!).pc = 0x8000211c by decide]
    simp only [SiteX, show (0x8000211c : Nat) ≠ 0x800020c0 by decide, if_false, if_true]
    refine ⟨hitem, ?_⟩
    rw [e12, h25]; simp only [w]; rw [BitVec.ofNat_add]; rfl
  refine ⟨_, hidx, hsx, fun m'' hpost => ?_⟩
  have hfld := CF.fields
  have hsite : SiteA (siteAt 109) (table[109]!).pc σ (L, items, ⟨[], []⟩) m' :=
    ⟨CF.ra, CF.common, CF.shape, CF.arms, CF.rest, hidx, hfld, CF.chk, hsx⟩
  have hSF : (siteAt 109).kind.SiteFine (siteAt 109) = true := by decide
  have hR := ret_len C hSF hsite hpost (by decide)
  have e22' : m''.reg 22 = m'.reg 22 := (ret_common hSF hsite hpost).1.2 22 (by decide)
  rw [show (siteAt 109).kind.bound = 197 by decide]
  unfold budgetOf
  rw [show budgetAt (table[109]!).pc = (2571, .list (.reg 22)) from rfl,
    show budgetAt (table[108]!).pc = (2791, .list (.reg 22)) from rfl,
    show ((leavesAt 0x800020c0)[3]!).S.steps - (table[108]!).shape.S.steps = 23 by decide]
  simp only [innerOf, Loc.word]
  rw [show (Fin.ofNat 32 22 : Fin 32) = 22 from rfl, e22', show (22 : Fin 32) = Fin.ofNat 32 22
    from rfl, e22]
  omega

end ZesuExec.Fn.DTF
