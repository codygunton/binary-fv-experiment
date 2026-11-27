import ZesuExec.Fn.DTF.Keep

/-!
# DTF: `decodeItem` outcomes and `rest` advances (programme plan S7 step 4)

After a `decodeItem` return with a zero error halfword, `rest` after `k + 1` items is `rest` after
`k` items plus the consumed length the outcome holds (`AdvOk`, from the callee's `Post` at the
return site, `adv_of_A`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Item counts -/

theorem decode_consumed_le {b : List Byte} {l : Bool} {h p : Nat}
    (hd : F2.decode b = .success l h p) : TX.itemConsumed h p ≤ b.length := by
  cases b with
  | nil => simp [F2.decode] at hd
  | cons pre rest =>
    unfold TX.itemConsumed
    simp only [F2.decode, F2.checkedPayload] at hd
    simp only [List.length_cons]
    repeat' split at hd
    all_goals (try simp only [F2.Item.success.injEq, reduceCtorEq] at hd)
    all_goals (try (obtain ⟨-, rfl, rfl⟩ := hd))
    all_goals omega

theorem skip_le : ∀ {k : Nat} {b : List Byte} {c : Nat}, skip k b = some c → c ≤ b.length
  | 0, _, c, h => by simp [skip] at h; omega
  | k + 1, b, c, h => by
    simp only [skip] at h
    split at h
    · next l hh p hd =>
      obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp h
      have := skip_le h'
      have := decode_consumed_le hd
      simp only [List.length_drop] at *
      omega
    · cases h

theorem skip_snoc : ∀ {k : Nat} {b : List Byte} {c : Nat}, skip k b = some c →
    ∀ {l : Bool} {h p : Nat}, F2.decode (b.drop c) = .success l h p →
    skip (k + 1) b = some (c + TX.itemConsumed h p)
  | 0, b, c, hs, l, h, p, hd => by
    simp [skip] at hs; subst hs
    simp only [List.drop_zero] at hd
    simp [skip, hd]
  | k + 1, b, c, hs, l, h, p, hd => by
    simp only [skip] at hs
    split at hs
    · next l0 h0 p0 hd0 =>
      obtain ⟨c', h', rfl⟩ := Option.map_eq_some_iff.mp hs
      have ih := skip_snoc h' (l := l) (h := h) (p := p) (by
        rw [List.drop_drop]; first | exact hd | (rw [Nat.add_comm]; exact hd))
      show (match F2.decode b with
        | .success _ h p => (skip (k + 1) (b.drop (TX.itemConsumed h p))).map
            (TX.itemConsumed h p + ·)
        | .error => none) = _
      rw [hd0]; simp only [ih, Option.map_some]; congr 1; omega
    · cases hs

theorem payload_len {σ : Sig} (hpre : Pre σ.A σ.g σ.m) : σ.payload.length = σ.len := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hl, -⟩ := hpre
  exact hl

/-- The payload after `c` bytes, at `inp + c`. -/
theorem input_bytes {σ : Sig} {m : Machine} (hc : Avail σ m) {c : Nat} (hcl : c ≤ σ.len) :
    BytesAt m (σ.inp + w c) (σ.payload.drop c) := by
  have hpre := hc.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, hl, -⟩ := hpre
  intro i hi
  simp only [List.length_drop] at hi
  have hl' : σ.payload.length = σ.len := hl
  have hlt : c + i < σ.len := by omega
  rw [show σ.inp + w c + BitVec.ofNat 64 i = σ.inp + BitVec.ofNat 64 (c + i) by
    simp only [w]; rw [F1.add_add_ofNat], hc.inp hlt, hb (c + i) (by rw [hl']; exact hlt)]
  simp

/-! ## Frame reads -/

/-- An initial frame read inside bytes `bs` at frame offset `ko`. -/
theorem init_frame {sh : Shape} {σ : Sig} {m : Machine} {ko : Nat} {bs : List Byte}
    (hb : BytesAt m (σ.fr + w ko) bs) {off n : Nat} (hn : off + n ≤ bs.length) :
    (Sym.init 0 (ko + off) n).eval (envOf sh σ m) = ofBytesLE ((bs.drop off).take n) := by
  simp only [Sym.eval]
  congr 1
  induction n generalizing off with
  | zero => simp [byteList]
  | succ n ih =>
    rw [show (bs.drop off).take (n + 1) = bs[off]'(by omega) :: (bs.drop (off + 1)).take n by
      rw [List.drop_eq_getElem_cons (by omega)]; rfl]
    simp only [byteList]
    congr 1
    · simp only [Env.byte0, envOf, entryEnv, regionsOf, List.cons_append, List.getD_cons_zero]
      rw [show σ.fr + BitVec.ofNat 64 (ko + off) = σ.fr + w ko + BitVec.ofNat 64 off by
        simp only [w]; rw [F1.add_add_ofNat], hb off (by omega)]
      rfl
    · rw [show ko + off + 1 = ko + (off + 1) by omega]
      exact ih (by omega)

/-! ## `decodeItem`'s outcome at a return site -/

/-- A `decodeItem` call site: the outcome's frame offset and the item count of the call's input
(`a1`/`a2` hold `rest` after `k` items). -/
def f2Site (s : Site) : Option (Nat × Nat) :=
  if s.kind = .f2 then
    match regFr s 10, s.rest.find? (fun r => r.loc == .reg 11 && !r.len),
      s.rest.find? (fun r => r.loc == .reg 12 && r.len) with
    | some ko, some r1, some r2 => if r1.k = r2.k then some (ko, r1.k) else none
    | _, _, _ => none
  else none

/-- A return site reached only from its `decodeItem` call. -/
def advOf (d : CutData) : Option (Nat × Nat) :=
  if d.plain then none else d.site.bind f2Site

/-- A zero error halfword means `rest` after `k + 1` items is `rest` after `k` plus the consumed
length at `ko + 24`. -/
def AdvOk (d : CutData) (σ : Sig) (m : Machine) (ko k : Nat) : Prop :=
  ∀ c, skip k σ.payload = some c → (Sym.init 0 (ko + 32) 2).eval (envOf d.shape σ m) = 0 →
    ∃ ic, skip (k + 1) σ.payload = some (c + ic) ∧
      (Sym.init 0 (ko + 24) 8).eval (envOf d.shape σ m) = w ic

theorem result40_consumed (p : Word) (input before : List Byte) :
    ((F2.result40 p input before).drop 24).take 8 =
      (List.range 8).map fun j => F2.resultByte p input before (24 + j) := rfl

theorem f2Site_spec {s : Site} {ko k : Nat} (h : f2Site s = some (ko, k)) :
    s.kind = .f2 ∧ regFr s 10 = some ko ∧
      (∃ r1 ∈ s.rest, r1.loc = .reg 11 ∧ r1.len = false ∧ r1.k = k) ∧
      (∃ r2 ∈ s.rest, r2.loc = .reg 12 ∧ r2.len = true ∧ r2.k = k) := by
  unfold f2Site at h
  by_cases hk : s.kind = .f2
  case neg => simp [hk] at h
  simp only [hk, if_true] at h
  cases hko : regFr s 10 <;> cases h1 : s.rest.find? (fun r => r.loc == .reg 11 && !r.len) <;>
    cases h2 : s.rest.find? (fun r => r.loc == .reg 12 && r.len) <;>
    simp only [hko, h1, h2, reduceCtorEq] at h
  rename_i ko' r1 r2
  by_cases h12 : r1.k = r2.k
  case neg => simp [h12] at h
  simp only [h12, if_true, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hr1 := List.find?_some h1
  have hr2 := List.find?_some h2
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hr1 hr2
  exact ⟨hk, rfl, ⟨r1, List.mem_of_find?_eq_some h1, hr1.1, hr1.2, h12⟩,
    ⟨r2, List.mem_of_find?_eq_some h2, hr2.1, hr2.2, rfl⟩⟩

theorem advOf_spec {d : CutData} {ko k : Nat} (h : advOf d = some (ko, k)) :
    d.plain = false ∧ ∃ s, d.site = some s ∧ s.kind = .f2 ∧ regFr s 10 = some ko ∧
      (∃ r1 ∈ s.rest, r1.loc = .reg 11 ∧ r1.len = false ∧ r1.k = k) ∧
      (∃ r2 ∈ s.rest, r2.loc = .reg 12 ∧ r2.len = true ∧ r2.k = k) := by
  unfold advOf at h
  cases hpl : d.plain
  case true => simp [hpl] at h
  simp only [hpl, Bool.false_eq_true, if_false] at h
  obtain ⟨s, hs, hf⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨rfl, s, hs, f2Site_spec hf⟩

/-- At a `decodeItem` return site: the outcome bytes at `ko` are `result40` of the call's input,
`rest` after `k` items. -/
theorem f2_out {d : CutData} {σ : Sig} {m : Machine} {ko k : Nat} (hpc : d.pc ≠ entry)
    (hsrc : SrcOk d = true) (hadv : advOf d = some (ko, k)) (hA : (mkCut d).A σ m) :
    ∃ c before, skip k σ.payload = some c ∧ c ≤ σ.len ∧ ko + 40 ≤ frameBytes ∧
      BytesAt m (σ.fr + w ko) (F2.result40 (σ.inp + w c) (σ.payload.drop c) before) := by
  obtain ⟨hpl, s, hs, hkind, hko, ⟨r1, hm1, hl1, hn1, hk1⟩, ⟨r2, hm2, hl2, hn2, hk2⟩⟩ :=
    advOf_spec hadv
  simp only [mkCut, if_neg hpc, ACut, hs] at hA
  rcases hA with ⟨h, -⟩ | ⟨s', hs', mc, x, hsite, hpost⟩
  · simp [hpl] at h
  simp only [Option.some.injEq] at hs'
  subst hs'
  simp only [SrcOk, hs, RetCheck, Bool.and_eq_true] at hsrc
  have hfine := hsrc.1.1.1
  rw [hkind] at hfine
  simp only [Kind.SiteFine, hko, Bool.and_eq_true, decide_eq_true_eq] at hfine
  have hko' := hfine.2
  have hc := hsite.2.1
  have hpre := hc.2.1
  have hav := hc.avail
  have hlen := payload_len hpre
  -- the call's registers
  have hout : mc.reg 10 = σ.fr + w ko := hsite.2.2.1.1 _ (lookup_mem (regFr_spec hko)) _ rfl
  obtain ⟨c1, hs1, hw1⟩ := hsite.2.2.2.2.1 r1 hm1
  obtain ⟨c2, hs2, hw2⟩ := hsite.2.2.2.2.1 r2 hm2
  rw [hk1] at hs1
  rw [hk2, hs1] at hs2
  simp only [Option.some.injEq] at hs2
  subst hs2
  rw [hl1, hn1] at hw1
  rw [hl2, hn2] at hw2
  simp only [Loc.word, if_true, Bool.false_eq_true, if_false] at hw1 hw2
  have hin : mc.reg 11 = σ.inp + w c1 := hw1
  have hln : mc.reg 12 = w σ.len - w c1 := hw2
  have hcl : c1 ≤ σ.len := by have := skip_le hs1; omega
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hl12 : (mc.reg 12).toNat = σ.len - c1 := by
    rw [hln]; simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- the outcome bytes
  obtain ⟨before, hbl, hbb⟩ := TX.bytes_of_present (m := mc) (a := mc.reg 10) (n := 40) fun j hj => by
    rw [hout, show σ.fr + w ko + BitVec.ofNat 64 j = σ.fr + BitVec.ofNat 64 (ko + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
    exact stack_present hav (by omega)
  have hkind' : s.kind = .f2 := hkind
  obtain ⟨hq, -⟩ := hpost
  replace hq : F2.Post mc m := by rw [hkind'] at hq; exact hq
  have hres := hq.2.2 (σ.payload.drop c1) before (by rw [hin]; exact input_bytes hav hcl)
    (by rw [hl12]; simp only [List.length_drop, hlen]) hbb hbl
  rw [hout, hin] at hres
  exact ⟨c1, before, hs1, hcl, by omega, hres⟩

theorem adv_of_A {d : CutData} {σ : Sig} {m : Machine} {ko k : Nat} (hpc : d.pc ≠ entry)
    (hsrc : SrcOk d = true) (hadv : advOf d = some (ko, k)) (hA : (mkCut d).A σ m) :
    AdvOk d σ m ko k := by
  intro c hskip herr
  obtain ⟨c1, before, hs1, -, -, hres⟩ := f2_out hpc hsrc hadv hA
  rw [hskip, Option.some.injEq] at hs1
  subst hs1
  have hrl : (F2.result40 (σ.inp + w c) (σ.payload.drop c) before).length = 40 := by
    simp [F2.result40]
  rw [init_frame hres (by rw [hrl]; decide), TX.result40_err] at herr
  have hne := (TX.err_half).mp (by simpa using herr)
  cases hd : F2.decode (σ.payload.drop c) with
  | error => exact absurd hd hne
  | success l h p =>
    refine ⟨TX.itemConsumed h p, skip_snoc hskip hd, ?_⟩
    rw [init_frame hres (by rw [hrl]; decide), result40_consumed]
    simp only [F2.resultByte, hd, F2.successByte]
    have e : ∀ j ∈ List.range 8, (if 24 + j < 8 then
          byteOf (if (σ.payload.drop c).head? = some 128 then 1 else σ.inp + w c + BitVec.ofNat 64 h)
            (24 + j)
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
    have hb : (List.range 8).map (byteOf (BitVec.ofNat 64 (h + p))) =
        byteList (byteOf (BitVec.ofNat 64 (h + p))) 0 8 := rfl
    rw [hb, ofBytesLE_bytes8]
    simp only [w, TX.itemConsumed]
    apply BitVec.eq_of_toNat_eq
    simp

/-- A `decodeItem` success: the header is at most 9 bytes, and the empty string `0x80` has an
empty payload. -/
theorem decode_hdr {b : List Byte} {l : Bool} {h p : Nat}
    (hd : F2.decode b = .success l h p) : h ≤ 9 ∧ (b.head? = some 128 → p = 0) := by
  cases b with
  | nil => simp [F2.decode] at hd
  | cons pre rest =>
    have hlt := pre.isLt
    simp only [F2.decode, F2.checkedPayload] at hd
    simp only [List.head?_cons, Option.some.injEq]
    repeat' split at hd
    all_goals (try simp only [F2.Item.success.injEq, reduceCtorEq] at hd)
    all_goals (try (obtain ⟨-, rfl, rfl⟩ := hd))
    all_goals (refine ⟨by omega, fun h128 => ?_⟩; subst h128; simp_all)

theorem result40_len (p : Word) (input before : List Byte) :
    ((F2.result40 p input before).drop 8).take 8 =
      (List.range 8).map fun j => F2.resultByte p input before (8 + j) := rfl

/-- A word whose eight bytes are those of `y`. -/
theorem word_of_bytes {x y : Word} (h : ∀ t < 8, byteOf x t = byteOf y t) : x = y := by
  rw [← ofBytesLE_bytes8 x, ← ofBytesLE_bytes8 y]
  simp only [byteList]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-- At a `decodeItem` return site with a zero error halfword and a nonzero payload length of at
most 32: the payload pointer word at `ko` is `inp + c'` and the payload ends inside the payload
(the header is at most 9 bytes, so the consumed length does not wrap). -/
theorem out_ptr {d : CutData} {σ : Sig} {m : Machine} {ko k : Nat} (hpc : d.pc ≠ entry)
    (hsrc : SrcOk d = true) (hadv : advOf d = some (ko, k)) (hA : (mkCut d).A σ m)
    (herr : (Sym.init 0 (ko + 32) 2).eval (envOf d.shape σ m) = 0)
    (hq0 : (Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m) ≠ 0)
    (hq : ((Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m)).toNat ≤ 32) :
    ∃ c', TX.wordAt m (σ.fr + w ko) = σ.inp + w c' ∧
      c' + ((Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m)).toNat ≤ σ.len := by
  obtain ⟨c, before, -, hcl, hko, hres⟩ := f2_out hpc hsrc hadv hA
  have hav : Avail σ m := (facts_of_A hpc hsrc hA).common.avail
  have hlen := payload_len hav.pre
  have hrl : (F2.result40 (σ.inp + w c) (σ.payload.drop c) before).length = 40 := by
    simp [F2.result40]
  rw [init_frame hres (by rw [hrl]; omega), TX.result40_err] at herr
  have hne := (TX.err_half).mp (by simpa using herr)
  rw [init_frame hres (by rw [hrl]; omega), result40_len] at hq0 hq ⊢
  cases hd : F2.decode (σ.payload.drop c) with
  | error => exact absurd hd hne
  | success l h p =>
    have hpw : ofBytesLE ((List.range 8).map fun j =>
        F2.resultByte (σ.inp + w c) (σ.payload.drop c) before (8 + j)) = w p := by
      simp only [F2.resultByte, hd, F2.successByte]
      have e : ∀ j ∈ List.range 8, (if 8 + j < 8 then
            byteOf (if (σ.payload.drop c).head? = some 128 then 1 else
              σ.inp + w c + BitVec.ofNat 64 h) (8 + j)
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
    rw [hpw] at hq0 hq ⊢
    have hp0 : p % 2 ^ 64 ≠ 0 := by
      intro h0; apply hq0; apply BitVec.eq_of_toNat_eq; simp [w, h0]
    have hpq : (w p).toNat = p % 2 ^ 64 := by simp [w]
    rw [hpq] at hq ⊢
    obtain ⟨hh9, h128⟩ := decode_hdr hd
    have hcons := decode_consumed_le hd
    simp only [TX.itemConsumed, List.length_drop] at hcons
    have hnot : (σ.payload.drop c).head? ≠ some 128 := fun h' => by
      have := h128 h'; subst this; simp at hp0
    refine ⟨c + h, ?_, by omega⟩
    -- the pointer word is bytes 0..7 of the outcome
    have hl := frame_load hav (o := ko) (by omega)
    have hb := load_bytes hl (by omega)
    apply word_of_bytes
    intro t ht
    have h1 := hb t ht
    have h2 := hres t (by rw [hrl]; omega)
    rw [h1] at h2
    simp only [Option.some.injEq] at h2
    rw [h2]
    simp only [F2.result40, List.getElem_map, List.getElem_range, F2.resultByte, hd,
      F2.successByte, if_pos ht, hnot, if_false]
    congr 1
    simp only [w]; rw [F1.add_add_ofNat]

/-! ## `decodeItem`'s precondition at a call -/

theorem f2_pre_dtf {σ : Sig} {m : Machine} (hc : Common σ m) {ko c : Nat}
    (hsp : m.reg 2 = σ.fr + w 0) (hout : m.reg 10 = σ.fr + w ko) (hko : ko + 40 + 104 ≤ frameBytes)
    (hko8 : ko % 8 = 0) (hin : m.reg 11 = σ.inp + w c) (hlen : m.reg 12 = w σ.len - w c)
    (hcl : c ≤ σ.len) (hra : RetAligned m) : F2.Pre m := by
  have hpre := hc.2.1
  have hav := hc.avail
  obtain ⟨hlo, hhi, hal⟩ := pre_sp hpre
  have hF : σ.fr.toNat = σ.S.toNat - frameBytes := fr_toNat hpre
  have h2 : (σ.S - w stackBytes).toNat = σ.S.toNat - stackBytes :=
    S_sub_toNat hpre (Nat.le_refl _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hia, -, -, -, -, -, -, -, -, -, -, hfi, -⟩ := hpre
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hia' : (Layout.inputLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.inputHi) ∨
      (Layout.ramLo ≤ σ.inp.toNat ∧ σ.inp.toNat + σ.len ≤ Layout.ramHi) := hia
  have hfi' : σ.S.toNat - stackBytes + stackBytes ≤ σ.inp.toNat ∨
      σ.inp.toNat + σ.len ≤ σ.S.toNat - stackBytes := by
    unfold TX.Apart at hfi; rw [← h2]; exact hfi
  clear hia hfi
  have hsp0 : (m.reg 2).toNat = σ.fr.toNat := by rw [hsp]; simp [w]
  have hio : (m.reg 11).toNat = σ.inp.toNat + c := by
    rw [hin]; exact toNat_add_ofNat (by
      unfold Layout.inputHi Layout.ramHi at hia'; omega)
  have hfrk : (m.reg 10).toNat = σ.fr.toNat + ko := by
    rw [hout]; exact toNat_add_ofNat (by unfold Layout.ramHi frameBytes at *; omega)
  have hl12 : (m.reg 12).toNat = σ.len - c := by
    rw [hlen]; simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsub : (m.reg 2 - 16).toNat = σ.fr.toNat - 16 := by
    rw [BitVec.toNat_sub, hsp0]
    rw [show (16 : Word).toNat = 16 from rfl]
    unfold Layout.ramLo stackBytes TX.stackBytes frameBytes at *; omega
  refine ⟨hc.2.2.1, ⟨?_, ?_, ?_, ?_⟩, hra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp0, hF]; unfold frameBytes; omega
  · rw [hsp0, hF]; unfold Layout.ramLo stackBytes TX.stackBytes frameBytes at *; omega
  · rw [hsp0, hF]; unfold frameBytes; omega
  · intro j hj
    have := hav.stack (stackBytes - frameBytes - 16 + j) (by
      unfold stackBytes TX.stackBytes frameBytes; omega)
    rwa [show σ.S - w stackBytes + BitVec.ofNat 64 (stackBytes - frameBytes - 16 + j) =
      m.reg 2 - BitVec.ofNat 64 16 + BitVec.ofNat 64 j by
        rw [hsp]; simp only [Sig.fr, w]; unfold stackBytes TX.stackBytes frameBytes
        bv_omega] at this
  · rw [hio, hl12]
    simp only [Machine.readable, Machine.inRange, Layout.rodataLo, Layout.rodataHi,
      Layout.inputLo, Layout.inputHi, Layout.ramLo, Layout.ramHi, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    unfold Layout.inputLo Layout.inputHi Layout.ramLo Layout.ramHi at hia'
    omega
  · intro j hj
    rw [hl12] at hj
    have := input_present hav (j := c + j) (by omega)
    rwa [hin, show σ.inp + w c + BitVec.ofNat 64 j = σ.inp + BitVec.ofNat 64 (c + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
  · rw [hfrk]
    simp only [Machine.writable, Machine.inRange, Layout.ramLo, Layout.ramHi,
      Bool.and_eq_true, decide_eq_true_eq]
    unfold Layout.ramLo Layout.ramHi stackBytes TX.stackBytes frameBytes at *; omega
  · rw [hfrk, hF]; unfold frameBytes at *; omega
  · intro j hj
    rw [hout, show σ.fr + w ko + BitVec.ofNat 64 j = σ.fr + BitVec.ofNat 64 (ko + j) by
      simp only [w]; rw [F1.add_add_ofNat]]
    exact stack_present hav (by unfold frameBytes at *; omega)
  · unfold Fn.Disjoint; simp only; rw [hio, hfrk, hl12, hF]
    unfold stackBytes TX.stackBytes frameBytes at *; omega
  · unfold Fn.Disjoint; simp only; rw [hio, hl12, hsub, hF]
    unfold stackBytes TX.stackBytes frameBytes at *; omega
  · have h16 : 16 ≤ σ.fr.toNat := by
      rw [hF]; simp only [Layout.ramLo, stackBytes, TX.stackBytes, frameBytes] at hlo ⊢; omega
    unfold Fn.Disjoint; simp only; rw [hfrk, hsub]; omega

/-! ## The generic leaf -/

/-- The advance a leaf may use: the source's outcome, when the leaf's conditions say its error
halfword is zero. -/
def advUse (d : CutData) (l : Leaf) : Option (Nat × Nat) :=
  match advOf d with
  | some (ko, k) =>
    if l.conds.contains (.eq (.init 0 (ko + 32) 2) (.lit 0)) then some (ko, k) else none
  | none => none

/-- `r'` (in the leaf state `S'`) holds what `r` held (in `S`), or that advanced by one item. -/
def locFrom (S S' : SState) (adv : Option (Nat × Nat)) (r r' : RestLoc) : Bool :=
  r.loc.fine && r'.loc.fine && r.len == r'.len &&
    ((r.k == r'.k && r'.loc.sym S' == r.loc.sym S) ||
     match adv with
     | some (ko, k) => r.k == k && r'.k == k + 1 &&
         r'.loc.sym S' == .bin (if r.len then .sub else .add) (r.loc.sym S) (.init 0 (ko + 24) 8)
     | none => false)

def restFrom (S S' : SState) (adv : Option (Nat × Nat)) (rs rs' : List RestLoc) : Bool :=
  rs'.all fun r' => rs.any fun r => locFrom S S' adv r r'

/-- The target's `rest` length location against a source length location of the same item count
as the source's first (all of them hold the same length, `RestOk`). -/
def lenFrom (S S' : SState) (adv : Option (Nat × Nat)) (rs kr rs' : List RestLoc) : Bool :=
  match rs'.find? (·.len) with
  | none => true
  | some r' => match rs.find? (·.len) with
    | some r => kr.contains r && kr.any fun r0 => r0.len && r0.k == r.k && locFrom S S' adv r0 r'
    | none => false

/-! ## `rest` after an accepted access list (TX return sites) -/

/-- A TX call site: the frame offsets of TX's result and of the `rest` slice it moves. -/
def txSite (s : Site) : Option (Nat × Nat) :=
  if s.kind = .tx then
    match regFr s 10, regFr s 12 with
    | some ko, some ro => some (ko, ro)
    | _, _ => none
  else none

theorem txSite_spec {s : Site} {ko ro : Nat} (h : txSite s = some (ko, ro)) :
    s.kind = .tx ∧ regFr s 10 = some ko ∧ regFr s 12 = some ro := by
  unfold txSite at h
  split at h
  · next hk =>
    split at h
    · next a b ha hb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hk, ha, hb⟩
    · cases h
  · cases h

/-- A return-site `rest` location of the slice TX moved, one item on from the call's, whose two
words the call site locates. -/
def txLoc (s : Site) (ro : Nat) (r : RestLoc) : Bool :=
  decide (0 < r.k) &&
    (r == ⟨.slot ro, false, r.k⟩ || r == ⟨.slot (ro + 8), true, r.k⟩) &&
    s.rest.contains ⟨.slot ro, false, r.k - 1⟩ && s.rest.contains ⟨.slot (ro + 8), true, r.k - 1⟩

/-- The return site's moved `rest` locations, for a leaf that tests TX's error halfword zero. -/
def txRest (d : CutData) (l : Leaf) : List RestLoc :=
  match d.site with
  | some s =>
    match txSite s with
    | some (ko, ro) =>
      if d.plain = false ∧ l.conds.contains (.eq (.init 0 (ko + 16) 2) (.lit 0)) then
        d.rest.filter (txLoc s ro)
      else []
    | none => []
  | none => []

/-- The source's `rest` locations a leaf may use. -/
def srcRest (d : CutData) (l : Leaf) : List RestLoc := kRest d ++ txRest d l

theorem bytes_unique {m : Machine} {a : Word} {xs ys : List Byte} (hx : BytesAt m a xs)
    (hy : BytesAt m a ys) (hl : xs.length = ys.length) : xs = ys :=
  List.ext_getElem hl fun i h1 h2 => by
    have e := (hx i h1).symm.trans (hy i h2)
    simpa using e

/-- TX's result word at a frame offset is three: its halfword reads three. -/
theorem init_three {sh : Shape} {σ : Sig} {m : Machine} {o : Nat}
    (h : m.load (σ.fr + w o) 8 = some 3) : (Sym.init 0 o 2).eval (envOf sh σ m) = 3 := by
  have hb : BytesAt m (σ.fr + w o) ((List.range 8).map (byteOf 3)) := fun i hi => by
    simp only [List.length_map, List.length_range] at hi
    rw [load_bytes h (Nat.le_refl _) i hi]
    simp
  have := init_frame (sh := sh) (off := 0) (n := 2) hb (by simp)
  rw [Nat.add_zero] at this
  rw [this]
  decide

theorem tx_rest {d : CutData} {l : Leaf} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hA : (mkCut d).A σ m) (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) :
    RestOk σ m (txRest d l) := by
  intro r hr
  unfold txRest at hr
  split at hr
  case h_2 => cases hr
  next s hs =>
  split at hr
  case h_2 => cases hr
  next ko ro hts =>
  split at hr
  case isFalse => cases hr
  next hcond =>
  obtain ⟨hpl, hcond⟩ := hcond
  obtain ⟨hkind, hko, hro⟩ := txSite_spec hts
  obtain ⟨-, hloc⟩ := List.mem_filter.mp hr
  simp only [txLoc, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem] at hloc
  obtain ⟨⟨⟨hk0, hrl⟩, hp⟩, hn⟩ := hloc
  simp only [mkCut, if_neg hpc, ACut, hs, hpl, Bool.false_eq_true, false_and, false_or,
    Option.some.injEq, exists_eq_left'] at hA
  obtain ⟨mc, x, hsite, hpost⟩ := hA
  have hcm := hsite.2.1
  have hav := hcm.avail
  have hlen := payload_len hcm.2.1
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  have hres : mc.reg 10 = σ.fr + w ko := hsite.2.2.1.1 _ (lookup_mem (regFr_spec hko)) _ rfl
  have hrst : mc.reg 12 = σ.fr + w ro := hsite.2.2.1.1 _ (lookup_mem (regFr_spec hro)) _ rfl
  -- `rest` at the call
  obtain ⟨c0, hs0, hw0⟩ := hsite.2.2.2.2.1 _ hp
  obtain ⟨c1, hs1, hw1⟩ := hsite.2.2.2.2.1 _ hn
  rw [hs0, Option.some.injEq] at hs1
  subst hs1
  simp only [Loc.word, Bool.false_eq_true, if_false, if_true] at hw0 hw1
  have hcl : c0 ≤ σ.len := by have := skip_le hs0; omega
  have hr8 : mc.reg 12 + 8 = σ.fr + w (ro + 8) := by
    rw [hrst, show (8 : Word) = BitVec.ofNat 64 8 from rfl]; simp only [w]
    rw [F1.add_add_ofNat]
  -- TX's input is the payload after `c0`
  have hidx := hsite.2.2.2.2.2
  rw [hkind] at hidx
  obtain ⟨hpre, -⟩ := hidx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hib, hil, -⟩ := hpre
  rw [hrst] at hib
  rw [hr8] at hil
  rw [hw0] at hib
  rw [hw1] at hil
  have hil' : x.2.2.input.length = σ.len - c0 := by
    rw [hil]; simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hin : x.2.2.input = σ.payload.drop c0 :=
    bytes_unique hib (input_bytes hav hcl) (by rw [hil', List.length_drop, hlen])
  -- TX's outcome
  obtain ⟨hq, -⟩ := hpost
  replace hq : TX.Post σ.A x.2.2 mc m := by rw [hkind] at hq; exact hq
  obtain ⟨-, -, -, cls, consumed, hallow, hl0, hl8, himg⟩ := hq
  simp only at hl0 hl8 himg
  have hok : ∃ h p, F2.decode (σ.payload.drop c0) = .success true h p ∧
      consumed = TX.itemConsumed h p := by
    cases cls with
    | ok es =>
      simp only [TX.OutcomeAllowed, TX.candidate, TX.walk, hin] at hallow
      split at hallow
      · next h p hd =>
        split at hallow
        · simp only [TX.Candidate.accepted.injEq] at hallow
          exact ⟨h, p, hd, hallow.2.symm⟩
        · cases hallow
      · cases hallow
    | invalidInput | allocationFailure =>
      exfalso
      obtain ⟨-, -, h3, -⟩ := himg
      rw [hres, show σ.fr + w ko + 16 = σ.fr + w (ko + 16) by
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl]; simp only [w]
        rw [F1.add_add_ofNat]] at h3
      have := hc _ (List.contains_iff_mem.mp hcond)
      simp only [SBool.eval, Sym.eval_lit, beq_iff_eq, init_three h3] at this
      exact absurd this (by decide)
  obtain ⟨h, p, hd, rfl⟩ := hok
  have hskip := skip_snoc hs0 hd
  rw [show r.k - 1 + 1 = r.k by omega] at hskip
  refine ⟨c0 + TX.itemConsumed h p, hskip, ?_⟩
  rcases hrl with e | e <;> rw [e] <;>
    simp only [Loc.word, Bool.false_eq_true, if_false, if_true, TX.wordAt]
  · rw [← hrst, hl0, hrst, hw0]
    simp only [Option.getD_some, w]
    rw [F1.add_add_ofNat]
  · rw [← hr8, hl8, hr8, hw1]
    simp only [Option.getD_some, w]
    bv_omega

/-- What a leaf of the source cut `d` ending in `m'` knows. -/
structure Ctx (d : CutData) (l : Leaf) (σ : Sig) (m m' : Machine) : Prop where
  F : Facts d σ m
  wf : Env.WF (envOf d.shape σ m) d.shape.S
  hm : Match (envOf d.shape σ m) d.shape.S m
  hS : BaseRegs d.shape.S
  wf' : Env.WF (envOf d.shape σ m) l.S
  hm' : Match (envOf d.shape σ m) l.S m'
  hS' : BaseRegs l.S
  so : SameOutside (InWritable (envOf d.shape σ m) d.shape.S) m m'
  low : writesLow l.S = true
  adv : ∀ ko k, advUse d l = some (ko, k) →
    AdvOk d σ m ko k ∧ (Sym.init 0 (ko + 32) 2).eval (envOf d.shape σ m) = 0
  rest : RestOk σ m (srcRest d l)

theorem locFrom_sound {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {r r' : RestLoc} (hr : r ∈ srcRest d l)
    (h : locFrom d.shape.S l.S (advUse d l) r r' = true) :
    (∃ c, skip r'.k σ.payload = some c ∧
      r'.loc.word σ m' = if r'.len then w σ.len - w c else σ.inp + w c) ∧
    (r'.len = true → (r'.loc.word σ m').toNat ≤ (r.loc.word σ m).toNat) := by
  simp only [locFrom, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hf, hf'⟩, hlen⟩, h⟩ := h
  obtain ⟨c, hs, hw⟩ := C.rest r hr
  have e' := loc_word_eval C.wf' C.hm' C.hS' hf'
  have e := loc_word_eval C.wf C.hm C.hS hf
  rcases h with ⟨hk, hsym⟩ | h
  · rw [e', hsym, ← e]
    exact ⟨⟨c, hk ▸ hs, hlen ▸ hw⟩, fun _ => Nat.le_refl _⟩
  · split at h
    · next ko k hadv =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hk, hk'⟩, hsym⟩ := h
      obtain ⟨hA, herr⟩ := C.adv ko k hadv
      obtain ⟨ic, hs', hic⟩ := hA c (hk ▸ hs) herr
      have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
      have hcl := skip_le hs'
      rw [payload_len C.F.common.2.1] at hcl
      rw [e', hsym]
      simp only [Sym.eval_bin, hic, ← e, hw, hk']
      rw [← hlen]
      refine ⟨⟨c + ic, hs', ?_⟩, fun hl => ?_⟩
      · cases r.len
        · simp only [Bool.false_eq_true, if_false, BinOp.eval, w]; rw [F1.add_add_ofNat]
        · simp only [if_true, BinOp.eval, w]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
          omega
      · rw [hl]
        simp only [if_true, BinOp.eval, w, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
    · cases h

theorem restFrom_sound {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {rs' : List RestLoc} (h : restFrom d.shape.S l.S (advUse d l) (srcRest d l) rs' = true) :
    RestOk σ m' rs' := fun r' hr' => by
  simp only [restFrom, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨r, hr, hl⟩ := h r' hr'
  exact (locFrom_sound C hr hl).1

theorem lenFrom_sound {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {rs' : List RestLoc}
    (h : lenFrom d.shape.S l.S (advUse d l) d.rest (srcRest d l) rs' = true) :
    (match rs'.find? (·.len) with
      | some r => (r.loc.word σ m').toNat
      | none => 0) ≤ restLen d σ m := by
  unfold lenFrom at h
  unfold restLen
  split at h
  · next hn => rw [hn]; exact Nat.zero_le _
  · next r' h' =>
    split at h
    · next r hr =>
      rw [h', hr]
      have hl' : r'.len = true := by have := List.find?_some h'; simpa using this
      have hrl : r.len = true := by have := List.find?_some hr; simpa using this
      simp only [Bool.and_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at h
      obtain ⟨hrk, r0, hr0, ⟨hl0, hk0⟩, h0⟩ := h
      have hle := (locFrom_sound C hr0 h0).2 hl'
      obtain ⟨c0, hs0, hw0⟩ := C.rest r0 hr0
      obtain ⟨c, hs, hw⟩ := C.rest r hrk
      rw [hk0, hs] at hs0
      simp only [Option.some.injEq] at hs0
      subst hs0
      rw [hw0, hl0] at hle
      show (r'.loc.word σ m').toNat ≤ (r.loc.word σ m).toNat
      rw [hw, hrl]
      exact hle
    · cases h

/-- The target's facts at the end of the leaf. -/
theorem target_facts {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {sh : Shape} {arms : List Nat} {rs : List RestLoc} (hfine : sh.Fine = true)
    (hsh : shapeHolds l.S sh = true) (harms : armsKeep d.arms arms = true)
    (hrest : restFrom d.shape.S l.S (advUse d l) (srcRest d l) rs = true) :
    Common σ m' ∧ ShapeOk σ sh m' ∧ ArmOk σ arms ∧ RestOk σ m' rs := by
  refine ⟨common_leaf C.F.common C.wf C.hS C.hS' C.hm' C.so C.low, ⟨?_, ?_⟩,
    armOk_keep harms C.F.arms, restFrom_sound C hrest⟩
  · intro p hp v hv
    simp only [shapeHolds, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', beq_iff_eq] at hsh
    rcases hsh.1 p hp with h | h
    · rw [Val.isWord_of hv] at h; cases h
    · simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine
      have hi := (hfine.1 p hp).1
      have e : (Fin.ofNat 32 p.1 : Fin 32) = ⟨p.1, hi⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hi])
      rw [e, ← C.hm'.regs ⟨p.1, hi⟩]
      show (l.S.reg p.1).eval _ = v
      rw [h]
      exact Val.sym_eval 0 hv
  · intro p hp v hv
    simp only [shapeHolds, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', beq_iff_eq] at hsh
    rcases hsh.2 p hp with h | h
    · rw [Val.isWord_of hv] at h; cases h
    · simp only [Shape.Fine, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hfine
      have ho := (hfine.2 p hp).1.2
      have hR : l.S.regions[0]? = some frameR := by rw [C.hS']; rfl
      have := load_cst C.wf' C.hm' hR (by rw [envOf_size0]; exact ho)
      rw [env_base0, h, Val.sym_eval 0 hv] at this
      exact this

/-- A return-site `rest` location keeps its value across the call. -/
theorem ret_loc_keep {d : CutData} {s : Site} {σ : Sig} {x : Idx} {r : Nat} {mc m : Machine}
    (hk : s.kind.SiteFine s = true) (hsite : SiteA s r σ x mc)
    (hpost : (calleeOf s.kind).Post σ x mc m) (hrr : restRet d s = true) {r0 : RestLoc}
    (hr : r0 ∈ d.rest) : r0.loc.word σ m = r0.loc.word σ mc := by
  obtain ⟨hret, -, hkeep⟩ := ret_common hk hsite hpost
  simp only [restRet, retKeep, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hrr
  obtain ⟨-, hloc⟩ := hrr r0 hr
  revert hloc
  cases r0.loc with
  | reg i =>
    intro hloc
    simp only [decide_eq_true_eq] at hloc
    exact hret.2 _ hloc
  | slot o =>
    intro hloc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hloc
    simp only [Loc.word, TX.wordAt]
    rw [hkeep o hloc.1 hloc.2]

/-- A leaf's target cut. -/
def targetOf (pc : Nat) : Option CutData := table.find? (·.pc = pc)

/-- A call's budget: the callee's bound and the return site's constant part. -/
def budgetCall (pc pc' b steps : Nat) : Bool :=
  match (budgetAt pc').2 with
  | .none => decide (b + (budgetAt pc').1 + steps ≤ (budgetAt pc).1)
  | _ => false

/-! ## Byte-loop cursors -/

/-- The cursor and end registers of a byte-loop head. -/
def beOf : Inner → Option (Nat × Nat)
  | .be cur fin => some (cur, fin)
  | _ => none

theorem beOf_spec {i : Inner} {cur fin : Nat} (h : beOf i = some (cur, fin)) :
    i = .be cur fin := by
  cases i with
  | be a b =>
    simp only [beOf, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1, h.2]
  | _ => simp [beOf] at h

/-- A symbolic value as the payload base plus `x`. -/
def inpOf (s : Sym) : Option Sym :=
  match s with
  | .bin op a x => if op = .add ∧ a = .ptr 3 0 then some x else none
  | _ => none

theorem inpOf_spec {s x : Sym} (h : inpOf s = some x) : s = .bin .add (.ptr 3 0) x := by
  unfold inpOf at h
  split at h
  · next op a y =>
    split at h
    · next hc =>
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h
      rw [h]
    · cases h
  · cases h

/-- Register `i` of `S` as the payload base plus `x`. -/
def inpIdx (S : SState) (i : Nat) : Option Sym := inpOf (S.reg i)

theorem inpIdx_spec {S : SState} {i : Nat} {x : Sym} (h : inpIdx S i = some x) :
    S.reg i = .bin .add (.ptr 3 0) x := inpOf_spec h

theorem reg_eval {env : Env} {S : SState} {mm : Machine} (hm : Match env S mm) {i : Nat}
    (hi : i < 32) : mm.reg (Fin.ofNat 32 i) = (S.reg i).eval env := by
  have := hm.regs ⟨i, hi⟩
  have e : (Fin.ofNat 32 i : Fin 32) = ⟨i, hi⟩ := Fin.ext (by simp [Nat.mod_eq_of_lt hi])
  rw [e, ← this]

theorem env_size3 (sh : Shape) (σ : Sig) (m : Machine) : (envOf sh σ m).size 3 = σ.len := by
  simp [envOf, entryEnv, Env.size, regionsOf]

theorem sub_inp (a : Word) {c e : Nat} (hce : c ≤ e) (he : e < 2 ^ 64) :
    (a + w e - (a + w c)).toNat = e - c := by
  rw [show a + w e - (a + w c) = w e - w c by bv_omega]
  simp only [w, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A byte-loop head reached only by jumps and branches has its cursor. -/
theorem cur_of_A {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hs : d.site = none) (hA : (mkCut d).A σ m) : CurOk σ m (budgetAt d.pc).2 := by
  simp only [mkCut, if_neg hpc, ACut, hs, reduceCtorEq, false_and, exists_false,
    or_false] at hA
  exact hA.2.2.2.2.2.2.2

/-- The cursor of the source, as the payload offset `c` its index `x` evaluates to. -/
theorem cur_idx {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry) (hs : d.site = none)
    (hA : (mkCut d).A σ m) (hm : Match (envOf d.shape σ m) d.shape.S m) {cur fin : Nat}
    (hbe : beOf (budgetAt d.pc).2 = some (cur, fin)) (hc32 : cur < 32) {x : Sym}
    (hx : inpIdx d.shape.S cur = some x) :
    ∃ c e, x.eval (envOf d.shape σ m) = w c ∧ m.reg (Fin.ofNat 32 cur) = σ.inp + w c ∧
      m.reg (Fin.ofNat 32 fin) = σ.inp + w e ∧ c < e ∧ e ≤ σ.len ∧ e ≤ c + 32 := by
  have hcur := cur_of_A hpc hs hA
  rw [beOf_spec hbe] at hcur
  obtain ⟨c, e, h1, h2, hlt, hle, h32⟩ := hcur
  refine ⟨c, e, ?_, h1, h2, hlt, hle, h32⟩
  have h := reg_eval hm hc32
  rw [inpIdx_spec hx, h1] at h
  simp only [Sym.eval, BinOp.eval, env_base3] at h
  simp at h
  bv_omega

/-- An obligation of a byte-loop head's leaf: the read at the cursor is inside the payload. -/
def curObl (d : CutData) (o : Oblig) : Bool :=
  d.site.isNone && match beOf (budgetAt d.pc).2 with
    | some (cur, _) => decide (cur < 32) && match inpIdx d.shape.S cur with
      | some x => o == .inBounds 3 0 x 1 1
      | none => false
    | none => false

theorem curObl_holds {d : CutData} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hA : (mkCut d).A σ m) (hm : Match (envOf d.shape σ m) d.shape.S m) {o : Oblig}
    (h : curObl d o = true) : o.holds (envOf d.shape σ m) := by
  unfold curObl at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hs, h⟩ := h
  split at h
  case h_2 => cases h
  next cur fin hbe =>
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc32, h⟩ := h
  split at h
  case h_2 => cases h
  next x hx =>
  simp only [beq_iff_eq] at h
  subst h
  obtain ⟨c, e, hxc, -, -, hlt, hle, -⟩ := cur_idx hpc hs hA hm hbe hc32 hx
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  simp only [Oblig.holds, env_size3, hxc, w, BitVec.toNat_ofNat]
  omega

/-- A leaf from a byte-loop head back to it: the cursor advances by one byte, the end is kept,
and the leaf's condition says they differ. -/
def stepOk (d : CutData) (l : Leaf) (pc' steps : Nat) : Bool :=
  d.site.isNone && match beOf (budgetAt d.pc).2 with
    | some (cur, fin) =>
      beOf (budgetAt pc').2 == some (cur, fin) && decide (cur < 32) && decide (fin < 32) &&
      match inpIdx d.shape.S cur with
      | some x => l.S.reg cur == .bin .add (.ptr 3 1) x && l.S.reg fin == d.shape.S.reg fin &&
          l.conds.contains (.ne (l.S.reg cur) (l.S.reg fin)) &&
          decide ((budgetAt pc').1 + steps ≤ (budgetAt d.pc).1 + 20)
      | none => false
    | none => false

/-- The bound `b` a condition `b ≥ len` of the leaf puts on the outcome's payload length. -/
def lenBound (conds : List SBool) (ko : Nat) : Option Nat :=
  conds.findSome? fun c => match c with
    | .geu (.lit b) x => if x = .init 0 (ko + 8) 8 then some b else none
    | _ => none

theorem lenBound_spec {conds : List SBool} {ko b : Nat} (h : lenBound conds ko = some b) :
    SBool.geu (.lit b) (.init 0 (ko + 8) 8) ∈ conds := by
  obtain ⟨c, hc, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · next b' x =>
    split at hf
    · next hx =>
      simp only [Option.some.injEq] at hf
      subst hf hx
      exact hc
    · cases hf
  · cases hf

/-- A leaf from a `decodeItem` return site into a byte loop over the outcome's payload: the
cursor is the payload pointer at `ko`, the end that plus the payload length at `ko + 8`, which
the leaf's conditions say is nonzero and at most `b ≤ 32`. -/
def entryOk (d : CutData) (l : Leaf) (adv : Option (Nat × Nat)) (pc' steps : Nat) : Bool :=
  match adv, beOf (budgetAt pc').2 with
  | some (ko, _), some (cur, fin) =>
    decide (cur < 32) && decide (fin < 32) && decide (ko + 8 ≤ frameBytes) &&
    l.S.reg cur == (Loc.slot ko).sym d.shape.S &&
    l.S.reg fin == .bin .add ((Loc.slot ko).sym d.shape.S) (.init 0 (ko + 8) 8) &&
    l.conds.contains (.ne (.init 0 (ko + 8) 8) (.lit 0)) &&
    match lenBound l.conds ko with
    | some b => decide (b ≤ 32) && decide ((budgetAt pc').1 + 20 * b + steps ≤ (budgetAt d.pc).1)
    | none => false
  | _, _ => false

/-- The target's cursor and budget: no inner budget (`budgetKeep`), the source's loop
(`stepOk`) or a loop entered from a `decodeItem` outcome (`entryOk`). -/
def tgtOk (d : CutData) (l : Leaf) (pc' : Nat) : Bool :=
  budgetKeep d.pc pc' (l.S.steps - d.shape.S.steps) ||
    stepOk d l pc' (l.S.steps - d.shape.S.steps) ||
    entryOk d l (advUse d l) pc' (l.S.steps - d.shape.S.steps)

theorem advUse_spec {d : CutData} {l : Leaf} {ko k : Nat} (h : advUse d l = some (ko, k)) :
    advOf d = some (ko, k) ∧ SBool.eq (.init 0 (ko + 32) 2) (.lit 0) ∈ l.conds := by
  unfold advUse at h
  split at h
  · next ko0 k0 h0 =>
    split at h
    · next hcond =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h0, List.contains_iff_mem.mp hcond⟩
    · cases h
  · cases h

theorem tgt_steps {d : CutData} {l : Leaf} {σ : Sig} {m : Machine} {pc' : Nat}
    (hpc : d.pc ≠ entry) (hA : (mkCut d).A σ m) (hm : Match (envOf d.shape σ m) d.shape.S m)
    (h : tgtOk d l pc' = true) : l.S.steps - d.shape.S.steps ≤ budgetOf d σ m := by
  unfold tgtOk at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold budgetKeep at h
    split at h
    · simp only [decide_eq_true_eq] at h; unfold budgetOf; omega
    · cases h
  · unfold stepOk at h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hs, h⟩ := h
    split at h
    case h_2 => cases h
    next cur fin hbe =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨-, hc32⟩, hf32⟩, h⟩ := h
    split at h
    case h_2 => cases h
    next x hx =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, e, -, h1, h2, hlt, hle, -⟩ := cur_idx hpc hs hA hm hbe hc32 hx
    have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
    unfold budgetOf
    rw [beOf_spec hbe]
    simp only [innerOf]
    rw [h1, h2, sub_inp _ (Nat.le_of_lt hlt) (by omega)]
    omega
  · unfold entryOk at h
    split at h
    case h_2 => cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, h⟩ := h
    split at h
    case h_2 => cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    unfold budgetOf; omega

theorem tgt_ok {d d' : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    (hpc : d.pc ≠ entry) (hsrc : SrcOk d = true) (hA : (mkCut d).A σ m)
    (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true)
    (hlen : restLen d' σ m' ≤ restLen d σ m) (h : tgtOk d l d'.pc = true) :
    CurOk σ m' (budgetAt d'.pc).2 ∧
      budgetOf d' σ m' + (l.S.steps - d.shape.S.steps) ≤ budgetOf d σ m := by
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  unfold tgtOk at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · unfold budgetKeep at h
    split at h
    · next hinner =>
      simp only [decide_eq_true_eq] at h
      refine ⟨by rw [hinner]; trivial, ?_⟩
      unfold budgetOf; rw [hinner]; simp only [innerOf]; omega
    · cases h
  · unfold stepOk at h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hs, h⟩ := h
    split at h
    case h_2 => cases h
    next cur fin hbe =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hbe', hc32⟩, hf32⟩, h⟩ := h
    split at h
    case h_2 => cases h
    next x hx =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨hl1, hl2⟩, hne⟩, hb⟩ := h
    obtain ⟨c, e, hxc, h1, h2, hlt, hle, h32⟩ := cur_idx hpc hs hA C.hm hbe hc32 hx
    have hm1 : m'.reg (Fin.ofNat 32 cur) = σ.inp + w (c + 1) := by
      rw [reg_eval C.hm' hc32, hl1]
      simp only [Sym.eval, BinOp.eval, env_base3, hxc, w]
      rw [show BitVec.ofInt 64 1 = 1 from rfl, BitVec.ofNat_add]; bv_omega
    have hm2 : m'.reg (Fin.ofNat 32 fin) = σ.inp + w e := by
      rw [reg_eval C.hm' hf32, hl2, ← reg_eval C.hm hf32, h2]
    have hd := hc _ hne
    simp only [SBool.eval, bne_iff_ne, ne_eq] at hd
    rw [← reg_eval C.hm' hc32, ← reg_eval C.hm' hf32, hm1, hm2] at hd
    have hce : c + 1 ≠ e := fun h' => hd (by rw [h'])
    have htb := beOf_spec hbe'
    refine ⟨by rw [htb]; exact ⟨c + 1, e, hm1, hm2, by omega, hle, by omega⟩, ?_⟩
    unfold budgetOf
    rw [htb, beOf_spec hbe]
    simp only [innerOf]
    rw [hm1, hm2, h1, h2, sub_inp _ (Nat.le_of_lt hlt) (by omega), sub_inp _ (by omega) (by omega)]
    omega
  · unfold entryOk at h
    split at h
    case h_2 => cases h
    next ko k cur fin hadv hbe =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨⟨⟨hc32, hf32⟩, hko⟩, hl1⟩, hl2⟩, hne⟩, h⟩ := h
    split at h
    case h_2 => cases h
    next b hb =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb32, hbud⟩ := h
    obtain ⟨hadv', herrc⟩ := advUse_spec hadv
    have herr := hc _ herrc
    simp only [SBool.eval, Sym.eval_lit, beq_iff_eq] at herr
    have hq0 := hc _ hne
    simp only [SBool.eval, Sym.eval_lit, bne_iff_ne, ne_eq] at hq0
    have hqb := hc _ (lenBound_spec hb)
    simp only [SBool.eval, Sym.eval_lit, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
      Nat.not_lt, BitVec.toNat_ofNat] at hqb
    have hq : ((Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m)).toNat ≤ b := by omega
    obtain ⟨c', hw, hcl⟩ := out_ptr hpc hsrc hadv' hA herr hq0 (by omega)
    generalize hP : (Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m) = P at hq0 hq hcl
    have hcur : m'.reg (Fin.ofNat 32 cur) = σ.inp + w c' := by
      rw [reg_eval C.hm' hc32, hl1, ← loc_word_eval C.wf C.hm C.hS
        (by simp only [Loc.fine, decide_eq_true_eq]; omega)]
      exact hw
    have hfin : m'.reg (Fin.ofNat 32 fin) = σ.inp + w (c' + P.toNat) := by
      rw [reg_eval C.hm' hf32, hl2, Sym.eval_bin, ← loc_word_eval C.wf C.hm C.hS
        (by simp only [Loc.fine, decide_eq_true_eq]; omega), hP]
      show TX.wordAt m (σ.fr + w ko) + P = _
      rw [hw]; simp only [w]; bv_omega
    have hP0 : P.toNat ≠ 0 := fun h0 => hq0 (BitVec.eq_of_toNat_eq (by simp [h0]))
    have htb := beOf_spec hbe
    refine ⟨by rw [htb]; exact ⟨c', c' + P.toNat, hcur, hfin, by omega, hcl, by omega⟩, ?_⟩
    unfold budgetOf
    rw [htb]
    simp only [innerOf]
    rw [hcur, hfin, sub_inp _ (by omega) (by omega)]
    omega

/-- The leaf writes error code 3 into the result and ends at the result-written cut. -/
def errDone (pc : Nat) (l : Leaf) : Bool :=
  pc == 0x800011f8 && readConst l.S 1 errOff 2 == .bytes (.lit 3) 0 2

theorem extra_err {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {pc : Nat} (h : errDone pc l = true) : Extra pc σ m' := by
  simp only [errDone, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, hr⟩ := h
  unfold Extra
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  left
  have hR : l.S.regions[1]? = some resR := by rw [C.hS']; rfl
  have := load_cst C.wf' C.hm' hR (off := errOff) (n := 2)
    (by simp [envOf, entryEnv, Env.size, regionsOf, resultBytes, errOff])
  rw [env_base1, hr] at this
  rw [this]
  congr 1
  simp [Sym.eval, byteList]
  decide

/-- The payload length a leaf's condition fixes at `ko + 8`. -/
def outLen (conds : List SBool) (ko : Nat) : Option Nat :=
  conds.findSome? fun c => match c with
    | .eq x (.lit n) => if x = .init 0 (ko + 8) 8 then some n else none
    | _ => none

theorem outLen_spec {conds : List SBool} {ko n : Nat} (h : outLen conds ko = some n) :
    SBool.eq (.init 0 (ko + 8) 8) (.lit n) ∈ conds := by
  obtain ⟨c, hc, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · next x n' =>
    split at hf
    · next hx =>
      simp only [Option.some.injEq] at hf
      subst hf hx
      exact hc
    · cases hf
  · cases hf

/-- An obligation of a leaf from a `decodeItem` return site: a read inside the outcome's payload,
whose length the leaf's condition fixes to `L ≤ 32`. -/
def outObl (d : CutData) (l : Leaf) (o : Oblig) : Bool :=
  match advUse d l, o with
  | some (ko, _), .inBounds r off y sc n =>
    decide (r = 3 ∧ sc = 1 ∧ ko + 8 ≤ frameBytes) &&
    match inpOf ((Loc.slot ko).sym d.shape.S), outLen l.conds ko with
    | some x, some L => y == x && decide (0 < L ∧ L ≤ 32 ∧ off + n ≤ L)
    | _, _ => false
  | _, _ => false

theorem outObl_holds {d : CutData} {l : Leaf} {σ : Sig} {m : Machine} (hpc : d.pc ≠ entry)
    (hsrc : SrcOk d = true) (hA : (mkCut d).A σ m) (hwf : Env.WF (envOf d.shape σ m) d.shape.S)
    (hm : Match (envOf d.shape σ m) d.shape.S m) (hS : BaseRegs d.shape.S)
    (hc : ∀ b ∈ l.conds, b.eval (envOf d.shape σ m) = true) {o : Oblig}
    (h : outObl d l o = true) : o.holds (envOf d.shape σ m) := by
  unfold outObl at h
  split at h
  case h_2 => cases h
  next ko k r off y sc n hadv =>
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, rfl, hko⟩, h⟩ := h
  split at h
  case h_2 => cases h
  next x L hx hL =>
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hyx, hL0, hL32, hoff⟩ := h
  obtain ⟨hadv', herrc⟩ := advUse_spec hadv
  have herr := hc _ herrc
  simp only [SBool.eval, Sym.eval_lit, beq_iff_eq] at herr
  have hlc := hc _ (outLen_spec hL)
  simp only [SBool.eval, Sym.eval_lit, beq_iff_eq] at hlc
  have hPn : ((Sym.init 0 (ko + 8) 8).eval (envOf d.shape σ m)).toNat = L := by
    rw [hlc]; simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨c', hw, hcl⟩ := out_ptr hpc hsrc hadv' hA herr
    (fun h0 => by rw [h0] at hPn; simp at hPn; omega) (by omega)
  have hxe := loc_word_eval hwf hm hS (loc := .slot ko)
    (by simp only [Loc.fine, decide_eq_true_eq]; omega)
  rw [inpOf_spec hx] at hxe
  simp only [Loc.word, Sym.eval, BinOp.eval, env_base3] at hxe
  rw [hw] at hxe
  have hxc : x.eval (envOf d.shape σ m) = w c' := by simp at hxe; bv_omega
  have hlen64 : σ.len < 2 ^ 64 := (σ.m.reg 14).isLt
  rw [hPn] at hcl
  simp only [Oblig.holds, env_size3, hyx, hxc, w, BitVec.toNat_ofNat]
  omega

/-- The checks of `leaf_gen`: a leaf whose only obligations are the reads at a byte-loop
cursor, writing only frame words below the save area, ending at a plain cut or calling
`decodeItem` with a return site, whose target facts hold (`shapeHolds`, `armsKeep`, `restFrom`
— kept or advanced by one item —, the cursor and the budget, `tgtOk`). -/
def GenCheck (d : CutData) (l : Leaf) : Bool :=
  let adv := advUse d l
  let steps := l.S.steps - d.shape.S.steps
  d.shape.extra.isEmpty && l.S.regions == baseRegions &&
    l.obligs.all (fun o => curObl d o || outObl d l o) &&
    writesLow l.S &&
  match l.exit with
  | .at pc' =>
    match targetOf pc' with
    | some d' => d'.pc != entry && d'.plain && (noExtra d'.pc || errDone d'.pc l) &&
        d'.shape.extra.isEmpty &&
        d'.shape.Fine && shapeHolds l.S d'.shape && armsKeep d.arms d'.arms &&
        restFrom d.shape.S l.S adv (srcRest d l) d'.rest &&
        lenFrom d.shape.S l.S adv d.rest (srcRest d l) d'.rest &&
        tgtOk d l d'.pc
    | none => false
  | .call t r =>
    match targetOf r with
    | some d' =>
      match d'.site with
      | some s =>
        match f2Site s with
        | some (ko, _) => t == F2.entry && d'.pc != entry && SrcOk d' && decide (ko % 8 = 0) &&
            s.shape.Fine && shapeHolds l.S s.shape && armsKeep d.arms s.arms &&
            restFrom d.shape.S l.S adv (srcRest d l) s.rest &&
            lenFrom d.shape.S l.S adv d.rest (srcRest d l) d'.rest && restRet d' s &&
            l.S.reg 1 == .lit r && decide ((w r &&& ~~~(1 : Word)).toNat = r) &&
            decide (r % 4 = 0) && budgetCall d.pc d'.pc F2.bound steps
        | none => false
      | none => false
    | none => false
  | _ => false

theorem targetOf_spec {pc : Nat} {d' : CutData} (h : targetOf pc = some d') :
    d' ∈ table ∧ d'.pc = pc := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem leaf_gen (d : CutData) (l : Leaf) (hpc : d.pc ≠ entry) (hcut : CutOK vcPlan (mkCut d))
    (hsrc : SrcOk d = true) (hck : GenCheck d l = true) : LeafGoal vcPlan (mkCut d) l := by
  intro σ m hA hc
  have F := facts_of_A hpc hsrc hA
  obtain ⟨hwf, hm, -, -⟩ := hcut σ m hA
  simp only [mkCut] at hwf hm hc
  unfold GenCheck at hck
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hck
  obtain ⟨⟨⟨⟨hx, hreg⟩, hob⟩, hlow⟩, hex⟩ := hck
  have hS : BaseRegs d.shape.S := baseRegs_shape hx
  have hS' : BaseRegs l.S := hreg
  have hwf' : Env.WF (envOf d.shape σ m) l.S :=
    wf_of_regions hwf ((show l.S.regions = baseRegions from hS').trans hS.symm)
  have hadv : ∀ ko k, advUse d l = some (ko, k) →
      AdvOk d σ m ko k ∧ (Sym.init 0 (ko + 32) 2).eval (envOf d.shape σ m) = 0 := by
    intro ko k h
    unfold advUse at h
    split at h
    · next ko0 k0 h0 =>
      split at h
      · next hcond =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨adv_of_A hpc hsrc h0 hA, ?_⟩
        have := hc _ (List.contains_iff_mem.mp hcond)
        simpa [SBool.eval, Sym.eval_lit] using this
      · cases h
    · cases h
  have hob' : ∀ o ∈ l.obligs, o.holds (envOf d.shape σ m) := fun o ho => by
    have h := List.all_eq_true.mp hob o ho
    simp only [Bool.or_eq_true] at h
    exact h.elim (curObl_holds hpc hA hm) (outObl_holds hpc hsrc hA hwf hm hS hc)
  have hsteps0 : d.shape.S.steps = 0 := by simp [Shape.S, entryState]
  have hrest0 : RestOk σ m (srcRest d l) := fun r hr =>
    (List.mem_append.mp hr).elim (F.rest r) (tx_rest hpc hA hc r)
  cases hexit : l.exit with
  | «at» pc' =>
    rw [hexit] at hex
    simp only at hex
    split at hex
    case h_2 => cases hex
    rename_i d' ht
    obtain ⟨hd', hpc'⟩ := targetOf_spec ht
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hex
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hne, hpl⟩, hnx⟩, hx'⟩, hfine'⟩, hsh⟩, harms⟩, hrest⟩, hlen⟩, hbud⟩ := hex
    refine ⟨hob', tgt_steps hpc hA hm hbud, fun m' hm' hexok hso => ?_⟩
    simp only [mkCut] at hm' hso
    simp only [ExitOk] at hexok
    have C : Ctx d l σ m m' := ⟨F, hwf, hm, hS, hwf', hm', hS', hso, hlow, hadv, hrest0⟩
    obtain ⟨hcm, hshp, harm, hrst⟩ := target_facts C hfine' hsh harms hrest
    have hlen' := lenFrom_sound C hlen
    obtain ⟨hcur', hbud'⟩ := tgt_ok C hpc hsrc hA hc
      (show restLen d' σ m' ≤ restLen d σ m from hlen') hbud
    refine ExitGoal.at_cut rfl ⟨mkCut d', List.mem_map_of_mem hd', hexok.trans hpc'.symm, ?_, ?_⟩
    · simp only [mkCut, if_neg hne, ACut]
      refine .inl ⟨hpl, hexok.trans hpc'.symm, hcm, hshp, harm, hrst, ?_, hcur'⟩
      simp only [Bool.or_eq_true] at hnx
      rcases hnx with hnx | hnx
      · simp only [noExtra, Bool.and_eq_true, bne_iff_ne, ne_eq] at hnx
        simp only [Extra, if_neg hnx.1.1.1, if_neg hnx.1.1.2, if_neg hnx.1.2, if_neg hnx.2]
      · exact extra_err C hnx
    · show budgetOf d' σ m' ≤ budgetOf d σ m - (l.S.steps - d.shape.S.steps)
      omega
  | call t r =>
    rw [hexit] at hex
    simp only at hex
    split at hex
    case h_2 => cases hex
    rename_i d' ht
    obtain ⟨hd', hpc'⟩ := targetOf_spec ht
    split at hex
    case h_2 => cases hex
    rename_i s hs
    split at hex
    case h_2 => cases hex
    rename_i ko k' hf2
    obtain ⟨hkind, hko, ⟨r1, hm1, hl1, hn1, hk1⟩, ⟨r2, hm2, hl2, hn2, hk2⟩⟩ := f2Site_spec hf2
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hex
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht', hne⟩, hsrc'⟩, hko8⟩, hfine'⟩, hsh⟩, harms⟩, hrest⟩, hlen⟩, hrr⟩,
      hra1⟩,
      hra⟩, hr4⟩, hbud⟩ := hex
    simp only [budgetCall] at hbud
    split at hbud
    case h_2 => cases hbud
    rename_i hinner
    simp only [decide_eq_true_eq] at hbud
    refine ⟨hob', ?_, fun m' hm' hexok hso => ?_⟩
    · show l.S.steps - d.shape.S.steps ≤ budgetOf d σ m
      unfold budgetOf; omega
    simp only [mkCut] at hm' hso
    simp only [ExitOk] at hexok
    have C : Ctx d l σ m m' := ⟨F, hwf, hm, hS, hwf', hm', hS', hso, hlow, hadv, hrest0⟩
    obtain ⟨hcm, hshp, harm, hrst⟩ := target_facts C hfine' hsh harms hrest
    have hlen' := lenFrom_sound C hlen
    -- the call site's facts
    have hSF : s.kind.SiteFine s = true := by
      simp only [SrcOk, hs, RetCheck, Bool.and_eq_true] at hsrc'; exact hsrc'.1.1.1
    have hSF' := hSF
    rw [hkind] at hSF'
    simp only [Kind.SiteFine, hko, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hSF'
    obtain ⟨h2, hko'⟩ := hSF'
    have hr1 : m'.reg 1 = w r := by
      rw [← C.hm'.regs 1]; show (l.S.reg 1).eval _ = _; rw [hra1]; rfl
    have hsp : m'.reg 2 = σ.fr + w 0 := hshp.1 _ (lookup_mem (regFr_spec h2)) _ rfl
    have hout : m'.reg 10 = σ.fr + w ko := hshp.1 _ (lookup_mem (regFr_spec hko)) _ rfl
    obtain ⟨c1, hs1, hw1⟩ := hrst r1 hm1
    obtain ⟨c2, hs2, hw2⟩ := hrst r2 hm2
    rw [hk1] at hs1
    rw [hk2, hs1] at hs2
    simp only [Option.some.injEq] at hs2
    subst hs2
    rw [hl1, hn1] at hw1
    rw [hl2, hn2] at hw2
    simp only [Loc.word, if_true, Bool.false_eq_true, if_false] at hw1 hw2
    have hcl : c1 ≤ σ.len := by
      have := skip_le hs1; rw [payload_len hcm.2.1] at this; exact this
    have hraM : RetAligned m' := by unfold RetAligned; rw [hr1, hra]; exact hr4
    have hpre2 : F2.Pre m' := f2_pre_dtf hcm hsp hout hko' hko8 hw1 hw2 hcl hraM
    let x0 : Idx := ([], [], ⟨[], []⟩)
    have hsite : SiteA s d'.pc σ x0 m' := ⟨by rw [hpc']; exact hr1, hcm, hshp, harm, hrst,
      by rw [hkind]; exact ⟨hpre2, trivial⟩⟩
    refine ⟨calleeOf .f2, x0, ?_, ?_, hpre2, fun m'' hpost => ?_⟩
    · show calleeAt r = _
      unfold calleeAt
      rw [show table.find? (·.pc = r) = targetOf r from rfl, ht]
      simp [hs, hkind]
    · rw [hexok, ht']; rfl
    have hpost' : (calleeOf s.kind).Post σ x0 m' m'' := by rw [hkind]; exact hpost
    have hpc'' : m''.pc.toNat = r := by rw [hpost.1.1.1, hr1, hra]
    refine ⟨mkCut d', List.mem_map_of_mem hd', hpc', hpc'', ?_, ?_⟩
    · simp only [mkCut, if_neg hne, ACut]
      exact .inr ⟨s, hs, m', x0, hsite, hpost'⟩
    · show F2.bound + budgetOf d' σ m'' ≤ budgetOf d σ m - (l.S.steps - d.shape.S.steps)
      have hl2 : restLen d' σ m' ≤ restLen d σ m := hlen'
      have hkeep : restLen d' σ m'' = restLen d' σ m' := by
        unfold restLen
        split
        · next r0 h0 => rw [ret_loc_keep hSF hsite hpost' hrr (List.mem_of_find?_eq_some h0)]
        · rfl
      unfold budgetOf
      rw [hinner, hkeep]
      simp only [innerOf]
      omega
  | _ => simp [hexit] at hex

end ZesuExec.Fn.DTF
