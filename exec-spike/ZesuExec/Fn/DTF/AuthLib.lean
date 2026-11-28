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

/-- Field `f` of the `n + 1`-th tuple (payload `tupPay`) fits (`Fits`: the items of a tuple). -/
theorem field_fits {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4) {c h p n j ht pt f q : Nat}
    (hl : AuthList σ c h p) (hsk : skip n (TX.itemPayload (σ.payload.drop c) h p) = some j)
    (hn : n < p) (hp : p ≤ (σ.payload.drop (c + h)).length)
    (hd : F2.decode ((σ.payload.drop (c + h + j)).take (p - j)) = .success true ht pt)
    (hpt : ht + pt ≤ p - j) (hf : skip f (tupPay σ c h p j ht pt) = some q) (hfq : f < pt) :
    TX.HeaderFits ((tupPay σ c h p j ht pt).drop q) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdom, -⟩ := hpre
  have hfit := hdom.2
  unfold Fits at hfit
  rw [show (σ.m.reg 12).toNat = 4 from h4] at hfit
  have hi := inner_at hfit hl.1 (by decide) hl.2
  have hlen : (TX.itemPayload (σ.payload.drop c) h p).length = p := by
    simp only [TX.itemPayload, List.length_take, List.length_drop] at hp ⊢
    omega
  rw [hlen] at hi
  have hi2 := inner_at hi hsk hn (by rwa [itemPayload_drop])
  rw [itemPayload_drop] at hi2
  have hlt : (tupPay σ c h p j ht pt).length = pt := by
    have hj := skip_le hsk
    simp only [TX.itemPayload, List.length_take, List.length_drop] at hj hp
    simp only [tupPay, TX.itemPayload, List.length_take, List.length_drop]
    omega
  exact fits_at (n := (tupPay σ c h p j ht pt).length) hi2 hf (by rw [hlt]; exact hfq)

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
  obtain ⟨hl, hs, hnj, l70, l68, l30, hok⟩ := ho
  exact ⟨hl, hs, hnj, h70.trans l70, h68.trans l68, h30.trans l30, hok⟩

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

/-- The frame words `EndAt` names. -/
def endSlots : List Nat := [0x70, 0x68, 0x30, 0x58, 0x60, 0x50, 0x48, 0x78]

theorem endAt_mono {σ : Sig} {m m' : Machine}
    (hk : ∀ o ∈ endSlots, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8)
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {f c h p n j ht pt q : Nat}
    (he : EndAt σ m f c h p n j ht pt q) : EndAt σ m' f c h p n j ht pt q := by
  obtain ⟨ho, l50, hb, hs, h22, l48, ⟨a, la, hla⟩, hd, hle, h5, hq, hs5, hok⟩ := he
  exact ⟨authOut_mono (hk _ (by decide)) (hk _ (by decide)) (hk _ (by decide)) ho,
    (hk _ (by decide)).trans l50, authBuf_mono (hk _ (by decide)) (hk _ (by decide)) hL hb, hs,
    h22, (hk _ (by decide)).trans l48, ⟨a, (hk _ (by decide)).trans la, hla⟩, hd, hle, h5, hq,
    hs5, hok⟩

/-- `AuthEnd` without the field cursor survives keeping `endSlots` and the live list. -/
theorem end_mono {σ : Sig} {m m' : Machine}
    (hk : ∀ o ∈ endSlots, m'.load (σ.fr + w o) 8 = m.load (σ.fr + w o) 8)
    (hL : ∀ L X, Live σ m L X → Live σ m' L X) {f : Nat} {cur : Bool} (he : AuthEnd σ m f cur) :
    AuthEnd σ m' f false := by
  obtain ⟨c, h, p, n, j, ht, pt, q, he, -⟩ := he
  exact ⟨c, h, p, n, j, ht, pt, q, endAt_mono hk hL he, fun h => absurd h (by decide)⟩

/-! ## The tuples' checks: `auth`'s walk -/

theorem tupOk_zero (tp : List Byte) : TupOk tp 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem tupOk_mono {tp : List Byte} {f g : Nat} (h : TupOk tp f) (hg : g ≤ f) : TupOk tp g :=
  fun i hi => h i (by omega)

/-- Field `f` at `q` passes its check. -/
theorem tupOk_succ {tp : List Byte} {f q h p : Nat} (hok : TupOk tp f) (hs : skip f tp = some q)
    (hd : F2.decode (tp.drop q) = .success false h p) (hl : tupLen f p) : TupOk tp (f + 1) := by
  intro i hi c hc
  rcases Nat.lt_or_ge i f with hlt | hge
  · exact hok i hlt c hc
  · obtain rfl : i = f := by omega
    rw [hs, Option.some.injEq] at hc
    subst hc
    exact ⟨h, p, hd, hl⟩

theorem authsOk_zero (pl : List Byte) : AuthsOk pl 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

/-- The tuple at `j` after `n` tuples passes. -/
theorem authsOk_succ {pl : List Byte} {n j : Nat} (hok : AuthsOk pl n) (hs : skip n pl = some j)
    (ht : TupleOk (pl.drop j)) : AuthsOk pl (n + 1) := by
  intro i hi c hc
  rcases Nat.lt_or_ge i n with hlt | hge
  · exact hok i hlt c hc
  · obtain rfl : i = n := by omega
    rw [hs, Option.some.injEq] at hc
    subst hc
    exact ht

/-- The tuple payload after `q` bytes is the payload slice from the field cursor. -/
theorem tupPay_drop {σ : Sig} {c h p j ht pt : Nat} (hle : ht + pt ≤ p - j) (q : Nat) :
    (tupPay σ c h p j ht pt).drop q = (σ.payload.drop (c + h + j + ht + q)).take (pt - q) := by
  simp only [tupPay, TX.itemPayload, List.drop_take, List.take_take, List.drop_drop]
  rw [Nat.min_eq_left (by omega)]

/-- The `n + 1`-th tuple, a list with its six fields checked, passes. -/
theorem tupleOk_of {σ : Sig} {c h p j ht pt : Nat}
    (hd : F2.decode ((σ.payload.drop (c + h + j)).take (p - j)) = .success true ht pt)
    (h6 : 6 ≤ pt) (hok : TupOk (tupPay σ c h p j ht pt) 6) :
    TupleOk ((TX.itemPayload (σ.payload.drop c) h p).drop j) := by
  rw [itemPayload_drop]
  exact ⟨ht, pt, hd, h6, hok⟩

/-- A tuple whose six fields fit and pass their checks: `auth` reads it. -/
theorem auth_run {b : List Byte} {ht pt : Nat} (hfb : TX.HeaderFits b)
    (hd : F2.decode b = .success true ht pt) (h6 : 6 ≤ pt)
    (hin : ItemsFit (fun _ => True) (TX.itemPayload b ht pt).length (TX.itemPayload b ht pt))
    (hok : TupOk (TX.itemPayload b ht pt) 6) :
    ∃ t, auth.run b = some (t, TX.itemRest b ht pt) := by
  have hlen := payload_length hfb hd
  have hck : ChecksL [.le 32, .str, .le 8, .le 8, .le 32, .le 32] (TX.itemPayload b ht pt) := by
    refine checksL_of (fun i hi c hs => fits_at hin hs (by
      simp only [List.length_cons, List.length_nil] at hi; omega)) (fun i hi c hs ch hch => ?_)
    simp only [List.length_cons, List.length_nil] at hi
    obtain ⟨h, p, hd', hl⟩ := hok i (by omega) c hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      omega
    all_goals
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hch
      subst hch
      simp [tupLen] at hl
    all_goals first | exact ⟨h, p, hd', by omega⟩ | exact ⟨h, p, hd'⟩
  obtain ⟨f0, k0, c1⟩ := checksL_cons hck
  obtain ⟨f1, k1, c2⟩ := checksL_cons c1
  obtain ⟨f2, k2, c3⟩ := checksL_cons c2
  obtain ⟨f3, k3, c4⟩ := checksL_cons c3
  obtain ⟨f4, k4, c5⟩ := checksL_cons c4
  obtain ⟨f5, k5, -⟩ := checksL_cons c5
  have h20 : (payOf (restOf (TX.itemPayload b ht pt))).length = 20 := by
    obtain ⟨l0, h0, p0, hd0⟩ := chk_decodes k0
    have hs1 : skip 1 (TX.itemPayload b ht pt) = some (TX.itemConsumed h0 p0) := by
      have := skip_snoc (k := 0) (b := TX.itemPayload b ht pt) rfl (by simpa using hd0)
      simpa using this
    obtain ⟨h, p, hd1, hl1⟩ := hok 1 (by decide) _ hs1
    simp only [tupLen, if_true] at hl1
    subst hl1
    have hr : restOf (TX.itemPayload b ht pt) =
        (TX.itemPayload b ht pt).drop (TX.itemConsumed h0 p0) := by
      rw [restOf, hdOf_eq hd0]; rfl
    rw [hr] at f1 ⊢
    rw [payOf, hdOf_eq hd1]
    exact payload_length f1 hd1
  have e0 := stepV_u256 _ f0 k0
  have e1 := stepV_bytesView _ f1 k1
  have e2 := stepV_u64 _ f2 k2
  have e3 := stepV_u64 _ f3 k3
  have e4 := stepV_u256 _ f4 k4
  have e5 := stepV_u256 _ f5 k5
  simp only [auth, listPayload, StateT.run_bind, item_run hd, Option.bind_eq_bind,
    Option.bind_some, if_true]
  simp only [StateT.run] at e0 e1 e2 e3 e4 e5
  have hb : ∀ {α β : Type} (x : P α) (f : α → P β) (s : List Byte),
      (x >>= f) s = (x s).bind (fun p => f p.1 p.2) := fun _ _ _ => rfl
  have hp : ∀ {α : Type} (a : α) (s : List Byte), (pure a : P α) s = some (a, s) :=
    fun _ _ => rfl
  simp only [Option.bind_some, StateT.run, hb, hp, e0, e1, e2, e3, e4, e5, h20, ne_eq,
    not_true_eq_false, if_false]
  exact ⟨_, rfl⟩

/-- The walk over `n` tuples `auth` accepts that fill `b` succeeds (the tuples' fields fit). -/
theorem walk_auth : ∀ (n : Nat) (b : List Byte) (fuel : Nat), n ≤ fuel →
    (∀ i < n, ∀ c, skip i b = some c → TX.HeaderFits (b.drop c) ∧ ∀ ht pt,
      F2.decode (b.drop c) = .success true ht pt →
      ItemsFit (fun _ => True) (TX.itemPayload (b.drop c) ht pt).length
        (TX.itemPayload (b.drop c) ht pt)) →
    AuthsOk b n → skip n b = some b.length → ∃ ts, walkList auth fuel b = some ts
  | 0, b, fuel, _, _, _, hs => by
    simp only [skip, Option.some.injEq] at hs
    rw [List.eq_nil_of_length_eq_zero hs.symm]
    exact ⟨[], walkList_nil _ _⟩
  | n + 1, b, fuel, hn, hfit, hok, hs => by
    obtain ⟨ht, pt, hd, h6, htok⟩ := hok 0 (by omega) 0 rfl
    obtain ⟨hf, hin⟩ := hfit 0 (by omega) 0 rfl
    simp only [List.drop_zero] at hd htok hf hin
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases b with
    | nil => simp [F2.decode] at hd
    | cons x xs =>
    obtain ⟨t, hrun⟩ := auth_run hf hd h6 (hin ht pt hd) htok
    have hsk : ∀ i c, skip i (TX.itemRest (x :: xs) ht pt) = some c →
        skip (i + 1) (x :: xs) = some (TX.itemConsumed ht pt + c) := by
      intro i c hc
      simp only [skip, hd]; rw [← TX.itemRest, hc]; rfl
    have hdrop : ∀ c, (TX.itemRest (x :: xs) ht pt).drop c =
        (x :: xs).drop (TX.itemConsumed ht pt + c) := by
      intro c; rw [TX.itemRest, List.drop_drop]
    have hs' : skip n (TX.itemRest (x :: xs) ht pt) =
        some (TX.itemRest (x :: xs) ht pt).length := by
      simp only [skip, hd] at hs
      obtain ⟨c', h', hc'⟩ := Option.map_eq_some_iff.mp hs
      rw [← TX.itemRest] at h'
      rw [h']
      simp only [TX.itemRest, List.length_drop]
      congr 1; omega
    obtain ⟨ts, hw⟩ := walk_auth n _ f (by omega)
      (fun i hi c hc => by rw [hdrop]; exact hfit (i + 1) (by omega) _ (hsk i c hc))
      (fun i hi c hc => by rw [hdrop]; exact hok (i + 1) (by omega) _ (hsk i c hc)) hs'
    refine ⟨t :: ts, ?_⟩
    simp only [walkList]
    rw [show auth (x :: xs) = auth.run (x :: xs) from rfl, hrun]
    simp only [hw, Option.map_some]

/-- The authorization list's walk succeeds once its `n` tuples passed and fill its payload. -/
theorem auth_walk_ok {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (h4 : σ.t = 4) {c h p n : Nat}
    (hl : AuthList σ c h p) (hs : skip n (TX.itemPayload (σ.payload.drop c) h p) = some p)
    (hn : n ≤ p) (hok : AuthsOk (TX.itemPayload (σ.payload.drop c) h p) n) :
    ∃ ts, walkList auth (TX.itemPayload (σ.payload.drop c) h p).length
      (TX.itemPayload (σ.payload.drop c) h p) = some ts := by
  obtain ⟨hs9, hd⟩ := hl
  have hfits := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  have h4' : (σ.m.reg 12).toNat = 4 := h4
  have hf := fits_at hfits hs9 (by rw [h4']; decide)
  have hlen := payload_length hf hd
  have hin := fits_inner hfits hs9 (by rw [h4']; decide) hd
  refine walk_auth n _ _ (by rw [hlen]; exact hn) (fun i hi c' hc => ⟨?_, fun ht pt hd' => ?_⟩)
    hok (by rw [hlen]; exact hs)
  · exact fits_at hin hc (by rw [hlen]; omega)
  · exact fits_inner hin hc (by rw [hlen]; omega) hd'

/-- Call-site entries that are all the tuple walk of item 9 hold once the walk succeeds. -/
theorem awalk_fields {σ : Sig} {m : Machine} {fs : List Field}
    (hv : ∀ f ∈ fs, f.v = .awalk 9) {c h p : Nat} (hl : AuthList σ c h p)
    (hw : ∃ ts, walkList auth (TX.itemPayload (σ.payload.drop c) h p).length
      (TX.itemPayload (σ.payload.drop c) h p) = some ts) : FieldsOk σ m fs := by
  intro f hf _
  rw [hv f hf]
  intro c' hs' l' h' p' hd'
  obtain ⟨hs9, hd⟩ := hl
  simp only [FieldVal.k] at hs'
  rw [hs9, Option.some.injEq] at hs'
  subst hs'
  rw [hd] at hd'
  cases hd'
  exact hw

/-- The entries `!(f.v != .awalk 9)` selects are the tuple walk. -/
theorem awalk_sel {fs : List Field} :
    ∀ f ∈ fs.filter (fun f => !(f.v != .awalk 9)), f.v = .awalk 9 := fun f hf => by
  simpa using (List.mem_filter.mp hf).2

end ZesuExec.Fn.DTF
