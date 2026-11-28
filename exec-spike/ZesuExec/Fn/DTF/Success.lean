import ZesuExec.Fn.DTF.ErrWrite
import ZesuExec.Fn.DTF.Bridge

/-!
# DTF: the success write (`0x80002dc4 → 0x800011f8`, programme plan S7 step 4)

The leaf from `0x80002dc4` stores the transaction into the result and the error code 0.
`TxAt`'s scalar fields come from the cut's row (`cutFields 0x80002dc4`): each result byte is
checked against a byte of a row location (`resLoc`, decided on the leaf's final state); the row's
values are the item values of the decoded transaction (`checksL_at`, `restN`).
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

set_option maxRecDepth 20000

/-! ## Bytes of numbers -/

theorem byteOf_w (x : Nat) {t : Nat} (ht : t < 8) : byteOf (w x) t = BitVec.ofNat 8 (x / 256 ^ t) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [byteOf, w, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat]
  rw [show (256 : Nat) ^ t = 2 ^ (8 * t) by rw [Nat.pow_mul]]
  rw [Nat.testBit_div_two_pow]
  have : k + 8 * t < 64 := by omega
  simp [this, Nat.add_comm]

theorem byteOf_limb (V i : Nat) {t : Nat} (ht : t < 8) :
    byteOf (limb V i) t = BitVec.ofNat 8 (V / 256 ^ (8 * i + t)) := by
  rw [limb, byteOf_w _ ht, Nat.div_div_eq_div_mul]
  congr 2
  rw [show (2 : Nat) ^ (64 * i) = 256 ^ (8 * i) by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega, ← Nat.pow_add]

theorem leBytes_length (n v : Nat) : (leBytes n v).length = n := by simp [leBytes]

theorem leBytes_getElem {n v j : Nat} (hj : j < (leBytes n v).length) :
    (leBytes n v)[j] = BitVec.ofNat 8 (v / 256 ^ j) := by simp [leBytes]

/-! ## Result bytes from the leaf's stores -/

/-- Result byte `a` is byte `j` of the row location `loc` at the source. -/
def resLoc (d : CutData) (l : Leaf) (a : Nat) (loc : Loc) (j : Nat) : Bool :=
  loc.fine && decide (j < 8) && decide (a < resultBytes) &&
    match byteAt (readConst l.S 1 a 1) 0 with
    | some s => byteAt (loc.sym d.shape.S) j == some s
    | none => false

/-- Result bytes `off ..< off + n`: byte `j` is byte `j % 8` of `locs[j / 8]`. -/
def resBytes (d : CutData) (l : Leaf) (off : Nat) (locs : List Loc) (n : Nat) : Bool :=
  (List.range n).all fun j => resLoc d l (off + j) (locs.getD (j / 8) (.reg 0)) (j % 8)

/-- Result byte `a` is zero. -/
def resZero (l : Leaf) (a : Nat) : Bool :=
  decide (a < resultBytes) && byteAt (readConst l.S 1 a 1) 0 == some (.lit 0)

theorem res_sym {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {a : Nat} (ha : a < resultBytes) {s : Sym} (hr : byteAt (readConst l.S 1 a 1) 0 = some s) :
    m'.mem (σ.res + w a) = some (byteOf (s.eval (envOf d.shape σ m)) 0) := by
  have hR : l.S.regions[1]? = some resR := by rw [C.hS']; rfl
  have hl := load_cst C.wf' C.hm' hR (off := a) (n := 1)
    (by simp only [envOf, entryEnv, Env.size, regionsOf]; simp; omega)
  rw [env_base1] at hl
  have := load_bytes hl (by decide) 0 (by decide)
  rw [show σ.res + BitVec.ofNat 64 a + BitVec.ofNat 64 0 = σ.res + BitVec.ofNat 64 a by simp]
    at this
  rw [this, byteAt_sound hr (by decide)]

/-- Result word `off` is the row location `loc`'s word at the source. -/
def resWord (d : CutData) (l : Leaf) (off : Nat) (loc : Loc) : Bool :=
  loc.fine && decide (off + 8 ≤ resultBytes) && readConst l.S 1 off 8 == loc.sym d.shape.S

theorem res_word {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {off : Nat} {loc : Loc} (h : resWord d l off loc = true) :
    m'.load (σ.res + w off) 8 = some (loc.word σ m) := by
  unfold resWord at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hf, ho⟩, hs⟩ := h
  have hR : l.S.regions[1]? = some resR := by rw [C.hS']; rfl
  have hl := load_cst C.wf' C.hm' hR (off := off) (n := 8)
    (by simp only [envOf, entryEnv, Env.size, regionsOf]; simp; omega)
  rw [env_base1, hs, ← loc_word_eval C.wf C.hm C.hS hf] at hl
  exact hl

theorem res_loc {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {a : Nat} {loc : Loc} {j : Nat} (h : resLoc d l a loc j = true) :
    m'.mem (σ.res + w a) = some (byteOf (loc.word σ m) j) := by
  unfold resLoc at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hf, hj⟩, ha⟩, hs⟩ := h
  split at hs
  · next s hr =>
    rw [res_sym C ha hr, loc_word_eval C.wf C.hm C.hS hf]
    have hb : byteAt (loc.sym d.shape.S) j = some s := by simpa using hs
    rw [byteAt_sound hb hj]
  · cases hs

theorem res_zero {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {a : Nat} (h : resZero l a = true) : m'.mem (σ.res + w a) = some 0 := by
  unfold resZero at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [res_sym C h.1 h.2]
  rfl

theorem res_bytes {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {off : Nat} {locs : List Loc} {n : Nat} (h : resBytes d l off locs n = true) {bs : List Byte}
    (hn : bs.length = n)
    (hv : ∀ j < n, byteOf ((locs.getD (j / 8) (.reg 0)).word σ m) (j % 8) = bs.getD j 0) :
    BytesAt m' (σ.res + w off) bs := by
  intro j hj
  have := res_loc C (List.all_eq_true.mp h j (List.mem_range.mpr (by omega)))
  rw [show σ.res + w off + BitVec.ofNat 64 j = σ.res + w (off + j) by
    simp only [w, BitVec.ofNat_add]; rw [BitVec.add_assoc], this, hv j (by omega),
    ← List.getElem_eq_getD]

/-- A number of `K` limbs at `locs`, little-endian at `off`. -/
theorem res_num {d : CutData} {l : Leaf} {σ : Sig} {m m' : Machine} (C : Ctx d l σ m m')
    {off : Nat} {locs : List Loc} (h : resBytes d l off locs (8 * locs.length) = true) {V : Nat}
    (hv : ∀ i (hi : i < locs.length), locs[i].word σ m = limb V i) :
    BytesAt m' (σ.res + w off) (leBytes (8 * locs.length) V) := by
  refine res_bytes C h (leBytes_length _ _) fun j hj => ?_
  have hi : j / 8 < locs.length := by omega
  rw [← List.getElem_eq_getD _ (h := hi), hv _ hi, byteOf_limb _ _ (by omega),
    ← List.getElem_eq_getD _ (h := by rw [leBytes_length]; omega), leBytes_getElem,
    Nat.div_add_mod]

/-! ## Item values of the checked payload -/

/-- Item `k` of checked items: reached by `skip`, at `restN k`, its check passed. -/
theorem checksL_at : ∀ {chs : List Chk} {b : List Byte} {k : Nat}, ChecksL chs b →
    k < chs.length → ∃ c, skip k b = some c ∧ restN k b = b.drop c ∧
      TX.HeaderFits (b.drop c) ∧ ∀ ch, chs[k]? = some ch → ch.Ok (b.drop c)
  | [], _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | ch :: chs, b, 0, h, _ => ⟨0, rfl, rfl, h.1, fun ch' hch => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hch; subst hch; exact h.2.1⟩
  | ch :: chs, b, k + 1, h, hk => by
    obtain ⟨hf, hok, htl⟩ := checksL_cons h
    obtain ⟨l, hh, p, hd⟩ := chk_decodes hok
    obtain ⟨c, hs, hr, hfit, hch⟩ := checksL_at htl (k := k) (by simp at hk; omega)
    have hro : restOf b = b.drop (TX.itemConsumed hh p) := by rw [restOf, hdOf_eq hd]; rfl
    refine ⟨TX.itemConsumed hh p + c, ?_, ?_, ?_, fun ch' hch' => ?_⟩
    · simp only [skip, hd]; rw [← hro, hs]; rfl
    · simp only [restN]; rw [hr, hro, List.drop_drop]
    · rw [← List.drop_drop, ← hro]; exact hfit
    · rw [← List.drop_drop, ← hro]; exact hch ch' (by simpa using hch')

/-- The full checks of arm `σ.t` from `ChecksOk` and `Pre`'s `Fits`. -/
theorem checksL_full {σ : Sig} (hpre : Pre σ.A σ.g σ.m) (hchk : ChecksOk σ (fieldCount σ.t)) :
    ChecksL (armChecks σ.t) σ.payload := by
  have h4 : σ.t ≤ 4 := hpre.2.2.2.2.2.2.2.2.2.1
  have hlen : (armChecks σ.t).length = fieldCount σ.t := by
    obtain h | h | h | h | h : σ.t = 0 ∨ σ.t = 1 ∨ σ.t = 2 ∨ σ.t = 3 ∨ σ.t = 4 := by omega
    all_goals rw [h]; rfl
  refine checksL_of (fun i hi c hs => ?_) (fun i hi c hs ch hch => hchk i (hlen ▸ hi) c hs ch hch)
  exact fits_at hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2 hs (hlen ▸ hi)

/-- An item value in terms of the item's bytes `b` (`numOf`, `payOf`, `hdOf`). -/
def FieldVal.AtB (σ : Sig) (b : List Byte) (x : Word) : FieldVal → Prop
  | .len _ => x = w (hdOf b).2
  | .num _ n i => x = limb (numOf n b) i
  | .nz _ => x = if (hdOf b).2 = 0 then 0 else 1
  | .raw _ o n => ∀ j < n, byteOf x j = (payOf b).getD (o + j) 0
  | .lc _ => 35 ≤ numOf 32 b → x = w ((numOf 32 b - 35) / 2)
  | .lt _ => x = if 35 ≤ numOf 32 b then 1 else 0
  | .lv _ => x = w (legacyV (numOf 32 b)).2
  | .ty => x = σ.m.reg 12
  | .cst v => x = w v
  | _ => True

theorem at_atB {σ : Sig} {m : Machine} {c h p : Nat} {l : Bool}
    (hd : F2.decode (σ.payload.drop c) = .success l h p) {x : Word} {v : FieldVal}
    (hv : v.At σ m c h p x) : v.AtB σ (σ.payload.drop c) x := by
  have e := hdOf_eq hd
  cases v <;> simp only [FieldVal.At] at hv <;>
    simp only [FieldVal.AtB, numOf, payOf, e] <;> first | exact hv | trivial

/-- A row entry of `0x80002dc4` at arm `σ.t`, in terms of the item's bytes. -/
theorem row_val {σ : Sig} {m : Machine} (hF : FieldsOk σ m (cutFields 0x80002dc4))
    (hck : ChecksL (armChecks σ.t) σ.payload) {f : Field} (hmem : f ∈ cutFields 0x80002dc4)
    (ha : ArmOk σ f.arms) (hk : f.v.k < (armChecks σ.t).length) :
    f.v.AtB σ (restN f.v.k σ.payload) (f.loc.word σ m) := by
  obtain ⟨c, hs, hr, -, hch⟩ := checksL_at hck hk
  obtain ⟨ch, hch'⟩ : ∃ ch, (armChecks σ.t)[f.v.k]? = some ch :=
    ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨l, h, p, hd⟩ := chk_decodes (hch ch hch')
  rw [hr]
  exact at_atB hd (hF f hmem ha c hs l h p hd)

theorem limb_idx0 (V : Nat) : limb V 0 = w V := by simp [limb]

theorem limb_of_zero (i : Nat) : limb 0 i = w 0 := by simp [limb]

theorem w_mod64 (x : Nat) : w (x % 2 ^ 64) = w x := by
  apply BitVec.eq_of_toNat_eq; simp [w]

theorem reg12_of {σ : Sig} {t : Nat} (ht : σ.t = t) : σ.m.reg 12 = w t := by
  rw [← ht]; simp [w]

/-- Item `k` checked as an address: empty, or a 20-byte payload. -/
theorem addr_item {σ : Sig} (hck : ChecksL (armChecks σ.t) σ.payload) {k : Nat}
    (hk : k < (armChecks σ.t).length) (ha : (armChecks σ.t)[k]? = some .addr) :
    (hdOf (restN k σ.payload)).2 = 0 ∨ (payOf (restN k σ.payload)).length = 20 := by
  obtain ⟨c, -, hr, hf, hch⟩ := checksL_at hck hk
  obtain ⟨h, p, hd, hp⟩ := hch _ ha
  rw [hr, payOf, hdOf_eq hd]
  rcases hp with rfl | rfl
  · exact .inl rfl
  · exact .inr (payload_length hf hd)

/-- `to` from its item's rows: the tag (`nz`) and the three address words (`raw`). -/
theorem to_rows {σ : Sig} {m : Machine} {b : List Byte} {k : Nat}
    (hz : FieldVal.AtB σ b ((Loc.slot 0x118).word σ m) (.nz k))
    (h0 : FieldVal.AtB σ b ((Loc.slot 0x138).word σ m) (.raw k 0 8))
    (h1 : FieldVal.AtB σ b ((Loc.slot 0x140).word σ m) (.raw k 8 8))
    (h2 : FieldVal.AtB σ b ((Loc.slot 0x148).word σ m) (.raw k 16 4))
    (hlen : (hdOf b).2 = 0 ∨ (payOf b).length = 20) :
    match addrOf b with
    | some a => a.length = 20 ∧ (∀ j < 20,
        byteOf ((([.slot 0x138, .slot 0x140, .slot 0x148] : List Loc).getD (j / 8) (.reg 0)).word
          σ m) (j % 8) = a.getD j 0) ∧ (Loc.slot 0x118).word σ m = w 1
    | none => (Loc.slot 0x118).word σ m = w 0 := by
  simp only [FieldVal.AtB] at hz h0 h1 h2
  by_cases hp : (hdOf b).2 = 0
  · simp only [addrOf, if_pos hp]; rw [hz, if_pos hp]; rfl
  · simp only [addrOf, if_neg hp]
    refine ⟨hlen.resolve_left hp, fun j hj => ?_, by rw [hz, if_neg hp]; rfl⟩
    obtain hq | hq | hq : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 := by omega
    · rw [hq]; simpa [show j % 8 = j by omega] using h0 (j % 8) (by omega)
    · rw [hq]; simpa [show 8 + j % 8 = j by omega] using h1 (j % 8) (by omega)
    · rw [hq]; simpa [show 16 + j % 8 = j by omega] using h2 (j % 8) (by omega)


/-! ## `TxAt` split: scalar fields (stored from the row) and the four buffers -/

/-- `TxAt` but the `data`, access-list, blob-hash and authorization slices. -/
def TxScal (m : Machine) (res : Word) (tx : Tx) : Prop :=
  BytesAt m res (leBytes 16 tx.gasPrice) ∧
  (match tx.gasPriorityFee with
   | some f => BytesAt m (res + 0x10) (leBytes 16 f) ∧ m.mem (res + 0x20) = some 1
   | none => m.mem (res + 0x20) = some 0) ∧
  BytesAt m (res + 0x30) (leBytes 32 tx.value) ∧
  BytesAt m (res + 0x50) (leBytes 16 tx.maxFeePerBlobGas) ∧
  BytesAt m (res + 0x60) (leBytes 32 tx.r) ∧ BytesAt m (res + 0x80) (leBytes 32 tx.s) ∧
  (match tx.chainId with
   | some c => BytesAt m (res + 0xa0) (leBytes 8 c) ∧ m.mem (res + 0xa8) = some 1
   | none => m.mem (res + 0xa8) = some 0) ∧
  BytesAt m (res + 0xb0) (leBytes 8 tx.nonce) ∧ BytesAt m (res + 0xb8) (leBytes 8 tx.gasLimit) ∧
  BytesAt m (res + 0x100) (leBytes 8 tx.v) ∧ m.mem (res + 0x108) = some (BitVec.ofNat 8 tx.txType) ∧
  (match tx.to with
   | some a => BytesAt m (res + 0x109) a ∧ m.mem (res + 0x11d) = some 1
   | none => m.mem (res + 0x11d) = some 0)

/-- `TxAt`'s four slices. -/
def TxBufs (m : Machine) (res : Word) (tx : Tx) : Prop :=
  SliceAt m (res + 0xc0) tx.data.length tx.data ∧
  (∃ is : List TX.EntryImage, is.length = tx.accessList.length ∧
    SliceAt m (res + 0xd0) tx.accessList.length (TX.entriesBytes tx.accessList is) ∧
    ∀ x ∈ List.zip tx.accessList is, x.2.padding.length = 4 ∧
      (x.1.keys ≠ [] → RamRange x.2.keysPtr (TX.keySize * x.1.keys.length) ∧
        BytesAt m x.2.keysPtr x.1.keys.flatten)) ∧
  SliceAt m (res + 0xe0) tx.blobHashes.length tx.blobHashes.flatten ∧
  (∃ p : Word, m.load (res + 0xf0) 8 = some p ∧
    m.load (res + 0xf8) 8 = some (BitVec.ofNat 64 tx.authorizationList.length) ∧
    (tx.authorizationList ≠ [] → RamRange p (0x90 * tx.authorizationList.length)) ∧
    ∀ k (h : k < tx.authorizationList.length),
      AuthAt m (p + BitVec.ofNat 64 (0x90 * k)) tx.authorizationList[k])

theorem txAt_of {m : Machine} {res : Word} {tx : Tx} (h : TxScal m res tx) (hb : TxBufs m res tx) :
    TxAt m res tx :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h14, h15, h16⟩ := h
  let ⟨h10, h11, h12, h13⟩ := hb
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The locations `locs` hold limbs `i, i+1, …` of `V`. -/
def LimbsFrom (σ : Sig) (m : Machine) (V : Nat) : Nat → List Loc → Prop
  | _, [] => True
  | i, loc :: locs => loc.word σ m = limb V i ∧ LimbsFrom σ m V (i + 1) locs

theorem limbsFrom_get {σ : Sig} {m : Machine} {V : Nat} :
    ∀ {i : Nat} {locs : List Loc}, LimbsFrom σ m V i locs →
      ∀ j (hj : j < locs.length), locs[j].word σ m = limb V (i + j)
  | _, [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _, _ :: _, h, 0, _ => h.1
  | i, _ :: _, h, j + 1, hj => by
    rw [List.getElem_cons_succ, limbsFrom_get h.2 j (by simp at hj; omega)]
    congr 1; omega

/-- The success write's result fields from the row words (the store layout of `0x80002dc4`). -/
theorem scal_of {σ : Sig} {m m' : Machine}
    (C : Ctx (table[152]!) ((leavesAt 0x80002dc4)[0]!) σ m m') {tx : Tx}
    (hgp : LimbsFrom σ m tx.gasPrice 0 [.reg 24, .reg 9])
    (hpf : match tx.gasPriorityFee with
      | some f => LimbsFrom σ m f 0 [.reg 18, .slot 0x128] ∧ (Loc.reg 15).word σ m = w 1
      | none => (Loc.reg 15).word σ m = w 0)
    (hval : LimbsFrom σ m tx.value 0 [.reg 21, .slot 0x100, .slot 0xf8, .slot 0x108])
    (hbf : LimbsFrom σ m tx.maxFeePerBlobGas 0 [.slot 0xe0, .slot 0xd8])
    (hr : LimbsFrom σ m tx.r 0 [.reg 22, .reg 19, .reg 20, .slot 0xd0])
    (hs : LimbsFrom σ m tx.s 0 [.reg 10, .reg 12, .reg 13, .reg 11])
    (hc : match tx.chainId with
      | some c => (Loc.reg 26).word σ m = w c ∧ (Loc.reg 14).word σ m = w 1
      | none => (Loc.reg 14).word σ m = w 0)
    (hn : (Loc.reg 27).word σ m = w tx.nonce) (hgl : (Loc.slot 0x120).word σ m = w tx.gasLimit)
    (hv : (Loc.reg 23).word σ m = w tx.v) (hty : (Loc.slot 0x130).word σ m = w tx.txType)
    (hto : match tx.to with
      | some a => a.length = 20 ∧ (∀ j < 20,
          byteOf ((([.slot 0x138, .slot 0x140, .slot 0x148] : List Loc).getD (j / 8) (.reg 0)).word
            σ m) (j % 8) = a.getD j 0) ∧ (Loc.slot 0x118).word σ m = w 1
      | none => (Loc.slot 0x118).word σ m = w 0) :
    TxScal m' σ.res tx := by
  have one : ∀ {loc : Loc} {V : Nat}, loc.word σ m = w V → LimbsFrom σ m V 0 [loc] :=
    fun h => ⟨by rw [h, limb]; simp, trivial⟩
  have num : ∀ (off : Nat) (locs : List Loc) {V : Nat},
      resBytes (table[152]!) ((leavesAt 0x80002dc4)[0]!) off locs (8 * locs.length) = true →
      LimbsFrom σ m V 0 locs → BytesAt m' (σ.res + w off) (leBytes (8 * locs.length) V) :=
    fun off locs V h hl => res_num C h fun i hi => by simpa using limbsFrom_get hl i hi
  have byte0 : ∀ (a : Nat) (loc : Loc) {V : Nat},
      resLoc (table[152]!) ((leavesAt 0x80002dc4)[0]!) a loc 0 = true →
      loc.word σ m = w V → m'.mem (σ.res + w a) = some (BitVec.ofNat 8 V) :=
    fun a loc V h hw => by rw [res_loc C h, hw, byteOf_w _ (by decide)]; simp
  refine ⟨?_, ?_, num 0x30 _ (by decide) hval, num 0x50 _ (by decide) hbf,
    num 0x60 _ (by decide) hr, num 0x80 _ (by decide) hs, ?_, num 0xb0 _ (by decide) (one hn),
    num 0xb8 _ (by decide) (one hgl), num 0x100 _ (by decide) (one hv),
    byte0 0x108 _ (by decide) hty, ?_⟩
  · have := num 0 _ (by decide) hgp
    rwa [show σ.res + w 0 = σ.res from BitVec.add_zero _] at this
  · split at hpf
    · exact ⟨num 0x10 _ (by decide) hpf.1, byte0 0x20 _ (by decide) hpf.2⟩
    · exact byte0 0x20 _ (by decide) hpf
  · split at hc
    · exact ⟨num 0xa0 _ (by decide) (one hc.1), byte0 0xa8 _ (by decide) hc.2⟩
    · exact byte0 0xa8 _ (by decide) hc
  · split at hto
    · exact ⟨res_bytes C (off := 0x109) (n := 20) (by decide) hto.1 hto.2.1,
        byte0 0x11d _ (by decide) hto.2.2⟩
    · exact byte0 0x11d _ (by decide) hto

set_option hygiene false in
/-- A row entry of `0x80002dc4` (`hF`, `hck`, `ht` in scope). -/
local macro "row " f:term : term =>
  `(row_val (f := $f) hF hck (by decide) (by simp [ArmOk, ht]) (by rw [ht]; decide))

/-- Arm 0 (legacy): the scalar fields of `legacyOf payload`. -/
theorem scal_legacy {σ : Sig} {m m' : Machine}
    (C : Ctx (table[152]!) ((leavesAt 0x80002dc4)[0]!) σ m m')
    (hF : FieldsOk σ m (cutFields 0x80002dc4)) (hck : ChecksL (armChecks σ.t) σ.payload)
    (ht : σ.t = 0) : TxScal m' σ.res (legacyOf σ.payload) := by
  refine scal_of C ⟨row ⟨.reg 24, [0], .num 1 16 0⟩, row ⟨.reg 9, [0], .num 1 16 1⟩, trivial⟩
    (row ⟨.reg 15, [0, 1], .cst 0⟩)
    ⟨row ⟨.reg 21, [0], .num 4 32 0⟩, row ⟨.slot 0x100, [0], .num 4 32 1⟩,
      row ⟨.slot 0xf8, [0], .num 4 32 2⟩, row ⟨.slot 0x108, [0], .num 4 32 3⟩, trivial⟩
    ⟨(row ⟨.slot 0xe0, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 0).symm,
      (row ⟨.slot 0xd8, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 1).symm, trivial⟩
    ⟨row ⟨.reg 22, [0], .num 7 32 0⟩, row ⟨.reg 19, [0], .num 7 32 1⟩,
      row ⟨.reg 20, [0], .num 7 32 2⟩, row ⟨.slot 0xd0, [0], .num 7 32 3⟩, trivial⟩
    ⟨row ⟨.reg 10, [0], .num 8 32 0⟩, row ⟨.reg 12, [0], .num 8 32 1⟩,
      row ⟨.reg 13, [0], .num 8 32 2⟩, row ⟨.reg 11, [0], .num 8 32 3⟩, trivial⟩
    ?_ ((row ⟨.reg 27, [0], .num 0 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x120, [0], .num 2 8 0⟩).trans (limb_idx0 _))
    (row ⟨.reg 23, [0], .lv 6⟩) ((row ⟨.slot 0x130, [], .ty⟩).trans (reg12_of ht))
    (to_rows (k := 3) (row ⟨.slot 0x118, [0], .nz 3⟩) (row ⟨.slot 0x138, [0], .raw 3 0 8⟩)
      (row ⟨.slot 0x140, [0], .raw 3 8 8⟩) (row ⟨.slot 0x148, [0], .raw 3 16 4⟩)
      (addr_item (k := 3) hck (by rw [ht]; decide) (by rw [ht]; rfl)))
  have hlc : FieldVal.AtB σ (restN 6 σ.payload) ((Loc.reg 26).word σ m) (.lc 6) :=
    row ⟨.reg 26, [0], .lc 6⟩
  have hlt : FieldVal.AtB σ (restN 6 σ.payload) ((Loc.reg 14).word σ m) (.lt 6) :=
    row ⟨.reg 14, [0], .lt 6⟩
  simp only [FieldVal.AtB] at hlc hlt
  show match (legacyV (numOf 32 (restN 6 σ.payload))).1 with
    | some c => (Loc.reg 26).word σ m = w c ∧ (Loc.reg 14).word σ m = w 1
    | none => (Loc.reg 14).word σ m = w 0
  unfold legacyV
  by_cases h35 : 35 ≤ numOf 32 (restN 6 σ.payload)
  · simp only [if_pos h35]
    exact ⟨(hlc h35).trans (w_mod64 _).symm, by rw [hlt, if_pos h35]; rfl⟩
  · simp only [if_neg h35]
    by_cases h27 : 27 ≤ numOf 32 (restN 6 σ.payload) <;>
      simp only [h27, if_true, if_false] <;> exact (by rw [hlt, if_neg h35]; rfl)

/-- Arm 1 (EIP-2930): the scalar fields of `typedOf 1 payload`. -/
theorem scal_t1 {σ : Sig} {m m' : Machine}
    (C : Ctx (table[152]!) ((leavesAt 0x80002dc4)[0]!) σ m m')
    (hF : FieldsOk σ m (cutFields 0x80002dc4)) (hck : ChecksL (armChecks σ.t) σ.payload)
    (ht : σ.t = 1) : TxScal m' σ.res (typedOf 1 σ.payload) :=
  scal_of C ⟨row ⟨.reg 24, [1], .num 2 16 0⟩, row ⟨.reg 9, [1], .num 2 16 1⟩, trivial⟩
    (row ⟨.reg 15, [0, 1], .cst 0⟩)
    ⟨row ⟨.reg 21, [1], .num 5 32 0⟩, row ⟨.slot 0x100, [1], .num 5 32 1⟩,
      row ⟨.slot 0xf8, [1], .num 5 32 2⟩, row ⟨.slot 0x108, [1], .num 5 32 3⟩, trivial⟩
    ⟨(row ⟨.slot 0xe0, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 0).symm,
      (row ⟨.slot 0xd8, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 1).symm, trivial⟩
    ⟨row ⟨.reg 22, [1], .num 9 32 0⟩, row ⟨.reg 19, [1], .num 9 32 1⟩,
      row ⟨.reg 20, [1], .num 9 32 2⟩, row ⟨.slot 0xd0, [1], .num 9 32 3⟩, trivial⟩
    ⟨row ⟨.reg 10, [1], .num 10 32 0⟩, row ⟨.reg 12, [1], .num 10 32 1⟩,
      row ⟨.reg 13, [1], .num 10 32 2⟩, row ⟨.reg 11, [1], .num 10 32 3⟩, trivial⟩
    ⟨(row ⟨.reg 26, [1, 2, 3, 4], .num 0 8 0⟩).trans (limb_idx0 _),
      row ⟨.reg 14, [1, 2, 3, 4], .cst 1⟩⟩
    ((row ⟨.reg 27, [1, 2, 3, 4], .num 1 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x120, [1], .num 3 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.reg 23, [1], .num 8 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x130, [], .ty⟩).trans (reg12_of ht))
    (to_rows (k := 4) (row ⟨.slot 0x118, [1], .nz 4⟩) (row ⟨.slot 0x138, [1], .raw 4 0 8⟩)
      (row ⟨.slot 0x140, [1], .raw 4 8 8⟩) (row ⟨.slot 0x148, [1], .raw 4 16 4⟩)
      (addr_item (k := 4) hck (by rw [ht]; decide) (by rw [ht]; rfl)))

/-- Arm 2 (EIP-1559): the scalar fields of `typedOf 2 payload`. -/
theorem scal_t2 {σ : Sig} {m m' : Machine}
    (C : Ctx (table[152]!) ((leavesAt 0x80002dc4)[0]!) σ m m')
    (hF : FieldsOk σ m (cutFields 0x80002dc4)) (hck : ChecksL (armChecks σ.t) σ.payload)
    (ht : σ.t = 2) : TxScal m' σ.res (typedOf 2 σ.payload) :=
  scal_of C ⟨row ⟨.reg 24, [2, 3, 4], .num 3 16 0⟩, row ⟨.reg 9, [2, 3, 4], .num 3 16 1⟩, trivial⟩
    ⟨⟨row ⟨.reg 18, [2, 3, 4], .num 2 16 0⟩, row ⟨.slot 0x128, [2, 3, 4], .num 2 16 1⟩, trivial⟩,
      row ⟨.reg 15, [2, 3, 4], .cst 1⟩⟩
    ⟨row ⟨.reg 21, [2, 3, 4], .num 6 32 0⟩, row ⟨.slot 0x100, [2, 3, 4], .num 6 32 1⟩,
      row ⟨.slot 0xf8, [2, 3, 4], .num 6 32 2⟩, row ⟨.slot 0x108, [2, 3, 4], .num 6 32 3⟩, trivial⟩
    ⟨(row ⟨.slot 0xe0, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 0).symm,
      (row ⟨.slot 0xd8, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 1).symm, trivial⟩
    ⟨row ⟨.reg 22, [2], .num 10 32 0⟩, row ⟨.reg 19, [2], .num 10 32 1⟩,
      row ⟨.reg 20, [2], .num 10 32 2⟩, row ⟨.slot 0xd0, [2], .num 10 32 3⟩, trivial⟩
    ⟨row ⟨.reg 10, [2], .num 11 32 0⟩, row ⟨.reg 12, [2], .num 11 32 1⟩,
      row ⟨.reg 13, [2], .num 11 32 2⟩, row ⟨.reg 11, [2], .num 11 32 3⟩, trivial⟩
    ⟨(row ⟨.reg 26, [1, 2, 3, 4], .num 0 8 0⟩).trans (limb_idx0 _),
      row ⟨.reg 14, [1, 2, 3, 4], .cst 1⟩⟩
    ((row ⟨.reg 27, [1, 2, 3, 4], .num 1 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x120, [2, 3, 4], .num 4 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.reg 23, [2], .num 9 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x130, [], .ty⟩).trans (reg12_of ht))
    (to_rows (k := 5) (row ⟨.slot 0x118, [2, 3, 4], .nz 5⟩)
      (row ⟨.slot 0x138, [2, 3, 4], .raw 5 0 8⟩) (row ⟨.slot 0x140, [2, 3, 4], .raw 5 8 8⟩)
      (row ⟨.slot 0x148, [2, 3, 4], .raw 5 16 4⟩)
      (addr_item (k := 5) hck (by rw [ht]; decide) (by rw [ht]; rfl)))

/-! ## Arms 3 and 4: the list walks -/

/-- The versioned hashes of the list item at `b` (empty when the walk fails). -/
def hashesOf (b : List Byte) : List (List Byte) :=
  (walkList hash (payOf b).length (payOf b)).getD []

/-- The authorization tuples of the list item at `b` (empty when the walk fails). -/
def authsOf (b : List Byte) : List Auth :=
  (walkList auth (payOf b).length (payOf b)).getD []

theorem hashList_run {b : List Byte} {h p : Nat} (hd : F2.decode b = .success true h p)
    {es : List (List Byte)} (hw : walkList hash (payOf b).length (payOf b) = some es) :
    hashList.run b = some (es, restOf b) := by
  rw [payOf, hdOf_eq hd] at hw
  simp only [hashList, listPayload, StateT.run_bind, item_run hd, Option.bind_eq_bind,
    Option.bind_some, if_true, StateT.run_pure, Option.pure_def, hw, restOf, hdOf_eq hd]

theorem authList_run {b : List Byte} {h p : Nat} (hd : F2.decode b = .success true h p)
    {es : List Auth} (hw : walkList auth (payOf b).length (payOf b) = some es) :
    authList.run b = some (es, restOf b) := by
  rw [payOf, hdOf_eq hd] at hw
  simp only [authList, listPayload, StateT.run_bind, item_run hd, Option.bind_eq_bind,
    Option.bind_some, if_true, StateT.run_pure, Option.pure_def, hw, restOf, hdOf_eq hd]

/-- The EIP-4844 transaction the items at `b` make. -/
def blobOf (b : List Byte) : Tx :=
  let hd := headOf true b
  let b8 := headRest true b; let b9 := restOf b8; let b10 := restOf b9; let b11 := restOf b10
  let b12 := restOf b11; let b13 := restOf b12
  ⟨3, some hd.1, hd.2.1, hd.2.2.2.1, hd.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2, alOf b8, hashesOf b10, numOf 16 b9, [], numOf 8 b11, numOf 32 b12,
    numOf 32 b13⟩

/-- The EIP-7702 transaction the items at `b` make. -/
def authOf (b : List Byte) : Tx :=
  let hd := headOf true b
  let b8 := headRest true b; let b9 := restOf b8; let b10 := restOf b9; let b11 := restOf b10
  let b12 := restOf b11
  ⟨4, some hd.1, hd.2.1, hd.2.2.2.1, hd.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2, alOf b8, [], 0, authsOf b9, numOf 8 b10, numOf 32 b11, numOf 32 b12⟩

theorem decode_blob {b : List Byte} (h : ChecksL (armChecks 3) b)
    (hw : ∃ hs, walkList hash (payOf (restN 10 b)).length (payOf (restN 10 b)) = some hs) :
    decode 3 b = some (blobOf b) := by
  have hsplit : armChecks 3 = headChecks true ++ [.al, .str, .list, .le 8, .le 32, .le 32] := rfl
  rw [hsplit] at h
  obtain ⟨hh, h⟩ := checksL_append h
  have hr : restN (headChecks true).length b = headRest true b := rfl
  rw [hr] at h
  obtain ⟨f8, k8, h⟩ := checksL_cons h
  obtain ⟨f9, k9, h⟩ := checksL_cons h
  obtain ⟨f10, k10, h⟩ := checksL_cons h
  obtain ⟨f11, k11, h⟩ := checksL_cons h
  obtain ⟨f12, k12, h⟩ := checksL_cons h
  obtain ⟨f13, k13, -⟩ := checksL_cons h
  obtain ⟨hs, hw⟩ := hw
  obtain ⟨hh10, p10, hd10⟩ := k10
  have hl := hashList_run hd10 hw
  have hb : hashesOf (restOf (restOf (headRest true b))) = hs := by
    simp only [hashesOf]; rw [show restOf (restOf (headRest true b)) = restN 10 b from rfl, hw]; rfl
  have := body_blob (head_checked hh) (stepV_accessList _ f8 k8) (stepV_u128 _ f9 k9) hl
    (stepV_u64 _ f11 k11) (stepV_u256 _ f12 k12) (stepV_u256 _ f13 k13)
  rw [decode_of_run this, ← hb]
  rfl

theorem decode_auth {b : List Byte} (h : ChecksL (armChecks 4) b)
    (hw : ∃ ts, walkList auth (payOf (restN 9 b)).length (payOf (restN 9 b)) = some ts) :
    decode 4 b = some (authOf b) := by
  have hsplit : armChecks 4 = headChecks true ++ [.al, .list, .le 8, .le 32, .le 32] := rfl
  rw [hsplit] at h
  obtain ⟨hh, h⟩ := checksL_append h
  have hr : restN (headChecks true).length b = headRest true b := rfl
  rw [hr] at h
  obtain ⟨f8, k8, h⟩ := checksL_cons h
  obtain ⟨f9, k9, h⟩ := checksL_cons h
  obtain ⟨f10, k10, h⟩ := checksL_cons h
  obtain ⟨f11, k11, h⟩ := checksL_cons h
  obtain ⟨f12, k12, -⟩ := checksL_cons h
  obtain ⟨ts, hw⟩ := hw
  obtain ⟨hh9, p9, hd9⟩ := k9
  have hl := authList_run hd9 hw
  have hb : authsOf (restOf (headRest true b)) = ts := by
    simp only [authsOf]; rw [show restOf (headRest true b) = restN 9 b from rfl, hw]; rfl
  have := body_auth (head_checked hh) (stepV_accessList _ f8 k8) hl (stepV_u64 _ f10 k10)
    (stepV_u256 _ f11 k11) (stepV_u256 _ f12 k12)
  rw [decode_of_run this, ← hb]
  rfl

/-- Arm 3 (EIP-4844): the scalar fields of `blobOf payload`. -/
theorem scal_t3 {σ : Sig} {m m' : Machine}
    (C : Ctx (table[152]!) ((leavesAt 0x80002dc4)[0]!) σ m m')
    (hF : FieldsOk σ m (cutFields 0x80002dc4)) (hck : ChecksL (armChecks σ.t) σ.payload)
    (ht : σ.t = 3) : TxScal m' σ.res (blobOf σ.payload) :=
  scal_of C ⟨row ⟨.reg 24, [2, 3, 4], .num 3 16 0⟩, row ⟨.reg 9, [2, 3, 4], .num 3 16 1⟩, trivial⟩
    ⟨⟨row ⟨.reg 18, [2, 3, 4], .num 2 16 0⟩, row ⟨.slot 0x128, [2, 3, 4], .num 2 16 1⟩, trivial⟩,
      row ⟨.reg 15, [2, 3, 4], .cst 1⟩⟩
    ⟨row ⟨.reg 21, [2, 3, 4], .num 6 32 0⟩, row ⟨.slot 0x100, [2, 3, 4], .num 6 32 1⟩,
      row ⟨.slot 0xf8, [2, 3, 4], .num 6 32 2⟩, row ⟨.slot 0x108, [2, 3, 4], .num 6 32 3⟩, trivial⟩
    ⟨row ⟨.slot 0xe0, [3], .num 9 16 0⟩, row ⟨.slot 0xd8, [3], .num 9 16 1⟩, trivial⟩
    ⟨row ⟨.reg 22, [3], .num 12 32 0⟩, row ⟨.reg 19, [3], .num 12 32 1⟩,
      row ⟨.reg 20, [3], .num 12 32 2⟩, row ⟨.slot 0xd0, [3], .num 12 32 3⟩, trivial⟩
    ⟨row ⟨.reg 10, [3], .num 13 32 0⟩, row ⟨.reg 12, [3], .num 13 32 1⟩,
      row ⟨.reg 13, [3], .num 13 32 2⟩, row ⟨.reg 11, [3], .num 13 32 3⟩, trivial⟩
    ⟨(row ⟨.reg 26, [1, 2, 3, 4], .num 0 8 0⟩).trans (limb_idx0 _),
      row ⟨.reg 14, [1, 2, 3, 4], .cst 1⟩⟩
    ((row ⟨.reg 27, [1, 2, 3, 4], .num 1 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x120, [2, 3, 4], .num 4 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.reg 23, [3], .num 11 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x130, [], .ty⟩).trans (reg12_of ht))
    (to_rows (k := 5) (row ⟨.slot 0x118, [2, 3, 4], .nz 5⟩)
      (row ⟨.slot 0x138, [2, 3, 4], .raw 5 0 8⟩) (row ⟨.slot 0x140, [2, 3, 4], .raw 5 8 8⟩)
      (row ⟨.slot 0x148, [2, 3, 4], .raw 5 16 4⟩)
      (addr_item (k := 5) hck (by rw [ht]; decide) (by rw [ht]; rfl)))

/-- Arm 4 (EIP-7702): the scalar fields of `authOf payload`. -/
theorem scal_t4 {σ : Sig} {m m' : Machine}
    (C : Ctx (table[152]!) ((leavesAt 0x80002dc4)[0]!) σ m m')
    (hF : FieldsOk σ m (cutFields 0x80002dc4)) (hck : ChecksL (armChecks σ.t) σ.payload)
    (ht : σ.t = 4) : TxScal m' σ.res (authOf σ.payload) :=
  scal_of C ⟨row ⟨.reg 24, [2, 3, 4], .num 3 16 0⟩, row ⟨.reg 9, [2, 3, 4], .num 3 16 1⟩, trivial⟩
    ⟨⟨row ⟨.reg 18, [2, 3, 4], .num 2 16 0⟩, row ⟨.slot 0x128, [2, 3, 4], .num 2 16 1⟩, trivial⟩,
      row ⟨.reg 15, [2, 3, 4], .cst 1⟩⟩
    ⟨row ⟨.reg 21, [2, 3, 4], .num 6 32 0⟩, row ⟨.slot 0x100, [2, 3, 4], .num 6 32 1⟩,
      row ⟨.slot 0xf8, [2, 3, 4], .num 6 32 2⟩, row ⟨.slot 0x108, [2, 3, 4], .num 6 32 3⟩, trivial⟩
    ⟨(row ⟨.slot 0xe0, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 0).symm,
      (row ⟨.slot 0xd8, [0, 1, 2, 4], .cst 0⟩).trans (limb_of_zero 1).symm, trivial⟩
    ⟨row ⟨.reg 22, [4], .num 11 32 0⟩, row ⟨.reg 19, [4], .num 11 32 1⟩,
      row ⟨.reg 20, [4], .num 11 32 2⟩, row ⟨.slot 0xd0, [4], .num 11 32 3⟩, trivial⟩
    ⟨row ⟨.reg 10, [4], .num 12 32 0⟩, row ⟨.reg 12, [4], .num 12 32 1⟩,
      row ⟨.reg 13, [4], .num 12 32 2⟩, row ⟨.reg 11, [4], .num 12 32 3⟩, trivial⟩
    ⟨(row ⟨.reg 26, [1, 2, 3, 4], .num 0 8 0⟩).trans (limb_idx0 _),
      row ⟨.reg 14, [1, 2, 3, 4], .cst 1⟩⟩
    ((row ⟨.reg 27, [1, 2, 3, 4], .num 1 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x120, [2, 3, 4], .num 4 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.reg 23, [4], .num 10 8 0⟩).trans (limb_idx0 _))
    ((row ⟨.slot 0x130, [], .ty⟩).trans (reg12_of ht))
    (to_rows (k := 5) (row ⟨.slot 0x118, [2, 3, 4], .nz 5⟩)
      (row ⟨.slot 0x138, [2, 3, 4], .raw 5 0 8⟩) (row ⟨.slot 0x140, [2, 3, 4], .raw 5 8 8⟩)
      (row ⟨.slot 0x148, [2, 3, 4], .raw 5 16 4⟩)
      (addr_item (k := 5) hck (by rw [ht]; decide) (by rw [ht]; rfl)))

end ZesuExec.Fn.DTF
