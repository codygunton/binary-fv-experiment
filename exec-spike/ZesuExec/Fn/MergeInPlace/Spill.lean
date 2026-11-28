import ZesuExec.Fn.MergeInPlace.Lemmas

/-!
# `mergeInPlace` copies that spill to the frame

A copy whose body keeps live values in frame slots (`__anon_11564`) cuts at states with the frame
as a writable region:

* `SF c`: the frame only (`sp` = `.ptr 0 0`, `s0` = `.ptr 0 fs`).
* `SR3 c lo hi`: two writable elements at `lo - 15`, `hi - 16` (as `SR`) and the frame as region 2.

`FrameU64 mh f off v`: the 8 frame bytes at `off` are `v`'s; `init_entry` (and `init_F`, `init_R3`,
`init_P`) turn a slot load `.init k off 8` of the frame region into `v`. A leaf's frame writes are
checked on its literal write list: `keepB` (offsets untouched, via `memSrc`), `slotB` (a slot
holds an 8-byte write of a value, `slot_of`). `step_frame` and `step_swap3` are `step_copy` and
`step_swap` for these states.
-/

namespace ZesuExec.Fn.MergeInPlace
open ZesuExec ZesuExec.Sym ZesuExec.Vc ZesuExec.Machine
open ZesuExec.Fn.Rotate (SliceIs elem_lt addr_ne SliceIs.keep)

/-! ## States and environments -/

def SF (c : Cfg) : SState := entryState (ovL [(2, .ptr 0 0), (8, .ptr 0 c.fs)]) [frameR c.fs] []
def SR3 (c : Cfg) (lo hi : Nat) : SState :=
  entryState (ovL [(lo, .ptr 0 15), (hi, .ptr 1 16), (2, .ptr 2 0), (8, .ptr 2 c.fs)])
    [elemW, elemW, frameR c.fs] []

def envF (c : Cfg) (mh : Machine) : Env := entryEnv mh [(mh.reg 2, c.fs)]
def envR3 (c : Cfg) (lo hi : Nat) (mh : Machine) : Env :=
  entryEnv mh [(mh.reg (Fin.ofNat 32 lo) - w 15, 32), (mh.reg (Fin.ofNat 32 hi) - w 16, 32),
    (mh.reg 2, c.fs)]

/-! ## Frame slots -/

/-- The 8 bytes at `f + off` are those of `v`. -/
def FrameU64 (mh : Machine) (f : Word) (off : Nat) (v : Word) : Prop :=
  ∀ t < 8, mh.mem (f + w (off + t)) = some (byteOf v t)

theorem FrameU64.keep {mh m' : Machine} {f : Word} {off : Nat} {v : Word} (h : FrameU64 mh f off v)
    (hk : ∀ t < 8, m'.mem (f + w (off + t)) = mh.mem (f + w (off + t))) : FrameU64 m' f off v :=
  fun t ht => by rw [hk t ht]; exact h t ht

theorem byteList_shift {f g : Nat → Byte} : ∀ {k j n : Nat}, (∀ t < n, f (k + t) = g (j + t)) →
    byteList f k n = byteList g j n
  | _, _, 0, _ => rfl
  | k, j, n + 1, h => by
    have h0 : f k = g j := by simpa using h 0 (by omega)
    have hr : byteList f (k + 1) n = byteList g (j + 1) n := byteList_shift fun t ht => by
      have := h (t + 1) (by omega)
      rw [show k + (t + 1) = k + 1 + t by omega, show j + (t + 1) = j + 1 + t by omega] at this
      exact this
    simp only [byteList, h0, hr]

/-- A slot load of region `k` of an entry environment. -/
theorem init_entry {mh : Machine} {regs : List (Word × Nat)} {k off : Nat} {v : Word}
    (hv : FrameU64 mh (regs.getD k (0, 0)).1 off v) :
    (Sym.init k off 8).eval (entryEnv mh regs) = v := by
  simp only [Sym.eval]
  rw [← ofBytesLE_bytes8 v]
  congr 1
  apply byteList_shift
  intro t ht
  simp only [Env.byte0, entryEnv, Nat.zero_add, hv t ht, Option.getD_some]

/-- The `u64` at a frame slot. -/
theorem u64_frame {mh : Machine} {f : Word} {off : Nat} {v : Word} (hv : FrameU64 mh f off v) :
    u64 mh f off = v.toNat := by
  unfold u64
  rw [← ofBytesLE_bytes8 v]
  congr 2
  apply byteList_shift
  intro t ht
  simp only [Nat.zero_add, hv t ht, Option.getD_some]

/-- Slot facts across a leaf that leaves the offsets `keep` alone. -/
theorem frame_keep {mh m' : Machine} {f : Word} {keep : List Nat}
    (hk : ∀ j ∈ keep, m'.mem (f + w j) = mh.mem (f + w j)) {off : Nat}
    (hin : (List.range 8).all (fun t => keep.contains (off + t)) = true) {v : Word}
    (h : FrameU64 mh f off v) : FrameU64 m' f off v :=
  h.keep fun t ht => hk _ (by
    have := List.all_eq_true.mp hin t (List.mem_range.mpr ht)
    simpa using this)

/-- `sp` and `s0` of a leaf whose frame region is region `k`, and the kept registers. -/
theorem regs_frame {c : Cfg} {m mh m' : Machine} {regs : List (Word × Nat)} {lS : SState} {k : Nat}
    (hc : Common c m mh) (hm : Match (entryEnv mh regs) lS m') (hb : (regs.getD k (0, 0)).1 = mh.reg 2)
    (hsp : lS.reg 2 = .ptr k 0) (hs0 : lS.reg 8 = .ptr k c.fs) (hkeep : keepsB lS c.kept = true) :
    ∀ i ∈ [2, 8] ++ c.kept, m'.reg (Fin.ofNat 32 i) = mh.reg (Fin.ofNat 32 i) := by
  have h2 : mh.reg 2 = frame c m := hc.2.1
  intro i hi
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hi
  rcases hi with rfl | rfl | hi
  · rw [reg_at hm 2, hsp, Sym.eval_ptr]; simp only [Env.base, entryEnv, hb]; simp
  · rw [reg_at hm 8, hs0, show mh.reg (Fin.ofNat 32 8) = m.reg 2 from hc.2.2.1]
    simp only [Sym.eval, Env.base, entryEnv, hb, h2]
    unfold frame; rw [BitVec.ofInt_natCast]; exact BitVec.sub_add_cancel _ _
  · exact keeps_of hm (entryEnv_vars_lt _ _) hkeep i hi

/-- A leaf that writes nothing changes no memory. -/
theorem mem_nowrite {mh m' : Machine} {regs : List (Word × Nat)} {S lS : SState}
    (hm : Match (entryEnv mh regs) lS m') (hso : SameOutside (InWritable (entryEnv mh regs) S) mh m')
    (hmem : lS.mem = []) (hlen : lS.regions.length = S.regions.length)
    (hpres : ∀ a, InWritable (entryEnv mh regs) S a → (mh.mem a).isSome) :
    ∀ a, m'.mem a = mh.mem a := by
  intro a
  by_cases hw : InWritable (entryEnv mh regs) S a
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres a hw)
    obtain ⟨k, R, j, hR, -, hj, rfl⟩ := hw
    have hk : k < lS.regions.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.mp hR).1
    rw [hm.mem k j hk hj, hmem, hb]
    simp only [memByte, List.find?_nil, Env.byte0, entryEnv]
    simp only [Env.base, entryEnv] at hb
    rw [hb]; rfl
  · exact hso a hw

theorem init_F {c : Cfg} {mh : Machine} {f : Word} {off : Nat} {v : Word} (h2 : mh.reg 2 = f)
    (hv : FrameU64 mh f off v) : (Sym.init 0 off 8).eval (envF c mh) = v :=
  init_entry (by show FrameU64 mh (mh.reg 2) off v; rw [h2]; exact hv)

theorem init_R3 {c : Cfg} {lo hi : Nat} {mh : Machine} {f : Word} {off : Nat} {v : Word}
    (h2 : mh.reg 2 = f) (hv : FrameU64 mh f off v) : (Sym.init 2 off 8).eval (envR3 c lo hi mh) = v :=
  init_entry (by show FrameU64 mh (mh.reg 2) off v; rw [h2]; exact hv)

theorem init_P {c : Cfg} {r : Nat} {mh : Machine} {f : Word} {off : Nat} {v : Word}
    (h2 : mh.reg 2 = f) (hv : FrameU64 mh f off v) : (Sym.init 0 off 8).eval (envP c r mh) = v :=
  init_entry (by show FrameU64 mh (mh.reg 2) off v; rw [h2]; exact hv)

/-- Offsets `keep` of region `r` untouched by the writes `ws`. -/
def keepB (ws : List Write) (r : Nat) (keep : List Nat) : Bool :=
  keep.all fun j => memSrc ws r j == some (r, j)

/-- Slot `off` of region `r` holds the newest write `⟨r, off, 8, v⟩` on each of its bytes. -/
def slotB (ws : List Write) (r off : Nat) (v : Sym) : Bool :=
  (List.range 8).all fun t => ws.find? (·.covers r (off + t)) == some ⟨r, off, 8, v⟩

theorem slot_of {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') {r off : Nat} {v : Sym}
    (hr : r < S.regions.length) (hs : off + 8 ≤ env.size r) (h : slotB S.mem r off v = true) :
    FrameU64 m' (env.base r) off (v.eval env) := by
  intro t ht
  rw [hm.mem r (off + t) hr (by omega)]
  have := List.all_eq_true.mp h t (List.mem_range.mpr ht)
  simp only [beq_iff_eq] at this
  simp [memByte, this]

/-- `slot_of` with the region's base and the value named. -/
theorem slot_at {env : Env} {S : SState} {m' : Machine} (hm : Match env S m') {r off : Nat} {v : Sym}
    {f val : Word} (hr : r < S.regions.length) (hs : off + 8 ≤ env.size r)
    (h : slotB S.mem r off v = true) (hb : env.base r = f) (hv : v.eval env = val) :
    FrameU64 m' f off val := by
  have := slot_of hm hr hs h; rwa [hb, hv] at this

/-- Frame slot `off` holds `v`, for every pair `(off, v)`. -/
def SlotsAre (mh : Machine) (f : Word) : List (Nat × Word) → Prop
  | [] => True
  | (off, v) :: rest => FrameU64 mh f off v ∧ SlotsAre mh f rest

theorem SlotsAre.get {mh : Machine} {f : Word} : ∀ {L : List (Nat × Word)}, SlotsAre mh f L →
    ∀ {off : Nat} {v : Word}, (off, v) ∈ L → FrameU64 mh f off v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (o', v') :: L, ⟨h1, h2⟩, off, v, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact h1
    · exact SlotsAre.get h2 h

theorem SlotsAre.keep {mh m' : Machine} {f : Word} {keep : List Nat}
    (hk : ∀ j ∈ keep, m'.mem (f + w j) = mh.mem (f + w j)) :
    ∀ {L : List (Nat × Word)},
      (L.all fun p => (List.range 8).all fun t => keep.contains (p.1 + t)) = true →
      SlotsAre mh f L → SlotsAre m' f L
  | [], _, _ => trivial
  | (o, v) :: L, hin, ⟨h1, h2⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at hin
    exact ⟨frame_keep hk hin.1 h1, SlotsAre.keep hk hin.2 h2⟩

theorem SlotsAre.same {mh m' : Machine} {f : Word} (hall : ∀ a, m'.mem a = mh.mem a) :
    ∀ {L : List (Nat × Word)}, SlotsAre mh f L → SlotsAre m' f L
  | [], _ => trivial
  | (o, v) :: L, ⟨h1, h2⟩ => ⟨h1.keep fun _ _ => hall _, SlotsAre.same hall h2⟩

theorem SlotsAre.append {mh : Machine} {f : Word} {L L' : List (Nat × Word)} (h : SlotsAre mh f L)
    (h' : SlotsAre mh f L') : SlotsAre mh f (L ++ L') := by
  induction L with
  | nil => exact h'
  | cons p L ih => obtain ⟨o, v⟩ := p; exact ⟨h.1, ih h.2⟩

theorem SlotsAre.left {mh : Machine} {f : Word} {L L' : List (Nat × Word)}
    (h : SlotsAre mh f (L ++ L')) : SlotsAre mh f L := by
  induction L with
  | nil => trivial
  | cons p L ih => obtain ⟨o, v⟩ := p; exact ⟨h.1, ih h.2⟩

theorem SlotsAre.right {mh : Machine} {f : Word} {L L' : List (Nat × Word)}
    (h : SlotsAre mh f (L ++ L')) : SlotsAre mh f L' := by
  induction L with
  | nil => exact h
  | cons p L ih => obtain ⟨o, v⟩ := p; exact ih h.2

theorem keep_of {mh m' : Machine} {regs : List (Word × Nat)} {S : SState} {r : Nat}
    {keep : List Nat} (hm : Match (entryEnv mh regs) S m') (hr : r < S.regions.length)
    (hk : keepB S.mem r keep = true) (hsz : ∀ j ∈ keep, j < (regs.getD r (0, 0)).2)
    (hpres : ∀ j ∈ keep, (mh.mem ((regs.getD r (0, 0)).1 + w j)).isSome) :
    ∀ j ∈ keep, m'.mem ((regs.getD r (0, 0)).1 + w j) = mh.mem ((regs.getD r (0, 0)).1 + w j) := by
  intro j hj
  have hs := List.all_eq_true.mp hk j hj
  simp only [beq_iff_eq] at hs
  have := mem_of_src hm hr (by simpa [Env.size, entryEnv] using hsz j hj) hs
  simp only [Env.base, entryEnv] at this
  rw [this]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hpres j hj)
  show some ((mh.mem ((regs.getD r (0, 0)).1 + w j)).getD 0) = _
  rw [hb]; rfl

/-! ## Cut facts -/

theorem cutF_facts {c : Cfg} {m mh : Machine} (h : Pre c m) (hc : Common c m mh) :
    Env.WF (envF c mh) (SF c) ∧ Match (envF c mh) (SF c) mh := by
  obtain ⟨-, h2, h8, -, -, hpres, -⟩ := hc
  refine ⟨?_, ?_⟩
  · have := entry_wf (m := mh) (ov := ovL [(2, .ptr 0 0), (8, .ptr 0 c.fs)]) (ks := [])
      [((mh.reg 2, c.fs), frameR c.fs)] ?_ (by simp)
    · exact this
    · simp only [List.mem_singleton]
      rintro p rfl; rw [h2]; exact frame_ok h
  · refine match_ovL ?_ (fun k j hk hj => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl)
      · simp [Sym.eval, entryEnv, Env.base]
      · simp only [Sym.eval, entryEnv, Env.base, List.getD_cons_zero, Fin.reduceOfNat]
        rw [h8, h2]; exact s0_eval c _
    · simp at hk; subst hk
      simp only [entryEnv, Env.base, Env.size, List.getD_cons_zero] at hj ⊢
      rw [h2]; exact hpres j hj

theorem elem_base {m : Machine} {c : Cfg} (h : Pre c m) {e k : Nat} (he : e < bE m) (hk : k < 32)
    {x : Word} (hx : x = ptr m + w (32 * e + k)) : x - w k = ptr m + w (32 * e) := by
  rw [hx]; apply BitVec.eq_of_toNat_eq
  have := elem_lt (E := 32) he hk
  have hfit := pre_hfit h
  rw [BitVec.toNat_sub, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
  simp; omega

/-- An `SR3` cut: elements `e₁ ≠ e₂` at `lo - 15`, `hi - 16`, and the frame. -/
theorem cutR3_facts {c : Cfg} {m mh : Machine} {G : Nat → Nat → Byte} {lo hi e₁ e₂ : Nat}
    (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G) (h1 : e₁ < bE m) (h2' : e₂ < bE m)
    (hne : e₁ ≠ e₂)
    (hlo : mh.reg (Fin.ofNat 32 lo) = ptr m + w (32 * e₁ + 15))
    (hhi : mh.reg (Fin.ofNat 32 hi) = ptr m + w (32 * e₂ + 16)) :
    Env.WF (envR3 c lo hi mh) (SR3 c lo hi) ∧ Match (envR3 c lo hi mh) (SR3 c lo hi) mh := by
  obtain ⟨-, h2, h8, -, -, hpres, -⟩ := hc
  have hd := pre_disj h
  have b1 := elem_base h h1 (by omega) hlo
  have b2 := elem_base h h2' (by omega) hhi
  refine ⟨?_, ?_⟩
  · have := entry_wf (m := mh)
      (ov := ovL [(lo, .ptr 0 15), (hi, .ptr 1 16), (2, .ptr 2 0), (8, .ptr 2 c.fs)]) (ks := [])
      [((mh.reg (Fin.ofNat 32 lo) - w 15, 32), elemW), ((mh.reg (Fin.ofNat 32 hi) - w 16, 32), elemW),
        ((mh.reg 2, c.fs), frameR c.fs)] ?_ ?_
    · exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl)
      · rw [b1]; exact elem_ok h h1 _ rfl rfl
      · rw [b2]; exact elem_ok h h2' _ rfl rfl
      · rw [h2]; exact frame_ok h
    · simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      rw [b1, b2, h2]
      unfold Disjoint at hd ⊢
      simp only at hd ⊢
      rw [elem_addr h h1, elem_addr h h2']
      have := Nat.mul_le_mul_left 32 (show e₁ + 1 ≤ bE m by omega)
      have := Nat.mul_le_mul_left 32 (show e₂ + 1 ≤ bE m by omega)
      refine ⟨⟨?_, by omega⟩, by omega, fun _ h => h.elim⟩
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · left; have := Nat.mul_le_mul_left 32 hl; omega
      · right; have := Nat.mul_le_mul_left 32 hl; omega
  · refine match_ovL ?_ (fun k j hk hj => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl)
      · simp only [Sym.eval, entryEnv, Env.base, List.getD_cons_zero]
        rw [show BitVec.ofInt 64 15 = w 15 from rfl]; exact BitVec.sub_add_cancel _ _
      · simp only [Sym.eval, entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero]
        rw [show BitVec.ofInt 64 16 = w 16 from rfl]; exact BitVec.sub_add_cancel _ _
      · simp [Sym.eval, entryEnv, Env.base]
      · simp only [Sym.eval, entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero,
          Fin.reduceOfNat]
        rw [h8, h2]; exact s0_eval c _
    · simp at hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
      · simp only [entryEnv, Env.base, Env.size, List.getD_cons_zero] at hj ⊢
        rw [b1, items_add, hs e₁ h1 j hj]; rfl
      · simp only [entryEnv, Env.base, Env.size, List.getD_cons_succ, List.getD_cons_zero] at hj ⊢
        rw [b2, items_add, hs e₂ h2' j hj]; rfl
      · simp only [entryEnv, Env.base, Env.size, List.getD_cons_succ, List.getD_cons_zero] at hj ⊢
        rw [h2]; exact hpres j hj

/-! ## Leaves -/

theorem inW_F {c : Cfg} {mh : Machine} {a : Word} (h : InWritable (envF c mh) (SF c) a) :
    ∃ j < c.fs, a = mh.reg 2 + w j := by
  obtain ⟨k, R, j, hR, hw, hj, rfl⟩ := inW_entry h
  rcases k with _ | k
  · exact ⟨j, by simpa using hj, by simp⟩
  · simp at hR

/-- A run from `SF`: the items unchanged, the frame offsets `keep` (covering the saved slots)
untouched. -/
theorem step_frame {c : Cfg} {m mh m' : Machine} {G : Nat → Nat → Byte} {lS : SState}
    {keep : List Nat} (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G)
    (hm : Match (envF c mh) lS m') (hso : SameOutside (InWritable (envF c mh) (SF c)) mh m')
    (hlen : lS.regions.length = 1)
    (hsv : ∀ s ∈ c.saved, ∀ t < 8, s.1 + t ∈ keep) (hkl : ∀ j ∈ keep, j < c.fs)
    (hkp : keepB lS.mem 0 keep = true)
    (hsp : lS.reg 2 = .ptr 0 0) (hs0 : lS.reg 8 = .ptr 0 c.fs) (hkeep : keepsB lS c.kept = true) :
    Common c m m' ∧ Items m m' G ∧
      (∀ j ∈ keep, m'.mem (frame c m + w j) = mh.mem (frame c m + w j)) := by
  have h2 : mh.reg 2 = frame c m := hc.2.1
  have hpres := hc.2.2.2.2.2.1
  have hkeepm : ∀ j ∈ keep, m'.mem (frame c m + w j) = mh.mem (frame c m + w j) := by
    have := keep_of (regs := [(mh.reg 2, c.fs)]) hm (by omega) hkp hkl
      (fun j hj => by simpa [h2] using hpres j (hkl j hj))
    simpa [h2] using this
  have hout : ∀ a, (∀ j < c.fs, a ≠ frame c m + w j) → m'.mem a = mh.mem a := by
    intro a ha; apply hso; intro hw
    obtain ⟨j, hj, rfl⟩ := inW_F hw
    exact ha j hj (by rw [h2])
  refine ⟨common_step h hc (fun a ha _ => hout a ha) (fun s hs t ht => hkeepm _ (hsv s hs t ht))
    (fun j hj => ?_) (regs_frame (regs := [(mh.reg 2, c.fs)]) hc hm rfl hsp hs0 hkeep), ?_, hkeepm⟩
  · have := hm.mem 0 j (by omega) (by simpa [envF, entryEnv, Env.size] using hj)
    simp only [envF, entryEnv, Env.base, List.getD_cons_zero, h2] at this
    rw [this]; rfl
  · exact hs.keep fun e' he' o ho => hout _ fun j hj => slice_ne_frame h he' ho hj

/-- `Common` after a leaf that changes no memory and keeps `sp`, `s0` and the kept registers. -/
theorem common_same {c : Cfg} {m mh m' : Machine} (h : Pre c m) (hc : Common c m mh)
    (hall : ∀ a, m'.mem a = mh.mem a)
    (hk : ∀ i ∈ [2, 8] ++ c.kept, m'.reg (Fin.ofNat 32 i) = mh.reg (Fin.ofNat 32 i)) :
    Common c m m' :=
  common_step h hc (fun a _ _ => hall a) (fun _ _ _ _ => hall _)
    (fun j hj => by rw [hall]; exact hc.2.2.2.2.2.1 j hj) hk

/-- A run from `SF` that writes nothing. -/
theorem step_roF {c : Cfg} {m mh m' : Machine} {lS : SState} (h : Pre c m) (hc : Common c m mh)
    (hm : Match (envF c mh) lS m') (hso : SameOutside (InWritable (envF c mh) (SF c)) mh m')
    (hmem : lS.mem = []) (hlen : lS.regions.length = 1)
    (hsp : lS.reg 2 = .ptr 0 0) (hs0 : lS.reg 8 = .ptr 0 c.fs) (hkeep : keepsB lS c.kept = true) :
    Common c m m' ∧ ∀ a, m'.mem a = mh.mem a := by
  have h2 : mh.reg 2 = frame c m := hc.2.1
  have hall := mem_nowrite hm hso hmem (by simpa [SF, entryState] using hlen) fun a hw => by
    obtain ⟨j, hj, rfl⟩ := inW_F hw; rw [h2]; exact hc.2.2.2.2.2.1 j hj
  exact ⟨common_same h hc hall (regs_frame (regs := [(mh.reg 2, c.fs)]) hc hm rfl hsp hs0 hkeep), hall⟩

/-- A run from `SP` that writes nothing. -/
theorem step_roP {c : Cfg} {m mh m' : Machine} {r : Nat} {extra : List (Nat × Sym)} {lS : SState}
    (h : Pre c m) (hc : Common c m mh)
    (hm : Match (envP c r mh) lS m') (hso : SameOutside (InWritable (envP c r mh) (SP c r extra)) mh m')
    (hmem : lS.mem = []) (hlen : lS.regions.length = 2)
    (hsp : lS.reg 2 = .ptr 0 0) (hs0 : lS.reg 8 = .ptr 0 c.fs) (hkeep : keepsB lS c.kept = true) :
    Common c m m' ∧ ∀ a, m'.mem a = mh.mem a := by
  have h2 : mh.reg 2 = frame c m := hc.2.1
  have hall := mem_nowrite hm hso hmem (by simpa [SP, entryState] using hlen) fun a hw => by
    obtain ⟨j, hj, rfl⟩ := inW_P hw; rw [h2]; exact hc.2.2.2.2.2.1 j hj
  exact ⟨common_same h hc hall (regs_frame (regs := [(mh.reg 2, c.fs), (mh.reg (Fin.ofNat 32 r), 32)])
    hc hm rfl hsp hs0 hkeep), hall⟩

theorem inW_R3 {c : Cfg} {lo hi : Nat} {mh : Machine} {a : Word}
    (h : InWritable (envR3 c lo hi mh) (SR3 c lo hi) a) :
    (∃ j < 32, a = mh.reg (Fin.ofNat 32 lo) - w 15 + w j ∨ a = mh.reg (Fin.ofNat 32 hi) - w 16 + w j) ∨
      ∃ j < c.fs, a = mh.reg 2 + w j := by
  obtain ⟨k, R, j, hR, hw, hj, rfl⟩ := inW_entry h
  rcases k with _ | _ | _ | k
  · exact .inl ⟨j, by simpa using hj, .inl (by simp)⟩
  · exact .inl ⟨j, by simpa using hj, .inr (by simp)⟩
  · exact .inr ⟨j, by simpa using hj, by simp⟩
  · simp at hR

/-- A run from `SR3`: elements `e₁ ≠ e₂` exchanged (`swapB`), the frame offsets `keep` (covering
the saved slots) untouched, nothing else outside the frame changed. -/
theorem step_swap3 {c : Cfg} {m mh m' : Machine} {G : Nat → Nat → Byte} {lo hi e₁ e₂ : Nat}
    {lS : SState} {keep : List Nat} (h : Pre c m) (hc : Common c m mh) (hs : Items m mh G)
    (h1 : aS m ≤ e₁) (h1' : e₁ < bE m) (h2 : aS m ≤ e₂) (h2' : e₂ < bE m) (hne : e₁ ≠ e₂)
    (hlo : mh.reg (Fin.ofNat 32 lo) = ptr m + w (32 * e₁ + 15))
    (hhi : mh.reg (Fin.ofNat 32 hi) = ptr m + w (32 * e₂ + 16))
    (hm : Match (envR3 c lo hi mh) lS m')
    (hso : SameOutside (InWritable (envR3 c lo hi mh) (SR3 c lo hi)) mh m')
    (hlen : lS.regions.length = 3) (hsw : swapB lS.mem = true)
    (hsv : ∀ s ∈ c.saved, ∀ t < 8, s.1 + t ∈ keep) (hkl : ∀ j ∈ keep, j < c.fs)
    (hkp : keepB lS.mem 2 keep = true)
    (hsp : lS.reg 2 = .ptr 2 0) (hs0 : lS.reg 8 = .ptr 2 c.fs) (hkeep : keepsB lS c.kept = true) :
    Common c m m' ∧ (Items m m' fun e o =>
      if e = e₁ then G e₂ o else if e = e₂ then G e₁ o else G e o) ∧
      (∀ j ∈ keep, m'.mem (frame c m + w j) = mh.mem (frame c m + w j)) := by
  have hfit := pre_hfit h
  have hf2 : mh.reg 2 = frame c m := hc.2.1
  have hpres := hc.2.2.2.2.2.1
  have hb0r := elem_base h h1' (by omega) hlo
  have hb1r := elem_base h h2' (by omega) hhi
  have hb0 : (envR3 c lo hi mh).base 0 = ptr m + w (32 * e₁) := hb0r
  have hb1 : (envR3 c lo hi mh).base 1 = ptr m + w (32 * e₂) := hb1r
  have hadd : ∀ e j, ptr m + w (32 * e) + w j = ptr m + w (32 * e + j) := fun _ _ => items_add
  simp only [swapB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hsw
  have hw1 : ∀ j < 32, m'.mem (ptr m + w (32 * e₁ + j)) = some (G e₂ j) := by
    intro j hj
    have := mem_of_src hm (by omega) (by simp [envR3, entryEnv, Env.size]; omega) (hsw j hj).1
    rw [hb0, hadd] at this; rw [this]
    simp only [Env.byte0]
    have hb1' : (envR3 c lo hi mh).mem0 1 j = (mh.mem (ptr m + w (32 * e₂ + j))).getD 0 := by
      rw [← hadd, ← hb1]; rfl
    rw [hb1', hs e₂ h2' j hj]; rfl
  have hw2 : ∀ j < 32, m'.mem (ptr m + w (32 * e₂ + j)) = some (G e₁ j) := by
    intro j hj
    have := mem_of_src hm (by omega) (by simp [envR3, entryEnv, Env.size]; omega) (hsw j hj).2
    rw [hb1, hadd] at this; rw [this]
    simp only [Env.byte0]
    have hb0' : (envR3 c lo hi mh).mem0 0 j = (mh.mem (ptr m + w (32 * e₁ + j))).getD 0 := by
      rw [← hadd, ← hb0]; rfl
    rw [hb0', hs e₁ h1' j hj]; rfl
  have hkeepm : ∀ j ∈ keep, m'.mem (frame c m + w j) = mh.mem (frame c m + w j) := by
    have := keep_of (regs := [(mh.reg (Fin.ofNat 32 lo) - w 15, 32),
      (mh.reg (Fin.ofNat 32 hi) - w 16, 32), (mh.reg 2, c.fs)]) hm (by omega) hkp hkl
      (fun j hj => by simpa [hf2] using hpres j (hkl j hj))
    simpa [hf2] using this
  have hout : ∀ a, (∀ j < 32, a ≠ ptr m + w (32 * e₁ + j)) → (∀ j < 32, a ≠ ptr m + w (32 * e₂ + j)) →
      (∀ j < c.fs, a ≠ frame c m + w j) → m'.mem a = mh.mem a := by
    intro a ha1 ha2 haf; apply hso; intro hw
    rcases inW_R3 hw with ⟨j, hj, hq | hq⟩ | ⟨j, hj, hq⟩
    · apply ha1 j hj; rw [hq, hb0r, hadd]
    · apply ha2 j hj; rw [hq, hb1r, hadd]
    · apply haf j hj; rw [hq, hf2]
  refine ⟨common_step h hc (fun a ha hi => hout a (fun j hj hq => hi ⟨e₁, j, h1, h1', hj, hq⟩)
      (fun j hj hq => hi ⟨e₂, j, h2, h2', hj, hq⟩) ha)
    (fun s hs t ht => hkeepm _ (hsv s hs t ht))
    (fun j hj => by
      have := hm.mem 2 j (by omega) (by simpa [envR3, entryEnv, Env.size] using hj)
      simp only [envR3, entryEnv, Env.base, List.getD_cons_succ, List.getD_cons_zero, hf2] at this
      rw [this]; rfl)
    (regs_frame (regs := [(mh.reg (Fin.ofNat 32 lo) - w 15, 32), (mh.reg (Fin.ofNat 32 hi) - w 16, 32),
      (mh.reg 2, c.fs)]) hc hm rfl hsp hs0 hkeep), ?_, hkeepm⟩
  intro e he o ho
  dsimp only
  by_cases c1 : e = e₁
  · subst c1; rw [if_pos rfl]; exact hw1 o ho
  · rw [if_neg c1]
    by_cases c2 : e = e₂
    · subst c2; rw [if_pos rfl]; exact hw2 o ho
    · rw [if_neg c2, hout _ (fun j hj => addr_ne hfit he h1' ho hj (by omega))
        (fun j hj => addr_ne hfit he h2' ho hj (by omega))
        (fun j hj => slice_ne_frame h he ho hj)]
      exact hs e he o ho

end ZesuExec.Fn.MergeInPlace
