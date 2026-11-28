import ZesuExec.Fn.SszRoot.Spec
import ZesuExec.Fn.Stage
import ZesuExec.Fn.Preserve

/-!
# Lemmas for the SSZ root proofs

* `byteSrc ws r j`: where byte `j` of region `r` comes from after the writes `ws`: the initial
  byte `(r', j')` of a region when the newest write covering it stores a whole initial word
  (`.init r' o 8`) or nothing covers it; `byteLit ws r j`: the byte when the newest write stores a
  literal. Both are decidable on the leaves `sym_run` computes; `memByte_of_byteSrc` and
  `memByte_of_byteLit` turn them into `memByte` equations.
* `chunksOf` under `take`, `drop` and memory agreement.
-/

namespace ZesuExec.Fn.SszRoot
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

/-! ## Bytes of a leaf's memory -/

theorem byteList_getElem (f : Nat → Byte) : ∀ (k n i : Nat) (h : i < (byteList f k n).length),
    (byteList f k n)[i] = f (k + i)
  | _, 0, i, h => by simp [byteList] at h
  | k, n + 1, 0, _ => by simp [byteList]
  | k, n + 1, i + 1, h => by
    simp only [byteList, List.getElem_cons_succ]
    rw [byteList_getElem f (k + 1) n i (by simpa [byteList] using h)]
    congr 1; omega

/-- `(r, off)` for an initial word `.init r off 8`. -/
def wordSrc : Sym → Option (Nat × Nat)
  | .init r off 8 => some (r, off)
  | _ => none

theorem wordSrc_eq {s : Sym} {r o : Nat} (h : wordSrc s = some (r, o)) : s = .init r o 8 := by
  unfold wordSrc at h
  split at h
  · cases h; rfl
  · cases h

def byteSrc (ws : List Write) (r j : Nat) : Option (Nat × Nat) :=
  match ws.find? (·.covers r j) with
  | some w => if w.n ≤ 8 then (wordSrc w.v).map fun p => (p.1, p.2 + (j - w.off)) else none
  | none => some (r, j)

def byteLit (ws : List Write) (r j : Nat) : Option Byte :=
  match ws.find? (·.covers r j) with
  | some w => match w.v with
    | .lit v => some (byteOf (BitVec.ofNat 64 v) (j - w.off))
    | _ => none
  | none => none

theorem byteOf_init8 (env : Env) (r o k : Nat) (hk : k < 8) :
    byteOf ((Sym.init r o 8).eval env) k = env.byte0 r (o + k) := by
  simp only [Sym.eval]
  rw [byteOf_ofBytesLE _ (by simp [byteList_length]) k (by simp [byteList_length]; omega)]
  exact byteList_getElem _ _ _ _ _

theorem memByte_of_byteSrc {env : Env} {ws : List Write} {r j r' j' : Nat}
    (h : byteSrc ws r j = some (r', j')) : memByte env ws r j = env.byte0 r' j' := by
  unfold byteSrc at h
  unfold memByte
  cases hf : ws.find? (·.covers r j) with
  | none => rw [hf] at h; cases h; rfl
  | some w =>
    rw [hf] at h
    simp only at h ⊢
    by_cases hn : w.n ≤ 8
    · rw [if_pos hn] at h
      cases hs : wordSrc w.v with
      | none => rw [hs] at h; cases h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc := List.find?_some hf
        simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        rw [wordSrc_eq hs]
        exact byteOf_init8 env _ _ _ (by omega)
    · rw [if_neg hn] at h; cases h

theorem memByte_of_byteLit {env : Env} {ws : List Write} {r j : Nat} {b : Byte}
    (h : byteLit ws r j = some b) : memByte env ws r j = b := by
  unfold byteLit at h
  unfold memByte
  cases hf : ws.find? (·.covers r j) with
  | none => rw [hf] at h; cases h
  | some w =>
    rw [hf] at h
    simp only at h ⊢
    cases hv : w.v with
    | lit v => rw [hv] at h; cases h; rfl
    | _ => rw [hv] at h; cases h

end ZesuExec.Fn.SszRoot

namespace ZesuExec.Fn.SszRoot
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

/-! ## Leaves: memory and what every leaf keeps -/

/-- A byte of a region after a leaf, from `byteSrc`, in the cut machine `m`. -/
theorem mem_of_src {m m' : Machine} {regs : List (Word × Nat)} {S' : SState} {r j r' j' : Nat}
    (hm' : Match (entryEnv m regs) S' m') (hr : r < S'.regions.length)
    (hj : j < (entryEnv m regs).size r) (hs : byteSrc S'.mem r j = some (r', j')) :
    m'.mem ((regs.getD r (0, 0)).1 + BitVec.ofNat 64 j) =
      some ((m.mem ((regs.getD r' (0, 0)).1 + BitVec.ofNat 64 j')).getD 0) := by
  have := hm'.mem r j hr hj
  rw [memByte_of_byteSrc hs] at this
  exact this

theorem mem_of_lit {m m' : Machine} {regs : List (Word × Nat)} {S' : SState} {r j : Nat} {b : Byte}
    (hm' : Match (entryEnv m regs) S' m') (hr : r < S'.regions.length)
    (hj : j < (entryEnv m regs).size r) (hs : byteLit S'.mem r j = some b) :
    m'.mem ((regs.getD r (0, 0)).1 + BitVec.ofNat 64 j) = some b := by
  have := hm'.mem r j hr hj
  rw [memByte_of_byteLit hs] at this
  exact this

theorem preserved_of_leaf {env : Env} {S S' : SState} {m m' : Machine} (hwf : Env.WF env S)
    (hm' : Match env S' m') (hreg : S.regions.length ≤ S'.regions.length)
    (hso : SameOutside (InWritable env S) m m') : Preserved m m' := by
  refine ⟨fun a ha => ?_, fun a ha => hso a ?_⟩
  · by_cases hw : InWritable env S a
    · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
      have hr : r < S.regions.length := (List.getElem?_eq_some_iff.mp hR).1
      rw [hm'.mem r j (by omega) hj]; rfl
    · rw [hso a hw]; exact ha
  · rintro ⟨r, R, j, hR, hwR, hj, rfl⟩
    have := hwf.range r R hR
    simp only [hwR, if_true, Machine.writable, Machine.inRange, Bool.and_eq_true,
      decide_eq_true_eq, Layout.ramLo, Layout.ramHi] at this
    have e : (env.base r + BitVec.ofNat 64 j).toNat = (env.base r).toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e] at ha; unfold Layout.ramLo at ha; omega

/-- Every rodata byte of the image lies below RAM. -/
theorem rodata_lo : ∀ a b, zesuImage.rodataByte? a = some b → a < Layout.ramLo := by
  intro a b h
  have := (zesu_rodata_range h).2
  unfold Layout.rodataHi at this; unfold Layout.ramLo; omega

/-! ## Chunks -/

theorem chunksOf_length (m : Machine) (a : Word) (n : Nat) : (chunksOf m a n).length = n := by
  simp [chunksOf]

theorem chunksOf_take (m : Machine) (a : Word) (n h : Nat) :
    (chunksOf m a n).take h = chunksOf m a (min h n) := by
  simp [chunksOf, ← List.map_take, List.take_range]

theorem chunksOf_drop (m : Machine) (a : Word) (n h : Nat) :
    (chunksOf m a n).drop h = chunksOf m (a + BitVec.ofNat 64 (32 * h)) (n - h) := by
  apply List.ext_getElem
  · simp [chunksOf_length]
  · intro i h1 h2
    simp only [chunksOf, List.getElem_drop, List.getElem_map, List.getElem_range]
    apply List.map_congr_left
    intro j _
    rw [ofNat_add_ofNat, show 32 * h + (32 * i + j) = 32 * (h + i) + j by
      rw [Nat.mul_add, Nat.add_assoc]]

/-- Chunks depend only on the bytes they cover. -/
theorem chunksOf_congr {m m' : Machine} {a : Word} {n : Nat}
    (h : ∀ i < n, ∀ j < 32, m'.mem (a + BitVec.ofNat 64 (32 * i + j)) =
      m.mem (a + BitVec.ofNat 64 (32 * i + j))) : chunksOf m' a n = chunksOf m a n := by
  simp only [chunksOf]
  apply List.map_congr_left
  intro i hi
  apply List.map_congr_left
  intro j hj
  rw [h i (List.mem_range.mp hi) j (List.mem_range.mp hj)]

/-! ## The model -/

theorem sparseRoot_succ (ls : List (List Byte)) (d : Nat) :
    sparseRoot ls (d + 1) = sha2 (sparseRoot (ls.take (2 ^ d)) d)
      (if ls.length ≤ 2 ^ d then zeroHash d else sparseRoot (ls.drop (2 ^ d)) d) := rfl

/-! ## Bytes -/

theorem byteList_getD (bs : List Byte) : byteList (fun i => bs.getD i 0) 0 bs.length = bs := by
  apply List.ext_getElem (by simp [byteList_length])
  intro i h1 h2
  rw [byteList_getElem]; simp [List.getD_eq_getElem?_getD, h2]

theorem readBytes_of_bytesAt {m : Machine} {a : Word} {bs : List Byte} (h : BytesAt m a bs) :
    readBytes m.mem a.toNat bs.length = some bs := by
  have := readBytes_of (mem := m.mem) (a := a.toNat) (k := 0) (n := bs.length)
    (f := fun i => bs.getD i 0) (fun t ht => by
      rw [ofNat_toNat_add, h t ht]; simp [List.getD_eq_getElem?_getD, ht])
  rw [this, byteList_getD]

end ZesuExec.Fn.SszRoot

namespace ZesuExec.Fn.SszRoot
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

/-- The value and byte index of the newest write covering byte `j` of region `r`. -/
def byteVal (ws : List Write) (r j : Nat) : Option (Sym × Nat) :=
  match ws.find? (·.covers r j) with
  | some w => some (w.v, j - w.off)
  | none => none

theorem memByte_of_byteVal {env : Env} {ws : List Write} {r j k : Nat} {s : Sym}
    (h : byteVal ws r j = some (s, k)) : memByte env ws r j = byteOf (s.eval env) k := by
  unfold byteVal at h
  unfold memByte
  cases hf : ws.find? (·.covers r j) with
  | none => rw [hf] at h; cases h
  | some w => rw [hf] at h; cases h; rfl

theorem mem_of_val {m m' : Machine} {regs : List (Word × Nat)} {S' : SState} {r j k : Nat} {s : Sym}
    (hm' : Match (entryEnv m regs) S' m') (hr : r < S'.regions.length)
    (hj : j < (entryEnv m regs).size r) (hs : byteVal S'.mem r j = some (s, k)) :
    m'.mem ((regs.getD r (0, 0)).1 + BitVec.ofNat 64 j) = some (byteOf (s.eval (entryEnv m regs)) k) := by
  have := hm'.mem r j hr hj
  rw [memByte_of_byteVal hs] at this
  exact this

end ZesuExec.Fn.SszRoot

namespace ZesuExec.Fn.SszRoot
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

/-! ## `PreN` as facts on numbers -/

structure PreFacts (need : Nat) (m : Machine) : Prop where
  sp16 : (m.reg 2).toNat % 16 = 0
  spLo : Layout.ramLo + need ≤ (m.reg 2).toNat
  spHi : (m.reg 2).toNat ≤ Layout.ramHi
  stack : ∀ j < need, (m.mem (m.reg 2 - BitVec.ofNat 64 need + BitVec.ofNat 64 j)).isSome
  ro : RodataLoaded zesuImage m
  ra : RetAligned m
  outLo : Layout.ramLo ≤ (outOf m).toNat
  outHi : (outOf m).toNat + 32 ≤ Layout.ramHi
  outP : present m.mem (outOf m).toNat 32 = true
  bumpP : present m.mem Sha256.bump 16 = true
  stageP : present m.mem Layout.extraParams 8 = true
  chR : readable (chunkPtr m).toNat (32 * lenOf m) = true
  chP : present m.mem (chunkPtr m).toNat (32 * lenOf m) = true
  dSO : (m.reg 2).toNat ≤ (outOf m).toNat ∨ (outOf m).toNat + 32 ≤ (m.reg 2).toNat - need
  dSB : (m.reg 2).toNat ≤ Sha256.bump ∨ Sha256.bump + 16 ≤ (m.reg 2).toNat - need
  dSS : (m.reg 2).toNat ≤ Layout.extraParams ∨ Layout.extraParams + 8 ≤ (m.reg 2).toNat - need
  dSC : (m.reg 2).toNat ≤ (chunkPtr m).toNat ∨
    (chunkPtr m).toNat + 32 * lenOf m ≤ (m.reg 2).toNat - need
  dOB : (outOf m).toNat + 32 ≤ Sha256.bump ∨ Sha256.bump + 16 ≤ (outOf m).toNat
  dOS : (outOf m).toNat + 32 ≤ Layout.extraParams ∨ Layout.extraParams + 8 ≤ (outOf m).toNat
  dOC : (outOf m).toNat + 32 ≤ (chunkPtr m).toNat ∨
    (chunkPtr m).toNat + 32 * lenOf m ≤ (outOf m).toNat
  dBC : Sha256.bump + 16 ≤ (chunkPtr m).toNat ∨ (chunkPtr m).toNat + 32 * lenOf m ≤ Sha256.bump
  dTC : Layout.extraParams + 8 ≤ (chunkPtr m).toNat ∨
    (chunkPtr m).toNat + 32 * lenOf m ≤ Layout.extraParams

theorem PreFacts.of {need : Nat} {m : Machine} (h : PreN need m) : PreFacts need m := by
  obtain ⟨hro, ⟨h16, hlo, hhi, hst⟩, hra, hsrc, hout, hbump, hstage, hd⟩ := h
  have hsub : (m.reg 2 - BitVec.ofNat 64 need).toNat = (m.reg 2).toNat - need := by
    rw [BitVec.toNat_sub]; simp [Layout.ramLo, Layout.ramHi] at hlo hhi ⊢; omega
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, Disjoint, outR, chunkR, Sha256.bumpR, Sha256.stageR,
    hsub] at hd
  unfold srcOk at hsrc
  unfold dstOk at hout hbump hstage
  simp only [Bool.and_eq_true] at hsrc hout hbump hstage
  have hw := hout.1
  simp only [writable, inRange, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hb : (BitVec.ofNat 64 Sha256.bump).toNat = Sha256.bump := by decide
  have hs : (BitVec.ofNat 64 Layout.extraParams).toNat = Layout.extraParams := by decide
  rw [hb, hs] at hd
  obtain ⟨⟨d1, d2, d3, d4⟩, ⟨d5, d6, d7⟩, ⟨-, d8⟩, d9, -⟩ := hd
  exact ⟨h16, hlo, hhi, hst, hro, hra, hw.1, hw.2, hout.2, hbump.2, hstage.2, hsrc.1,
    hsrc.2, by omega, by omega, by omega, by omega, d5, d6, d7, d8, d9⟩

end ZesuExec.Fn.SszRoot

namespace ZesuExec.Fn.SszRoot
open ZesuExec

/-! ## Lengths in the model -/

theorem compress_length (H : List Sha256.W32) (blk : List Byte) :
    (Sha256.sha256Compress H blk).length = 8 := by
  simp [Sha256.sha256Compress]

theorem foldl_length8 {α : Type} (f : List Sha256.W32 → α → List Sha256.W32)
    (hf : ∀ H a, (f H a).length = 8) : ∀ (l : List α) (H : List Sha256.W32), H.length = 8 →
      (l.foldl f H).length = 8
  | [], _, h => h
  | a :: l, H, _ => foldl_length8 f hf l (f H a) (hf H a)

theorem hash_length (msg : List Byte) : (Sha256.hash msg).length = 32 := by
  unfold Sha256.hash
  simp only [List.length_flatMap, List.length_map, List.length_reverse, List.length_range]
  have h8 := foldl_length8
    (fun H i => Sha256.sha256Compress H (List.take 64 (List.drop (64 * i) (Sha256.pad msg))))
    (fun H _ => compress_length H _) (List.range ((Sha256.pad msg).length / 64)) Sha256.H0 rfl
  generalize List.foldl _ _ _ = H at h8 ⊢
  rw [List.map_const', h8]; rfl

theorem sha2_length (a b : List Byte) : (sha2 a b).length = 32 := hash_length _

theorem zeroHash_length : ∀ k, (zeroHash k).length = 32
  | 0 => rfl
  | _ + 1 => sha2_length _ _

theorem sparseRoot_length : ∀ (d : Nat) (ls : List (List Byte)), (∀ c ∈ ls, c.length = 32) →
    (sparseRoot ls d).length = 32
  | 0, [], _ => rfl
  | 0, c :: _, h => h c (by simp)
  | _ + 1, _, _ => sha2_length _ _

theorem progressiveRootAt_length (ls : List (List Byte)) (d : Nat) :
    (progressiveRootAt ls d).length = 32 := by
  rw [progressiveRootAt]; split
  · exact zeroHash_length 0
  · exact sha2_length _ _

theorem chunksOf_mem_length {m : Machine} {a : Word} {n : Nat} :
    ∀ c ∈ chunksOf m a n, c.length = 32 := by
  intro c hc; simp only [chunksOf, List.mem_map] at hc; obtain ⟨_, _, rfl⟩ := hc; simp

theorem chunksOf_take_mem {m : Machine} {a : Word} {n h : Nat} :
    ∀ c ∈ (chunksOf m a n).take h, c.length = 32 :=
  fun c hc => chunksOf_mem_length c (List.mem_of_mem_take hc)

theorem chunksOf_drop_mem {m : Machine} {a : Word} {n h : Nat} :
    ∀ c ∈ (chunksOf m a n).drop h, c.length = 32 :=
  fun c hc => chunksOf_mem_length c (List.mem_of_mem_drop hc)

end ZesuExec.Fn.SszRoot
