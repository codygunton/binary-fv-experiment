import ZesuExec.Fn.Common
import ZesuExec.Fn.Preserve

/-!
# The free-list invariant of `alt_fl_alloc` (programme plan S13)

Transcribed from `src/zkvm/alt_fl_alloc.zig` and `FREELIST_ALLOC.md` beside it. The allocator's
memory (`Arena`) is fixed by the linker script: the 22 free-list heads `free_lists`
(`0xa0534008`, 176 bytes), the bump pointers `ZKVM_HEAP_POS` (`0xa0d34520`) and `ZKVM_HEAP_TOP`
(`0xa0d34528`), and the heap `[__zesu_heap_bottom, __zesu_heap_top) = [0xa0d34530, 0xbfff0000)`.

`Heap L m`: some abstract state `St` (the bump pointer and, per size class `k < 22`, the list
of free blocks) is what `m` stores (`Decode`: each head cell starts a null-terminated chain
through the first word of each free block, `HEAP_POS` holds the bump pointer, `HEAP_TOP` holds
`heapTop`, every arena byte is present), and `Good L st`: every free block of class `k` spans
`classBytes k` bytes, every live block `(p, n)` of `L` reserves `cap n` bytes at `p` (the
bytes `alloc` set aside for it: `classBytes (sizeClassOfBytes n)` below 16 MiB, `n` above), all
these blocks lie in the heap below the bump pointer and are pairwise disjoint.

`Priv L` is the arena outside the live blocks.
-/

namespace ZesuExec.Fn
open ZesuExec ZesuExec.Machine
open ZesuExec.Sym (toNat_add_ofNat ofNat_toNat_add)

/-- An address inside one of the live blocks. -/
def InLive (L : List (Word × Nat)) (a : Word) : Prop := ∃ b ∈ L, InRange b.1 b.2 a

/-- `[lo, lo+n)` lies in RAM. -/
def RamRange (lo : Word) (n : Nat) : Prop :=
  Layout.ramLo ≤ lo.toNat ∧ lo.toNat + n ≤ Layout.ramHi

/-- The `n` bytes at `a` are present. -/
def Present (m : Machine) (a : Word) (n : Nat) : Prop :=
  ∀ j < n, (m.mem (a + BitVec.ofNat 64 j)).isSome

/-- The 16-byte frame an allocator callee uses avoids the allocator's memory. -/
def CalleeFrameFree (Priv : Word → Prop) (m : Machine) : Prop :=
  ∀ a, InRange (m.reg 2 - 16) 16 a → ¬ Priv a

namespace Alloc

def flBase : Nat := 0xa0534008
def posAddr : Nat := 0xa0d34520
def topAddr : Nat := 0xa0d34528
def heapLo : Nat := 0xa0d34530
def heapTop : Nat := 0xbfff0000

/-- `sizeClassOfBytes` of `alt_fl_alloc.zig`, line for line: `ceilLog2(size) - 3` clamped at 0,
`22` (the oversized sentinel) above 16 MiB. -/
def sizeClassOfBytes (size : Nat) : Nat :=
  if size ≤ 2048 then
    if size ≤ 64 then
      if size ≤ 16 then (if size ≤ 8 then 0 else 1)
      else if size ≤ 32 then 2 else 3
    else if size ≤ 512 then
      if size ≤ 128 then 4 else if size ≤ 256 then 5 else 6
    else if size ≤ 1024 then 7 else 8
  else if size ≤ 262144 then
    if size ≤ 16384 then
      if size ≤ 4096 then 9 else if size ≤ 8192 then 10 else 11
    else if size ≤ 65536 then
      if size ≤ 32768 then 12 else 13
    else if size ≤ 131072 then 14 else 15
  else if size ≤ 4194304 then
    if size ≤ 1048576 then
      if size ≤ 524288 then 16 else 17
    else if size ≤ 2097152 then 18 else 19
  else if size ≤ 8388608 then 20
  else if size ≤ 16777216 then 21
  else 22

/-- `classBytes`: bytes of a block of class `c`. -/
def classBytes (c : Nat) : Nat := 2 ^ (c + 3)

/-- Bytes `alloc` sets aside for a request of `n` bytes (any log2 alignment up to 4). -/
def cap (n : Nat) : Nat :=
  if sizeClassOfBytes n < 22 then classBytes (sizeClassOfBytes n) else n

/-- The allocator's memory. -/
def Arena (a : Word) : Prop :=
  (flBase ≤ a.toNat ∧ a.toNat < flBase + 176) ∨ (posAddr ≤ a.toNat ∧ a.toNat < heapTop)

/-- The word at `a`. -/
def rd (m : Machine) (a : Nat) : Option Word := m.load (BitVec.ofNat 64 a) 8

/-- A null-terminated list: the word at `c` is the first block, the first word of each block
the next. -/
def Chain (m : Machine) : Nat → List Nat → Prop
  | c, [] => rd m c = some 0
  | c, p :: ps => rd m c = some (BitVec.ofNat 64 p) ∧ Chain m p ps

structure St where
  pos : Nat
  fl : Nat → List Nat

def freeBlocks (st : St) : List (Nat × Nat) :=
  (List.range 22).flatMap fun k => (st.fl k).map fun p => (p, classBytes k)

def liveBlocks (L : List (Word × Nat)) : List (Nat × Nat) := L.map fun b => (b.1.toNat, cap b.2)

def blocks (L : List (Word × Nat)) (st : St) : List (Nat × Nat) := freeBlocks st ++ liveBlocks L

def NDisj (a b : Nat × Nat) : Prop := a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

structure Good (L : List (Word × Nat)) (st : St) : Prop where
  pos_lo : heapLo ≤ st.pos
  pos_hi : st.pos ≤ Layout.ramHi
  live_pos : ∀ b ∈ L, 0 < b.2
  inside : ∀ b ∈ blocks L st, heapLo ≤ b.1 ∧ b.1 + b.2 ≤ st.pos ∧ b.1 + b.2 ≤ heapTop
  disj : (blocks L st).Pairwise NDisj

structure Decode (m : Machine) (st : St) : Prop where
  present : ∀ a, Arena a → (m.mem a).isSome
  pos : rd m posAddr = some (BitVec.ofNat 64 st.pos)
  top : rd m topAddr = some (BitVec.ofNat 64 heapTop)
  chains : ∀ k < 22, Chain m (flBase + 8 * k) (st.fl k)

/-- The free-list invariant with live blocks `L`. -/
def Heap (L : List (Word × Nat)) (m : Machine) : Prop := ∃ st, Decode m st ∧ Good L st

/-- The arena outside the live blocks. -/
def Priv (L : List (Word × Nat)) (a : Word) : Prop := Arena a ∧ ¬ InLive L a

/-! ## Size classes -/

theorem sc_le (n : Nat) : sizeClassOfBytes n ≤ 22 := by
  unfold sizeClassOfBytes; repeat' split
  all_goals omega

theorem sc_lt_iff (n : Nat) : sizeClassOfBytes n < 22 ↔ n ≤ 16777216 := by
  unfold sizeClassOfBytes; repeat' split
  all_goals omega

/-- A block of the class holds the request. -/
theorem le_classBytes_sc {n : Nat} (h : n ≤ 16777216) : n ≤ classBytes (sizeClassOfBytes n) := by
  unfold sizeClassOfBytes classBytes; repeat' split
  all_goals first | omega | simp_all

theorem sc_pos {n : Nat} (h : 8 < n) : 1 ≤ sizeClassOfBytes n := by
  unfold sizeClassOfBytes; repeat' split
  all_goals omega

theorem le_cap (n : Nat) : n ≤ cap n := by
  unfold cap; split
  · exact le_classBytes_sc ((sc_lt_iff n).mp ‹_›)
  · exact Nat.le_refl _

theorem classBytes_pos (c : Nat) : 0 < classBytes c := Nat.pow_pos (by decide)

theorem classBytes_mono {c d : Nat} (h : c ≤ d) : classBytes c ≤ classBytes d :=
  Nat.pow_le_pow_right (by decide) (by omega)

theorem eight_le_classBytes (c : Nat) : 8 ≤ classBytes c := by
  have := classBytes_mono (Nat.zero_le c); simpa [classBytes] using this

theorem classBytes_le_24 {c : Nat} (h : c < 22) : classBytes c ≤ 2 ^ 24 :=
  classBytes_mono (d := 21) (by omega)

theorem cap_le_classBytes {n k : Nat} (h : sizeClassOfBytes n ≤ k) (hk : k < 22) :
    cap n ≤ classBytes k := by
  unfold cap; split
  · exact classBytes_mono h
  · omega

theorem cap_pos {n : Nat} (h : 0 < n) : 0 < cap n := Nat.lt_of_lt_of_le h (le_cap n)


/-! ## Memory reads -/

theorem readBytes_congr {mem mem' : Word → Option Byte} :
    ∀ {a n : Nat}, (∀ t < n, mem' (BitVec.ofNat 64 (a + t)) = mem (BitVec.ofNat 64 (a + t))) →
      readBytes mem' a n = readBytes mem a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    have ih := readBytes_congr (mem := mem) (mem' := mem') (a := a + 1) (n := n) fun t ht => by
      have := h (t + 1) (by omega); rwa [show a + (t + 1) = a + 1 + t by omega] at this
    simp only [readBytes, Nat.add_zero] at h0 ⊢
    rw [h0, ih]

theorem rd_congr {m m' : Machine} {a : Nat} (ha : a < 2 ^ 64)
    (h : ∀ t < 8, m'.mem (BitVec.ofNat 64 (a + t)) = m.mem (BitVec.ofNat 64 (a + t))) :
    rd m' a = rd m a := by
  unfold rd Machine.load
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, readBytes_congr h]

theorem chain_congr {m m' : Machine} :
    ∀ {c : Nat} {ps : List Nat}, Chain m c ps → c < 2 ^ 64 →
      (∀ t < 8, m'.mem (BitVec.ofNat 64 (c + t)) = m.mem (BitVec.ofNat 64 (c + t))) →
      (∀ p ∈ ps, p < 2 ^ 64 ∧
        ∀ t < 8, m'.mem (BitVec.ofNat 64 (p + t)) = m.mem (BitVec.ofNat 64 (p + t))) →
      Chain m' c ps
  | c, [], h, hc, h0, _ => by simp only [Chain] at h ⊢; rw [rd_congr hc h0]; exact h
  | c, p :: ps, ⟨h1, h2⟩, hc, h0, hps => by
    refine ⟨by rw [rd_congr hc h0]; exact h1, ?_⟩
    obtain ⟨hp, hp0⟩ := hps p (List.mem_cons_self ..)
    exact chain_congr h2 hp hp0 fun q hq => hps q (List.mem_cons_of_mem _ hq)

/-! ## Blocks -/

theorem mem_freeBlocks {st : St} {k p : Nat} (hk : k < 22) (hp : p ∈ st.fl k) :
    (p, classBytes k) ∈ freeBlocks st := by
  simp only [freeBlocks, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨k, hk, p, hp, rfl⟩

theorem mem_liveBlocks {L : List (Word × Nat)} {b : Word × Nat} (hb : b ∈ L) :
    (b.1.toNat, cap b.2) ∈ liveBlocks L := List.mem_map_of_mem hb

theorem Good.live_in {L : List (Word × Nat)} {st : St} (hg : Good L st) {b : Word × Nat}
    (hb : b ∈ L) : heapLo ≤ b.1.toNat ∧ b.1.toNat + cap b.2 ≤ st.pos ∧
      b.1.toNat + cap b.2 ≤ heapTop :=
  hg.inside _ (List.mem_append_right _ (mem_liveBlocks hb))

theorem Good.free_in {L : List (Word × Nat)} {st : St} (hg : Good L st) {k p : Nat} (hk : k < 22)
    (hp : p ∈ st.fl k) : heapLo ≤ p ∧ p + classBytes k ≤ st.pos ∧ p + classBytes k ≤ heapTop :=
  hg.inside _ (List.mem_append_left _ (mem_freeBlocks hk hp))

theorem Good.free_live {L : List (Word × Nat)} {st : St} (hg : Good L st) {k p : Nat}
    (hk : k < 22) (hp : p ∈ st.fl k) {b : Word × Nat} (hb : b ∈ L) :
    NDisj (p, classBytes k) (b.1.toNat, cap b.2) :=
  (List.pairwise_append.mp hg.disj).2.2 _ (mem_freeBlocks hk hp) _ (mem_liveBlocks hb)

/-- A live address lies in the heap. -/
theorem Good.inLive_heap {L : List (Word × Nat)} {st : St} (hg : Good L st) {a : Word}
    (h : InLive L a) : heapLo ≤ a.toNat ∧ a.toNat < heapTop := by
  obtain ⟨b, hb, h1, h2⟩ := h
  have := hg.live_in hb; have := le_cap b.2; omega

/-- The first word of a free block is outside the live blocks. -/
theorem Good.free_not_live {L : List (Word × Nat)} {st : St} (hg : Good L st) {k p t : Nat}
    (hk : k < 22) (hp : p ∈ st.fl k) (ht : t < 8) : ¬ InLive L (BitVec.ofNat 64 (p + t)) := by
  rintro ⟨b, hb, h1, h2⟩
  have hin := hg.free_in hk hp
  have hd := hg.free_live hk hp hb
  have h8 := eight_le_classBytes k
  have hc := le_cap b.2
  simp only [NDisj] at hd
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold heapTop at hin; omega)] at h1 h2
  omega

theorem cell_not_live {L : List (Word × Nat)} {st : St} (hg : Good L st) {c t : Nat}
    (hc : c + t < heapLo) : ¬ InLive L (BitVec.ofNat 64 (c + t)) := fun h => by
  have := hg.inLive_heap h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold heapLo at hc; omega)] at this
  omega

/-! ## The fields of the former `AllocAssumptions` -/

theorem priv_not_live (L : List (Word × Nat)) (a : Word) (h : Priv L a) : ¬ InLive L a := h.2

theorem arena_split (L : List (Word × Nat)) (m : Machine) (a : Word) (h : Heap L m) :
    Arena a ↔ Priv L a ∨ InLive L a := by
  obtain ⟨st, -, hg⟩ := h
  refine ⟨fun ha => (Classical.em (InLive L a)).elim .inr fun hn => .inl ⟨ha, hn⟩, ?_⟩
  rintro (h | h)
  · exact h.1
  · have := hg.inLive_heap h; right; unfold posAddr; unfold heapLo at this; omega

theorem live_ok (L : List (Word × Nat)) (m : Machine) (h : Heap L m) :
    L.Pairwise (fun b c => b.1.toNat + b.2 ≤ c.1.toNat ∨ c.1.toNat + c.2 ≤ b.1.toNat) ∧
    ∀ b ∈ L, RamRange b.1 b.2 ∧ Present m b.1 b.2 := by
  obtain ⟨st, hd, hg⟩ := h
  refine ⟨?_, fun b hb => ?_⟩
  · have := (List.pairwise_append.mp hg.disj).2.1
    unfold liveBlocks at this
    rw [List.pairwise_map] at this
    refine this.imp fun {b c} h => ?_
    have := le_cap b.2; have := le_cap c.2
    simp only [NDisj] at h; omega
  · have hin := hg.live_in hb
    have hc := le_cap b.2
    refine ⟨by unfold RamRange; unfold heapLo heapTop at hin; unfold Layout.ramLo Layout.ramHi; omega,
      fun j hj => hd.present _ ?_⟩
    right
    rw [toNat_add_ofNat (by unfold heapTop at hin; omega)]
    unfold posAddr; unfold heapLo heapTop at hin; unfold heapTop; omega

/-- Arena bytes outside the live blocks are what `Decode` reads. -/
theorem decode_frame {L : List (Word × Nat)} {st : St} {m m' : Machine} (hd : Decode m st)
    (hg : Good L st) (hagree : ∀ a, Priv L a → m'.mem a = m.mem a)
    (hpres : ∀ a, InLive L a → (m'.mem a).isSome) : Decode m' st where
  present a ha := (Classical.em (InLive L a)).elim (hpres a) fun hn => by
    rw [hagree a ⟨ha, hn⟩]; exact hd.present a ha
  pos := by
    rw [rd_congr (by unfold posAddr; omega) fun t ht => hagree _ ⟨?_, cell_not_live hg ?_⟩]
    · exact hd.pos
    · right; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold posAddr; omega)]
      unfold posAddr heapTop; omega
    · unfold posAddr heapLo; omega
  top := by
    rw [rd_congr (by unfold topAddr; omega) fun t ht => hagree _ ⟨?_, cell_not_live hg ?_⟩]
    · exact hd.top
    · right; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold topAddr; omega)]
      unfold posAddr topAddr heapTop; omega
    · unfold topAddr heapLo; omega
  chains k hk := by
    refine chain_congr (hd.chains k hk) (by unfold flBase; omega)
      (fun t ht => hagree _ ⟨?_, cell_not_live hg ?_⟩) (fun p hp => ?_)
    · left; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold flBase; omega)]
      unfold flBase; omega
    · unfold flBase heapLo; omega
    · have hin := hg.free_in hk hp
      refine ⟨by unfold heapTop at hin; omega, fun t ht => hagree _ ⟨?_, hg.free_not_live hk hp ht⟩⟩
      right
      have := eight_le_classBytes k
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold heapTop at hin; omega)]
      unfold posAddr; unfold heapLo heapTop at hin; unfold heapTop; omega

theorem heap_frame (L : List (Word × Nat)) (m m' : Machine) (h : Heap L m)
    (hpriv : ∀ a, Priv L a → m'.mem a = m.mem a) (hpres : ∀ b ∈ L, Present m' b.1 b.2) :
    Heap L m' := by
  obtain ⟨st, hd, hg⟩ := h
  refine ⟨st, decode_frame hd hg hpriv fun a ⟨b, hb, h1, h2⟩ => ?_, hg⟩
  have hin := hg.live_in hb
  have := hpres b hb (a.toNat - b.1.toNat) (by omega)
  rwa [← ofNat_toNat_add, show b.1.toNat + (a.toNat - b.1.toNat) = a.toNat by omega,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

/-- `heap_frame` for a step that keeps present bytes present (every run does, `Preserved`). -/
theorem heap_frame' (L : List (Word × Nat)) (m m' : Machine) (h : Heap L m)
    (hpriv : ∀ a, Priv L a → m'.mem a = m.mem a) (hp : Preserved m m') : Heap L m' :=
  heap_frame L m m' h hpriv fun b hb j hj => hp.1 _ (((live_ok L m h).2 b hb).2 j hj)

/-! ## Transitions: pop (`alloc` from a free list), bump (`sysAllocAligned`), push (`free`) -/

/-- Linear arithmetic over the allocator's address constants. -/
macro "anum" : tactic => `(tactic| ((try simp only [flBase, posAddr, topAddr, heapLo, heapTop,
  Layout.ramLo, Layout.ramHi] at *) <;> omega))

theorem flatMap_congr' {α : Type} {f g : Nat → List α} :
    ∀ {l : List Nat}, (∀ j ∈ l, f j = g j) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | j :: l, h => by
    simp only [List.flatMap_cons]
    rw [h j (List.mem_cons_self ..), flatMap_congr' fun i hi => h i (List.mem_cons_of_mem _ hi)]

theorem flatMap_update_perm {α : Type} (f g : Nat → List α) (a : α) (k : Nat) (hfk : f k = a :: g k)
    (hfg : ∀ j, j ≠ k → f j = g j) :
    ∀ n, k < n → ((List.range n).flatMap f).Perm (a :: (List.range n).flatMap g)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_or_ge k n with hl | hge
    · rw [hfg n (by omega)]
      exact (flatMap_update_perm f g a k hfk hfg n hl).append_right _
    · obtain rfl : k = n := by omega
      have : (List.range k).flatMap f = (List.range k).flatMap g :=
        flatMap_congr' fun j hj => hfg j (by simp at hj; omega)
      rw [this, hfk]; exact List.perm_middle

theorem ndisj_symm {x y : Nat × Nat} (h : NDisj x y) : NDisj y x := h.symm

theorem ofNat_toNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem inLive_append {L : List (Word × Nat)} {b : Word × Nat} {a : Word} :
    InLive (L ++ [b]) a ↔ InLive L a ∨ InRange b.1 b.2 a := by
  simp [InLive, or_and_right, exists_or]

theorem priv_append {L : List (Word × Nat)} {b : Word × Nat} {a : Word}
    (h : Priv (L ++ [b]) a) : Priv L a :=
  ⟨h.1, fun hl => h.2 (inLive_append.mpr (.inl hl))⟩

/-- Addresses of the arena cells and free-block words, as `Nat`s below `2^64`. -/
theorem free_word_lt {L : List (Word × Nat)} {st : St} (hg : Good L st) {k p : Nat} (hk : k < 22)
    (hp : p ∈ st.fl k) (t : Nat) (ht : t < 8) : p + t < heapTop := by
  have := hg.free_in hk hp; have := eight_le_classBytes k; omega

theorem priv_free {L : List (Word × Nat)} {st : St} (hg : Good L st) {k p t : Nat} (hk : k < 22)
    (hp : p ∈ st.fl k) (ht : t < 8) : Priv L (BitVec.ofNat 64 (p + t)) := by
  have hlt := free_word_lt hg hk hp t ht
  have := (hg.free_in hk hp).1
  refine ⟨.inr ?_, hg.free_not_live hk hp ht⟩
  rw [ofNat_toNat_lt (by anum)]; anum

theorem priv_cell {L : List (Word × Nat)} {st : St} (hg : Good L st) {c : Nat}
    (hc : (flBase ≤ c ∧ c < flBase + 176) ∨ (posAddr ≤ c ∧ c < heapLo)) :
    Priv L (BitVec.ofNat 64 c) := by
  have hlt : c < 2 ^ 64 := by anum
  refine ⟨?_, ?_⟩
  · unfold Arena; rw [ofNat_toNat_lt hlt]; anum
  · have := cell_not_live (t := 0) hg (c := c) (by unfold flBase posAddr heapLo at *; omega)
    simpa using this

/-- `InRange` of literal addresses as `Nat` intervals. -/
theorem inRange_ofNat {lo n x : Nat} (hlo : lo < 2 ^ 64) (hx : x < 2 ^ 64) :
    InRange (BitVec.ofNat 64 lo) n (BitVec.ofNat 64 x) ↔ lo ≤ x ∧ x < lo + n := by
  simp only [InRange, ofNat_toNat_lt hlo, ofNat_toNat_lt hx]

/-- Chains of every class but `k` stay when memory changes only outside `Priv L` or inside
`W`, and `W` misses every cell and free-block word they use. -/
theorem chain_keep {L : List (Word × Nat)} {st : St} {m m' : Machine} (hd : Decode m st)
    (hg : Good L st) {W : Word → Prop} (hagree : ∀ a, Priv L a → ¬ W a → m'.mem a = m.mem a)
    {j : Nat} (hj : j < 22) (hwc : ∀ t < 8, ¬ W (BitVec.ofNat 64 (flBase + 8 * j + t)))
    (hwp : ∀ p ∈ st.fl j, ∀ t < 8, ¬ W (BitVec.ofNat 64 (p + t))) :
    Chain m' (flBase + 8 * j) (st.fl j) :=
  chain_congr (hd.chains j hj) (by anum)
    (fun t ht => hagree _ (priv_cell hg (by anum)) (hwc t ht))
    (fun p hp => ⟨by have := free_word_lt hg hj hp 0 (by omega); anum,
      fun t ht => hagree _ (priv_free hg hj hp ht) (hwp p hp t ht)⟩)

def setFl (st : St) (k : Nat) (l : List Nat) : St :=
  { st with fl := fun j => if j = k then l else st.fl j }

theorem pop_perm {st : St} {k h : Nat} {t : List Nat} (hk : k < 22) (hfl : st.fl k = h :: t) :
    (freeBlocks st).Perm ((h, classBytes k) :: freeBlocks (setFl st k t)) :=
  flatMap_update_perm _ _ _ k (by simp [hfl, setFl]) (fun j hj => by simp [setFl, hj]) 22 hk

theorem pop_ok {L : List (Word × Nat)} {st : St} {m m' : Machine} (hd : Decode m st)
    (hg : Good L st) {k h n : Nat} {t : List Nat} (hk : k < 22) (hfl : st.fl k = h :: t)
    (hn : 0 < n) (hsc : sizeClassOfBytes n ≤ k)
    (hcell : rd m' (flBase + 8 * k) = rd m h)
    (hagree : ∀ a, Priv L a → ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 a → m'.mem a = m.mem a)
    (hpres : ∀ a, Arena a → (m.mem a).isSome → (m'.mem a).isSome) :
    Heap (L ++ [(BitVec.ofNat 64 h, n)]) m' := by
  have hh : h ∈ st.fl k := by rw [hfl]; exact List.mem_cons_self ..
  have hin := hg.free_in hk hh
  have hcap := cap_le_classBytes hsc hk
  have hhlt : h < 2 ^ 64 := by anum
  have hcellW : ∀ {x}, x < heapLo → (flBase + 8 * k ≤ x → x < flBase + 8 * k + 8 → False) →
      ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 (BitVec.ofNat 64 x) := fun hx hne hr => by
    rw [inRange_ofNat (by anum) (by anum)] at hr
    exact hne hr.1 hr.2
  have hblkW : ∀ p ∈ st.fl k ++ (List.range 22).flatMap st.fl, ∀ t < 8, ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 (BitVec.ofNat 64 (p + t)) := by
    intro p hp t ht hr
    have : heapLo ≤ p ∧ p + t < heapTop := by
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨(hg.free_in hk hp).1, free_word_lt hg hk hp t ht⟩
      · obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
        exact ⟨(hg.free_in (List.mem_range.mp hj) hp).1, free_word_lt hg (List.mem_range.mp hj) hp t ht⟩
    rw [inRange_ofNat (by anum) (by anum)] at hr
    unfold flBase heapLo at *; omega
  refine ⟨setFl st k t, ⟨fun a ha => hpres a ha (hd.present a ha), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [rd_congr (by anum) fun t ht => hagree _
      (priv_cell hg (by anum)) (hcellW (by anum)
        (by anum))]
    exact hd.pos
  · rw [rd_congr (by anum) fun t ht => hagree _
      (priv_cell hg (by anum)) (hcellW (by anum)
        (by anum))]
    exact hd.top
  · by_cases hjk : j = k
    · subst hjk
      simp only [setFl, ↓reduceIte]
      have hc := hd.chains j hj
      rw [hfl] at hc
      obtain ⟨-, hc⟩ := hc
      cases t with
      | nil => simp only [Chain] at hc ⊢; rw [hcell]; exact hc
      | cons q qs =>
        obtain ⟨hq, hqs⟩ := hc
        refine ⟨by rw [hcell]; exact hq, ?_⟩
        have hq' : q ∈ st.fl j := by rw [hfl]; simp
        refine chain_congr hqs (by have := free_word_lt hg hj hq' 0 (by omega); anum)
          (fun t ht => hagree _ (priv_free hg hj hq' ht) (hblkW q (by simp [hq']) t ht))
          (fun p hp => ⟨(by have := free_word_lt hg hj (p := p) (by rw [hfl]; simp [hp]) 0 (by omega); anum),
            fun t ht => hagree _ (priv_free hg hj (by rw [hfl]; simp [hp]) ht)
              (hblkW p (by rw [hfl]; simp [hp]) t ht)⟩)
    · simp only [setFl, if_neg hjk]
      refine chain_keep hd hg hagree hj (fun t ht => hcellW (by anum)
        (by omega)) (fun p hp t ht => hblkW p ?_ t ht)
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hp⟩)
  · have hperm := pop_perm hk hfl
    have hall : (blocks L st).Perm ((h, classBytes k) :: blocks L (setFl st k t)) := by
      unfold blocks; exact hperm.append_right _
    have hd' := (hall.pairwise_iff ndisj_symm).mp hg.disj
    obtain ⟨hhd, hrest⟩ := List.pairwise_cons.mp hd'
    have hlb : liveBlocks (L ++ [(BitVec.ofNat 64 h, n)]) = liveBlocks L ++ [(h, cap n)] := by
      simp [liveBlocks, ofNat_toNat_lt hhlt]
    have hnew : blocks (L ++ [(BitVec.ofNat 64 h, n)]) (setFl st k t) =
        blocks L (setFl st k t) ++ [(h, cap n)] := by
      unfold blocks; rw [hlb, List.append_assoc]
    refine ⟨hg.pos_lo, hg.pos_hi, fun b hb => ?_, fun b hb => ?_, ?_⟩
    · rcases List.mem_append.mp hb with hb | hb
      · exact hg.live_pos b hb
      · simp at hb; subst hb; exact hn
    · rw [hnew] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hg.inside b ((hall.mem_iff).mpr (List.mem_cons_of_mem _ hb))
      · simp at hb; subst hb; simp only [setFl]; omega
    · rw [hnew, List.pairwise_append]
      refine ⟨hrest, List.pairwise_singleton _ _, fun b hb c hc => ?_⟩
      simp at hc; subst hc
      have := hhd b hb
      simp only [NDisj] at this ⊢; omega

theorem bump_ok {L : List (Word × Nat)} {st : St} {m m' : Machine} (hd : Decode m st)
    (hg : Good L st) {L' : List (Word × Nat)} {pos' : Nat} (hlo : st.pos ≤ pos')
    (hhi : pos' ≤ Layout.ramHi)
    (hL : L' = L ∨ ∃ p n, L' = L ++ [(BitVec.ofNat 64 p, n)] ∧ 0 < n ∧ st.pos ≤ p ∧
      p + cap n ≤ pos' ∧ p + cap n ≤ heapTop)
    (hpos : rd m' posAddr = some (BitVec.ofNat 64 pos'))
    (hagree : ∀ a, Priv L a → ¬ InRange (BitVec.ofNat 64 posAddr) 8 a → m'.mem a = m.mem a)
    (hpres : ∀ a, Arena a → (m.mem a).isSome → (m'.mem a).isSome) :
    Heap L' m' := by
  have hW : ∀ {x}, x < heapTop → (posAddr ≤ x → x < posAddr + 8 → False) →
      ¬ InRange (BitVec.ofNat 64 posAddr) 8 (BitVec.ofNat 64 x) := fun hx hne hr => by
    rw [inRange_ofNat (by anum) (by anum)] at hr
    exact hne hr.1 hr.2
  have hblk : st.fl = ({ st with pos := pos' } : St).fl := rfl
  refine ⟨{ st with pos := pos' }, ⟨fun a ha => hpres a ha (hd.present a ha), hpos, ?_,
    fun j hj => ?_⟩, ?_⟩
  · rw [rd_congr (by anum) fun t ht => hagree _
      (priv_cell hg (by anum)) (hW (by anum)
        (by anum))]
    exact hd.top
  · exact chain_keep hd hg hagree hj (fun t ht => hW (by anum)
      (by anum)) (fun p hp t ht => hW (free_word_lt hg hj hp t ht)
        (by have := (hg.free_in hj hp).1; anum))
  · have hfb : freeBlocks { st with pos := pos' } = freeBlocks st := rfl
    rcases hL with rfl | ⟨p, n, rfl, hn, hp1, hp2, hp3⟩
    · refine ⟨by have := hg.pos_lo; simp only; omega, hhi, hg.live_pos, fun b hb => ?_, hg.disj⟩
      have := hg.inside b hb; simp only; omega
    · have hplt : p < 2 ^ 64 := by anum
      have hnew : blocks (L ++ [(BitVec.ofNat 64 p, n)]) { st with pos := pos' } =
          blocks L st ++ [(p, cap n)] := by
        simp [blocks, hfb, liveBlocks, ofNat_toNat_lt hplt]
      refine ⟨by have := hg.pos_lo; simp only; omega, hhi, fun b hb => ?_, fun b hb => ?_, ?_⟩
      · rcases List.mem_append.mp hb with hb | hb
        · exact hg.live_pos b hb
        · simp at hb; subst hb; exact hn
      · rw [hnew] at hb
        rcases List.mem_append.mp hb with hb | hb
        · have := hg.inside b hb; simp only; omega
        · simp at hb; subst hb; have := hg.pos_lo; simp only; omega
      · rw [hnew, List.pairwise_append]
        refine ⟨hg.disj, List.pairwise_singleton _ _, fun b hb c hc => ?_⟩
        simp at hc; subst hc
        have := hg.inside b hb
        simp only [NDisj]; omega

theorem push_perm {st : St} {k p : Nat} (hk : k < 22) :
    (freeBlocks (setFl st k (p :: st.fl k))).Perm ((p, classBytes k) :: freeBlocks st) :=
  flatMap_update_perm _ _ _ k (by simp [setFl]) (fun j hj => by simp [setFl, hj]) 22 hk

theorem push_ok {L : List (Word × Nat)} {st : St} {m m' : Machine} (hd : Decode m st)
    (hg : Good L st) {p : Word} {n k : Nat} (hb : (p, n) ∈ L) (hk : k < 22)
    (hcap : classBytes k = cap n)
    (hcell : rd m' (flBase + 8 * k) = some p)
    (hnext : rd m' p.toNat = rd m (flBase + 8 * k))
    (hagree : ∀ a, Priv L a → ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 a → m'.mem a = m.mem a)
    (hpres : ∀ a, Arena a → (m.mem a).isSome → (m'.mem a).isSome) :
    Heap (L.erase (p, n)) m' := by
  have hin := hg.live_in hb
  simp only at hin
  have hplt : p.toNat < 2 ^ 64 := p.isLt
  have hcellW : ∀ {x}, x < heapLo → (flBase + 8 * k ≤ x → x < flBase + 8 * k + 8 → False) →
      ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 (BitVec.ofNat 64 x) := fun hx hne hr => by
    rw [inRange_ofNat (by anum) (by anum)] at hr
    exact hne hr.1 hr.2
  have hW : ∀ {q t j}, j < 22 → q ∈ st.fl j → t < 8 →
      ¬ InRange (BitVec.ofNat 64 (flBase + 8 * k)) 8 (BitVec.ofNat 64 (q + t)) := by
    intro q t j hj hq ht hr
    have h1 := (hg.free_in hj hq).1; have h2 := free_word_lt hg hj hq t ht
    rw [inRange_ofNat (by anum) (by anum)] at hr
    unfold flBase heapLo at *; omega
  -- the freed block's first word is not any other block's
  have hpw : ∀ j < 22, ∀ q ∈ st.fl j, ∀ t < 8, ∀ u < 8, q + t ≠ p.toNat + u := by
    intro j hj q hq t ht u hu he
    have := hg.free_live hj hq hb
    have := eight_le_classBytes j; have := (hg.free_in hj hq)
    have h8 : 8 ≤ cap n := by rw [← hcap]; exact eight_le_classBytes k
    simp only [NDisj] at *; omega
  have hcellp : ∀ t < 8, ∀ u < 8, ¬ (BitVec.ofNat 64 (p.toNat + u) = BitVec.ofNat 64 (flBase + 8 * k + t)) := by
    intro t ht u hu he
    have := congrArg BitVec.toNat he
    rw [ofNat_toNat_lt (by anum), ofNat_toNat_lt (by anum)] at this
    unfold flBase heapLo at *; omega
  refine ⟨setFl st k (p.toNat :: st.fl k), ⟨fun a ha => hpres a ha (hd.present a ha), ?_, ?_,
    fun j hj => ?_⟩, ?_⟩
  · rw [rd_congr (by anum) fun t ht => hagree _
      (priv_cell hg (by anum)) (hcellW (by anum)
        (by anum))]
    exact hd.pos
  · rw [rd_congr (by anum) fun t ht => hagree _
      (priv_cell hg (by anum)) (hcellW (by anum)
        (by anum))]
    exact hd.top
  · by_cases hjk : j = k
    · subst hjk
      simp only [setFl, ↓reduceIte]
      refine ⟨by rw [hcell, BitVec.ofNat_toNat, BitVec.setWidth_eq], ?_⟩
      have hc := hd.chains j hj
      -- the old chain, read from the freed block's first word
      cases hfl : st.fl j with
      | nil => rw [hfl] at hc; simp only [Chain] at hc ⊢; rw [hnext]; exact hc
      | cons q qs =>
        rw [hfl] at hc
        obtain ⟨hq, hqs⟩ := hc
        have hq' : q ∈ st.fl j := by rw [hfl]; simp
        refine ⟨by rw [hnext]; exact hq, chain_congr hqs ?_ (fun t ht => ?_) (fun r hr => ?_)⟩
        · have := free_word_lt hg hj hq' 0 (by omega); anum
        · refine hagree _ (priv_free hg hj hq' ht) (hW hj hq' ht)
        · have hr' : r ∈ st.fl j := by rw [hfl]; simp [hr]
          exact ⟨by have := free_word_lt hg hj hr' 0 (by omega); anum,
            fun t ht => hagree _ (priv_free hg hj hr' ht) (hW hj hr' ht)⟩
    · simp only [setFl, if_neg hjk]
      exact chain_keep hd hg hagree hj (fun t ht => hcellW (by anum)
        (by omega)) (fun q hq t ht => hW hj hq ht)
  · have hlive : (liveBlocks L).Perm ((p.toNat, cap n) :: liveBlocks (L.erase (p, n))) :=
      (List.perm_cons_erase hb).map _
    have hall : (blocks (L.erase (p, n)) (setFl st k (p.toNat :: st.fl k))).Perm (blocks L st) := by
      unfold blocks
      refine ((push_perm hk).append_right _).trans ?_
      rw [hcap]
      exact (List.perm_middle.trans (List.Perm.refl _)).symm.trans
        ((List.Perm.refl _).append hlive.symm) |>.symm.symm
    refine ⟨hg.pos_lo, hg.pos_hi, fun b hb' => hg.live_pos b (List.mem_of_mem_erase hb'),
      fun b hb' => hg.inside b (hall.mem_iff.mp hb'), (hall.pairwise_iff ndisj_symm).mpr hg.disj⟩

/-! ## Start-up state -/

/-- The allocator's state before its first call: every head is null, `HEAP_POS` is
`__zesu_heap_bottom`, `HEAP_TOP` is `__zesu_heap_top`, the arena is present. -/
structure Init (m : Machine) : Prop where
  present : ∀ a, Arena a → (m.mem a).isSome
  heads : ∀ k < 22, rd m (flBase + 8 * k) = some 0
  pos : rd m posAddr = some (BitVec.ofNat 64 heapLo)
  top : rd m topAddr = some (BitVec.ofNat 64 heapTop)

theorem init_heap {m : Machine} (h : Init m) : Heap [] m :=
  ⟨⟨heapLo, fun _ => []⟩, ⟨h.present, h.pos, h.top, fun k hk => h.heads k hk⟩,
    ⟨Nat.le_refl _, by anum, by simp, by simp [blocks, freeBlocks, liveBlocks],
      by rw [show blocks [] ⟨heapLo, fun _ => []⟩ = [] from rfl]; exact List.Pairwise.nil⟩⟩

end Alloc
end ZesuExec.Fn
