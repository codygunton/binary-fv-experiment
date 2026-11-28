import ZesuExec.Service.Sha256f

/-!
# `zkvm_sha256`: the SHA-256 model in the shape the code computes it

The code compresses the `⌊n / 64⌋` whole blocks of the input in place, then one buffer holding
the remaining `r = n mod 64` bytes, `0x80` and zeros, with the bit length big-endian in its last
8 bytes when `r ≤ 55`, else followed by a buffer of 56 zeros and the bit length. `hash_eq` states
that this is `Sha256.hash` (`Service/Sha256f.lean`, FIPS 180-4 padding).
-/

namespace ZesuExec.Sha256

/-- The bit length `8 n`, big-endian. -/
def lenBytes (n : Nat) : List Byte :=
  (List.range 8).reverse.map fun j => BitVec.ofNat 8 ((8 * n) / 256 ^ j)

/-- Compression of the first `k` whole blocks of `msg` into `H0`. -/
def foldBlocks (msg : List Byte) (k : Nat) : List W32 :=
  (List.range k).foldl (fun H i => sha256Compress H ((msg.drop (64 * i)).take 64)) H0

/-- The tail buffer after the `0x80` marker: the remaining bytes, `0x80`, zeros to 64 bytes. -/
def tailBuf (msg : List Byte) : List Byte :=
  let r := msg.length % 64
  msg.drop (64 * (msg.length / 64)) ++ [0x80] ++ List.replicate (63 - r) 0

/-- The final state from the state after the whole blocks. -/
def finish (msg : List Byte) (H : List W32) : List W32 :=
  if msg.length % 64 ≤ 55 then
    sha256Compress H ((tailBuf msg).take 56 ++ lenBytes msg.length)
  else
    sha256Compress (sha256Compress H (tailBuf msg)) (List.replicate 56 0 ++ lenBytes msg.length)

/-- Big-endian bytes of the state words. -/
def beBytes (H : List W32) : List Byte :=
  H.flatMap fun x => (List.range 4).reverse.map fun j => x.extractLsb' (8 * j) 8

theorem foldl_range_congr {α : Type} {f g : α → Nat → α} (k : Nat)
    (h : ∀ H i, i < k → f H i = g H i) (H : α) :
    (List.range k).foldl f H = (List.range k).foldl g H := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun H i hi => h H i (by omega))]
    simp [h _ k (by omega)]

theorem foldl_range_add {α : Type} (f : α → Nat → α) (k t : Nat) (H : α) :
    (List.range (k + t)).foldl f H =
      (List.range t).foldl (fun H i => f H (k + i)) ((List.range k).foldl f H) := by
  rw [List.range_add, List.foldl_append, List.foldl_map]

theorem block_left (q s : List Byte) (i : Nat) (h : 64 * i + 64 ≤ q.length) :
    ((q ++ s).drop (64 * i)).take 64 = (q.drop (64 * i)).take 64 := by
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp; omega)]

theorem block_right (q s : List Byte) (k i : Nat) (h : q.length = 64 * k) :
    ((q ++ s).drop (64 * (k + i))).take 64 = (s.drop (64 * i)).take 64 := by
  rw [show 64 * (k + i) = q.length + 64 * i by rw [h, Nat.mul_add], List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

theorem hash_eq (msg : List Byte) :
    hash msg = beBytes (finish msg (foldBlocks msg (msg.length / 64))) := by
  obtain ⟨n, hn⟩ : ∃ n, msg.length = n := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, n / 64 = k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, n % 64 = r := ⟨_, rfl⟩
  have hdm : 64 * k + r = n := by rw [← hk, ← hr]; exact Nat.div_add_mod n 64
  have hr64 : r < 64 := by rw [← hr]; exact Nat.mod_lt _ (by decide)
  obtain ⟨q, hq⟩ : ∃ q, q = msg.take (64 * k) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = msg.drop (64 * k) := ⟨_, rfl⟩
  have hql : q.length = 64 * k := by simp [hq, hn]; omega
  have hDl : D.length = r := by simp [hD, hn]; omega
  have hmsg : msg = q ++ D := by rw [hq, hD]; exact (List.take_append_drop _ _).symm
  have hfold : foldBlocks msg k = (List.range k).foldl
      (fun H i => sha256Compress H ((q.drop (64 * i)).take 64)) H0 := by
    unfold foldBlocks
    apply foldl_range_congr
    intro H i hi
    rw [hmsg, block_left q D i (by omega)]
  have htail : tailBuf msg = D ++ [0x80] ++ List.replicate (63 - r) 0 := by
    simp only [tailBuf, hn, hk, hr, hD]
  have hpad : pad msg = q ++ (D ++ [0x80] ++ List.replicate ((119 - r) % 64) 0 ++ lenBytes n) := by
    show msg ++ [0x80] ++ List.replicate ((119 - msg.length % 64) % 64) 0 ++
      (List.range 8).reverse.map (fun j => BitVec.ofNat 8 ((8 * msg.length) / 256 ^ j)) = _
    rw [hn, hr]
    conv => lhs; rw [hmsg]
    simp only [List.append_assoc]; rfl
  have hq' : ∀ s : List Byte, (List.range k).foldl
      (fun H i => sha256Compress H (((q ++ s).drop (64 * i)).take 64)) H0 =
      (List.range k).foldl (fun H i => sha256Compress H ((q.drop (64 * i)).take 64)) H0 :=
    fun s => foldl_range_congr k (fun H i hi => by rw [block_left q s i (by omega)]) H0
  show beBytes ((List.range ((pad msg).length / 64)).foldl
      (fun H i => sha256Compress H (((pad msg).drop (64 * i)).take 64)) H0) = _
  rw [hpad, hn, hk, hfold]
  apply congrArg beBytes
  unfold finish
  rw [hn, hr, htail]
  split
  · rename_i hle
    have h1 : (119 - r) % 64 = 55 - r := by omega
    rw [h1]
    have hlen : (q ++ (D ++ [0x80] ++ List.replicate (55 - r) 0 ++ lenBytes n)).length / 64 =
        k + 1 := by
      simp [hql, hDl, lenBytes]; omega
    rw [hlen, foldl_range_add, hq']
    simp only [List.range_one, List.foldl_cons, List.foldl_nil]
    rw [block_right q _ k 0 hql]
    have hb : List.take 56 (D ++ [128] ++ List.replicate (63 - r) 0) =
        D ++ [128] ++ List.replicate (55 - r) 0 := by
      rw [show 63 - r = (55 - r) + 8 by omega, ← List.replicate_append_replicate, ← List.append_assoc,
        List.take_left' (by simp [hDl]; omega)]
    rw [hb, Nat.mul_zero, List.drop_zero,
      List.take_of_length_le (by simp [hDl, lenBytes]; omega)]
  · rename_i hgt
    have h1 : (119 - r) % 64 = 119 - r := by omega
    have hs : D ++ [128] ++ List.replicate (119 - r) 0 ++ lenBytes n =
        (D ++ [128] ++ List.replicate (63 - r) 0) ++ (List.replicate 56 0 ++ lenBytes n) := by
      rw [show 119 - r = (63 - r) + 56 by omega, ← List.replicate_append_replicate]
      simp only [List.append_assoc]
    have hA : (D ++ [128] ++ List.replicate (63 - r) 0).length = 64 := by simp [hDl]; omega
    have hB : (List.replicate 56 (0 : Byte) ++ lenBytes n).length = 64 := by simp [lenBytes]
    rw [h1, hs]
    have hlen : (q ++ ((D ++ [128] ++ List.replicate (63 - r) 0) ++
        (List.replicate 56 0 ++ lenBytes n))).length / 64 = k + 2 := by
      simp only [List.length_append, hql, hA, hB]; omega
    rw [hlen, foldl_range_add, hq']
    simp only [show List.range 2 = [0, 1] from rfl, List.foldl_cons, List.foldl_nil]
    rw [block_right q _ k 0 hql, block_right q _ k 1 hql, Nat.mul_zero, List.drop_zero,
      Nat.mul_one, List.take_left' hA, List.drop_left' hA, List.take_of_length_le (by omega)]
end ZesuExec.Sha256
