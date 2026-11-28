import ZesuExec.Fn.Sha256.Model
import ZesuExec.Sym.Env

/-!
# `zkvm_sha256`: byte-level facts about the SHA-256 state and `rev8`
-/

namespace ZesuExec.Sha256
open ZesuExec ZesuExec.Sym

theorem cat4 (x : BitVec 32) :
    (x.extractLsb' 24 8 ++ x.extractLsb' 16 8) ++ (x.extractLsb' 8 8 ++ x.extractLsb' 0 8) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => simp
  | _ + 32, h => exact absurd h (by omega)

/-- The eight little-endian words of the state bytes are the state. -/
theorem leWords_leBytes : ∀ H : List W32, H.length = 8 → (List.range 8).map (leWord (leBytes H)) = H
  | [a, b, c, d, e, f, g, h], _ => by
    simp [leWord, leBytes, List.range_succ]
    exact ⟨cat4 a, cat4 b, cat4 c, cat4 d, cat4 e, cat4 f, cat4 g, cat4 h⟩

theorem compress_length (H : List W32) (blk : List Byte) : (sha256Compress H blk).length = 8 := by
  simp [sha256Compress]

theorem leBytes_length {H : List W32} (h : H.length = 8) : (leBytes H).length = 32 := by
  simp [leBytes, List.length_flatMap, List.map_const', h]

theorem foldBlocks_length (msg : List Byte) : ∀ k, (foldBlocks msg k).length = 8
  | 0 => rfl
  | k + 1 => by
    simp only [foldBlocks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact compress_length _ _

theorem foldBlocks_succ (msg : List Byte) (k : Nat) :
    foldBlocks msg (k + 1) = sha256Compress (foldBlocks msg k) ((msg.drop (64 * k)).take 64) := by
  simp only [foldBlocks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end ZesuExec.Sha256

namespace ZesuExec.Machine
open ZesuExec.Sym

/-- `rev8` then a right shift by `8 k`: the low byte is byte `7 - k`. -/
theorem byteOf_rev8_shift (x : Word) (k : Nat) (hk : k < 8) :
    byteOf (rev8 x >>> (8 * k)) 0 = byteOf x (7 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [byteOf, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, rev8,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  match k, hk, i, hi with
  | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _ | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _ | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _ | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _ | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _ | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _ | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 5, _ | 5, _, 6, _ | 5, _, 7, _ | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 6, _ | 6, _, 7, _ | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ | 7, _, 7, _ => simp
