import ZesuExec.Service.Sha256f
import ZesuExec.Image.Gen

/-!
# SSZ Merkle roots of `ssz_output.zig`: Lean model (meaning level `model`)

From `src/stateless/stateless/ssz_output.zig` lines 41-166 of the zesu source:

* `ZERO_HASHES[0] = 0^32`, `ZERO_HASHES[i+1] = sha256(ZERO_HASHES[i] ‖ ZERO_HASHES[i])` (`zeroHash`);
* `sparseRoot(leaves, depth)`: the Merkle root of `2^depth` leaves, `leaves` followed by zero chunks;
  at depth 0 the first leaf or the zero chunk; else `sha2` of the left half's root and of the right
  half's root, the right half being `ZERO_HASHES[depth-1]` when no leaf reaches it;
* `progressiveRootAt(nodes, depth)`: `ZERO_HASHES[0]` for no nodes; else `sha2` of the sparse root
  of the first `min(2^depth, len)` nodes at `depth` and of `progressiveRootAt` of the rest at
  `depth + 2`.

Chunks are `List Byte` (32 bytes each in the machine), `sha2 a b = Sha256.hash (a ++ b)`.
`zeroTable_eq` proves the 26 rodata segments `0x80113728 + 32 i` of the image are `zeroHash i`.
-/

namespace ZesuExec.Fn.SszRoot
open ZesuExec

def zeroChunk : List Byte := List.replicate 32 0

def sha2 (a b : List Byte) : List Byte := Sha256.hash (a ++ b)

def zeroHash : Nat → List Byte
  | 0 => zeroChunk
  | k + 1 => let z := zeroHash k; sha2 z z

def sparseRoot (ls : List (List Byte)) : Nat → List Byte
  | 0 => ls.headD zeroChunk
  | d + 1 =>
    sha2 (sparseRoot (ls.take (2 ^ d)) d)
      (if ls.length ≤ 2 ^ d then zeroHash d else sparseRoot (ls.drop (2 ^ d)) d)

def progressiveRootAt (ls : List (List Byte)) (d : Nat) : List Byte :=
  if ls = [] then zeroHash 0
  else
    sha2 (sparseRoot (ls.take (2 ^ d)) d) (progressiveRootAt (ls.drop (2 ^ d)) (d + 2))
termination_by ls.length
decreasing_by
  have : 0 < 2 ^ d := Nat.two_pow_pos d
  have : ls.length ≠ 0 := by simpa using ‹¬ls = []›
  simp only [List.length_drop]; omega

/-- `progressiveRootAt` of `n` nodes at `d` asks only `sparseRoot` depths at most 26 (the size
of `ZERO_HASHES`): `n = 0`, or `d ≤ 26` and the rest fits at `d + 2`. -/
def progFits (n d : Nat) : Bool :=
  if n = 0 then true else if d ≤ 26 then progFits (n - 2 ^ d) (d + 2) else false
termination_by n
decreasing_by
  have : 0 < 2 ^ d := Nat.two_pow_pos d
  omega

/-! ## The rodata table `ZERO_HASHES` -/

/-- Byte `j` of entry `i` of `ZERO_HASHES` in the image (`0x80113728 + 32 i + j`). -/
def tableEntry (i : Nat) : List Byte :=
  (List.range 32).map fun j =>
    BitVec.ofNat 8 ((zesuImage.rodataByte? (0x80113728 + 32 * i + j)).getD 0)

theorem tableEntry_zero : tableEntry 0 = zeroChunk := by decide +kernel

theorem tableEntry_succ : ∀ i < 25, tableEntry (i + 1) = sha2 (tableEntry i) (tableEntry i) := by
  decide +kernel

theorem tableEntry_present : ∀ i < 26, ∀ j < 32,
    (zesuImage.rodataByte? (0x80113728 + 32 * i + j)).isSome := by
  decide +kernel

theorem zeroHash_eq_table : ∀ i, i < 26 → zeroHash i = tableEntry i
  | 0, _ => tableEntry_zero.symm
  | i + 1, h => by
    rw [tableEntry_succ i (by omega), ← zeroHash_eq_table i (by omega)]; rfl

end ZesuExec.Fn.SszRoot
