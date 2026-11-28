import ZesuExec.Fn.SszRoot.Spec
import ZesuExec.Fn.SszRoot.SparseSnapData
import ZesuExec.Fn.SszRoot.ProgSnapData

/-!
# `sparseRoot`, `progressiveRootAt`: `Pre` and `Post` on emulator snapshots (contract rule (b))

`rootOk` on an `ESnap` (`Fn/EmuSnap.lean`, the real function run by `ziskemu`, `zkvm_sha256`'s
`rev8` sites through harness stubs): `RetAligned`, `sp` 16-aligned, the `32 a2` chunk bytes
present, the model's depth bound; `Returns`, the 32 bytes at `a0` are the model's root of the
chunks, and every observed byte outside the stack the contract allows, the result, the bump
words and the staging word unchanged (`PostN`).
-/

namespace ZesuExec.Fn.SszRoot
open ZesuExec.Fn.Emu

def rootOk (fits : Nat → Nat → Bool) (need : Nat → Nat → Nat)
    (root : List (List Byte) → Nat → List Byte) (s : ESnap) : Bool :=
  let sp := s.r0 2; let out := s.r0 10; let p := s.r0 11; let n := s.r0 12; let d := s.r0 13
  (s.r0 1 - s.r0 1 % 2) % 4 == 0 && sp % 16 == 0 && fits n d &&
  match s.read false p (32 * n) with
  | none => false
  | some cs =>
    let chunks := (List.range n).map fun i => toBytes ((cs.drop (32 * i)).take 32)
    returnsB s && bytesAtB s out (ofBytes (root chunks d)) &&
    keepsB s fun x =>
      inR (sp - need n d) (need n d) x || inR out 32 x || inR Sha256.bump 16 x ||
        inR Layout.extraParams 8 x

/-! The kernel cannot evaluate `progressiveRootAt`, `progFits` and `progStack` (well-founded
recursion) on the snapshots; the checks run their fuel copies, proved equal below. -/

def progRootF : Nat → List (List Byte) → Nat → List Byte
  | 0, _, _ => []
  | k + 1, ls, d =>
    if ls = [] then zeroHash 0
    else sha2 (sparseRoot (ls.take (2 ^ d)) d) (progRootF k (ls.drop (2 ^ d)) (d + 2))

def progFitsF : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | k + 1, n, d =>
    if n = 0 then true else if d ≤ 26 then progFitsF k (n - 2 ^ d) (d + 2) else false

def progStackF : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, n, d =>
    if n = 0 then 0xa0 else 0xa0 + max (sparseStack d) (progStackF k (n - 2 ^ d) (d + 2))

theorem progRootF_eq : ∀ k (ls : List (List Byte)) d, ls.length < k →
    progRootF k ls d = progressiveRootAt ls d
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, ls, d, h => by
    rw [progRootF, progressiveRootAt]
    split
    · rfl
    · rw [progRootF_eq k]
      have : ls.length ≠ 0 := by simpa using ‹¬ls = []›
      have := Nat.two_pow_pos d
      simp only [List.length_drop]; omega

theorem progFitsF_eq : ∀ k n d, n < k → progFitsF k n d = progFits n d
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, d, h => by
    rw [progFitsF, progFits]
    split
    · rfl
    · split
      · have := Nat.two_pow_pos d
        exact progFitsF_eq k _ _ (by omega)
      · rfl

theorem progStackF_eq : ∀ k n d, n < k → progStackF k n d = progStack n d
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, d, h => by
    rw [progStackF, progStack]
    split
    · rfl
    · have := Nat.two_pow_pos d
      rw [progStackF_eq k _ _ (by omega)]

/-- Contract rule (b): `SparsePre` and `SparsePost` hold on the emulator snapshots
`test/snapshots/emu/fn-sparseRoot` (`tools/svc_test.py --snap-out`), evaluated by `decide`. -/
theorem Sparse.post_snapshot :
    Sparse.snaps.all (rootOk (fun _ d => decide (d ≤ 26)) (fun _ d => sparseStack d) sparseRoot) =
      true := by
  decide +kernel

/-- Contract rule (b): `ProgPre` and `ProgPost` hold on the emulator snapshots
`test/snapshots/emu/fn-progressiveRootAt` (`tools/svc_test.py --snap-out`), evaluated by
`decide`. -/
theorem Prog.post_snapshot :
    Prog.snaps.all (rootOk progFits progStack progressiveRootAt) = true := by
  have hf : progFits = fun n d => progFitsF (n + 1) n d :=
    funext fun n => funext fun d => (progFitsF_eq _ _ _ (Nat.lt_succ_self n)).symm
  have hs : progStack = fun n d => progStackF (n + 1) n d :=
    funext fun n => funext fun d => (progStackF_eq _ _ _ (Nat.lt_succ_self n)).symm
  have hr : progressiveRootAt = fun ls d => progRootF (ls.length + 1) ls d :=
    funext fun ls => funext fun d => (progRootF_eq _ _ _ (Nat.lt_succ_self _)).symm
  rw [hf, hs, hr]
  decide +kernel

end ZesuExec.Fn.SszRoot
