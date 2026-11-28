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
  decide +kernel

end ZesuExec.Fn.SszRoot
