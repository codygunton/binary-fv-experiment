import ZesuExec.Fn.Memset.Spec
import ZesuExec.Fn.Memset.SnapData

/-!
# `memset`: `Pre` and `Post` on emulator snapshots (contract rule (b))

`memsetOk` on an `ESnap` (`Fn/EmuSnap.lean`, the real function run by `ziskemu`): `RetAligned`;
`pc` is the return address, every register but `t0` and `a1` unchanged, and every observed byte
is `fillMem a0 a2 (a1 & 0xff)` of the entry bytes.
-/

namespace ZesuExec.Fn.Memset
open ZesuExec.Fn.Emu

def memsetOk (s : ESnap) : Bool :=
  let d := s.r0 10; let c := s.r0 11 % 256; let n := s.r0 12
  (s.r0 1 - s.r0 1 % 2) % 4 == 0 && s.pc1 == s.r0 1 - s.r0 1 % 2 &&
  (List.range 31).all (fun i => i + 1 == 5 || i + 1 == 11 || s.r1 (i + 1) == s.r0 (i + 1)) &&
  s.wins.all fun (b, bs0, bs1) =>
    allIdx (fun i x y => y == if inR d n i then c else x) b bs0 bs1

/-- Contract rule (b): `Pre` and `Post` hold on the emulator snapshots
`test/snapshots/emu/fn-memset` (`tools/svc_test.py --snap-out`), evaluated by `decide`. -/
theorem post_snapshot : snaps.all memsetOk = true := by decide +kernel

end ZesuExec.Fn.Memset
