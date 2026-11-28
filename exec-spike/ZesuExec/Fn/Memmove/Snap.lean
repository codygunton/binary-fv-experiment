import ZesuExec.Logic
import ZesuExec.Fn.Memmove.SnapData

/-!
# `memmove`: `MemcpyPre` and `MemcpyPost` on emulator snapshots (contract rule (b))

`memmoveOk` on an `ESnap` (`Fn/EmuSnap.lean`, the real function run by `ziskemu`): `ra & ~1`
4-aligned; `pc` is the return address, every register unchanged, and every observed byte is
`ziskMemcpyMem`'s: the count staged little-endian at `Layout.extraParams`, then `[a0, a0 + a2)`
copied from `[a1, a1 + a2)` of the staged memory (`a0 ≠ a1`, `a2 ≠ 0`).
-/

namespace ZesuExec.Fn.Memmove
open ZesuExec.Fn.Emu

def memmoveOk (s : ESnap) : Bool :=
  let d := s.r0 10; let src := s.r0 11; let n := s.r0 12; let st := Layout.extraParams
  let staged : Nat → Option Nat := fun x =>
    if inR st 8 x then some (n / 2 ^ (8 * (x - st)) % 256)
    else (s.read false x 1).bind List.head?
  (s.r0 1 - s.r0 1 % 2) % 4 == 0 && s.pc1 == s.r0 1 - s.r0 1 % 2 &&
  (List.range 31).all (fun i => s.r1 (i + 1) == s.r0 (i + 1)) &&
  s.wins.all fun (b, bs0, bs1) =>
    allIdx (fun i _ y => some y ==
      if n != 0 && d != src && inR d n i then staged (src + i - d) else staged i) b bs0 bs1

/-- Contract rule (b): `MemcpyPre` and `MemcpyPost` hold on the emulator snapshots
`test/snapshots/emu/fn-memmove` (`tools/svc_test.py --snap-out`), evaluated by `decide`. -/
theorem post_snapshot : snaps.all memmoveOk = true := by decide +kernel

end ZesuExec.Fn.Memmove
