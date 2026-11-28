import ZesuExec.Fn.Sha256.Spec
import ZesuExec.Fn.Sha256.SnapData

/-!
# `zkvm_sha256`: `Pre` and `Post` on emulator snapshots (contract rule (b))

`shaOk` is the observable part of `Pre`/`Post` on an `ESnap` (`Fn/EmuSnap.lean`; the real
function run by `ziskemu`, `rev8` sites through harness stubs): `RetAligned`, `sp` 16-aligned,
the input bytes present; `Returns`, `a0 = 0`, the 32 bytes at `a2` are `Sha256.hash` of the input,
the bump words, and every observed byte outside the frame, `out`, the bump words and the staging
word unchanged.
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec.Fn.Emu

def shaOk (s : ESnap) : Bool :=
  let sp := s.r0 2; let a := s.r0 10; let n := s.r0 11; let out := s.r0 12
  (s.r0 1 - s.r0 1 % 2) % 4 == 0 && sp % 16 == 0 &&
  match s.read false a n with
  | none => false
  | some inp =>
    returnsB s && s.r1 10 == 0 &&
    bytesAtB s out (ofBytes (Sha256.hash (toBytes inp))) &&
    bytesAtB s bump (ofBytes bumpBytes) &&
    keepsB s fun x =>
      Emu.inR (sp - frameSize) frameSize x || Emu.inR out 32 x || Emu.inR bump 16 x ||
        Emu.inR Layout.extraParams 8 x

/-- Contract rule (b): `Pre` and `Post` hold on the emulator snapshots
`test/snapshots/emu/fn-sha256` (`tools/svc_test.py --snap-out`), evaluated by `decide`. -/
theorem post_snapshot : snaps.all shaOk = true := by decide +kernel

end ZesuExec.Fn.Sha256
