import ZesuExec.Fn.Common

/-!
# Emulator snapshots (contract rule (b) for functions Unicorn cannot run)

Functions that reach ZisK CSR services (and `rev8`, which the pinned ZisK lacks; the harness
stubs it) cannot be snapshotted under Unicorn (`tools/snap.py`). Their snapshots come from
`tools/svc_test.py --snap-out`: the real function run by `ziskemu`, schema `zesu-emusnap/1`,
rendered as Lean data by `tools/snap_emu.py`. An `ESnap` holds the registers `x1 … x31` at entry
and as dumped after the return, the return address the run reached, and the dumped windows, each
`(base, bytes at entry, bytes after the return)`. The per-function checks (`*Ok`) evaluate the
clauses of `Post` the windows observe; memory outside the windows is not observed.
-/

namespace ZesuExec.Fn.Emu

structure ESnap where
  regs0 : List Nat
  regs1 : List Nat
  pc1 : Nat
  wins : List (Nat × List Nat × List Nat)

def ESnap.r0 (s : ESnap) (i : Nat) : Nat := s.regs0.getD (i - 1) 0
def ESnap.r1 (s : ESnap) (i : Nat) : Nat := s.regs1.getD (i - 1) 0


def hexDigit (c : Char) : Nat :=
  if c.toNat ≤ '9'.toNat then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- Lowercase hex, two digits per byte. -/
def hexBytes : List Char → List Nat
  | h :: l :: rest => (16 * hexDigit h + hexDigit l) :: hexBytes rest
  | _ => []

/-- A snapshot whose windows are given as hex strings (`tools/snap_emu.py`). -/
def ESnap.ofHex (regs0 regs1 : List Nat) (pc1 : Nat) (wins : List (Nat × String × String)) :
    ESnap :=
  ⟨regs0, regs1, pc1, wins.map fun (b, h0, h1) => (b, hexBytes h0.toList, hexBytes h1.toList)⟩
def wmod (x : Nat) : Nat := x % 2 ^ 64

/-- The `n` bytes at `a` from one window, at entry (`after = false`) or after the return. -/
def ESnap.read (s : ESnap) (after : Bool) (a n : Nat) : Option (List Nat) :=
  match s.wins.find? fun w => w.1 ≤ a && a + n ≤ w.1 + w.2.1.length with
  | some (b, bs0, bs1) => some (((if after then bs1 else bs0).drop (a - b)).take n)
  | none => if n = 0 then some [] else none

/-- `Returns`: `pc` is `ra` with bit 0 clear, `sp` and `s0`–`s11` restored. -/
def returnsB (s : ESnap) : Bool :=
  s.pc1 == s.r0 1 - s.r0 1 % 2 &&
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].all fun i => s.r1 i == s.r0 i

/-- Every observed byte outside `W` is unchanged, and the windows are well formed. -/
def keepsB (s : ESnap) (W : Nat → Bool) : Bool :=
  s.wins.all fun (b, bs0, bs1) =>
    bs0.length == bs1.length &&
      (List.range bs0.length).all fun i => W (b + i) || bs0.getD i 0 == bs1.getD i 0

/-- The bytes `bs` at `a` after the return. -/
def bytesAtB (s : ESnap) (a : Nat) (bs : List Nat) : Bool := s.read true a bs.length == some bs

def inR (lo n a : Nat) : Bool := lo ≤ a && a < lo + n

def toBytes (l : List Nat) : List Byte := l.map (BitVec.ofNat 8)
def ofBytes (l : List Byte) : List Nat := l.map (·.toNat)

end ZesuExec.Fn.Emu
