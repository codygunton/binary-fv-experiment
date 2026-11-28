import ZesuExec.Fn.Rotate.Spec

/-!
# `std.mem.rotate` copies: `Post` on Unicorn snapshots (contract rule (b))

A `Snap` holds what `tools/snap_post.py` reads from a `zesu-snap/1` snapshot of a copy: the
registers at entry and exit, the exit `pc`, the slice's bytes at entry and exit and the addresses
of every changed byte. `SnapOk c s` is `Post c` on these values: the return (`pc` is `ra` with bit
0 clear, callee-saved registers kept), only slice and frame bytes changed, and element `e` of the
slice holds the entry's element `(e + amount) % len`; plus `amount ≤ len` of `Pre`. Each copy's
`post_snapshot` evaluates it on its snapshots by `decide`.
-/

namespace ZesuExec.Fn.Rotate

structure Snap where
  /-- `x1 … x31` at entry -/
  regs0 : List Nat
  /-- `x1 … x31` at the return -/
  regs1 : List Nat
  pc1 : Nat
  /-- the slice at entry and at the return -/
  before : List Nat
  after : List Nat
  /-- every byte address whose value changed -/
  changed : List Nat

def Snap.r0 (s : Snap) (i : Nat) : Nat := s.regs0.getD (i - 1) 0
def Snap.r1 (s : Snap) (i : Nat) : Nat := s.regs1.getD (i - 1) 0

def SnapOk (c : Cfg) (s : Snap) : Bool :=
  let p := s.r0 10; let n := s.r0 11; let a := s.r0 12; let sp := s.r0 2
  decide (a ≤ n) && s.before.length == c.E * n && s.after.length == c.E * n &&
  s.pc1 == s.r0 1 - s.r0 1 % 2 &&
  [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27].all (fun i => s.r1 i == s.r0 i) &&
  s.changed.all (fun x => (decide (p ≤ x) && decide (x < p + c.E * n)) ||
    (decide (sp - c.fs ≤ x) && decide (x < sp))) &&
  (List.range n).all fun e => (List.range c.E).all fun o =>
    s.after.getD (c.E * e + o) 0 == s.before.getD (c.E * ((e + a) % n) + o) 0

end ZesuExec.Fn.Rotate
