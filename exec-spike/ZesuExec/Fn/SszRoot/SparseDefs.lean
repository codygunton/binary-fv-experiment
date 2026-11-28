import ZesuExec.Fn.SszRoot.Spec
import ZesuExec.Sym.Tactic

/-!
# `sparseRoot` in the recursive obligation framework: plan

Plan `plan hsha` (a `PlanR`, `σ` = the entry machine): cuts at the entry (`cE`), after the left
recursive call (`c70`, `0x80042c70`), after the right recursive call (`c94`), after `zkvm_sha256`
(`c54`, also reached by the depth-0 paths, so its state reads the 32 result bytes through a
region at `s2`: the frame or the zero chunk in rodata), and 26 cuts at `0x80042cc4` (`ccK k`,
`k < 26`), one per value `k` of `s4 = depth - 1`: the run from there loads `ZERO_HASHES[k]` at the
literal address `0x80113728 + 32 k` (the executor reads rodata only at literal addresses).

Each cut's state is an entry state over the machine at the cut (`entryState`/`entryEnv`): its
registers are variables except the pointers into its regions (and `s4 = k` at `ccK k`).
-/

namespace ZesuExec.Fn.SszRoot.Sparse
open ZesuExec ZesuExec.Machine ZesuExec.Fn ZesuExec.Sym

def pc70 : Nat := 0x80042c70
def pc94 : Nat := 0x80042c94
def pc54 : Nat := 0x80042d54
def pcC4 : Nat := 0x80042cc4

/-- The cut pcs of the plan, in the order of its cuts (26 cuts at `pcC4`). -/
def pcs : List Nat := [sparseEntry, pc70, pc94, pc54] ++ List.replicate 26 pcC4
def fuel : Nat := 100

def frR : Region := ⟨some 0x120, 1, true⟩
def lvR : Region := ⟨none, 1, false⟩
def svR : Region := ⟨some 0x38, 1, false⟩
def srcR : Region := ⟨some 32, 1, false⟩
def outW : Region := ⟨some 32, 1, true⟩

def ovE (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0x120) else if i = 11 then some (.ptr 1 0) else none
def ov94 (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 0x120)
  else if i = 18 then some (.ptr 0 0x68) else none
def ovC (k i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 8 then some (.ptr 0 0x120)
  else if i = 20 then some (.lit k) else none
def ov54 (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 (-0xe8)) else if i = 18 then some (.ptr 1 0)
  else if i = 9 then some (.ptr 2 0) else none

def SE : SState := entryState ovE [frR, lvR] []
def S70 : SState := entryState (fun _ => none) [] []
def S94 : SState := entryState ov94 [frR] []
def SC (k : Nat) : SState := entryState (ovC k) [frR] []
def S54 : SState := entryState ov54 [svR, srcR, outW] []

/-- Region bases and sizes at each cut, from the machine at the cut. -/
def regsE (m : Machine) : List (Word × Nat) :=
  [(m.reg 2 - BitVec.ofNat 64 0x120, 0x120), (m.reg 11, 32 * lenOf m)]
def regsF (m : Machine) : List (Word × Nat) := [(m.reg 2, 0x120)]
def regs54 (m : Machine) : List (Word × Nat) :=
  [(m.reg 2 + BitVec.ofNat 64 0xe8, 0x38), (m.reg 18, 32), (m.reg 9, 32)]

sym_run runE := run zesuImage pcs fuel sparseEntry SE
sym_run run70 := run zesuImage pcs fuel pc70 S70
sym_run run94 := run zesuImage pcs fuel pc94 S94
sym_run run54 := run zesuImage pcs fuel pc54 S54
sym_run runC0 := run zesuImage pcs fuel pcC4 (SC 0)
sym_run runC1 := run zesuImage pcs fuel pcC4 (SC 1)
sym_run runC2 := run zesuImage pcs fuel pcC4 (SC 2)
sym_run runC3 := run zesuImage pcs fuel pcC4 (SC 3)
sym_run runC4 := run zesuImage pcs fuel pcC4 (SC 4)
sym_run runC5 := run zesuImage pcs fuel pcC4 (SC 5)
sym_run runC6 := run zesuImage pcs fuel pcC4 (SC 6)
sym_run runC7 := run zesuImage pcs fuel pcC4 (SC 7)
sym_run runC8 := run zesuImage pcs fuel pcC4 (SC 8)
sym_run runC9 := run zesuImage pcs fuel pcC4 (SC 9)
sym_run runC10 := run zesuImage pcs fuel pcC4 (SC 10)
sym_run runC11 := run zesuImage pcs fuel pcC4 (SC 11)
sym_run runC12 := run zesuImage pcs fuel pcC4 (SC 12)
sym_run runC13 := run zesuImage pcs fuel pcC4 (SC 13)
sym_run runC14 := run zesuImage pcs fuel pcC4 (SC 14)
sym_run runC15 := run zesuImage pcs fuel pcC4 (SC 15)
sym_run runC16 := run zesuImage pcs fuel pcC4 (SC 16)
sym_run runC17 := run zesuImage pcs fuel pcC4 (SC 17)
sym_run runC18 := run zesuImage pcs fuel pcC4 (SC 18)
sym_run runC19 := run zesuImage pcs fuel pcC4 (SC 19)
sym_run runC20 := run zesuImage pcs fuel pcC4 (SC 20)
sym_run runC21 := run zesuImage pcs fuel pcC4 (SC 21)
sym_run runC22 := run zesuImage pcs fuel pcC4 (SC 22)
sym_run runC23 := run zesuImage pcs fuel pcC4 (SC 23)
sym_run runC24 := run zesuImage pcs fuel pcC4 (SC 24)
sym_run runC25 := run zesuImage pcs fuel pcC4 (SC 25)

/-- The leaves of `ccK k`, by `k`. -/
def lvC : List (List Leaf) :=
  [runC0_leaves, runC1_leaves, runC2_leaves, runC3_leaves, runC4_leaves, runC5_leaves,
    runC6_leaves, runC7_leaves, runC8_leaves, runC9_leaves, runC10_leaves, runC11_leaves,
    runC12_leaves, runC13_leaves, runC14_leaves, runC15_leaves, runC16_leaves, runC17_leaves,
    runC18_leaves, runC19_leaves, runC20_leaves, runC21_leaves, runC22_leaves, runC23_leaves,
    runC24_leaves, runC25_leaves]

theorem runC (k : Nat) (hk : k < 26) :
    run zesuImage pcs fuel pcC4 (SC k) = some (lvC.getD k []) := by
  match k, hk with
  | 0, _ => exact runC0
  | 1, _ => exact runC1
  | 2, _ => exact runC2
  | 3, _ => exact runC3
  | 4, _ => exact runC4
  | 5, _ => exact runC5
  | 6, _ => exact runC6
  | 7, _ => exact runC7
  | 8, _ => exact runC8
  | 9, _ => exact runC9
  | 10, _ => exact runC10
  | 11, _ => exact runC11
  | 12, _ => exact runC12
  | 13, _ => exact runC13
  | 14, _ => exact runC14
  | 15, _ => exact runC15
  | 16, _ => exact runC16
  | 17, _ => exact runC17
  | 18, _ => exact runC18
  | 19, _ => exact runC19
  | 20, _ => exact runC20
  | 21, _ => exact runC21
  | 22, _ => exact runC22
  | 23, _ => exact runC23
  | 24, _ => exact runC24
  | 25, _ => exact runC25
  | k + 26, h => exact absurd h (by omega)

end ZesuExec.Fn.SszRoot.Sparse
