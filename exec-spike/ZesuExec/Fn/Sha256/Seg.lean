import ZesuExec.Fn.Sha256.Spec
import ZesuExec.Fn.Sha256.Model
import ZesuExec.Fn.Stage
import ZesuExec.Fn.Preserve

/-!
# `zkvm_sha256`: straight-line pieces between service sites

The symbolic executor stops at a word it cannot decode, so every CSR service site of
`zkvm_sha256` ends a symbolic run (it is in the run's cut list) and the next run starts after it
from a fresh symbolic state built from the concrete machine (`seg_sound`). Three shapes:
`shapeE` at the entry (the frame below `sp`), `shapeM` between the prologue and the output (the
frame at `sp`), `shapeO` for the output (the frame and `out`).
-/

namespace ZesuExec.Fn.Sha256
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Fn

def frameRg : Region := ⟨some 0xe0, 16, true⟩
def outRg : Region := ⟨some 32, 1, true⟩

/-- At the entry: the frame below `sp`. -/
def shapeE (m : Machine) : Shape := [((m.reg 2 - BitVec.ofNat 64 frameSize, 0xe0), frameRg)]
/-- After the prologue: the frame at `sp`. -/
def shapeM (m : Machine) : Shape := [((m.reg 2, 0xe0), frameRg)]
/-- The output: the frame at `sp` and `out` at `a2`. -/
def shapeO (m : Machine) : Shape := [((m.reg 2, 0xe0), frameRg), ((m.reg 12, 32), outRg)]

def ovE (i : Nat) : Option Sym := if i = 2 then some (.ptr 0 0xe0) else none
def ovM (i : Nat) : Option Sym := if i = 2 then some (.ptr 0 0) else none
def ovO (i : Nat) : Option Sym :=
  if i = 2 then some (.ptr 0 0) else if i = 12 then some (.ptr 1 0) else none

def SE : SState := entryState ovE [frameRg] []
def SM : SState := entryState ovM [frameRg] []
def SO : SState := entryState ovO [frameRg, outRg] []

/-- `run_sound` from a fresh entry state of `shape` at the machine `m`. -/
theorem seg_sound {ov : Nat → Option Sym} {shape : Shape} {cuts : List Nat} {fuel pc : Nat}
    {ls : List Leaf} (h : run zesuImage cuts fuel pc (entryState ov (shape.map (·.2)) []) = some ls)
    {m : Machine} (hok : ∀ p ∈ shape, RegionOk p) (hdis : (shape.map (·.1)).Pairwise Disjoint)
    (hpres : ∀ r j, r < shape.length → j < (entryEnv m (shape.map (·.1))).size r →
      (m.mem ((entryEnv m (shape.map (·.1))).base r + BitVec.ofNat 64 j)).isSome)
    (hov : ∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
      s.eval (entryEnv m (shape.map (·.1))) = m.reg i)
    (hpc : m.pc.toNat = pc) (hro : RodataLoaded zesuImage m) :
    ∃ l ∈ ls, (∀ c ∈ l.conds, c.eval (entryEnv m (shape.map (·.1))) = true) ∧
      ((∀ o ∈ l.obligs, o.holds (entryEnv m (shape.map (·.1)))) →
        ∃ m', RunsIn zesuImage l.S.steps m m' ∧ Match (entryEnv m (shape.map (·.1))) l.S m' ∧
          ExitOk (entryEnv m (shape.map (·.1))) l.exit m' ∧
          SameOutside (InWritable (entryEnv m (shape.map (·.1)))
            (entryState ov (shape.map (·.2)) [])) m m') := by
  have hwf := entry_wf (m := m) (ov := ov) (ks := []) shape hok hdis
  have hm : Match (entryEnv m (shape.map (·.1))) (entryState ov (shape.map (·.2)) []) m :=
    entry_match hov (fun r j hr hj => hpres r j (by simpa using hr) hj) (by simp)
  obtain ⟨l, hl, hc, hr⟩ := run_sound h hwf hm hpc hro
  refine ⟨l, hl, hc, fun ho => ?_⟩
  obtain ⟨m', h1, h2, h3, h4⟩ := hr ho
  exact ⟨m', by simpa [entryState] using h1, h2, h3, h4⟩

end ZesuExec.Fn.Sha256
