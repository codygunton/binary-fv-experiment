import ZesuExec.Sail.Run
import ZesuExec.Sail.ModelInit
import ZesuExec.Image.Gen

/-!
# Engine A of `zesu-difftest`: the specialised Sail model

`engineA img m0 bytes stop` builds a Sail state from the model's own initialisation
(`modelInit`, which is `sail_model_init` by `ZesuExec.Sail.InitCheck.modelInit_eq`, then
`init_model ""`, whose `reset` is the model's reset path), writes `PC`,
`x1 … x31`, the image's `.text` words and the snapshot bytes, checks `configuredB`, and runs
`try_step` until `PC = stop`. At `Layout.memcpyEntry` it substitutes the ZisK service exactly as
`SailReaches.service` does: `ziskMemcpy` on the machine read off the Sail state, and the Sail state
`sailMemcpy`. Returns the final machine read off the Sail state and the number of transitions.
-/

namespace ZesuExec.DifftestSail

open BinaryFv.RiscV (State)
open LeanRV64DExecutable.Functions
open ZesuExec.SailLink
open Register

/-- The machine `s` represents: `x1 … x31`, `PC`, and every byte present in Sail's byte map. -/
def machineOf (s : State) : Machine where
  regs := fun i => if i.val = 0 then 0 else
    ((s.regs.get? (xreg i)).map (cast (xreg_type i))).getD 0
  pc := (s.regs.get? Register.PC).getD 0
  mem := fun a => s.mem.get? a.toNat

/-- Run a generated action, rendering a failure. -/
def runSail {α : Type} (act : SailM α) (s : State) : Except String (α × State) :=
  match act.run s with
  | .ok a s' => .ok (a, s')
  | .error _ _ => .error "Sail action failed"

/-- The model's own initialisation and reset path. -/
def initState : Except String State := do
  let (_, s) ← runSail modelInit default
  let (_, s) ← runSail (init_model "") s
  return s

/-- Load the machine's registers, `PC`, the `.text` words of `img` and the listed bytes. -/
def load (img : Image) (m0 : Machine) (bytes : List (Nat × Nat)) (s : State) : State :=
  let regs := (List.range 31).foldl (fun r k =>
    let i : Fin 32 := Fin.ofNat 32 (k + 1)
    r.insert (xreg i) (cast (xreg_type i).symm (m0.regs i))) s.regs
  let regs := regs.insert Register.PC m0.pc
  let mem := img.text.foldl (fun mem seg =>
    (List.range seg.words.length).foldl (fun mem k =>
      let w := seg.words[k]!
      let a := seg.base + 4 * k
      if Layout.textLo ≤ a ∧ a < Layout.textHi then
        (List.range 4).foldl (fun mem j => mem.insert (a + j) (BitVec.ofNat 8 (w / 256 ^ j))) mem
      else mem) mem) s.mem
  let mem := bytes.foldl (fun mem (a, b) => mem.insert a (BitVec.ofNat 8 b)) mem
  { s with regs, mem }

/-- Iterate `try_step` (and the service at `memcpy`) until `PC = stop`. -/
def runTo (stop : Nat) : Nat → State → Nat → Except String (State × Nat)
  | 0, _, k => .error s!"step cap reached after {k} transitions"
  | fuel + 1, s, k =>
    let m := machineOf s
    if m.pc.toNat = stop then .ok (s, k)
    else if m.pc.toNat = Layout.memcpyEntry then
      match ziskMemcpy m with
      | some _ => runTo stop fuel (sailMemcpy m s) (k + 1)
      | none => .error s!"memcpy service outside its domain after {k} transitions"
    else
      match (try_step k false).run s with
      | .ok false s' => runTo stop fuel s' (k + 1)
      | .ok true _ => .error s!"try_step requested exit at pc {m.pc.toNat} after {k} transitions"
      | .error _ _ => .error s!"try_step failed at pc {m.pc.toNat} after {k} transitions"

/-- Engine A from the machine `m0` holding the listed `bytes`. -/
def engineA (img : Image) (m0 : Machine) (bytes : List (Nat × Nat)) (stop cap : Nat) :
    Except String (Machine × Nat) := do
  let s0 := load img m0 bytes (← initState)
  unless configuredB s0 do throw "configuredB fails on the initial Sail state"
  let (s, k) ← runTo stop cap s0 0
  return (machineOf s, k)

/-- First difference between engine A and engine B on `pc`, `x1 … x31`, the bytes `addrs` and the
transition count, if any. -/
def diffAB (mA mB : Machine) (kA kB : Nat) (addrs : Array Nat) : Option String := Id.run do
  if mA.pc ≠ mB.pc then return some s!"pc: sail {mA.pc.toNat}, machine {mB.pc.toNat}"
  if kA ≠ kB then return some s!"transitions: sail {kA}, machine {kB}"
  for i in [1:32] do
    let a := mA.reg (Fin.ofNat 32 i)
    let b := mB.reg (Fin.ofNat 32 i)
    if a ≠ b then return some s!"x{i}: sail {a.toNat}, machine {b.toNat}"
  for a in addrs do
    let x := mA.mem (BitVec.ofNat 64 a)
    let y := mB.mem (BitVec.ofNat 64 a)
    if x ≠ y then return some s!"byte {a}: sail {x.map (·.toNat)}, machine {y.map (·.toNat)}"
  return none

end ZesuExec.DifftestSail
