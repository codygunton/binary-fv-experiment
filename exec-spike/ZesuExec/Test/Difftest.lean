import Lean.Data.Json
import Std.Data.HashMap
import ZesuExec.Service
import ZesuExec.Image.Gen
import ZesuExec.Test.DifftestSail

/-!
# `zesu-difftest`: Sail model (engine A), machine (engine B) and Unicorn snapshots

`zesu-difftest --fn <Id> --snap <file>` reads a `zesu-snap/1` snapshot written by
`tools/snap.py`, builds a `Machine` whose memory holds exactly the entry bytes the snapshot lists
(rodata included), iterates `next zesuImage` until `pc` equals the entry `x1` (at most
`stepCap` transitions), and compares `pc`, `x1..x31` and every listed byte with the return
snapshot: a byte listed under `exit.changed` must hold that value, every other entry byte its
entry value; the number of transitions must equal Unicorn's instruction count (both count the
`memcpy` service as one). Engine A (`ZesuExec.Test.DifftestSail`) then runs the specialised
Sail model from its own initialisation on the same entry state (`configuredB` must hold) and must
agree with the machine on all of the above. Prints `agree`, or the first difference and exits 1.
-/

namespace ZesuExec.Difftest

open Lean (Json)

def stepCap : Nat := 1000000

def segOf : String → Option Seg
  | "F0" => some Gen.F0 | "F1" => some Gen.F1 | "F2" => some Gen.F2 | "F3" => some Gen.F3
  | "F4" => some Gen.F4 | "F5" => some Gen.F5 | "F6" => some Gen.F6 | "TX" => some Gen.TX
  | "DTF" => some Gen.DTF
  | "R8330" => some Gen.fn_mem_rotate__anon_8330 | "R10572" => some Gen.fn_mem_rotate__anon_10572
  | "R12629" => some Gen.fn_mem_rotate__anon_12629
  | "M7964" => some Gen.fn_sort_block_mergeInPlace__anon_7964
  | "M11564" => some Gen.fn_sort_block_mergeInPlace__anon_11564
  | _ => none

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def hexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
  else throw s!"bad hex digit {c}"

def parseHex (s : String) : Except String (Array Nat) := do
  let rec go : List Char → Array Nat → Except String (Array Nat)
    | [], acc => pure acc
    | hi :: lo :: cs, acc => do go cs (acc.push ((← hexDigit hi) * 16 + (← hexDigit lo)))
    | [_], _ => throw "odd hex length"
  go s.toList #[]

/-- `[{"base", "hex"}]` rows as (address, byte) pairs. -/
def parseBytes (j : Json) : Except String (Array (Nat × Nat)) := do
  let mut out := #[]
  for row in ← j.getArr? do
    let base ← (← row.getObjVal? "base").getNat?
    let bs ← parseHex (← (← row.getObjVal? "hex").getStr?)
    for i in [0:bs.size] do
      out := out.push (base + i, bs[i]!)
  return out

structure Side where
  pc   : Nat
  regs : Array Nat   -- x1 .. x31

def parseSide (j : Json) : Except String Side := do
  let pc ← (← j.getObjVal? "pc").getNat?
  let regs ← (← (← j.getObjVal? "regs").getArr?).mapM (·.getNat?)
  unless regs.size = 31 do throw s!"expected 31 registers, got {regs.size}"
  return { pc, regs }

def initial (s : Side) (mem : Std.HashMap Nat Nat) : Machine where
  regs := fun i => if i.val = 0 then 0 else BitVec.ofNat 64 (s.regs[i.val - 1]!)
  pc := BitVec.ofNat 64 s.pc
  mem := fun a => (mem.get? a.toNat).map (BitVec.ofNat 8)

/-- Iterate `next` until `pc = stop`; returns the machine, transitions and cost, or the failing
machine. -/
def runTo (stop : Nat) : Nat → Machine → Nat → Nat → Except (Machine × Nat) (Machine × Nat × Nat)
  | 0, m, k, _ => .error (m, k)
  | fuel + 1, m, k, c =>
    if m.pc.toNat = stop then .ok (m, k, c)
    else match next zesuImage m with
      | some (m', d) => runTo stop fuel m' (k + 1) (c + d)
      | none => .error (m, k)

def describe (m : Machine) : String :=
  let pc := m.pc.toNat
  let ins := match zesuImage.word? pc with
    | some w => s!"word {hex w}, decode " ++
        (match decodeNat w with | some i => i.mnemonic | none => "none")
    | none => "no image word"
  let regs := String.intercalate " " ((List.range 31).map fun i =>
    s!"x{i+1}={hex (m.reg (Fin.ofNat 32 (i+1))).toNat}")
  s!"pc {hex pc} ({ins}); {regs}"

def check (fn file : String) : ExceptT String IO Unit := do
  let seg ← match segOf fn with | some s => pure s | none => throw s!"unknown --fn {fn}"
  let j ← match Json.parse (← IO.FS.readFile file) with
    | .ok j => pure j | .error e => throw s!"{file}: {e}"
  let liftE {α} (x : Except String α) : ExceptT String IO α := match x with
    | .ok a => pure a | .error e => throw s!"{file}: {e}"
  let sfn ← liftE ((← liftE (j.getObjVal? "fn")).getStr?)
  unless sfn = fn do throw s!"{file}: snapshot is for {sfn}, not {fn}"
  let entryJ ← liftE (j.getObjVal? "entry")
  let exitJ ← liftE (j.getObjVal? "exit")
  let entry ← liftE (parseSide entryJ)
  let exit ← liftE (parseSide exitJ)
  unless entry.pc = seg.base do throw s!"entry pc {hex entry.pc} is not {fn} at {hex seg.base}"
  let bytes ← liftE (parseBytes (← liftE (entryJ.getObjVal? "mem")))
  let changed ← liftE (parseBytes (← liftE (exitJ.getObjVal? "changed")))
  let mem := bytes.foldl (fun h (a, b) => h.insert a b) ({} : Std.HashMap Nat Nat)
  let want := changed.foldl (fun h (a, b) => h.insert a b) mem
  let stop := entry.regs[0]!
  let m0 := initial entry mem
  match runTo stop stepCap m0 0 0 with
  | .error (m, k) =>
    throw s!"machine stuck after {k} transitions (next = none or step cap): {describe m}"
  | .ok (m, k, cost) =>
    unless m.pc.toNat = exit.pc do throw s!"pc: machine {hex m.pc.toNat}, unicorn {hex exit.pc}"
    if let .ok n := j.getObjValAs? Nat "unicorn_insns" then
      unless k = n do throw s!"instruction count: machine {k} transitions, unicorn {n}"
    for i in [1:32] do
      let mv := (m.reg (Fin.ofNat 32 i)).toNat
      let uv := exit.regs[i - 1]!
      unless mv = uv do throw s!"x{i}: machine {hex mv}, unicorn {hex uv}"
    let addrs := (want.toArray.map (·.1)).qsort (· < ·)
    for a in addrs do
      let mv := (m.mem (BitVec.ofNat 64 a)).map (·.toNat)
      let uv := want.get? a
      unless mv = uv do
        throw s!"byte {hex a}: machine {mv.map hex}, unicorn {uv.map hex} (entry {(mem.get? a).map hex})"
    -- Engine A: the specialised Sail model from its own initialisation (configuredB checked).
    match DifftestSail.engineA zesuImage m0 bytes.toList stop stepCap with
    | .error e => throw s!"sail: {e}"
    | .ok (mA, kA) =>
      if let some d := DifftestSail.diffAB mA m kA k addrs then throw s!"sail vs machine: {d}"
    IO.println s!"agree ({fn} {file}: sail = machine = unicorn, {k} transitions, cost {cost}, {addrs.size} bytes, configuredB)"

end ZesuExec.Difftest

def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Option String → Option String → Option (String × String)
    | "--fn" :: v :: rest, _, s => opts rest (some v) s
    | "--snap" :: v :: rest, f, _ => opts rest f (some v)
    | [], some f, some s => some (f, s)
    | _, _, _ => none
  match opts args none none with
  | none =>
    IO.eprintln "usage: zesu-difftest --fn <Id> --snap <file>"
    return 2
  | some (fn, file) =>
    match ← (ZesuExec.Difftest.check fn file).run with
    | .ok () => return 0
    | .error e =>
      IO.println s!"DIFFER {e}"
      return 1
