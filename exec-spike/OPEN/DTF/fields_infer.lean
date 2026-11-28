import ZesuExec.Fn.DTF.Hand

/-!
Field-row inference for `shape.py --fields` (not part of the build; run with `lake env lean`).

A greatest-fixpoint must-analysis over DTF's leaves with `Gen.lean`'s own carry rules: per arm `t`
the item values a cut (plain row, `cutFields`) or a call site (`siteFields`, by return address)
holds are those every leaf into it produces (`fieldOk` on a candidate entry with guard `[t]`)
from its source's row; sources not yet reached are skipped. Afterwards only the entries a later
row needs are kept (backward from the seeds: every entry at the success write and the allocator
call sites' `data` lengths and pointers). Prints `ROW <cut|site> <pc> <loc> <arms> <value>`.
-/

open ZesuExec ZesuExec.Sym ZesuExec.Fn.DTF

namespace Infer

/-- Arms analysed (`shape.py` substitutes the list). -/
def active : List Nat := ACTIVE_ARMS

def allLocs : List Loc :=
  ((List.range 31).map fun i => Loc.reg (i + 1)) ++
    (List.range (frameBytes / 8)).map (fun i => Loc.slot (8 * i))

abbrev Ent := Loc × FieldVal
/-- Per target key and arm: `none` = not reached yet. -/
abbrev Rows := List ((Bool × Nat) × List (Nat × List Ent))

def lookupArm (rs : Rows) (key : Bool × Nat) (t : Nat) : Option (List Ent) :=
  (rs.lookup key).bind (·.lookup t)

/-- Entries with guards, `[]` when the value holds for every arm reaching the key. -/
def pack (arms : List Nat) (per : List (Nat × List Ent)) : List Field :=
  let keys := (per.flatMap (·.2)).eraseDups
  keys.map fun e =>
    let g := ((per.filter fun p => p.2.contains e).map (·.1)).eraseDups.mergeSort
    ⟨e.1, if !arms.isEmpty && arms.all g.contains then [] else g, e.2⟩

def cutArms (pc : Nat) : List Nat := (dataAt pc).arms
def siteArms (r : Nat) : List Nat := match (dataAt r).site with
  | some s => s.arms
  | none => []

def packed (rs : Rows) (key : Bool × Nat) (seeds : List Field) : List Field :=
  let arms := if key.1 then siteArms key.2 else cutArms key.2
  pack arms ((rs.lookup key).getD []) ++ seeds

/-- The existing `siteFieldsTable` entries for arms outside `active` (kept as they are). -/
def seedSite (r : Nat) : List Field :=
  if (siteArms r).any active.contains then [] else siteFields r

def cfOf (rs : Rows) (pc : Nat) : List Field := packed rs (false, pc) []
def sfOf (rs : Rows) (r : Nat) : List Field := packed rs (true, r) (seedSite r)

/-- The jump-table targets (reached by the `.jumpInd` leaf of `0x80000574`, before any item). -/
def heads : List Nat := [0x80000588, 0x8000081c, 0x8000069c, 0x8000075c, 0x800005dc]

/-- The source row of a leaf of `d` is known for arm `t`. -/
def srcKnown (rs : Rows) (d : CutData) (t : Nat) : Bool :=
  if d.pc == entry || d.arms.isEmpty || heads.contains d.pc then true else
  match d.site with
  | none => (lookupArm rs (false, d.pc) t).isSome
  | some _ => if d.plain then true else
      (lookupArm rs (true, d.pc) t).isSome || !active.contains t

def sizes : List (Nat × Nat) := [(8, 1), (16, 2), (32, 4)]

def kindsAt (d : CutData) (l : Leaf) (ko k : Nat) : List FieldVal :=
  let base : List FieldVal := [.len k, .ptr k, .nz k, .raw k 0 8, .raw k 8 8, .raw k 16 4] ++
    sizes.flatMap fun (n, c) => (List.range c).map fun i => .num k n i
  let ptr := (Loc.slot ko).sym d.shape.S
  let curs := (List.range 32).filter fun c => l.S.reg c == ptr
  let fins := (List.range 32).filter fun f =>
    l.S.reg f == .bin .add ptr (.init 0 (ko + 8) 8)
  -- a loop over at most `b` bytes accumulates a number of exactly `b` bytes (`u64`, `u128`, `u256`)
  let accs := match lenBound l.conds ko with
    | some b => curs.flatMap fun c => fins.flatMap fun f =>
        (sizes.filter (·.1 == b)).flatMap fun (n, cnt) =>
          (List.range cnt).map fun i => FieldVal.acc k n i c f
    | none => []
  base ++ accs

/-- Entries a leaf produces for arm `t` at its target, from the source's entries `src`. -/
def produce (src : List (Sym × Field)) (d : CutData) (l : Leaf) (t : Nat) : List Ent :=
  let syms := allLocs.map fun loc => (loc, loc.sym l.S)
  let kept := src.flatMap fun a =>
    if a.2.v.free && guardOk d.arms a.2.arms [t] then
      (syms.filter (·.2 == a.1)).map fun p => (p.1, a.2.v)
    else []
  let fromOut := match advOf d with
    | some (ko, k) => (syms.flatMap fun p => (kindsAt d l ko k).map (p.1, ·)).filter fieldFrom'
    | none => []
  let loops := (src.flatMap fun a => match a.2.v with
      | .acc k n i cur fin => syms.flatMap fun p => [(p.1, FieldVal.acc k n i cur fin),
          (p.1, FieldVal.num k n i)]
      | _ => []).filter (loopFrom src d l [t])
  (kept ++ fromOut ++ loops).eraseDups
where fieldFrom' (e : Ent) : Bool := e.1.fine && fieldFrom d l e

/-- A leaf of `d` into key `key` (`true`: the call site returning to it). -/
def target (l : Leaf) : Option (Bool × Nat) :=
  match l.exit with
  | .at pc => match targetOf pc with
    | some d' => if d'.plain && pc != entry then some (false, pc) else none
    | none => none
  | .call _ r => match targetOf r with
    | some d' => if d'.site.isSome then some (true, r) else none
    | none => none
  | _ => none

def edges : List (CutData × Leaf × (Bool × Nat)) :=
  table.flatMap fun d => (leavesAt d.pc).filterMap fun l => (target l).map (d, l, ·)

def keys : List (Bool × Nat) := (edges.map (·.2.2)).eraseDups

def keyArms (key : Bool × Nat) : List Nat :=
  (if key.1 then siteArms key.2 else cutArms key.2).filter active.contains

def inter (a b : List Ent) : List Ent := a.filter b.contains

/-- One pass over every key. -/
def pass (rs : Rows) : Rows :=
  keys.map fun key =>
    let ins := edges.filter (·.2.2 == key)
    let per := (keyArms key).filterMap fun t =>
      let outs := ins.filterMap fun (d, l, _) =>
        if (d.arms.isEmpty || d.arms.contains t) && srcKnown rs d t then
          some (produce (srcFieldsOf (cfOf rs) (sfOf rs) d) d l t)
        else none
      match outs with
      | [] => none
      | o :: os => some (t, os.foldl inter o)
    (key, per)

partial def fix (rs : Rows) (n : Nat) : Rows × Nat :=
  let rs' := pass rs
  if rs' == rs || n == 0 then (rs', n) else fix rs' (n - 1)

/-! ## Backward pruning: keep the entries a needed entry is carried from -/

/-- The source entries (key, arm, entry) a target entry `e` (arm `t`) of a leaf rests on. -/
def deps (rs : Rows) (d : CutData) (l : Leaf) (t : Nat) (e : Ent) : List (Nat × Ent) :=
  let src := srcFieldsOf (cfOf rs) (sfOf rs) d
  let sym := e.1.sym l.S
  let kept := src.filter fun a => a.2.v.free && a.2.v == e.2 && a.1 == sym
  let loop := src.filter fun a => match a.2.v, e.2 with
    | .acc k n i c f, .acc k' n' i' c' f' => k == k' && n == n' && c == c' && f == f' &&
        (i == i' || i + 1 == i')
    | .acc k n i _ _, .num k' n' i' => k == k' && n == n' && (i == i' || i + 1 == i')
    | _, _ => false
  -- back to source locations: a source entry is identified by its field and symbol
  let srcLocs := allLocs.filter fun loc => loc.fine
  ((kept ++ loop).flatMap fun a =>
    (srcLocs.filter fun loc => (match d.site with
      | none => loc.sym d.shape.S == a.1
      | some _ => keptSym loc == some a.1 || keptPtr loc == some a.1) &&
        a.2.loc == loc).map fun loc => (t, (loc, a.2.v)))

def srcKey (d : CutData) : Option (Bool × Nat) :=
  match d.site with
  | none => some (false, d.pc)
  | some _ => if d.plain then none else some (true, d.pc)

partial def need (rs : Rows) (work : List ((Bool × Nat) × Nat × Ent))
    (seen : List ((Bool × Nat) × Nat × Ent)) : List ((Bool × Nat) × Nat × Ent) :=
  match work with
  | [] => seen
  | (key, t, e) :: rest =>
    let ins := edges.filter (·.2.2 == key)
    let new := ins.flatMap fun (d, l, _) =>
      match srcKey d with
      | some sk => if d.arms.isEmpty || d.arms.contains t then
          (deps rs d l t e).map fun (t', e') => (sk, t', e')
        else []
      | none => []
    let new := new.filter fun x => !seen.contains x && !rest.contains x
    need rs (rest ++ new) (seen ++ new)

def seeds (rs : Rows) : List ((Bool × Nat) × Nat × Ent) :=
  rs.flatMap fun (key, per) =>
    let isSeed := (key == (false, 0x80002dc4)) ||
      (key.1 && match (dataAt key.2).site with
        | some s => s.kind == .alloc
        | none => false)
    if isSeed then per.flatMap fun (t, es) =>
      (es.filter fun e => key.2 == 0x80002dc4 || (match e.2 with
        | .len _ | .ptr _ => true
        | _ => false)).map (key, t, ·)
    else []

def prune (rs : Rows) : Rows :=
  let sd := seeds rs
  let keep := need rs sd sd
  rs.map fun (key, per) => (key, per.map fun (t, es) => (t, es.filter fun e => keep.contains (key, t, e)))

def locStr : Loc → String
  | .reg i => s!".reg {i}"
  | .slot o => s!".slot 0x{String.ofList (Nat.toDigits 16 o)}"

def valStr : FieldVal → String
  | .ptr k => s!".ptr {k}"
  | .len k => s!".len {k}"
  | .num k n i => s!".num {k} {n} {i}"
  | .nz k => s!".nz {k}"
  | .raw k o n => s!".raw {k} {o} {n}"
  | .acc k n i c f => s!".acc {k} {n} {i} {c} {f}"

end Infer

open Infer in
#eval show IO Unit from do
  let init : Rows := []
  let (rs, left) := fix init 200
  IO.println s!"PASSES_LEFT {left}"
  let rs := if PRUNE then prune rs else rs
  for (key, _) in rs do
    let fs := if key.1 then sfOf rs key.2 else cfOf rs key.2
    for f in fs do
      IO.println s!"ROW {if key.1 then "site" else "cut"} {key.2} {locStr f.loc} {f.arms} {valStr f.v}"
  -- every leaf carries its target's packed row (`fieldsCarry`, as the proofs check it)
  for (d, l, key) in edges do
    let tgt := if key.1 then sfOf rs key.2 else cfOf rs key.2
    let src := srcFieldsOf (cfOf rs) (sfOf rs) d
    for f in tgt do
      if !fieldOk src d l f then
        IO.println s!"FAIL {d.pc} {key.2} {locStr f.loc} {f.arms} {valStr f.v}"
