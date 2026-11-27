import ZesuExec.Sym.Compose

/-!
# Callee summaries in the executor: `runWith`, `runWith_sound` (programme plan S5 probe 2)

`runWith img sums cuts F0 fuel pc S` is `run` that continues through a direct call whose
target has a `Summary` instead of ending the leaf there. At such a call the state at the callee
entry is recorded in a `CallRec`; the state after the return (`CallRec.post`) has the summary's
clobbered registers replaced by the fresh variables `var (F + i)` (`F = F0 + 32 * calls so far`),
`a0` set to the summary's result if it has one, the byte ranges the callee may write
(`CallRec.wr`, resolved from argument registers) turned into fresh initial memory, and `bound`
more steps. Each leaf (`LeafW`) carries the calls on its path and the union of their ranges.

`runWith_sound` takes, per recorded call, a proof `CallHyp` that from any machine matching the
call's state the callee returns within `bound` steps to a machine satisfying `CallPost` (return
address, kept registers, result, the bytes outside the written ranges, presence of the written
bytes, footprint inside the caller's writable regions or the caller-chosen `X`) and a
caller-chosen fact `Qc`. It concludes `run_sound`'s statement with three changes: the leaf's
environment `env'` extends the start environment by the fresh variables and the written ranges
(`Env.Agree`); the step count is an upper bound; and for every call on the path there are the
concrete machines at its entry and return with `Qc` (`CallFact`), which is how a caller reads the
callee's postcondition back.

Restrictions (checked by `CallRec.okB` at each summarised call; `runWith` returns `none`
otherwise): every term of the state at the call, every path condition so far and the result
mention only variables below `F` and no initial byte of a written range, and no symbolic write or
known fact overlaps a written range. A summary adds no region, so `alloc` (whose new block is a
region that does not exist before the call) cannot be summarised; its call sites stay leaves.
-/

namespace ZesuExec.Sym
open ZesuExec ZesuExec.Machine

/-- What a direct call does, as the executor continues through it. -/
structure Summary where
  /-- instructions the callee takes at most, from its entry to its return -/
  bound : Nat
  /-- registers replaced by fresh variables -/
  clobbers : List Nat
  /-- `a0` after the call, a term over the caller's state (takes precedence over a clobber) -/
  result : Option Sym
  /-- (argument register, bytes): the callee may write that many bytes at the constant region
  place the register holds; they become fresh initial memory -/
  writes : List (Nat × Nat)

/-- Registers a callee may change under the ABI: all but `x0` and the callee-saved. -/
def abiClobbers : List Nat := [1, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-! ## Byte ranges -/

/-- `(region, offset, length)` byte ranges. -/
abbrev Ranges := List (Nat × Nat × Nat)

def Ranges.covers (wr : Ranges) (r j : Nat) : Bool :=
  wr.any fun x => x.1 == r && x.2.1 ≤ j && j < x.2.1 + x.2.2

def Ranges.overlaps (wr : Ranges) (r off n : Nat) : Bool :=
  wr.any fun x => x.1 == r && x.2.1 < off + n && off < x.2.1 + x.2.2

def Ranges.hasRegion (wr : Ranges) (r : Nat) : Bool := wr.any (·.1 == r)

theorem Ranges.covers_append (w₁ w₂ : Ranges) (r j : Nat) :
    Ranges.covers (w₁ ++ w₂) r j = (w₁.covers r j || w₂.covers r j) := by
  simp [Ranges.covers, List.any_append]

theorem Ranges.covers_of_overlaps {wr : Ranges} {r off n t : Nat}
    (h : wr.overlaps r off n = false) (ht : t < n) : wr.covers r (off + t) = false := by
  simp only [Ranges.overlaps, Ranges.covers, List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  rintro x hx ⟨⟨h1, h2⟩, h3⟩
  exact h x hx ⟨⟨h1, by omega⟩, by omega⟩

theorem Ranges.covers_of_hasRegion {wr : Ranges} {r : Nat} (h : wr.hasRegion r = false) (j : Nat) :
    wr.covers r j = false := by
  simp only [Ranges.hasRegion, Ranges.covers, List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  rintro x hx ⟨⟨h1, -⟩, -⟩
  exact h x hx h1

/-! ## Terms that keep their meaning across a call -/

/-- `s` mentions only variables below `F` and no initial byte inside `wr`. -/
def Sym.okB (F : Nat) (wr : Ranges) : Sym → Bool
  | .lit _ => true
  | .var i => i < F
  | .ptr _ _ => true
  | .init r off n => !wr.overlaps r off n
  | .initx r _ idx _ _ => !wr.hasRegion r && Sym.okB F wr idx
  | .bin _ a b => Sym.okB F wr a && Sym.okB F wr b
  | .sext _ a => Sym.okB F wr a
  | .bytes a _ _ => Sym.okB F wr a
  | .cat lo hi _ => Sym.okB F wr lo && Sym.okB F wr hi

def SBool.okB (F : Nat) (wr : Ranges) : SBool → Bool
  | .eq a b | .ne a b | .ltu a b | .geu a b | .lts a b | .ges a b => a.okB F wr && b.okB F wr

/-- The value is kept and the bytes lie outside `wr`. -/
def Write.okB (F : Nat) (wr : Ranges) (w : Write) : Bool :=
  w.v.okB F wr && !wr.overlaps w.r w.off w.n

def SState.okB (F : Nat) (wr : Ranges) (S : SState) : Bool :=
  S.regs.all (Sym.okB F wr) && S.mem.all (Write.okB F wr) && S.known.all (Write.okB F wr)

/-- `env'` agrees with `env` on variables below `F`, on the regions and on every initial byte
outside `wr`. -/
structure Env.Agree (env env' : Env) (F : Nat) (wr : Ranges) : Prop where
  vars : ∀ i < F, env'.vars i = env.vars i
  regions : env'.regions = env.regions
  mem0 : ∀ r j, wr.covers r j = false → env'.mem0 r j = env.mem0 r j

theorem Env.Agree.refl (env : Env) (F : Nat) (wr : Ranges) : Env.Agree env env F wr :=
  ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl⟩

theorem Env.Agree.trans {a b c : Env} {F F' : Nat} {w₁ w₂ : Ranges} (h₁ : Env.Agree a b F w₁)
    (h₂ : Env.Agree b c F' w₂) (hF : F ≤ F') : Env.Agree a c F (w₁ ++ w₂) :=
  ⟨fun i hi => (h₂.vars i (by omega)).trans (h₁.vars i hi), h₂.regions.trans h₁.regions,
    fun r j h => by
      rw [Ranges.covers_append, Bool.or_eq_false_iff] at h
      exact (h₂.mem0 r j h.2).trans (h₁.mem0 r j h.1)⟩

theorem Env.Agree.base {env env' : Env} {F : Nat} {wr : Ranges} (h : Env.Agree env env' F wr)
    (r : Nat) : env'.base r = env.base r := by simp [Env.base, h.regions]

theorem Env.Agree.size {env env' : Env} {F : Nat} {wr : Ranges} (h : Env.Agree env env' F wr)
    (r : Nat) : env'.size r = env.size r := by simp [Env.size, h.regions]

theorem Sym.eval_agree {env env' : Env} {F : Nat} {wr : Ranges} (h : Env.Agree env env' F wr) :
    ∀ s : Sym, s.okB F wr = true → s.eval env' = s.eval env
  | .lit _, _ => rfl
  | .var i, hs => h.vars i (by simpa [Sym.okB] using hs)
  | .ptr r _, _ => by simp [Sym.eval, h.base r]
  | .init r off n, hs => by
    simp only [Sym.okB, Bool.not_eq_true'] at hs
    simp only [Sym.eval]
    congr 1
    exact byteList_congr fun t ht => h.mem0 r _ (Ranges.covers_of_overlaps hs ht)
  | .initx r off idx sc n, hs => by
    simp only [Sym.okB, Bool.and_eq_true, Bool.not_eq_true'] at hs
    simp only [Sym.eval, Sym.eval_agree h idx hs.2]
    congr 1
    exact byteList_congr fun t _ => h.mem0 r _ (Ranges.covers_of_hasRegion hs.1 _)
  | .bin op a b, hs => by
    simp only [Sym.okB, Bool.and_eq_true] at hs
    simp only [Sym.eval, Sym.eval_agree h a hs.1, Sym.eval_agree h b hs.2]
  | .sext _ a, hs => by simp only [Sym.eval, Sym.eval_agree h a (by simpa [Sym.okB] using hs)]
  | .bytes a _ _, hs => by simp only [Sym.eval, Sym.eval_agree h a (by simpa [Sym.okB] using hs)]
  | .cat lo hi _, hs => by
    simp only [Sym.okB, Bool.and_eq_true] at hs
    simp only [Sym.eval, Sym.eval_agree h lo hs.1, Sym.eval_agree h hi hs.2]

theorem SBool.eval_agree {env env' : Env} {F : Nat} {wr : Ranges} (h : Env.Agree env env' F wr)
    (c : SBool) (hc : c.okB F wr = true) : c.eval env' = c.eval env := by
  cases c <;> simp only [SBool.okB, Bool.and_eq_true] at hc <;>
    simp only [SBool.eval, Sym.eval_agree h _ hc.1, Sym.eval_agree h _ hc.2]

theorem memByte_agree {env env' : Env} {F : Nat} {wr : Ranges} (h : Env.Agree env env' F wr)
    {ws : List Write} (hws : ws.all (Write.okB F wr) = true) {r j : Nat}
    (hj : wr.covers r j = false) : memByte env' ws r j = memByte env ws r j := by
  unfold memByte
  cases hf : ws.find? (·.covers r j) with
  | none => simp [Env.byte0, h.mem0 r j hj]
  | some w =>
    have hw := List.all_eq_true.mp hws w (List.mem_of_find?_eq_some hf)
    simp only [Write.okB, Bool.and_eq_true] at hw
    simp [Sym.eval_agree h w.v hw.1]

/-- No write of `ws` covers a byte of `wr`. -/
theorem find_covers_none_okB {F : Nat} {wr : Ranges} {ws : List Write}
    (hws : ws.all (Write.okB F wr) = true) {r j : Nat} (hj : wr.covers r j = true) :
    ws.find? (·.covers r j) = none := by
  refine List.find?_eq_none.mpr fun w hw hc => ?_
  have hw' := List.all_eq_true.mp hws w hw
  simp only [Write.okB, Bool.and_eq_true, Bool.not_eq_true'] at hw'
  have ho := hw'.2
  simp only [Write.covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  simp only [Ranges.covers, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hj
  simp only [Ranges.overlaps, List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ho
  obtain ⟨x, hx, ⟨hx1, hx2⟩, hx3⟩ := hj
  exact ho x hx ⟨⟨by rw [hx1, hc.1.1], by omega⟩, by omega⟩

theorem SState.okB_reg {F : Nat} {wr : Ranges} {S : SState} (h : S.okB F wr = true) (i : Nat) :
    (S.reg i).okB F wr = true := by
  simp only [SState.okB, Bool.and_eq_true] at h
  unfold SState.reg
  split
  · rfl
  · rw [List.getD_eq_getElem?_getD]
    cases hx : S.regs[i]? with
    | none => rfl
    | some s => exact List.all_eq_true.mp h.1.1 s (List.mem_of_getElem? hx)

/-- A state whose terms keep their meaning keeps its `Match` when only variables from `F` on
change. -/
theorem Match.agree {env env' : Env} {F : Nat} {S : SState} {m : Machine}
    (h : Env.Agree env env' F []) (hS : S.okB F [] = true) (hm : Match env S m) :
    Match env' S m := by
  have hS' := hS
  simp only [SState.okB, Bool.and_eq_true] at hS'
  refine ⟨hm.regsLen, fun i => ?_, fun r j hr hj => ?_, fun k hk t ht => ?_⟩
  · rw [Sym.eval_agree h _ (SState.okB_reg hS i.val)]; exact hm.regs i
  · rw [h.base, memByte_agree h hS'.1.2 rfl]; exact hm.mem r j hr (by rwa [← h.size])
  · have hk' := List.all_eq_true.mp hS'.2 k hk
    simp only [Write.okB, Bool.and_eq_true] at hk'
    rw [Env.byte0, h.mem0 _ _ rfl, Sym.eval_agree h _ hk'.1]
    exact hm.known k hk t ht

theorem Env.WF.of_regions {env env' : Env} {S : SState} (hwf : Env.WF env S)
    (h : env'.regions = env.regions) : Env.WF env' S := by
  have hb : ∀ r, env'.base r = env.base r := fun r => by simp [Env.base, h]
  have hs : ∀ r, env'.size r = env.size r := fun r => by simp [Env.size, h]
  exact ⟨h ▸ hwf.len, fun r r' j j' hne hj hj' => by
      rw [hb, hb]; rw [hs] at hj hj'; exact hwf.disjoint r r' j j' hne hj hj',
    fun r R s hR hsz => by rw [hs]; exact hwf.size r R s hR hsz,
    fun r R hR => by rw [hb]; exact hwf.align r R hR,
    fun r R hR => by rw [hb, hs]; exact hwf.range r R hR⟩

theorem InWritable.of_regions {env env' : Env} {S S' : SState} (h : env'.regions = env.regions)
    (hS : S'.regions = S.regions) {a : Word} (ha : InWritable env' S' a) : InWritable env S a := by
  obtain ⟨r, R, j, hR, hw, hj, rfl⟩ := ha
  refine ⟨r, R, j, hS ▸ hR, hw, by simpa [Env.size, h] using hj, by simp [Env.base, h]⟩

/-! ## Calls -/

/-- A summarised call on a path: the state at the callee entry, the path conditions so far, the
first fresh variable, the summary, the ranges it writes and the ranges earlier calls wrote. -/
structure CallRec where
  target : Nat
  ret : Nat
  S : SState
  conds : List SBool
  F : Nat
  bound : Nat
  clobbers : List Nat
  result : Option Sym
  wr : List (Nat × Nat × Nat)
  prevWr : List (Nat × Nat × Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- The register replacement at the return. -/
def CallRec.ov (c : CallRec) (i : Nat) : Option Sym :=
  if i = 0 then none
  else if i = 10 ∧ c.result.isSome then c.result
  else if c.clobbers.contains i then some (.var (c.F + i)) else none

/-- The state after the return. -/
def CallRec.post (c : CallRec) : SState :=
  { c.S.override c.ov with steps := c.S.steps + c.bound }

def CallRec.okB (c : CallRec) : Bool :=
  c.S.okB c.F c.wr && c.conds.all (SBool.okB c.F c.wr) && c.result.all (Sym.okB c.F c.wr)

/-- The ranges `(region, offset, bytes)` of a summary's writes at a state. -/
def resolveWrites (S : SState) : List (Nat × Nat) → Option Ranges
  | [] => some []
  | (a, n) :: rest =>
    match place (S.reg a) with
    | some (.cst r off) =>
      match S.region r with
      | some R => if R.writable then (resolveWrites S rest).map ((r, off, n) :: ·) else none
      | none => none
    | _ => none

def mkCall (sm : Summary) (S : SState) (t r : Nat) (cs : List SBool) (F : Nat) (prev : Ranges) :
    Option CallRec :=
  (resolveWrites S sm.writes).map fun wrs =>
    { target := t, ret := r, S := S, conds := cs, F := F, bound := sm.bound,
      clobbers := sm.clobbers, result := sm.result, wr := wrs, prevWr := prev }

theorem mkCall_spec {sm : Summary} {S : SState} {t r : Nat} {cs : List SBool} {F : Nat}
    {prev : Ranges} {c : CallRec} (h : mkCall sm S t r cs F prev = some c) :
    c.S = S ∧ c.target = t ∧ c.ret = r ∧ c.conds = cs ∧ c.F = F ∧ c.prevWr = prev := by
  unfold mkCall at h
  cases hw : resolveWrites S sm.writes with
  | none => simp [hw] at h
  | some wrs => simp [hw] at h; subst h; simp

/-- A leaf of `runWith`: the leaf, the summarised calls on its path, the ranges they wrote. -/
structure LeafW where
  leaf : Leaf
  calls : List CallRec
  wr : List (Nat × Nat × Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

def goW (img : Image) (sums : Nat → Option Summary) (cuts : List Nat) (F0 : Nat) :
    Nat → Bool → Nat → SState → List SBool → List Oblig → List CallRec → Ranges →
      Option (List LeafW)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, started, pc, S, cs, os, cl, wr =>
    if (started && cuts.contains pc) || pc == Layout.memcpyEntry then
      some [⟨⟨S, .at pc, cs, os⟩, cl, wr⟩]
    else
      match fetchI img pc with
      | none => none
      | some i =>
        match stepI img pc i S with
        | none => none
        | some (S', e, ob) =>
          match e with
          | .next pc' => goW img sums cuts F0 fuel true pc' S' cs (os ++ ob) cl wr
          | .branch c t f =>
            match goW img sums cuts F0 fuel true t S' (cs ++ [c]) (os ++ ob) cl wr,
                  goW img sums cuts F0 fuel true f S' (cs ++ [c.neg]) (os ++ ob) cl wr with
            | some l₁, some l₂ => some (l₁ ++ l₂)
            | _, _ => none
          | .call t r =>
            match sums t with
            | none => some [⟨⟨S', .call t r, cs, os ++ ob⟩, cl, wr⟩]
            | some sm =>
              match mkCall sm S' t r cs (F0 + 32 * cl.length) wr with
              | none => none
              | some c =>
                if c.okB then
                  goW img sums cuts F0 fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr)
                else none
          | .callInd t r => some [⟨⟨S', .callInd t r, cs, os ++ ob⟩, cl, wr⟩]
          | .ret t => some [⟨⟨S', .ret t, cs, os ++ ob⟩, cl, wr⟩]
          | .jumpInd t => some [⟨⟨S', .jumpInd t, cs, os ++ ob⟩, cl, wr⟩]

/-- `run` through summarised direct calls; fresh variables from `F0` on. -/
def runWith (img : Image) (sums : Nat → Option Summary) (cuts : List Nat) (F0 fuel pc : Nat)
    (S : SState) : Option (List LeafW) :=
  goW img sums cuts F0 fuel false pc S [] [] [] []

/-- The environment after a call: variables `F .. F+31` are `m`'s registers, the bytes of `wr`
are `m`'s memory. -/
def Env.havoc (env : Env) (F : Nat) (m : Machine) (wr : Ranges) : Env where
  vars i := if F ≤ i ∧ i < F + 32 then m.reg (Fin.ofNat 32 (i - F)) else env.vars i
  regions := env.regions
  mem0 r j := if wr.covers r j then (m.mem (env.base r + BitVec.ofNat 64 j)).getD 0
    else env.mem0 r j

theorem Env.agree_havoc (env : Env) (F : Nat) (m : Machine) (wr : Ranges) :
    Env.Agree env (env.havoc F m wr) F wr :=
  ⟨fun i hi => by simp [Env.havoc, Nat.not_le.mpr hi], rfl, fun r j h => by simp [Env.havoc, h]⟩

/-! ## What a summarised call must satisfy, and what a caller gets back -/

/-- The callee's return `m₂` from the entry `m₁` of call `c` (under the call's environment). -/
structure CallPost (img : Image) (X : Word → Prop) (c : CallRec) (env : Env) (m₁ m₂ : Machine) :
    Prop where
  pc : m₂.pc.toNat = c.ret
  keep : ∀ i : Fin 32, c.ov i.val = none → m₂.reg i = m₁.reg i
  result : ∀ v, c.result = some v → m₂.reg 10 = v.eval env
  frame : ∀ r j, r < c.S.regions.length → j < env.size r → Ranges.covers c.wr r j = false →
    m₂.mem (env.base r + BitVec.ofNat 64 j) = m₁.mem (env.base r + BitVec.ofNat 64 j)
  present : ∀ r j, r < c.S.regions.length → j < env.size r → Ranges.covers c.wr r j = true →
    (m₂.mem (env.base r + BitVec.ofNat 64 j)).isSome
  outside : SameOutside (fun a => InWritable env c.S a ∨ X a) m₁ m₂
  ro : RoLoaded img m₂

/-- The caller's footprint: its writable regions and `X`. -/
def FootW (env : Env) (S : SState) (X : Word → Prop) (a : Word) : Prop := InWritable env S a ∨ X a

/-- Per recorded call: from any machine at its entry reached from `m₀`, the callee returns. -/
def CallHyp (img : Image) (X : Word → Prop) (Qc : CallRec → Machine → Machine → Prop) (env₀ : Env)
    (S₀ : SState) (m₀ : Machine) (F0 : Nat) (c : CallRec) : Prop :=
  ∀ env₁ m₁ k, Env.Agree env₀ env₁ F0 c.prevWr → (∀ b ∈ c.conds, b.eval env₁ = true) →
    Env.WF env₁ c.S → Match env₁ c.S m₁ → m₁.pc.toNat = c.target → RunsIn img k m₀ m₁ →
    SameOutside (FootW env₀ S₀ X) m₀ m₁ →
    Reaches img c.bound (fun m₂ => CallPost img X c env₁ m₁ m₂ ∧ Qc c m₁ m₂) m₁

/-- A call on the path of a leaf with ranges `lwr` and final environment `env'`: the machines at
its entry and return, and how `env'` reads the return. -/
def CallFact (img : Image) (X : Word → Prop) (Qc : CallRec → Machine → Machine → Prop)
    (env₀ : Env) (F0 : Nat) (env' : Env) (lwr : Ranges) (c : CallRec) : Prop :=
  ∃ env₁ m₁ m₂, Env.Agree env₀ env₁ F0 c.prevWr ∧ Match env₁ c.S m₁ ∧
    CallPost img X c env₁ m₁ m₂ ∧ Qc c m₁ m₂ ∧
    ∃ rest, lwr = c.prevWr ++ c.wr ++ rest ∧ Env.Agree (env₁.havoc c.F m₂ c.wr) env' (c.F + 32) rest

theorem Env.Agree.symm {env env' : Env} {F : Nat} {wr : Ranges} (h : Env.Agree env env' F wr) :
    Env.Agree env' env F wr :=
  ⟨fun i hi => (h.vars i hi).symm, h.regions.symm, fun r j hj => (h.mem0 r j hj).symm⟩

/-- Every register the call keeps is `x0` or callee-saved. -/
def CallRec.keptB (c : CallRec) : Bool :=
  (List.range 32).all fun i => (c.ov i).isSome || i == 0 || (calleeSaved.map Fin.val).contains i

/-- `CallPost.keep` from `Returns` when the call replaces every register that is not callee-saved. -/
theorem CallRec.keep_of_returns {c : CallRec} {m₁ m₂ : Machine} (h : c.keptB = true)
    (hret : Returns m₁ m₂) : ∀ i : Fin 32, c.ov i.val = none → m₂.reg i = m₁.reg i := by
  intro i hi
  have hb := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simp only [hi, Option.isSome_none, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem, List.mem_map] at hb
  rcases hb with h0 | ⟨j, hj, hji⟩
  · simp [Machine.reg, h0]
  · exact hret.2 i (Fin.ext hji ▸ hj)

/-! ## The state after a summarised call -/

theorem Match.post {img : Image} {X : Word → Prop} {c : CallRec} {env : Env} {m₁ m₂ : Machine}
    (hm : Match env c.S m₁) (hok : c.okB = true) (hp : CallPost img X c env m₁ m₂) :
    Match (env.havoc c.F m₂ c.wr) c.post m₂ := by
  have ha := Env.agree_havoc env c.F m₂ c.wr
  simp only [CallRec.okB, Bool.and_eq_true] at hok
  obtain ⟨⟨hS, -⟩, hres⟩ := hok
  have hS' := hS
  simp only [SState.okB, Bool.and_eq_true] at hS'
  refine ⟨by simp [CallRec.post, SState.override, hm.regsLen], fun i => ?_, fun r j hr hj => ?_,
    fun k hk t ht => ?_⟩
  · by_cases hi0 : i.val = 0
    · simp only [SState.reg, hi0, if_true, Sym.eval, Machine.reg, BitVec.ofNat_eq_ofNat]
    · have hreg : c.post.reg i.val = (c.ov i.val).getD (c.S.reg i.val) :=
        SState.override_reg c.S c.ov hm.regsLen i hi0
      rw [hreg]
      cases hov : c.ov i.val with
      | none =>
        rw [Option.getD_none, Sym.eval_agree ha _ (SState.okB_reg hS _), hm.regs i, hp.keep i hov]
      | some s =>
        rw [Option.getD_some]
        have hov' := hov
        unfold CallRec.ov at hov'
        rw [if_neg hi0] at hov'
        split at hov'
        · next h10 =>
          have : i = 10 := Fin.ext h10.1
          subst this
          rw [hov'] at hres
          rw [Sym.eval_agree ha s (by simpa using hres), hp.result s hov']
        · split at hov'
          · cases hov'
            simp [Sym.eval, Env.havoc]
          · cases hov'
  · have hr' : r < c.S.regions.length := hr
    have hj' : j < env.size r := by rwa [ha.size] at hj
    rw [ha.base]
    show m₂.mem _ = some (memByte _ c.S.mem r j)
    cases hcov : Ranges.covers c.wr r j
    · rw [memByte_agree ha hS'.1.2 hcov, hp.frame r j hr' hj' hcov]; exact hm.mem r j hr' hj'
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hp.present r j hr' hj' hcov)
      rw [hx]
      simp [memByte, find_covers_none_okB hS'.1.2 hcov, Env.byte0, Env.havoc, hcov, hx]
  · have hk' := List.all_eq_true.mp hS'.2 k hk
    simp only [Write.okB, Bool.and_eq_true, Bool.not_eq_true'] at hk'
    rw [Env.byte0, ha.mem0 _ _ (Ranges.covers_of_overlaps hk'.2 ht), Sym.eval_agree ha _ hk'.1]
    exact hm.known k hk t ht

/-- One machine step of `stepI`. -/
theorem stepW {img : Image} {env : Env} {pc : Nat} {i : Instr} {S S' : SState} {e : StepExit}
    {ob : List Oblig} {m : Machine} (hf : fetchI img pc = some i)
    (hs : stepI img pc i S = some (S', e, ob)) (hmc : pc ≠ Layout.memcpyEntry)
    (hwf : Env.WF env S) (hm : Match env S m) (hpc : m.pc.toNat = pc) (hro : RoLoaded img m)
    (hob : ∀ o ∈ ob, o.holds env) :
    ∃ m₁, RunsIn img 1 m m₁ ∧ StepOk env S S' m m₁ e ∧ RoLoaded img m₁ ∧ Env.WF env S' := by
  obtain ⟨m₁, hx, hok⟩ := stepI_sound hs hwf hm hpc hro hob
  have hn : next img m = some (m₁, 1) := by simp [next, hpc, hmc, fetch_step hpc hf, hx]
  exact ⟨m₁, by simpa using RunsIn.step hn .refl, hok, hro.frame hwf hok.frame,
    hwf.congr hok.regions⟩

/-! ## Following one environment through a run (no machine) -/

/-- Some leaf's conditions hold under `env`; every leaf extends the path's obligations, calls and
ranges. -/
theorem goW_follow {img : Image} {sums : Nat → Option Summary} {cuts : List Nat} {F0 : Nat}
    (env : Env) :
    ∀ fuel started pc S cs os cl wr ls, goW img sums cuts F0 fuel started pc S cs os cl wr = some ls →
      (∀ c ∈ cs, c.eval env = true) →
      ∃ l ∈ ls, (∀ c ∈ l.leaf.conds, c.eval env = true) ∧ (∀ o ∈ os, o ∈ l.leaf.obligs) ∧
        (∃ nc, l.calls = cl ++ nc) ∧ (∃ rest, l.wr = wr ++ rest)
  | 0, _, _, _, _, _, _, _, _, h, _ => by simp [goW] at h
  | fuel + 1, started, pc, S, cs, os, cl, wr, ls, h, hcs => by
    unfold goW at h
    split at h
    · simp at h; subst h
      exact ⟨_, List.mem_singleton_self _, hcs, fun o ho => ho, ⟨[], by simp⟩, ⟨[], by simp⟩⟩
    · cases hf : fetchI img pc with
      | none => simp [hf] at h
      | some i =>
        simp only [hf] at h
        cases hs : stepI img pc i S with
        | none => simp [hs] at h
        | some res =>
          obtain ⟨S', e, ob⟩ := res
          simp only [hs] at h
          have leaf1 : ∀ x, some [(⟨⟨S', x, cs, os ++ ob⟩, cl, wr⟩ : LeafW)] = some ls →
              ∃ l ∈ ls, (∀ c ∈ l.leaf.conds, c.eval env = true) ∧ (∀ o ∈ os, o ∈ l.leaf.obligs) ∧
                (∃ nc, l.calls = cl ++ nc) ∧ (∃ rest, l.wr = wr ++ rest) := by
            intro x hh; simp at hh; subst hh
            exact ⟨_, List.mem_singleton_self _, hcs, fun o ho => by simp [ho], ⟨[], by simp⟩,
              ⟨[], by simp⟩⟩
          cases e with
          | next pc' =>
            obtain ⟨l, hl, hc, ho, hn, hw⟩ :=
              goW_follow env fuel true pc' S' cs (os ++ ob) cl wr ls h hcs
            exact ⟨l, hl, hc, fun o h' => ho o (by simp [h']), hn, hw⟩
          | branch c t f =>
            cases h₁ : goW img sums cuts F0 fuel true t S' (cs ++ [c]) (os ++ ob) cl wr with
            | none => simp [h₁] at h
            | some l₁ =>
              cases h₂ : goW img sums cuts F0 fuel true f S' (cs ++ [c.neg]) (os ++ ob) cl wr with
              | none => simp [h₁, h₂] at h
              | some l₂ =>
                simp [h₁, h₂] at h; subst h
                cases hce : c.eval env
                · obtain ⟨l, hl, hc, ho, hn, hw⟩ :=
                    goW_follow env fuel true f S' (cs ++ [c.neg]) (os ++ ob) cl wr l₂ h₂
                      (by intro c' hc'; simp at hc'; rcases hc' with hc' | rfl
                          · exact hcs c' hc'
                          · simp [SBool.neg_eval, hce])
                  exact ⟨l, by simp [hl], hc, fun o h' => ho o (by simp [h']), hn, hw⟩
                · obtain ⟨l, hl, hc, ho, hn, hw⟩ :=
                    goW_follow env fuel true t S' (cs ++ [c]) (os ++ ob) cl wr l₁ h₁
                      (by intro c' hc'; simp at hc'; rcases hc' with hc' | rfl
                          · exact hcs c' hc'
                          · exact hce)
                  exact ⟨l, by simp [hl], hc, fun o h' => ho o (by simp [h']), hn, hw⟩
          | call t r =>
            cases hsm : sums t with
            | none => simp only [hsm] at h; exact leaf1 _ h
            | some sm =>
              simp only [hsm] at h
              cases hc : mkCall sm S' t r cs (F0 + 32 * cl.length) wr with
              | none => simp [hc] at h
              | some c =>
                simp only [hc] at h
                split at h
                · obtain ⟨l, hl, hcd, ho, ⟨nc, hn⟩, ⟨rest, hw⟩⟩ :=
                    goW_follow env fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr) ls h hcs
                  exact ⟨l, hl, hcd, fun o h' => ho o (by simp [h']), ⟨c :: nc, by simp [hn]⟩,
                    ⟨c.wr ++ rest, by simp [hw]⟩⟩
                · simp at h
          | callInd t r => exact leaf1 _ h
          | ret t => exact leaf1 _ h
          | jumpInd t => exact leaf1 _ h

/-- Every leaf of a run extends the path's calls. -/
theorem goW_calls {img : Image} {sums : Nat → Option Summary} {cuts : List Nat} {F0 : Nat} :
    ∀ fuel started pc S cs os cl wr ls, goW img sums cuts F0 fuel started pc S cs os cl wr = some ls →
      ∀ l ∈ ls, ∃ nc, l.calls = cl ++ nc
  | 0, _, _, _, _, _, _, _, _, h => by simp [goW] at h
  | fuel + 1, started, pc, S, cs, os, cl, wr, ls, h => by
    unfold goW at h
    split at h
    · simp at h; subst h; intro l hl; simp at hl; subst hl; exact ⟨[], by simp⟩
    · cases hf : fetchI img pc with
      | none => simp [hf] at h
      | some i =>
        simp only [hf] at h
        cases hs : stepI img pc i S with
        | none => simp [hs] at h
        | some res =>
          obtain ⟨S', e, ob⟩ := res
          simp only [hs] at h
          have leaf1 : ∀ x, some [(⟨⟨S', x, cs, os ++ ob⟩, cl, wr⟩ : LeafW)] = some ls →
              ∀ l ∈ ls, ∃ nc, l.calls = cl ++ nc := by
            intro x hh l hl; simp at hh; subst hh; simp at hl; subst hl; exact ⟨[], by simp⟩
          cases e with
          | next pc' => exact goW_calls fuel true pc' S' cs (os ++ ob) cl wr ls h
          | branch c t f =>
            cases h₁ : goW img sums cuts F0 fuel true t S' (cs ++ [c]) (os ++ ob) cl wr with
            | none => simp [h₁] at h
            | some l₁ =>
              cases h₂ : goW img sums cuts F0 fuel true f S' (cs ++ [c.neg]) (os ++ ob) cl wr with
              | none => simp [h₁, h₂] at h
              | some l₂ =>
                simp [h₁, h₂] at h; subst h
                intro l hl
                rcases List.mem_append.mp hl with hl | hl
                · exact goW_calls fuel true t S' _ _ cl wr l₁ h₁ l hl
                · exact goW_calls fuel true f S' _ _ cl wr l₂ h₂ l hl
          | call t r =>
            cases hsm : sums t with
            | none => simp only [hsm] at h; exact leaf1 _ h
            | some sm =>
              simp only [hsm] at h
              cases hc : mkCall sm S' t r cs (F0 + 32 * cl.length) wr with
              | none => simp [hc] at h
              | some c =>
                simp only [hc] at h
                split at h
                · intro l hl
                  obtain ⟨nc, hn⟩ :=
                    goW_calls fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr) ls h l hl
                  exact ⟨c :: nc, by simp [hn]⟩
                · simp at h
          | callInd t r => exact leaf1 _ h
          | ret t => exact leaf1 _ h
          | jumpInd t => exact leaf1 _ h

/-! ## Soundness -/

section Sound
variable {img : Image} {sums : Nat → Option Summary} {cuts : List Nat} {F0 : Nat}
  {X : Word → Prop} {Qc : CallRec → Machine → Machine → Prop} {env₀ : Env} {S₀ : SState}
  {m₀ : Machine}

variable (img X Qc env₀ S₀ m₀ F0) in
/-- What `goW_sound` concludes for the leaves `ls` of a run under `env`, with path calls `cl` and
ranges `wr` so far. -/
def ConclW (env : Env) (cl : List CallRec) (wr : Ranges) (ls : List LeafW) : Prop :=
  ∃ l ∈ ls, ∃ env', (∃ rest, l.wr = wr ++ rest ∧ Env.Agree env env' (F0 + 32 * cl.length) rest) ∧
    (l.calls = cl → env' = env) ∧ (∀ c ∈ l.leaf.conds, c.eval env' = true) ∧
    ((∀ o ∈ l.leaf.obligs, o.holds env') →
      (∃ nc, l.calls = cl ++ nc ∧ ∀ c ∈ nc, CallFact img X Qc env₀ F0 env' l.wr c) ∧
      ∃ k m', S₀.steps + k ≤ l.leaf.S.steps ∧ RunsIn img k m₀ m' ∧ Match env' l.leaf.S m' ∧
        ExitOk env' l.leaf.exit m' ∧ SameOutside (FootW env₀ S₀ X) m₀ m' ∧
        (l.calls = [] → SameOutside (InWritable env₀ S₀) m₀ m'))

theorem ConclW.mono {env : Env} {cl : List CallRec} {wr : Ranges} {ls ls' : List LeafW}
    (h : ∀ l ∈ ls, l ∈ ls') (hc : ConclW img F0 X Qc env₀ S₀ m₀ env cl wr ls) :
    ConclW img F0 X Qc env₀ S₀ m₀ env cl wr ls' :=
  let ⟨l, hl, rest⟩ := hc; ⟨l, h l hl, rest⟩

/-- The leaf right here. -/
theorem ConclW.here {env : Env} {cl : List CallRec} {wr : Ranges} {ls : List LeafW} {l : LeafW}
    (hl : l ∈ ls) (hcl : l.calls = cl) (hwr : l.wr = wr) (hc : ∀ c ∈ l.leaf.conds, c.eval env = true)
    {k : Nat} {m' : Machine} (hst : S₀.steps + k ≤ l.leaf.S.steps) (hr : RunsIn img k m₀ m')
    (hm : Match env l.leaf.S m') (he : ExitOk env l.leaf.exit m')
    (hfo : SameOutside (FootW env₀ S₀ X) m₀ m')
    (hpl : l.calls = [] → SameOutside (InWritable env₀ S₀) m₀ m') :
    ConclW img F0 X Qc env₀ S₀ m₀ env cl wr ls :=
  ⟨l, hl, env, ⟨[], by simp [hwr], Env.Agree.refl _ _ _⟩, fun _ => rfl, hc,
    fun _ => ⟨⟨[], by simp [hcl], by simp⟩, k, m', hst, hr, hm, he, hfo, hpl⟩⟩

/-- A failing obligation on the path: any leaf the conditions select will do. -/
theorem ConclW.vac {env : Env} {cl : List CallRec} {wr : Ranges} {ls : List LeafW} {os ob : List Oblig}
    (hob : ¬ ∀ o ∈ ob, o.holds env)
    (hf : ∃ l ∈ ls, (∀ c ∈ l.leaf.conds, c.eval env = true) ∧ (∀ o ∈ os ++ ob, o ∈ l.leaf.obligs) ∧
      (∃ nc, l.calls = cl ++ nc) ∧ (∃ rest, l.wr = wr ++ rest)) :
    ConclW img F0 X Qc env₀ S₀ m₀ env cl wr ls := by
  obtain ⟨l, hl, hc, ho, -, rest, hw⟩ := hf
  refine ⟨l, hl, env, ⟨rest, hw, Env.Agree.refl _ _ _⟩, fun _ => rfl, hc, fun hall => absurd ?_ hob⟩
  exact fun o h' => hall o (ho o (by simp [h']))

theorem goW_sound :
    ∀ fuel started pc S cs os cl wr ls, goW img sums cuts F0 fuel started pc S cs os cl wr = some ls →
    (∀ l ∈ ls, ∀ c ∈ l.calls, CallHyp img X Qc env₀ S₀ m₀ F0 c) →
    ∀ env m k, Env.Agree env₀ env F0 wr → (∀ c ∈ cs, c.eval env = true) → Env.WF env S →
      Match env S m → m.pc.toNat = pc → RoLoaded img m → RunsIn img k m₀ m →
      S₀.steps + k ≤ S.steps → SameOutside (FootW env₀ S₀ X) m₀ m → S.regions = S₀.regions →
      (cl = [] → SameOutside (InWritable env₀ S₀) m₀ m) →
      ConclW img F0 X Qc env₀ S₀ m₀ env cl wr ls
  | 0, _, _, _, _, _, _, _, _, h, _ => by simp [goW] at h
  | fuel + 1, started, pc, S, cs, os, cl, wr, ls, h, hcall => by
    intro env m k hag hcs hwf hm hpc hro hrun hst hfoot hreg hplain
    -- a step inside the caller's writable regions stays inside its footprint
    have footStep : ∀ {S' : SState} m₁, S'.regions = S₀.regions →
        SameOutside (InWritable env S') m m₁ → SameOutside (FootW env₀ S₀ X) m₀ m₁ :=
      fun m₁ hr h => SameOutside.trans hfoot fun a ha =>
        h a fun hw => ha (.inl (InWritable.of_regions hag.regions hr hw))
    have plainStep : ∀ {S' : SState} m₁, S'.regions = S₀.regions →
        SameOutside (InWritable env S') m m₁ → cl = [] → SameOutside (InWritable env₀ S₀) m₀ m₁ :=
      fun m₁ hr h h0 => SameOutside.trans (hplain h0) fun a ha =>
        h a fun hw => ha (InWritable.of_regions hag.regions hr hw)
    unfold goW at h
    split at h
    · simp at h; subst h
      exact ConclW.here (List.mem_singleton_self _) rfl rfl hcs (by omega) hrun hm hpc hfoot
        fun h => hplain h
    · next hcut =>
      have hmc : pc ≠ Layout.memcpyEntry := by intro e; apply hcut; simp [e]
      cases hf : fetchI img pc with
      | none => simp [hf] at h
      | some i =>
        simp only [hf] at h
        cases hs : stepI img pc i S with
        | none => simp [hs] at h
        | some res =>
          obtain ⟨S', e, ob⟩ := res
          simp only [hs] at h
          -- a leaf right after this instruction
          have leafHere : ∀ x, (∀ m₁, StepExitOk env e m₁ → ExitOk env x m₁) →
              some [(⟨⟨S', x, cs, os ++ ob⟩, cl, wr⟩ : LeafW)] = some ls →
              ConclW img F0 X Qc env₀ S₀ m₀ env cl wr ls := by
            intro x hx hh
            simp at hh; subst hh
            by_cases hob : ∀ o ∈ ob, o.holds env
            · obtain ⟨m₁, h1, hok, -, -⟩ := stepW hf hs hmc hwf hm hpc hro hob
              exact ConclW.here (List.mem_singleton_self _) rfl rfl hcs
                (by show _ ≤ S'.steps; rw [hok.steps]; omega) (hrun.trans h1) hok.hmatch
                (hx m₁ hok.exit) (footStep m₁ hreg hok.frame) (fun h => plainStep m₁ hreg hok.frame h)
            · exact ConclW.vac hob ⟨_, List.mem_singleton_self _, hcs, fun o ho => ho, ⟨[], by simp⟩,
                ⟨[], by simp⟩⟩
          cases e with
          | next pc' =>
            by_cases hob : ∀ o ∈ ob, o.holds env
            · obtain ⟨m₁, h1, hok, hro₁, hwf₁⟩ := stepW hf hs hmc hwf hm hpc hro hob
              exact goW_sound fuel true pc' S' cs (os ++ ob) cl wr ls h hcall env m₁ (k + 1) hag hcs
                hwf₁ hok.hmatch hok.exit hro₁ (hrun.trans h1) (by rw [hok.steps]; omega)
                (footStep m₁ hreg hok.frame) (hok.regions.trans hreg) (plainStep m₁ hreg hok.frame)
            · exact ConclW.vac hob (goW_follow env fuel true pc' S' cs (os ++ ob) cl wr ls h hcs)
          | branch c t f =>
            cases h₁ : goW img sums cuts F0 fuel true t S' (cs ++ [c]) (os ++ ob) cl wr with
            | none => simp [h₁] at h
            | some l₁ =>
              cases h₂ : goW img sums cuts F0 fuel true f S' (cs ++ [c.neg]) (os ++ ob) cl wr with
              | none => simp [h₁, h₂] at h
              | some l₂ =>
                simp [h₁, h₂] at h; subst h
                have hc₂ : c.eval env = false → ∀ c' ∈ cs ++ [c.neg], c'.eval env = true := by
                  intro hce c' hc'; simp at hc'; rcases hc' with hc' | rfl
                  · exact hcs c' hc'
                  · simp [SBool.neg_eval, hce]
                have hc₁ : c.eval env = true → ∀ c' ∈ cs ++ [c], c'.eval env = true := by
                  intro hce c' hc'; simp at hc'; rcases hc' with hc' | rfl
                  · exact hcs c' hc'
                  · exact hce
                by_cases hob : ∀ o ∈ ob, o.holds env
                · obtain ⟨m₁, h1, hok, hro₁, hwf₁⟩ := stepW hf hs hmc hwf hm hpc hro hob
                  have hpc₁ := hok.exit
                  simp only [StepExitOk] at hpc₁
                  cases hce : c.eval env
                  · refine ConclW.mono (fun l hl => by simp [hl]) (goW_sound fuel true f S'
                      (cs ++ [c.neg]) (os ++ ob) cl wr l₂ h₂ (fun l hl => hcall l (by simp [hl]))
                      env m₁ (k + 1) hag (hc₂ hce) hwf₁ hok.hmatch (by simpa [hce] using hpc₁) hro₁
                      (hrun.trans h1) (by rw [hok.steps]; omega)
                      (footStep m₁ hreg hok.frame) (hok.regions.trans hreg) (plainStep m₁ hreg hok.frame))
                  · refine ConclW.mono (fun l hl => by simp [hl]) (goW_sound fuel true t S'
                      (cs ++ [c]) (os ++ ob) cl wr l₁ h₁ (fun l hl => hcall l (by simp [hl]))
                      env m₁ (k + 1) hag (hc₁ hce) hwf₁ hok.hmatch (by simpa [hce] using hpc₁) hro₁
                      (hrun.trans h1) (by rw [hok.steps]; omega)
                      (footStep m₁ hreg hok.frame) (hok.regions.trans hreg) (plainStep m₁ hreg hok.frame))
                · cases hce : c.eval env
                  · obtain ⟨l, hl, rest⟩ := goW_follow env fuel true f S' (cs ++ [c.neg]) (os ++ ob)
                      cl wr l₂ h₂ (hc₂ hce)
                    exact ConclW.vac hob ⟨l, by simp [hl], rest⟩
                  · obtain ⟨l, hl, rest⟩ := goW_follow env fuel true t S' (cs ++ [c]) (os ++ ob)
                      cl wr l₁ h₁ (hc₁ hce)
                    exact ConclW.vac hob ⟨l, by simp [hl], rest⟩
          | call t r =>
            cases hsm : sums t with
            | none => simp only [hsm] at h; exact leafHere (.call t r) (fun _ h => h) h
            | some sm =>
              simp only [hsm] at h
              cases hmk : mkCall sm S' t r cs (F0 + 32 * cl.length) wr with
              | none => simp [hmk] at h
              | some c =>
                simp only [hmk] at h
                split at h
                · next hokc =>
                  obtain ⟨hcS, hct, hcr, hcc, hcF, hcp⟩ := mkCall_spec hmk
                  by_cases hob : ∀ o ∈ ob, o.holds env
                  · obtain ⟨m₁, h1, hok, hro₁, hwf₁⟩ := stepW hf hs hmc hwf hm hpc hro hob
                    have hreg₁ : c.S.regions = S₀.regions := by rw [hcS]; exact hok.regions.trans hreg
                    have hm₁c : Match env c.S m₁ := hcS ▸ hok.hmatch
                    obtain ⟨l₀, hl₀, -, -, ⟨nc₀, hnc₀⟩, -⟩ :=
                      goW_follow env fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr) ls h hcs
                    obtain ⟨k₂, m₂, hk₂, hr₂, hpost, hq⟩ := hcall l₀ hl₀ c (by rw [hnc₀]; simp) env m₁
                      (k + 1) (by rw [hcp]; exact hag) (by rw [hcc]; exact hcs) (hcS ▸ hwf₁) hm₁c
                      (by rw [hct]; exact hok.exit) (hrun.trans h1)
                      (footStep m₁ hreg hok.frame)
                    have hagh := Env.agree_havoc env c.F m₂ c.wr
                    have hcok : c.conds.all (SBool.okB c.F c.wr) = true := by
                      simp only [CallRec.okB, Bool.and_eq_true] at hokc; exact hokc.1.2
                    have hcs₂ : ∀ b ∈ cs, b.eval (env.havoc c.F m₂ c.wr) = true := fun b hb => by
                      rw [SBool.eval_agree hagh b (List.all_eq_true.mp hcok b (hcc ▸ hb))]
                      exact hcs b hb
                    have hwf₂ : Env.WF (env.havoc c.F m₂ c.wr) c.post :=
                      (Env.WF.of_regions (env' := env.havoc c.F m₂ c.wr) (hcS ▸ hwf₁ : Env.WF env c.S) rfl).congr rfl
                    have hfoot₂ : SameOutside (FootW env₀ S₀ X) m₀ m₂ :=
                      SameOutside.trans (footStep m₁ hreg hok.frame)
                        fun a ha => hpost.outside a fun h' => ha (h'.elim
                          (fun hw => .inl (InWritable.of_regions hag.regions hreg₁ hw)) .inr)
                    have hst₂ : S₀.steps + (k + 1 + k₂) ≤ c.post.steps := by
                      show _ ≤ c.S.steps + c.bound
                      rw [hcS, hok.steps]; omega
                    have IH := goW_sound fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr) ls h
                      hcall (env.havoc c.F m₂ c.wr) m₂ (k + 1 + k₂)
                      (hag.trans hagh (by rw [hcF]; omega)) hcs₂ hwf₂ (Match.post hm₁c hokc hpost)
                      (by rw [hpost.pc, hcr]) hpost.ro ((hrun.trans h1).trans hr₂) hst₂ hfoot₂
                      hreg₁ (fun h => absurd h (by simp))
                    obtain ⟨l, hl, env', ⟨rest, hw, hag'⟩, -, hcd, himp⟩ := IH
                    obtain ⟨nc₁, hnc₁⟩ :=
                      goW_calls fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr) ls h l hl
                    have e32 : F0 + 32 * (cl ++ [c]).length = c.F + 32 := by
                      simp [hcF]; omega
                    rw [e32] at hag'
                    have hagF : Env.Agree env (env.havoc c.F m₂ c.wr) (F0 + 32 * cl.length) c.wr := by
                      rw [← hcF]; exact hagh
                    refine ⟨l, hl, env', ⟨c.wr ++ rest, by rw [hw, List.append_assoc],
                      hagF.trans hag' (by omega)⟩, fun h' => ?_, hcd, fun hob' => ?_⟩
                    · have := congrArg List.length (hnc₁.symm.trans h')
                      simp at this <;> omega
                    obtain ⟨⟨nc, hnc, hfacts⟩, k', m', a1, a2, a3, a4, a5, -⟩ := himp hob'
                    refine ⟨⟨c :: nc, by rw [hnc]; simp, fun c' hc' => ?_⟩, k', m', a1, a2, a3, a4, a5,
                      fun h0 => ?_⟩
                    rotate_left
                    · rw [hnc] at h0; simp at h0
                    rcases List.mem_cons.mp hc' with rfl | hc'
                    · exact ⟨env, m₁, m₂, by rw [hcp]; exact hag, hm₁c, hpost, hq, rest,
                        by rw [hw, hcp, List.append_assoc], hag'⟩
                    · exact hfacts c' hc'
                  · exact ConclW.vac hob (by
                      obtain ⟨l, hl, hcd, ho, ⟨nc, hnc⟩, ⟨rest, hw⟩⟩ :=
                        goW_follow env fuel true r c.post cs (os ++ ob) (cl ++ [c]) (wr ++ c.wr) ls h hcs
                      exact ⟨l, hl, hcd, ho, ⟨c :: nc, by simp [hnc]⟩, ⟨c.wr ++ rest, by simp [hw]⟩⟩)
                · simp at h
          | callInd t r => exact leafHere (.callInd t r) (fun _ h => h) h
          | ret t => exact leafHere (.ret t) (fun _ h => h) h
          | jumpInd t => exact leafHere (.jumpInd t) (fun _ h => h) h

/-- Soundness of `runWith`: some leaf's conditions hold under an extension `env'` of `env` by the
calls' fresh variables and written bytes; if its obligations hold, every call on its path has its
`CallFact` and the machine runs to a state matching the leaf within the leaf's steps, changing
memory only in the caller's writable regions and `X`. -/
theorem runWith_sound {fuel pc : Nat} {S : SState} {ls : List LeafW} {env : Env} {m : Machine}
    (h : runWith img sums cuts F0 fuel pc S = some ls)
    (hcall : ∀ l ∈ ls, ∀ c ∈ l.calls, CallHyp img X Qc env S m F0 c)
    (hwf : Env.WF env S) (hm : Match env S m) (hpc : m.pc.toNat = pc) (hro : RodataLoaded img m) :
    ∃ l ∈ ls, ∃ env', Env.Agree env env' F0 l.wr ∧ (l.calls = [] → env' = env) ∧
      (∀ c ∈ l.leaf.conds, c.eval env' = true) ∧
      ((∀ o ∈ l.leaf.obligs, o.holds env') →
        (∀ c ∈ l.calls, CallFact img X Qc env F0 env' l.wr c) ∧
        ∃ k m', k ≤ l.leaf.S.steps - S.steps ∧ RunsIn img k m m' ∧ Match env' l.leaf.S m' ∧
          ExitOk env' l.leaf.exit m' ∧ SameOutside (FootW env S X) m m' ∧
          (l.calls = [] → SameOutside (InWritable env S) m m')) := by
  obtain ⟨l, hl, env', ⟨rest, hw, hag⟩, henv, hc, himp⟩ :=
    goW_sound fuel false pc S [] [] [] [] ls h hcall env m 0 (Env.Agree.refl _ _ _) (by simp) hwf hm
      hpc (fun a b _ _ hb => hro a b hb) .refl (by omega) (fun _ _ => rfl) rfl (fun _ _ _ => rfl)
  refine ⟨l, hl, env', by simpa [hw] using hag, henv, hc, fun ho => ?_⟩
  obtain ⟨⟨nc, hnc, hf⟩, k, m', hk, hr, hm', he, hfo, hpl⟩ := himp ho
  exact ⟨fun c hc' => hf c (by simpa [hnc] using hc'), k, m', by omega, hr, hm', he, hfo, hpl⟩

/-- `runWith_sound` as a `Reaches` step: each leaf whose conditions hold meets its obligations
and continues to `Q` within the remaining budget. -/
theorem runWith_reaches {fuel pc : Nat} {S : SState} {ls : List LeafW} {env : Env} {m : Machine}
    {b : Nat} {Q : Machine → Prop}
    (h : runWith img sums cuts F0 fuel pc S = some ls)
    (hcall : ∀ l ∈ ls, ∀ c ∈ l.calls, CallHyp img X Qc env S m F0 c)
    (hwf : Env.WF env S) (hm : Match env S m) (hpc : m.pc.toNat = pc) (hro : RodataLoaded img m)
    (hleaf : ∀ l ∈ ls, ∀ env', Env.Agree env env' F0 l.wr →
      (∀ c ∈ l.leaf.conds, c.eval env' = true) →
      (∀ o ∈ l.leaf.obligs, o.holds env') ∧ l.leaf.S.steps - S.steps ≤ b ∧
      ((∀ c ∈ l.calls, CallFact img X Qc env F0 env' l.wr c) → ∀ m', Match env' l.leaf.S m' →
        ExitOk env' l.leaf.exit m' → SameOutside (FootW env S X) m m' →
        Reaches img (b - (l.leaf.S.steps - S.steps)) Q m')) :
    Reaches img b Q m := by
  obtain ⟨l, hl, env', hag, -, hc, himp⟩ := runWith_sound h hcall hwf hm hpc hro
  obtain ⟨hob, hb, hk⟩ := hleaf l hl env' hag hc
  obtain ⟨hf, k, m', hkle, hr, hm', he, hfo, -⟩ := himp hob
  obtain ⟨k₂, m'', hk₂, hr₂, hQ⟩ := hk hf m' hm' he hfo
  exact ⟨k + k₂, m'', by omega, hr.trans hr₂, hQ⟩

end Sound

end ZesuExec.Sym
