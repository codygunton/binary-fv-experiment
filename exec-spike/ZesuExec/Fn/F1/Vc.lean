import ZesuExec.Fn.F1.Lemmas
import ZesuExec.Fn.F0.Summary
import ZesuExec.Sym.Join
import ZesuExec.Vc.Tactics
import ZesuExec.Vc.AssembleW
import ZesuExec.Vc.RunWith

/-!
# F1 in the obligation framework

Plan `F1` (a `PlanW`: runs by `runWith`): the entry and three call return sites: after `alloc`
(`0x800cb55c`), after `memcpy` (`0x800cb588`), after `free` (`0x800cb5a8`). `remap` (F0) is not a
cut: the entry run continues through its call with `F0.summary` (it returns null and writes only
its frame, `X`), so entry leaves 4–6 carry the call, whose `CallGoal` is discharged by
`F0.f0_spec` and `F0.callPost` (programme plan S5 probe 2). `σ` = `Sig`: the allocator
assumptions, the allocator list, the items and the entry machine.

Cut states: the entry state `S0`. The other three are join cuts (programme plan S5 probe 1):
their state is `generalise F Ss 32` of the leaf states `Ss` that reach them (`Sym/Join.lean`),
their `Env` is `envJ F Ss` = `joinEnv 32 F Ss` over the entry `Env`: entry variables from the
entry machine, `var (F + i)` = register `i` at the cut, frame bytes from the machine at the cut,
header and allocator-object bytes from the entry. After `alloc` two paths meet (capacity 0, or
after `remap`); after `memcpy` one; after `free` two (capacity 0 skips `free`). Each assertion is
machine facts, `RodataLoaded`, and `JoinIn`: some incoming state matches the machine under an
`Env` that agrees with the entry `Env`; the cut lemmas are `cut_auto`'s (`JoinIn.ok`).
So each segment is run once, not once per path. Budgets: 197 at the entry (`remap`'s 9 included
in the leaves' steps), `103`/`78` after `alloc`, `18`/`67` after `memcpy` (capacity 0 /
positive), 17 after `free`.
-/

namespace ZesuExec.Fn.F1
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

/-! ## Runs and join states -/

def cutPcs : List Nat := [entry, 0x800cb55c, 0x800cb588, 0x800cb5a8]

/-- `remap` (F0) as a summary: it returns null and writes only its own frame. -/
def sums (t : Nat) : Option Summary := if t = F0.entry then some F0.summary else none

sym_runw runE := runWith zesuImage sums cutPcs 64 400 entry S0

/-- After `alloc`, from capacity 0 (entry leaf 2) or after `remap` (entry leaf 5). -/
def S2a : SState := (runE_leaves[2]!).leaf.S.override (callOv (runE_leaves[2]!).leaf.S 200 none)
def S2b : SState := (runE_leaves[5]!).leaf.S.override (callOv (runE_leaves[5]!).leaf.S 300 none)
def SJ2 : SState := generalise 500 [S2a, S2b] 32
sym_runw runJ2 := runWith zesuImage sums cutPcs 64 400 0x800cb55c SJ2

/-- After `memcpy` (leaf 0 of `runJ2`). -/
def S3 : SState := (runJ2_leaves[0]!).leaf.S
def SJ3 : SState := generalise 600 [S3] 32
sym_runw runJ3 := runWith zesuImage sums cutPcs 64 400 0x800cb588 SJ3

/-- At `0x800cb5a8`, with capacity 0 (leaf 0 of `runJ3`) or after `free` (leaf 1). -/
def S4a : SState := (runJ3_leaves[0]!).leaf.S
def S4b : SState := (runJ3_leaves[1]!).leaf.S.override (callOv (runJ3_leaves[1]!).leaf.S 650 none)
def SJ4 : SState := generalise 700 [S4a, S4b] 32
sym_runw runJ4 := runWith zesuImage sums cutPcs 64 400 0x800cb5a8 SJ4

/-! ## Parameters, environments, assertions -/

structure Sig where
  A : AllocContract zesuImage
  L : List (Word × Nat)
  items : List Byte
  m : Machine

/-- Capacity and request of the entry machine. -/
abbrev capOf (m : Machine) : Nat := (wordAt m (m.reg 10 + 16)).toNat
abbrev reqOf (m : Machine) : Nat := (m.reg 12).toNat

/-- At a join: `joinEnv` over the entry `Env`. -/
def envJ (F : Nat) (Ss : List SState) (g : Sig) : Machine → Env := joinEnv 32 F Ss (env0 g.m)

theorem envJ_ok {F : Nat} {Ss : List SState} (hF : 32 ≤ F) (h1 : dirtyB Ss 1 = false)
    (h2 : dirtyB Ss 2 = false) (g : Sig) (mh : Machine) : EnvOk g.m (envJ F Ss g mh) where
  vars i := by simp [envJ, joinEnv, entryEnv, i.isLt]
  base0 := by simp [envJ, joinEnv, Env.base, entryEnv, shape]
  base1 := by simp [envJ, joinEnv, Env.base, entryEnv, shape]
  size1 := by simp [envJ, joinEnv, Env.size, entryEnv, shape]
  mem1 j := by simp [envJ, joinEnv, h1, entryEnv, shape]
  size0 := by simp [envJ, joinEnv, Env.size, entryEnv, shape]
  base2 := by simp [envJ, joinEnv, Env.base, entryEnv, shape]
  size2 := by simp [envJ, joinEnv, Env.size, entryEnv, shape]
  len := by simp [envJ, joinEnv, entryEnv, shape]
  mem2 j := by simp [envJ, joinEnv, h2, entryEnv, shape]

theorem envJ_fresh {F : Nat} {Ss : List SState} (hF : 32 ≤ F) (g : Sig) (mh : Machine)
    (i : Fin 32) : (envJ F Ss g mh).vars (F + i.val) = mh.reg i :=
  joinEnv_fresh hF Ss _ mh i

/-- An `Env` extending the entry's agrees with it where a join that writes the frame keeps
terms. -/
theorem EnvOk.agrees {m : Machine} {env : Env} {Ss : List SState} (he : EnvOk m env)
    (hd : dirtyB Ss 0 = true) : Agrees 32 Ss (env0 m) env where
  vars i hi := by
    rw [he.vars ⟨i, hi⟩]; simp [entryEnv]; congr 1; exact Fin.ext (Nat.mod_eq_of_lt hi).symm
  regions := by rw [he.regions]; rfl
  mem0 r hr hdr j := by
    have hr3 : r < 3 := by simpa [entryEnv, shape] using hr
    match r, hr3, hdr with
    | 0, _, hdr => rw [hd] at hdr; cases hdr
    | 1, _, _ => rw [he.mem1]; simp [entryEnv, shape]
    | 2, _, _ => rw [he.mem2]; simp [entryEnv, shape]

def AE (g : Sig) (m : Machine) : Prop := m = g.m ∧ m.pc.toNat = entry ∧ Pre g.A g.L g.items m

/-- After `alloc`: its answer in `a0`, the grown capacity in `s6`. -/
def AJ2 (g : Sig) (m2 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ m2.pc.toNat = 0x800cb55c ∧ Inv g.A g.L g.m m2 ∧
  capOf g.m < reqOf g.m ∧ BytesAt m2 (wordAt g.m (g.m.reg 10)) g.items ∧ ScratchSame g.m m2 ∧
  AllocOut g.A g.L (grown (reqOf g.m) * elemBytes) m2 ∧
  m2.reg 22 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧ RodataLoaded zesuImage m2 ∧
  JoinIn 32 [S2a, S2b] (env0 g.m) m2

/-- After `memcpy`, for the new buffer `p'`. -/
def Copied (g : Sig) (m4 : Machine) (p' : Word) : Prop :=
  0 < p'.toNat ∧ RamRange p' (grown (reqOf g.m) * elemBytes) ∧ BytesAt m4 p' g.items ∧
  BytesAt m4 (BitVec.ofNat 64 Layout.extraParams)
    (wordBytes (BitVec.ofNat 64 ((wordAt g.m (g.m.reg 10 + 8)).toNat * elemBytes))) ∧
  g.A.Heap (g.L ++ [(p', grown (reqOf g.m) * elemBytes)]) m4 ∧
  (∀ a, g.A.Priv (g.L ++ [(p', grown (reqOf g.m) * elemBytes)]) a → g.A.Priv g.L a) ∧
  (∀ a, InRange p' (grown (reqOf g.m) * elemBytes) a → g.A.Priv g.L a)

/-- After `memcpy`: the new buffer in `s3`, the grown capacity in `s6`. -/
def AJ3 (g : Sig) (m3 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ m3.pc.toNat = 0x800cb588 ∧ Inv g.A g.L g.m m3 ∧
  capOf g.m < reqOf g.m ∧ m3.reg 22 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧
  Copied g m3 (m3.reg 19) ∧ RodataLoaded zesuImage m3 ∧ JoinIn 32 [S3] (env0 g.m) m3

/-- The allocator list at the end of the growing paths. -/
def newL (g : Sig) (p' : Word) : List (Word × Nat) :=
  (if 0 < capOf g.m then g.L.erase (wordAt g.m (g.m.reg 10), capOf g.m * elemBytes) else g.L) ++
    [(p', grown (reqOf g.m) * elemBytes)]

/-- After `free` (or its skip), for the new buffer `p'`. -/
def Freed (g : Sig) (m4 : Machine) (p' : Word) : Prop :=
  0 < p'.toNat ∧ RamRange p' (grown (reqOf g.m) * elemBytes) ∧ BytesAt m4 p' g.items ∧
  BytesAt m4 (BitVec.ofNat 64 Layout.extraParams)
    (wordBytes (BitVec.ofNat 64 ((wordAt g.m (g.m.reg 10 + 8)).toNat * elemBytes))) ∧
  g.A.Heap (newL g p') m4 ∧
  (∀ a, g.A.Priv (newL g p') a →
    g.A.Priv g.L a ∨ InRange (wordAt g.m (g.m.reg 10)) (capOf g.m * elemBytes) a) ∧
  (∀ a, InRange p' (grown (reqOf g.m) * elemBytes) a → g.A.Priv g.L a)

/-- At `0x800cb5a8`: the new buffer in `s3`, the grown capacity in `s6`. -/
def AJ4 (g : Sig) (m4 : Machine) : Prop :=
  Entry g.A g.L g.items g.m ∧ m4.pc.toNat = 0x800cb5a8 ∧ Inv g.A g.L g.m m4 ∧
  capOf g.m < reqOf g.m ∧ m4.reg 22 = BitVec.ofNat 64 (grown (reqOf g.m)) ∧
  Freed g m4 (m4.reg 19) ∧ RodataLoaded zesuImage m4 ∧ JoinIn 32 [S4a, S4b] (env0 g.m) m4

def cE : Cut Sig := ⟨entry, S0, AE, fun _ m => env0 m, fun _ _ => bound⟩
def cJ2 : Cut Sig :=
  ⟨0x800cb55c, SJ2, AJ2, envJ 500 [S2a, S2b], fun g _ => if capOf g.m = 0 then 103 else 78⟩
def cJ3 : Cut Sig :=
  ⟨0x800cb588, SJ3, AJ3, envJ 600 [S3], fun g _ => if capOf g.m = 0 then 18 else 67⟩
def cJ4 : Cut Sig := ⟨0x800cb5a8, SJ4, AJ4, envJ 700 [S4a, S4b], fun _ _ => 17⟩

/-! ## Callees -/

def allocC : Callee Sig zesuImage where
  entry := allocEntry
  bound := 53
  Pre := fun g _ m => g.A.Heap g.L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧
    (m.reg 12).toNat ≤ 4 ∧ StackOk m 16 ∧ RetAligned m ∧ CalleeFrameFree (g.A.Priv g.L) m
  Post := fun g _ m m' => (Returns m m' ∧
      SameOutside (fun a => g.A.Priv g.L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
      ((m'.reg 10 = 0 ∧ g.A.Heap g.L m') ∨
       (m'.reg 10 ≠ 0 ∧ g.A.Heap (g.L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
        RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
        (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → g.A.Priv g.L a) ∧
        (∀ a, g.A.Priv (g.L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → g.A.Priv g.L a)))) ∧
    Preserved m m'
  spec := fun g _ m hpc hpre => Reaches.preserve (g.A.alloc_spec g.L m hpc hpre)

/-- `free` of a block of the allocator list `L'` (the index: at F1's call, the entry list and the
new buffer in `s3`). -/
def freeC : Callee Sig zesuImage where
  X := List (Word × Nat)
  entry := freeEntry
  bound := 42
  Pre := fun g L' m => g.A.Heap L' m ∧ (m.reg 11, (m.reg 12).toNat) ∈ L' ∧
    0 < (m.reg 12).toNat ∧ (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 4 ∧
    ((m.reg 13).toNat ≤ 3 ∨ 8 < (m.reg 12).toNat) ∧ StackOk m 16 ∧ RetAligned m ∧
    CalleeFrameFree (g.A.Priv L') m ∧
    ∀ a, InRange (m.reg 2 - 16) 16 a → ¬ InRange (m.reg 11) (m.reg 12).toNat a
  Post := fun g L' m m' => (Returns m m' ∧
      SameOutside (fun a => g.A.Priv L' a ∨ InRange (m.reg 11) (m.reg 12).toNat a ∨
        InRange (m.reg 2 - 16) 16 a) m m' ∧
      g.A.Heap (L'.erase (m.reg 11, (m.reg 12).toNat)) m' ∧
      (∀ a, g.A.Priv (L'.erase (m.reg 11, (m.reg 12).toNat)) a →
        g.A.Priv L' a ∨ InRange (m.reg 11) (m.reg 12).toNat a)) ∧ Preserved m m'
  spec := fun g L' m hpc hpre => Reaches.preserve (g.A.free_spec L' m hpc hpre)

/-- `Post` and, on the no-growth branch, the list's items unchanged: the early return writes
only F1's frame and the header (`f1_spec_keep`). -/
def PostKeep (A : AllocContract zesuImage) (L : List (Word × Nat)) (items : List Byte)
    (m m' : Machine) : Prop :=
  Post A L items m m' ∧
  ((m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat → BytesAt m' (wordAt m (m.reg 10)) items)

def vcPlan : PlanW Sig zesuImage where
  cuts := [cE, cJ2, cJ3, cJ4]
  fuel := 400
  leaves := fun _ => []
  callee := fun r =>
    if r = 0x800cb55c then some allocC
    else if r = 0x800cb588 then some (Callee.memcpy Sig zesuImage)
    else if r = 0x800cb5a8 then some freeC else none
  Post := fun g => PostKeep g.A g.L g.items g.m
  sums := sums
  X := fun g _ => InRange (g.m.reg 2 - 128) 16
  wleaves := fun pc =>
    if pc = entry then runE_leaves else if pc = 0x800cb55c then runJ2_leaves
    else if pc = 0x800cb588 then runJ3_leaves else if pc = 0x800cb5a8 then runJ4_leaves else []

/-! ## Assertion facts for `leaf_auto` (`zesu_facts`) -/

@[zesu_fact] theorem AE.req {g : Sig} {m : Machine} (h : AE g m) : (m.reg 12).toNat < 2 ^ 32 :=
  (Entry.of_pre h.2.2).req

@[zesu_fact] theorem AE.cap {g : Sig} {m : Machine} (h : AE g m) :
    (Sym.init 1 16 8).eval (env0 m) = wordAt m (m.reg 10 + 16) :=
  (Entry.of_pre h.2.2).cap

@[zesu_fact] theorem AE.grown_or {g : Sig} {m : Machine} (h : AE g m) :
    ((- if BitVec.ult (m.reg 12 >>> 1 + m.reg 12 + BitVec.ofNat 64 2) (m.reg 12) = true
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) |||
      (m.reg 12 >>> 1 + m.reg 12 + BitVec.ofNat 64 2)) = BitVec.ofNat 64 (grown (m.reg 12).toNat) :=
  g_or' _ (AE.req h)

@[zesu_fact] theorem AE.grown_shl5 {g : Sig} {m : Machine} (h : AE g m) :
    BitVec.ofNat 64 (grown (m.reg 12).toNat) <<< 5 =
      BitVec.ofNat 64 (grown (m.reg 12).toNat * elemBytes) := F1.grown_shl5 _ (AE.req h)

@[zesu_fact] theorem AE.grown_srl59 {g : Sig} {m : Machine} (h : AE g m) :
    BitVec.ofNat 64 (grown (m.reg 12).toNat) >>> 59 = 0 := F1.grown_srl59 _ (AE.req h)

@[zesu_fact] theorem AE.grown_bytes_ne {g : Sig} {m : Machine} (h : AE g m) :
    BitVec.ofNat 64 (grown (m.reg 12).toNat * elemBytes) ≠ 0 := F1.grown_bytes_ne _ (AE.req h)

/-- The return alignment at the entry cut's returns. -/
@[zesu_oblig] theorem ra_oblig {g : Sig} {m : Machine} (h : AE g m) :
    (Oblig.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4).holds (env0 m) := by
  simpa [Oblig.holds, Sym.eval, BinOp.eval, entryEnv] using (Entry.of_pre h.2.2).ra

/-- The return alignment at a join cut's returns: `var 1` is the entry's `ra`. -/
@[zesu_oblig] theorem ra_oblig_join {g : Sig} {F : Nat} {Ss : List SState} {mh : Machine}
    (e : Entry g.A g.L g.items g.m) :
    (Oblig.aligned (.bin .and (.var 1) (.lit 18446744073709551614)) 4).holds
      (envJ F Ss g mh) := by
  simpa [Oblig.holds, Sym.eval, BinOp.eval, envJ, joinEnv, entryEnv] using e.ra

zesu_planw F1 := vcPlan

zesu_autow F1

/-! ## Items `zesu_auto` left open, by hand -/

/-- A leaf's run keeps every present byte and every byte below RAM: it writes only inside the
writable regions of its start state, which lie in RAM and stay present. -/
theorem preserved_of_leaf {env : Env} {S S' : SState} {m m' : Machine} (hwf : Env.WF env S)
    (hm' : Match env S' m') (hreg : S.regions.length ≤ S'.regions.length)
    (hso : SameOutside (InWritable env S) m m') : Preserved m m' := by
  refine ⟨fun a ha => ?_, fun a ha => hso a ?_⟩
  · by_cases hw : InWritable env S a
    · obtain ⟨r, R, j, hR, -, hj, rfl⟩ := hw
      have hr : r < S.regions.length := (List.getElem?_eq_some_iff.mp hR).1
      rw [hm'.mem r j (by omega) hj]; rfl
    · rw [hso a hw]; exact ha
  · rintro ⟨r, R, j, hR, hwR, hj, rfl⟩
    have := hwf.range r R hR
    simp only [hwR, if_true, Machine.writable, Machine.inRange, Bool.and_eq_true,
      decide_eq_true_eq, Layout.ramLo, Layout.ramHi] at this
    have e : (env.base r + BitVec.ofNat 64 j).toNat = (env.base r).toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e] at ha; unfold Layout.ramLo at ha; omega

theorem F1.cut_800cb40c : CutOK F1.plan.toPlan F1.plan.cuts[0]! := by
  show CutOK F1.plan.toPlan cE
  rintro g m ⟨rfl, hpc, hpre⟩
  have E := Entry.of_pre hpre
  exact ⟨E.wf, E.match, E.ro, hpc⟩

/-- Entry leaf 0: no growth, return 0. -/
theorem F1.leaf_800cb40c_0 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[0]! (((F1.plan.wleaves 0x800cb40c)[0]!).leaf) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  sym_simp at hc
  simp only [E.cap] at hc
  refine ⟨fun o ho => ?_, by decide, fun mf hm hex hfr => ?_⟩
  · simp at ho; subst ho; simpa [Oblig.holds, Sym.eval, BinOp.eval, entryEnv] using E.ra
  show PostKeep A L items m mf
  have hret : Returns m mf := returns_leaf hm (envOk0 m).vars (by decide)
    (by simp [SState.reg, Sym.eval, entryEnv, Env.base, shape, BitVec.sub_add_cancel]) hex
  have hfr' : SameOutside (Allowed A L m) m mf := SameOutside.mono hfr fun a ha => by
    rcases E.inWritable ha with h | h
    · exact .inr (.inl (frame_sub_stack (by have := E.sp.1; unfold Layout.ramLo at this; omega) h))
    · exact .inl h
  have hle : (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by
    simp [BitVec.ult, entryEnv] at hc ⊢; omega
  refine ⟨⟨hret, hfr', ?_⟩, fun _ i hi => ?_⟩
  rotate_left
  · obtain ⟨hc0, hin⟩ := E.itemsOld hi
    rw [hfr _ fun hw => E.oldNotOwn hc0 hin (E.inWritable hw)]; exact E.items i hi
  simp only [hle, if_true]
  refine ⟨by rw [← hm.regs 10]; rfl, E.header_same (envOk0 m) hm (by decide) (by decide),
    A.heap_frame' L m mf E.heap (fun a hp => hfr a fun hw => ?_)
      (preserved_of_leaf E.wf hm (by decide) hfr), fun j hj => hfr _ fun hw => ?_⟩
  · exact E.ownNotPriv (E.inWritable hw) hp
  · exact E.scratchNotOwn hj (E.inWritable hw)

/-! ## Through `remap` (F0): entry leaves 4–6 and their call -/

theorem EnvOk.of_agree {m : Machine} {env env' : Env} {F : Nat} (h : EnvOk m env)
    (hag : Env.Agree env env' F []) (hF : 32 ≤ F) : EnvOk m env' where
  vars i := (hag.vars i.val (by omega)).trans (h.vars i)
  base0 := (hag.base 0).trans h.base0
  base1 := (hag.base 1).trans h.base1
  size1 := (hag.size 1).trans h.size1
  mem1 j := (hag.mem0 1 j rfl).trans (h.mem1 j)
  size0 := (hag.size 0).trans h.size0
  base2 := (hag.base 2).trans h.base2
  size2 := (hag.size 2).trans h.size2
  len := by rw [hag.regions]; exact h.len
  mem2 j := (hag.mem0 2 j rfl).trans (h.mem2 j)

/-- Conditions that mention neither `remap`'s fresh variables nor written bytes evaluate as at
the entry. -/
theorem conds_env0 {m : Machine} {env' : Env} {cs : List SBool}
    (hag : Env.Agree (env0 m) env' 64 []) (hok : cs.all (SBool.okB 64 []) = true)
    (hc : ∀ b ∈ cs, b.eval env' = true) : ∀ b ∈ cs, b.eval (env0 m) = true := fun b hb => by
  rw [← SBool.eval_agree hag b (List.all_eq_true.mp hok b hb)]; exact hc b hb

/-- The call of `remap` (F0) on entry leaves 4–6 (capacity > 0): it returns null and changes
only its frame. -/
theorem F1.call_800cb40c_0 :
    CallGoal F1.plan F1.plan.cuts[0]! ((F1.plan.callsAt 0x800cb40c)[0]!) := by
  call_intro
  intro g m hA env₁ mc k hag _ _ hmc hex hrun hfr
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hag hmc hex hfr ⊢
  have E := Entry.of_pre hpre
  have hmc0 := Match.agree hag.symm (by decide) hmc
  have hp : Preserved m mc := hrun.preserved
  have g2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [Match.reg_eq hmc0 2 2 rfl]; show (env0 m).base 0 + BitVec.ofInt 64 0 = _
    rw [(envOk0 m).base0]; simp
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb4f8 := by rw [Match.reg_eq hmc0 1 1 rfl]; rfl
  have hinv1 : Inv A L m mc := Inv.refl.step hfr (fun a h => Or.elim h
    (E.inWritable' (envOk0 m) (by decide)) fun (h : InRange (m.reg 2 - 128) 16 a) =>
      .inr (.inl ⟨h.1, by have := h.2; omega⟩)) hp
  have hstk := E.calleeStack hp g2
  have hpre : F0.Pre mc := ⟨hinv1.ro E, hstk, by unfold RetAligned; rw [g1]; decide⟩
  obtain ⟨k₂, m2, hk₂, hr₂, hpost⟩ := F0.f0_spec mc (by simpa [F0.entry] using hex) hpre
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [g2]; bv_omega
  refine ⟨k₂, m2, hk₂, hr₂, F0.callPost (by decide) rfl rfl (by rw [g1]; decide) hpost hstk
    (fun a b _ _ hb => hinv1.ro E a b hb) (fun r j hr hj h => ?_) (fun a h => ?_), trivial⟩
  · rw [hcf] at h
    exact E.calleeApart ((envOk0 m).of_agree hag (by decide)) r j (by simpa using hr) hj h
  · rw [hcf] at h; exact h

/-- `alloc_step` split for `ExitGoal`: the callee's precondition, and what every result of
`alloc` gives at the return site. -/
theorem alloc_call {A : AllocContract zesuImage} {L : List (Word × Nat)} {items : List Byte}
    {m : Machine} (E : Entry A L items m) {env : Env} {S Sl : SState} {mk mc : Machine} {F : Nat}
    (he : EnvOk m env) (hS : S.regions = [frameR, headerR, allocObjR])
    (hSl : Sl.regions = [frameR, headerR, allocObjR]) (hmc : Match env Sl mc) (hwf : Env.WF env S)
    (hfr : SameOutside (fun a => InWritable env S a ∨ InRange (m.reg 2 - 128) 16 a) mk mc)
    (hp : Preserved mk mc)
    (hinv : Inv A L m mk) (hheap : A.Heap L mk) (hscr : ScratchSame m mk)
    (hitems : BytesAt mk (wordAt m (m.reg 10)) items) (hwfB : Sl.wfB F = true)
    (r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes) (r12 : Sl.reg 12 = .lit 0)
    (r1 : Sl.reg 1 = .lit 0x800cb55c) (r2 : Sl.reg 2 = .ptr 0 0) :
    allocC.Pre ⟨A, L, items, m⟩ () mc ∧ ∀ m2, allocC.Post ⟨A, L, items, m⟩ () mc m2 →
      Match (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) m2 ∧
      Env.WF (env.setVars F fun i => m2.reg (Fin.ofNat 32 i)) (Sl.override (callOv Sl F none)) ∧
      m2.pc.toNat = 0x800cb55c ∧ Inv A L m m2 ∧ ScratchSame m m2 ∧
      BytesAt m2 (wordAt m (m.reg 10)) items ∧
      AllocOut A L (grown (m.reg 12).toNat * elemBytes) m2 ∧ Returns mc m2 := by
  have own : ∀ a, InWritable env S a → InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he hS h
  have g2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [← hmc.regs 2]; show Sym.eval env (Sl.reg 2) = _; rw [r2]
    show env.base 0 + BitVec.ofInt 64 0 = _; rw [he.base0]; simp
  have g1 : mc.reg 1 = BitVec.ofNat 64 0x800cb55c := by
    rw [← hmc.regs 1]; show Sym.eval env (Sl.reg 1) = _; rw [r1]; rfl
  have g12 : mc.reg 12 = 0 := by
    rw [← hmc.regs 12]; show Sym.eval env (Sl.reg 12) = _; rw [r12]; rfl
  have in128 : ∀ a, InRange (m.reg 2 - 128) 16 a → InRange (m.reg 2 - 128) 128 a :=
    fun a h => ⟨h.1, by have := h.2; omega⟩
  have hheapc : A.Heap L mc := A.heap_frame' L mk mc hheap (fun a ha => hfr a fun hw =>
    hw.elim (fun h => E.ownNotPriv (own a h) ha) fun h => E.priv a (.inr (.inr (.inl (in128 a h)))) ha) hp
  have hreq := E.req
  refine ⟨⟨hheapc, ?_, ?_, by rw [g12]; decide, E.calleeStack (hinv.2.trans hp) g2,
    by unfold RetAligned; rw [g1]; decide, E.calleeFree (fun _ h => h) g2⟩, fun m2 hpost => ?_⟩
  · show 0 < (mc.reg 11).toNat; rw [r11]; simp only [grown, elemBytes]; omega
  · show (mc.reg 11).toNat < 2 ^ 63; rw [r11]; simp only [grown, elemBytes]; omega
  obtain ⟨⟨hret, hfrA, hout⟩, hp2⟩ := hpost
  rw [r11] at hout
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [g2]; bv_omega
  rw [hcf] at hfrA
  have hframe : ∀ r j, r < Sl.regions.length → j < env.size r →
      m2.mem (env.base r + BitVec.ofNat 64 j) = mc.mem (env.base r + BitVec.ofNat 64 j) := by
    intro r j hr hj
    have hr3 : r < 3 := by rw [hSl] at hr; simpa using hr
    refine hfrA _ fun h => ?_
    rcases h with h | h
    · exact E.regionNotPriv he hr3 hj h
    · exact E.calleeApart he r j hr3 hj h
  obtain ⟨hm2, hwf2⟩ := after_call_ov (F := F) (a0 := none) hmc (hwf.congr (hSl.trans hS.symm)) hwfB
    hret (fun s h => by simp at h) hframe
  have hinv2 : Inv A L m m2 := by
    refine (hinv.step hfr (fun a h => h.elim (E.inWritable' he hS) fun h => .inr (.inl (in128 a h)))
      hp).step hfrA ?_ hp2
    intro a h
    rcases h with h | h
    · exact .inr (.inr (.inr (.inl h)))
    · refine .inr (.inl ?_)
      have h128 := sp128 E
      simp only [InRange, h128] at h ⊢; omega
  have hpc2 : m2.pc.toNat = 0x800cb55c := by rw [hret.1, g1]; decide
  have hsame : ∀ x, ¬ A.Priv L x → ¬ InRange (m.reg 2 - 128) 16 x → ¬ (InRange (m.reg 2 - 112) 112 x ∨
      InRange (m.reg 10) 24 x) → m2.mem x = mk.mem x := fun x h1 h2 h3 =>
    (hfrA x fun h => h.elim h1 h2).trans (hfr x fun hw => hw.elim (fun h => h3 (own x h)) h2)
  refine ⟨hm2, hwf2, hpc2, hinv2, fun j hj => ?_, fun i hi => ?_, hout, hret⟩
  · have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j).toNat = Layout.extraParams + j := by
      simp [Layout.extraParams]; omega
    have hin : InRange (BitVec.ofNat 64 Layout.extraParams) 8
        (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 j) := by
      simp only [InRange]; rw [hs]; simp [Layout.extraParams]; omega
    rw [hsame _ (E.priv _ (.inr (.inr (.inr hin)))) (fun h => by
        have d := E.d6; have h128 := sp128 E
        simp only [InRange] at h; rw [hs, h128] at h
        simp only [Apart, h128, Layout.extraParams, BitVec.toNat_ofNat, Nat.reduceMod,
          Nat.reducePow] at d h; omega)
      (fun h => E.scratchNotOwn hj h)]
    exact hscr j hj
  · obtain ⟨hc, hin⟩ := E.itemsOld hi
    obtain ⟨h1, h2⟩ := E.oldSafe hc hin
    rw [hsame _ h1 h2 (E.oldNotOwn hc hin)]; exact hitems i hi

/-- Entry leaf 2: capacity 0, call `alloc`; its return establishes the `stage2a` side of the
assertion after `alloc`. -/
theorem F1.leaf_800cb40c_2 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[0]! (((F1.plan.wleaves 0x800cb40c)[2]!).leaf) := by
  leaf_intro
  intro g m hA hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  have hc2 := hc
  sym_simp at hc2; simp only [E.cap] at hc2; simp only [entryEnv, Fin.ofNat] at hc2; simp at hc2
  have hc0 : (wordAt m (m.reg 10 + 16)).toNat = 0 := by simp [hc2.2.1]
  have hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat := by
    have := hc2.1; simp [BitVec.ult] at this; simpa using this
  refine ⟨fun o ho => by simp at ho, by decide, fun mc hmc hex hfr => ?_⟩
  have hp : Preserved m mc := preserved_of_leaf E.wf hmc (by decide) hfr
  have h22 : mc.reg 22 = BitVec.ofNat 64 (grown (m.reg 12).toNat) := by
    rw [Match.reg_eq hmc 22 22 rfl]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    exact g_or' _ hreq
  have h11 : mc.reg 11 = BitVec.ofNat 64 (grown (m.reg 12).toNat * elemBytes) := by
    rw [Match.reg_eq hmc 11 11 rfl]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    simp only [g_or' _ hreq, grown_shl5 _ hreq]
  have r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes := by
    rw [h11, BitVec.toNat_ofNat]; simp only [grown, elemBytes]; omega
  obtain ⟨hpreA, hpostA⟩ := alloc_call (F := 200) E (envOk0 m) (by decide) (by decide) hmc E.wf
    (fun a ha => hfr a fun h => ha (.inl h)) hp Inv.refl E.heap (fun _ _ => rfl) E.items (by decide)
    r11 rfl rfl rfl
  refine ⟨allocC, (), rfl, by simpa using hex, hpreA, fun m2 hpost => ?_⟩
  obtain ⟨hm2, hwf2, hpc2, hinv2, hscr2, hitems2, hout, hret⟩ := hpostA m2 hpost
  refine ⟨cJ2, by simp [F1.plan, vcPlan], rfl, hpc2, ⟨E, hpc2, hinv2, hlt, hitems2, hscr2, hout,
    by rw [hret.2 22 (by decide), h22],
    hinv2.ro E, S2a, by simp, _, ((envOk0 m).setVars (by decide) _).agrees (by decide), hm2, hwf2⟩,
    ?_⟩
  show 53 + (if capOf m = 0 then 103 else 78) ≤ 197 - (41 - 0)
  simp only [capOf, hc0, if_true]; decide

/-- Entry leaf 5: capacity > 0, `remap` returned null, call `alloc`; its return establishes the
`S2b` side of the assertion after `alloc`. -/
theorem F1.leaf_800cb40c_5 :
    LeafGoalC F1.plan F1.plan.cuts[0]! ((F1.plan.wleaves 0x800cb40c)[5]!) := by
  leafc_intro
  intro g m hA env' hag hc
  obtain ⟨A, L, items, m0⟩ := g
  obtain ⟨h, hpc, hpre⟩ := hA; subst h
  dsimp only at hag hc ⊢
  have E := Entry.of_pre hpre
  have hreq := E.req
  have hc2 := conds_env0 hag (by decide) hc
  sym_simp at hc2; simp only [E.cap] at hc2; simp only [entryEnv, Fin.ofNat] at hc2; simp at hc2
  have hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat := by
    have := hc2.2.1
    refine Nat.pos_of_ne_zero fun h => this ?_
    apply BitVec.eq_of_toNat_eq; simpa using h
  have hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat := by
    have := hc2.1; simp [BitVec.ult] at this; simpa using this
  have he : EnvOk m env' := (envOk0 m).of_agree hag (by decide)
  refine ⟨fun o ho => by simp at ho, by decide, fun _ k mc hrun hmc hex hfr => ?_⟩
  have hp : Preserved m mc := hrun.preserved
  have hfr' : SameOutside (fun a => InWritable env' S0 a ∨ InRange (m.reg 2 - 128) 16 a) m mc :=
    fun a ha => hfr a fun h => ha (Or.elim h
      (fun hw => .inl (InWritable.of_regions (env' := env0 m) hag.regions.symm rfl hw)) .inr)
  have h22 : mc.reg 22 = BitVec.ofNat 64 (grown (m.reg 12).toNat) := by
    rw [Match.reg_eq hmc 22 22 rfl, Sym.eval_agree hag _ (by decide)]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    exact g_or' _ hreq
  have h11 : mc.reg 11 = BitVec.ofNat 64 (grown (m.reg 12).toNat * elemBytes) := by
    rw [Match.reg_eq hmc 11 11 rfl, Sym.eval_agree hag _ (by decide)]
    simp only [SState.reg]; simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, Nat.succ_ne_zero, if_false]
    simp only [Sym.eval_bin, Sym.eval_var, Sym.eval_lit, BinOp.eval]
    simp [entryEnv]
    simp only [g_or' _ hreq, grown_shl5 _ hreq]
  have r11 : (mc.reg 11).toNat = grown (m.reg 12).toNat * elemBytes := by
    rw [h11, BitVec.toNat_ofNat]; simp only [grown, elemBytes]; omega
  obtain ⟨hpreA, hpostA⟩ := alloc_call (F := 300) E he (by decide) (by decide) hmc
    (E.wf.of_regions hag.regions) hfr' hp Inv.refl E.heap (fun _ _ => rfl) E.items (by decide)
    r11 rfl rfl rfl
  refine ⟨allocC, (), rfl, by simpa using hex, hpreA, fun m3 hpost => ?_⟩
  obtain ⟨hm3, hwf3, hpc3, hinv3, hscr3, hitems3, hout, hret⟩ := hpostA m3 hpost
  refine ⟨cJ2, by simp [F1.plan, vcPlan], rfl, hpc3, ⟨E, hpc3, hinv3, hlt, hitems3, hscr3, hout,
    by rw [hret.2 22 (by decide), h22],
    hinv3.ro E, S2b, by simp, _, (he.setVars (by decide) _).agrees (by decide), hm3, hwf3⟩, ?_⟩
  show 53 + (if capOf m = 0 then 103 else 78) ≤ 197 - (66 - 0)
  simp only [capOf, Nat.pos_iff_ne_zero.mp hc0, if_false]; decide

/-! ## The join cuts and the leaves of their runs -/

theorem AJ2.ok {g : Sig} {m : Machine} (h : AJ2 g m) :
    Env.WF (envJ 500 [S2a, S2b] g m) SJ2 ∧ Match (envJ 500 [S2a, S2b] g m) SJ2 m :=
  JoinIn.ok (by decide) (by decide) h.2.2.2.2.2.2.2.2.2

theorem AJ3.ok {g : Sig} {m : Machine} (h : AJ3 g m) :
    Env.WF (envJ 600 [S3] g m) SJ3 ∧ Match (envJ 600 [S3] g m) SJ3 m :=
  JoinIn.ok (by decide) (by decide) h.2.2.2.2.2.2.2

theorem AJ4.ok {g : Sig} {m : Machine} (h : AJ4 g m) :
    Env.WF (envJ 700 [S4a, S4b] g m) SJ4 ∧ Match (envJ 700 [S4a, S4b] g m) SJ4 m :=
  JoinIn.ok (by decide) (by decide) h.2.2.2.2.2.2.2

/-- The new block's bytes survive a run of F1's own code. -/
theorem Entry.blockSame {A : AllocContract zesuImage} {L : List (Word × Nat)}
    {items : List Byte} {m : Machine} (E : Entry A L items m) {env : Env} {S : SState}
    {m1 m2 : Machine} {p' : Word} (he : EnvOk m env) (hS : S.regions = [frameR, headerR, allocObjR])
    (hfr : SameOutside (InWritable env S) m1 m2)
    (hlt : (wordAt m (m.reg 10 + 16)).toNat < (m.reg 12).toNat)
    (hram : RamRange p' (grown (m.reg 12).toNat * elemBytes))
    (hblk : ∀ a, InRange p' (grown (m.reg 12).toNat * elemBytes) a → A.Priv L a)
    (hitems : BytesAt m1 p' items) : BytesAt m2 p' items := by
  intro i hi
  rw [hfr _ fun hw => ?_]
  · exact hitems i hi
  · have hlen := E.itemsLen; have hnc := E.nc
    have hram' := hram; unfold RamRange Layout.ramHi at hram'
    simp only [elemBytes, grown] at hlen hram' hi ⊢
    have hin : InRange p' (((m.reg 12).toNat + (m.reg 12).toNat / 2 + 2) * 32)
        (p' + BitVec.ofNat 64 i) := by
      simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
    exact E.ownNotPriv (E.inWritable2 he hS hw) (hblk _ (by simpa only [grown, elemBytes] using hin))

/-- The scratch word survives a run of F1's own code. -/
theorem Entry.scratchKeep {A : AllocContract zesuImage} {L : List (Word × Nat)}
    {items : List Byte} {m : Machine} (E : Entry A L items m) {env : Env} {S : SState}
    {m1 m2 : Machine} {bs : List Byte} (hbs : bs.length = 8) (he : EnvOk m env)
    (hS : S.regions = [frameR, headerR, allocObjR]) (hfr : SameOutside (InWritable env S) m1 m2)
    (hscr : BytesAt m1 (BitVec.ofNat 64 Layout.extraParams) bs) :
    BytesAt m2 (BitVec.ofNat 64 Layout.extraParams) bs := by
  intro i hi
  rw [hfr _ fun hw => E.scratchNotOwn (by omega) (E.inWritable2 he hS hw)]
  exact hscr i hi

/-- After `alloc`, leaf 0: a block; call `memcpy`. -/
theorem F1.leaf_800cb55c_0 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[1]! (((F1.plan.wleaves 0x800cb55c)[0]!).leaf) := by
  leaf_intro
  intro g m2 hA hc
  obtain ⟨hwf, -⟩ := AJ2.ok hA
  obtain ⟨A, L, items, m⟩ := g
  simp only [AJ2, capOf, reqOf] at hA
  obtain ⟨E, -, hinv, hlt, hitems, -, hout, h22, -, -⟩ := hA
  dsimp only at hc ⊢
  have he := envJ_ok (F := 500) (Ss := [S2a, S2b]) (by decide) (by decide) (by decide)
    ⟨A, L, items, m⟩ m2
  have h10 : (envJ 500 [S2a, S2b] ⟨A, L, items, m⟩ m2).vars 510 = m2.reg 10 :=
    envJ_fresh (i := 10) (by decide) _ _
  sym_simp at hc; rw [h10] at hc; simp only [bne_iff_ne, ne_eq] at hc
  obtain ⟨hne, hheap, hram', hpres', hblk, hpriv⟩ := hout.resolve_left fun h => hc h.1
  refine ⟨fun o ho => by simp at ho, by split <;> decide, fun mc hmc hex hfr => ?_⟩
  have hp : Preserved m2 mc := preserved_of_leaf hwf hmc (by decide) hfr
  have hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat ∨ (wordAt m (m.reg 10 + 8)).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (wordAt m (m.reg 10 + 16)).toNat with h | h
    · exact .inr (by have := E.nc; omega)
    · exact .inl h
  obtain ⟨hpre, hpost⟩ := copy_call (iP := 510) E he hwf hmc hfr hp hinv hc0 hlt h10 hitems hne
    hheap hram' hpres' hblk hpriv (by decide) (by decide) rfl rfl rfl rfl
  refine ⟨Callee.memcpy Sig zesuImage, (), rfl, by simpa using hex, hpre, fun m3 hz => ?_⟩
  obtain ⟨hm3, hwf3, hpc3, hinv3, hitems3, hscr3, hheap3⟩ := hpost m3 hz
  have r19 : m3.reg 19 = m2.reg 10 := by rw [← hm3.regs 19]; exact h10
  have r22 : m3.reg 22 = m2.reg 22 := by
    rw [← hm3.regs 22]; exact envJ_fresh (i := 22) (by decide) _ _
  have hp0 : 0 < (m2.reg 10).toNat :=
    Nat.pos_of_ne_zero fun e => hne (BitVec.eq_of_toNat_eq (by simpa using e))
  refine ⟨cJ3, by simp [F1.plan, vcPlan], rfl, hpc3, ⟨E, hpc3, hinv3, hlt, by rw [r22, h22],
    by rw [r19]; exact ⟨hp0, hram', hitems3, hscr3, hheap3, hpriv, hblk⟩,
    hinv3.ro E, S3, by simp, _, he.agrees (by decide), hm3, hwf3⟩, ?_⟩
  show 3 + (if capOf m = 0 then 18 else 67) ≤ (if capOf m = 0 then 103 else 78) - (8 - 0)
  by_cases h : capOf m = 0 <;> simp [h]

/-- After `alloc`, leaf 1: null; OutOfMemory. -/
theorem F1.leaf_800cb55c_1 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[1]! (((F1.plan.wleaves 0x800cb55c)[1]!).leaf) := by
  leaf_intro
  intro g m2 hA hc
  obtain ⟨hwf, -⟩ := AJ2.ok hA
  obtain ⟨A, L, items, m⟩ := g
  simp only [AJ2, capOf, reqOf] at hA
  obtain ⟨E, -, hinv, hlt, -, hscr, hout, -, -, -⟩ := hA
  dsimp only at hc ⊢
  have he := envJ_ok (F := 500) (Ss := [S2a, S2b]) (by decide) (by decide) (by decide)
    ⟨A, L, items, m⟩ m2
  have h10 : (envJ 500 [S2a, S2b] ⟨A, L, items, m⟩ m2).vars 510 = m2.reg 10 :=
    envJ_fresh (i := 10) (by decide) _ _
  sym_simp at hc; rw [h10] at hc; simp only [beq_iff_eq] at hc
  have hheap : A.Heap L m2 := by
    rcases hout with ⟨-, h⟩ | ⟨hne, -⟩
    · exact h
    · exact absurd hc hne
  refine ⟨fun o ho => ?_, by split <;> decide, fun mf hmf hex hfr => ?_⟩
  · simp at ho; subst ho
    simpa [Oblig.holds, Sym.eval, BinOp.eval,
      show (envJ 500 [S2a, S2b] ⟨A, L, items, m⟩ m2).vars 1 = m.reg 1 from he.vars 1] using E.ra
  show PostKeep A L items m mf
  exact ⟨oom_post E he (by decide) hmf (by decide) (by decide) (by decide) rfl rfl hex hinv hfr
    (preserved_of_leaf hwf hmf (by decide) hfr) hlt hheap hscr, fun h => absurd h (by omega)⟩

/-- After `memcpy`, leaf 0: capacity 0, nothing to free. -/
theorem F1.leaf_800cb588_0 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[2]! (((F1.plan.wleaves 0x800cb588)[0]!).leaf) := by
  leaf_intro
  intro g m3 hA hc
  obtain ⟨hwf, -⟩ := AJ3.ok hA
  obtain ⟨A, L, items, m⟩ := g
  simp only [AJ3, Copied, capOf, reqOf] at hA
  obtain ⟨E, -, hinv, hlt, h22, ⟨hp0, hram, hitems, hscr, hheap, hpriv, hblk⟩, -, -⟩ := hA
  dsimp only at hc ⊢
  have he := envJ_ok (F := 600) (Ss := [S3]) (by decide) (by decide) (by decide)
    ⟨A, L, items, m⟩ m3
  sym_simp at hc; rw [he.init_eq, E.cap] at hc; simp only [beq_iff_eq] at hc
  have hc0 : capOf m = 0 := by show (wordAt m (m.reg 10 + 16)).toNat = 0; rw [hc]; rfl
  refine ⟨fun o ho => by simp at ho, by split <;> decide, fun m4 hm4 hex hfr => ?_⟩
  have hp : Preserved m3 m4 := preserved_of_leaf hwf hm4 (by decide) hfr
  have r19 : m4.reg 19 = m3.reg 19 := by
    rw [← hm4.regs 19]; exact envJ_fresh (i := 19) (by decide) _ _
  have r22 : m4.reg 22 = m3.reg 22 := by
    rw [← hm4.regs 22]; exact envJ_fresh (i := 22) (by decide) _ _
  have hL : newL ⟨A, L, items, m⟩ (m3.reg 19) = L ++ [(m3.reg 19, grown (reqOf m) * elemBytes)] := by
    simp [newL, hc0]
  refine ⟨cJ4, by simp [F1.plan, vcPlan], hex, ⟨E, hex,
    hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp, hlt, by rw [r22, h22], ?_,
    (hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp).ro E,
    S4a, by simp, _, he.agrees (by decide), hm4, hwf.congr (by decide)⟩, ?_⟩
  · rw [r19]
    refine ⟨hp0, hram, E.blockSame he (by decide) hfr hlt hram hblk hitems,
      E.scratchKeep (by simp [wordBytes]) he (by decide) hfr hscr, ?_, ?_, hblk⟩
    · rw [hL]
      exact A.heap_frame' _ m3 m4 hheap (fun a ha => hfr a fun hw =>
        E.ownNotPriv (E.inWritable2 he (by decide) hw) (hpriv a ha)) hp
    · rw [hL]; exact fun a h => .inl (hpriv a h)
  · show 17 ≤ (if capOf m = 0 then 18 else 67) - (1 - 0)
    simp [hc0]

/-- After `memcpy`, leaf 1: capacity > 0; `free` the old buffer. -/
theorem F1.leaf_800cb588_1 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[2]! (((F1.plan.wleaves 0x800cb588)[1]!).leaf) := by
  leaf_intro
  intro g m3 hA hc
  obtain ⟨hwf, -⟩ := AJ3.ok hA
  obtain ⟨A, L, items, m⟩ := g
  simp only [AJ3, Copied, capOf, reqOf] at hA
  obtain ⟨E, -, hinv, hlt, h22, ⟨hp0, hram, hitems, hscr, hheap, hpriv, hblk⟩, -, -⟩ := hA
  dsimp only at hc ⊢
  have he := envJ_ok (F := 600) (Ss := [S3]) (by decide) (by decide) (by decide)
    ⟨A, L, items, m⟩ m3
  sym_simp at hc; rw [he.init_eq, E.cap] at hc; simp only [bne_iff_ne, ne_eq] at hc
  have hc0 : 0 < (wordAt m (m.reg 10 + 16)).toNat :=
    Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
  refine ⟨fun o ho => by simp at ho, by split <;> decide, fun mc hmc hex hfr => ?_⟩
  have hp : Preserved m3 mc := preserved_of_leaf hwf hmc (by decide) hfr
  have own : ∀ a, InWritable (envJ 600 [S3] ⟨A, L, items, m⟩ m3) SJ3 a →
      InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he (by decide) h
  -- the call's arguments
  obtain ⟨hbufR, hbufL⟩ := E.buf hc0
  have hcR := hbufR; unfold RamRange Layout.ramHi at hcR
  have r11 : mc.reg 11 = wordAt m (m.reg 10) := by
    rw [← hmc.regs 11]; show (Sym.init 1 0 8).eval _ = _; rw [he.init_eq, E.ptr]
  have r12 : (mc.reg 12).toNat = (wordAt m (m.reg 10 + 16)).toNat * elemBytes := by
    rw [← hmc.regs 12]
    show ((Sym.bin .sll (Sym.init 1 16 8) (Sym.lit 5)).eval _).toNat = _
    simp only [Sym.eval_bin, BinOp.eval, Sym.eval_lit]
    rw [he.init_eq, E.cap, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [elemBytes, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at hcR ⊢; omega
  have r13 : mc.reg 13 = 0 := by rw [← hmc.regs 13]; rfl
  have r1 : mc.reg 1 = BitVec.ofNat 64 0x800cb5a8 := by rw [← hmc.regs 1]; rfl
  have r2 : mc.reg 2 = m.reg 2 - 112 := by
    rw [← hmc.regs 2]; show (envJ 600 [S3] ⟨A, L, items, m⟩ m3).base 0 + BitVec.ofInt 64 0 = _
    rw [he.base0]; simp
  have r19 : mc.reg 19 = m3.reg 19 := by
    rw [← hmc.regs 19]; exact envJ_fresh (i := 19) (by decide) _ _
  have r22 : mc.reg 22 = m3.reg 22 := by
    rw [← hmc.regs 22]; exact envJ_fresh (i := 22) (by decide) _ _
  generalize hp' : m3.reg 19 = p' at hp0 hram hitems hheap hpriv hblk r19
  generalize hL3 : L ++ [(p', grown (m.reg 12).toNat * elemBytes)] = L3 at hheap hpriv
  have hheapc : A.Heap L3 mc := A.heap_frame' L3 m3 mc hheap (fun a ha => hfr a fun hw =>
    E.ownNotPriv (own a hw) (hpriv a ha)) hp
  have hpre : freeC.Pre ⟨A, L, items, m⟩ L3 mc := by
    refine ⟨hheapc, ?_, ?_, ?_, by rw [r13]; decide, .inl (by rw [r13]; decide),
      E.calleeStack (hinv.2.trans hp) r2, by unfold RetAligned; rw [r1]; decide,
      E.calleeFree hpriv r2, by rw [r11, r12]; exact E.calleeNotOld hc0 r2⟩
    · rw [r11, r12, ← hL3]; exact List.mem_append_left _ hbufL
    · rw [r12]; simp only [elemBytes]; omega
    · rw [r12]; simp only [elemBytes] at hcR ⊢; omega
  refine ⟨freeC, L3, rfl, by simpa using hex, hpre, fun m4 hpost => ?_⟩
  obtain ⟨⟨hret, hfrF, hheap4, hpriv4⟩, hp4⟩ := hpost
  rw [r11, r12] at hfrF hheap4 hpriv4
  have hcf : mc.reg 2 - 16 = m.reg 2 - 128 := by rw [r2]; bv_omega
  rw [hcf] at hfrF
  -- the old and new blocks are apart
  have hlive := (A.live_ok L3 m3 hheap).1
  have hapart : ∀ a, InRange p' (grown (m.reg 12).toNat * elemBytes) a →
      ¬ InRange (wordAt m (m.reg 10)) ((wordAt m (m.reg 10 + 16)).toNat * elemBytes) a := by
    intro a h1 h2
    rw [← hL3] at hlive
    have := (List.pairwise_append.mp hlive).2.2 _ hbufL _ (List.mem_singleton_self _)
    simp only [InRange] at h1 h2 this; omega
  obtain ⟨hm4, hwf4⟩ := after_call_ov (F := 650) (a0 := none) hmc (hwf.congr (by decide))
    (by decide) hret (fun s h => by simp at h) fun r j hr hj => by
      have hr3 : r < 3 := by simpa using hr
      refine hfrF _ fun h => ?_
      rcases h with h | h | h
      · exact E.regionNotPriv he hr3 hj (hpriv _ h)
      · exact E.regionNotOld he hc0 hr3 hj h
      · exact E.calleeApart he r j hr3 hj h
  have hinv4 : Inv A L m m4 := by
    refine (hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp).step hfrF ?_ hp4
    intro a h
    rcases h with h | h | h
    · exact .inr (.inr (.inr (.inl (hpriv a h))))
    · exact .inr (.inr (.inr (.inr ⟨hc0, h⟩)))
    · refine .inr (.inl ?_)
      have h128 := sp128 E
      simp only [InRange, h128] at h ⊢; omega
  have hpc4 : m4.pc.toNat = 0x800cb5a8 := by rw [hret.1, r1]; decide
  have hL : L3.erase (wordAt m (m.reg 10), (wordAt m (m.reg 10 + 16)).toNat * elemBytes) =
      newL ⟨A, L, items, m⟩ p' := by
    rw [← hL3, List.erase_append_left _ hbufL]
    show _ = (if 0 < capOf m then _ else L) ++ _
    rw [if_pos hc0]
  rw [hL] at hheap4 hpriv4
  have s19 : m4.reg 19 = p' := by rw [hret.2 19 (by decide), r19]
  refine ⟨cJ4, by simp [F1.plan, vcPlan], rfl, hpc4, ⟨E, hpc4, hinv4, hlt,
    by rw [hret.2 22 (by decide), r22, h22], ?_,
    hinv4.ro E, S4b, by simp, _, (he.setVars (by decide) _).agrees (by decide), hm4, hwf4⟩, ?_⟩
  · rw [s19]
    refine ⟨hp0, hram, ?_, ?_, hheap4, fun a h => ?_, hblk⟩
    · intro i hi
      have hin : InRange p' (grown (m.reg 12).toNat * elemBytes) (p' + BitVec.ofNat 64 i) := by
        have hlen := E.itemsLen; have hnc := E.nc; have hram' := hram
        unfold RamRange Layout.ramHi at hram'
        simp only [elemBytes, grown] at hlen hram' hi ⊢
        simp only [InRange]; rw [toNat_add_ofNat (by omega)]; omega
      have hpl : ¬ A.Priv L3 (p' + BitVec.ofNat 64 i) := fun hp =>
        A.priv_not_live L3 _ hp
          ⟨_, by rw [← hL3]; exact List.mem_append_right _ (List.mem_singleton_self _), hin⟩
      rw [hfrF _ fun h => ?_, hfr _ fun hw => E.ownNotPriv (own _ hw) (hblk _ hin)]
      · exact hitems i hi
      · rcases h with h | h | h
        · exact hpl h
        · exact hapart _ hin h
        · exact E.priv _ (.inr (.inr (.inl ⟨h.1, by have := h.2; omega⟩))) (hblk _ hin)
    · intro i hi
      have hi8 : i < 8 := by simpa [wordBytes] using hi
      have hs : (BitVec.ofNat 64 Layout.extraParams + BitVec.ofNat 64 i).toNat =
          Layout.extraParams + i := by
        simp [Layout.extraParams]; omega
      rw [hfrF _ fun h => ?_, hfr _ fun hw => E.scratchNotOwn hi8 (own _ hw)]
      · exact hscr i hi
      · rcases h with h | h | h
        · exact E.priv _ (.inr (.inr (.inr ⟨by rw [hs]; simp [Layout.extraParams],
            by rw [hs]; simp [Layout.extraParams]; omega⟩))) (hpriv _ h)
        · obtain ⟨-, -, -, d⟩ := E.dbuf hc0
          simp only [Apart, InRange, hs] at d h; simp [Layout.extraParams] at d h; omega
        · have d := E.d6; have h128 := sp128 E
          simp only [Apart, InRange, hs, h128] at d h; simp [Layout.extraParams] at d h; omega
    · rcases hpriv4 a h with h | h
      · exact .inl (hpriv a h)
      · exact .inr h
  · show 42 + 17 ≤ (if capOf m = 0 then 18 else 67) - (8 - 0)
    simp [Nat.pos_iff_ne_zero.mp hc0]

/-- At `0x800cb5a8`: write the header and return 0. -/
theorem F1.leaf_800cb5a8_0 :
    LeafGoal F1.plan.toPlan F1.plan.cuts[3]! (((F1.plan.wleaves 0x800cb5a8)[0]!).leaf) := by
  leaf_intro
  intro g m4 hA hc
  obtain ⟨hwf, -⟩ := AJ4.ok hA
  obtain ⟨A, L, items, m⟩ := g
  simp only [AJ4, Freed, capOf, reqOf] at hA
  obtain ⟨E, -, hinv, hlt, h22, ⟨hp0, hram, hitems, hscr, hheap, hpriv, hblk⟩, -, -⟩ := hA
  dsimp only at hc ⊢
  have he := envJ_ok (F := 700) (Ss := [S4a, S4b]) (by decide) (by decide) (by decide)
    ⟨A, L, items, m⟩ m4
  refine ⟨fun o ho => ?_, by decide, fun mf hmf hex hfr => ?_⟩
  · simp at ho; subst ho
    simpa [Oblig.holds, Sym.eval, BinOp.eval,
      show (envJ 700 [S4a, S4b] ⟨A, L, items, m⟩ m4).vars 1 = m.reg 1 from he.vars 1] using E.ra
  show PostKeep A L items m mf
  have hp := preserved_of_leaf hwf hmf (by decide) hfr
  have own : ∀ a, InWritable (envJ 700 [S4a, S4b] ⟨A, L, items, m⟩ m4) SJ4 a →
      InRange (m.reg 2 - 112) 112 a ∨ InRange (m.reg 10) 24 a :=
    fun a h => E.inWritable2 he (by decide) h
  have hret : Returns m mf := returns_leaf hmf he.vars (by decide)
    (by show (envJ 700 [S4a, S4b] ⟨A, L, items, m⟩ m4).base 0 + BitVec.ofInt 64 112 = m.reg 2
        rw [he.base0]; simp [BitVec.sub_add_cancel]) hex
  have hlt' : ¬ (m.reg 12).toNat ≤ (wordAt m (m.reg 10 + 16)).toNat := by omega
  refine ⟨⟨hret, (hinv.step hfr (fun a h => E.inWritable' he (by decide) h) hp).1, ?_⟩,
    fun h => absurd h hlt'⟩
  simp only [hlt', if_false]
  refine .inl ⟨by rw [← hmf.regs 10]; rfl, m4.reg 19, ⟨?_, ?_, ?_⟩, hp0, hram,
    E.blockSame he (by decide) hfr hlt hram hblk hitems, ?_,
    E.scratchKeep (by simp [wordBytes]) he (by decide) hfr hscr⟩
  · have := header_load he (hwf.congr (by decide)) hmf (by decide) 0 (by decide)
    rw [show m.reg 10 + BitVec.ofNat 64 0 = m.reg 10 by simp] at this
    rw [this]; rfl
  · have := header_load he (hwf.congr (by decide)) hmf (by decide) 8 (by decide)
    show mf.load (m.reg 10 + BitVec.ofNat 64 8) 8 = _
    rw [this]; show some ((Sym.init 1 8 8).eval _) = _
    rw [he.init_eq, E.len]
  · have := header_load he (hwf.congr (by decide)) hmf (by decide) 16 (by decide)
    show mf.load (m.reg 10 + BitVec.ofNat 64 16) 8 = _
    rw [this]; show some (m4.reg 22) = _; rw [h22]
  · show A.Heap (newL ⟨A, L, items, m⟩ (m4.reg 19)) mf
    refine A.heap_frame' _ m4 mf hheap (fun a ha => hfr a fun hw => ?_) hp
    rcases hpriv a ha with h | h
    · exact E.ownNotPriv (own a hw) h
    · rcases Nat.eq_zero_or_pos (capOf m) with hc0 | hc0
      · simp only [InRange, capOf] at h hc0; rw [hc0] at h; omega
      · exact E.oldNotOwn hc0 h (own a hw)

zesu_assemblew F1

end ZesuExec.Fn.F1
