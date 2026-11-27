import ZesuExec.Fn.DTF.Runs
import ZesuExec.Fn.F0.Proof
import ZesuExec.Fn.F1.Proof
import ZesuExec.Fn.F2.Proof
import ZesuExec.Fn.F4.Proof
import ZesuExec.Fn.TX.Proof
import ZesuExec.Fn.Preserve
import ZesuExec.Vc.Tactics

/-!
# DTF cut assertions, callees, budgets and plan (programme plan S7 step 3)

`σ` = `Sig`: the allocator assumptions, the parameters (`payload`, `L`) and the entry machine.
`txAccessList`'s callee is `TX.tx_spec` (bound `TX.bound = 32 · 2^30 + 424`, TX's budget for the
largest input an input area can hold).

Assertions (one generic form per kind, instantiated by the cut table of `Regions.lean`):

* the entry: `σ.m` itself with `Pre`;
* a cut reached by a jump or a branch (`PlainA`): `pc`; `Common` (the frame, saved registers,
  `SameOutside` from the entry, presence, the heap `Live`); `ShapeOk` (the registers and frame
  slots of the cut's shape hold the frame, result and allocator pointers and the vtable word);
  `ArmOk` (`tx_type` is one of the arms that reach the cut); `RestOk` (every location of the
  `rest` slice after `k` top-level items holds `inp + c` / `len - c`, `c` the bytes of the first
  `k` items of the payload, each an `rlp.decodeItem` success, `skip k`); and `Extra` for four
  cuts: the jump-table word address (`0x80000574`), the store slot of a list buffer
  (`0x80002138`, `0x80002434`: RAM, present, carved from the allocator's private memory), the
  written result (`0x800011f8`: error code 3, or code 0 and the decoded transaction);
* a call return site (`RetA`, TX's `ARet`): the call-site predicate (`Common`, the shape, arms
  and `rest` at the call instruction, the return address and the callee's index) at the machine of
  the call, and the callee's `Post` from it; a return site also reached by a jump
  (`0x80002a6c`) has the disjunction.

Not yet stated (open assertion items, `OPEN/DTF/CUTS.md`): the values of the decoded fields held in
registers and frame slots, the state of the `txHashList`/`txAuthList` buffers, and the per-field
checks before the current item. Leaves whose goal needs them (callee preconditions on the field
values, the success write at `0x80002dc4`) stay open until those conjuncts are added.

Budgets: `K + 256 · (rest length) + inner`, `K` the longest path to the return over the cut graph
(back edges of the two list loops and the byte loops' self edges removed, callee bounds added,
640 for every entry into a byte loop), `inner` = `20 · (end - cursor)` at a byte-loop head and
`256 · (list bytes left)` inside the hash and authorization list loops.
-/

namespace ZesuExec.Fn.DTF
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

abbrev w (n : Nat) : Word := BitVec.ofNat 64 n

structure Sig where
  A : AllocAssumptions zesuImage
  g : Params
  m : Machine

namespace Sig
variable (σ : Sig)
abbrev S : Word := σ.m.reg 2
abbrev res : Word := σ.m.reg 10
abbrev ao : Word := σ.m.reg 11
abbrev t : Nat := (σ.m.reg 12).toNat
abbrev inp : Word := σ.m.reg 13
abbrev len : Nat := (σ.m.reg 14).toNat
/-- The frame base `S - 0x370`. -/
abbrev fr : Word := σ.S - w frameBytes
abbrev payload : List Byte := σ.g.payload
end Sig

/-! ## Region bases, environments -/

/-- Region bases and sizes, indices as in `Regions.lean`; region 4 is `a0` at the cut. -/
def regionsOf (sh : Shape) (σ : Sig) (m : Machine) : List (Word × Nat) :=
  [(σ.fr, frameBytes), (σ.res, resultBytes), (σ.ao, 16), (σ.inp, σ.len)] ++
    sh.extra.map fun R => (m.reg 10, R.size.getD 0)

/-- `entryEnv` with the payload-pointer variables: `var (32 + i)` = register `i` minus the payload
base, `var (64 + j)` = the frame word at `8 j` minus the payload base. -/
def envOf (sh : Shape) (σ : Sig) (m : Machine) : Env :=
  { entryEnv m (regionsOf sh σ m) with
    vars := fun i => if i < 32 then m.reg (Fin.ofNat 32 i)
      else if i < 64 then m.reg (Fin.ofNat 32 (i - 32)) - σ.inp
      else TX.wordAt m (σ.fr + w (8 * (i - 64))) - σ.inp }

/-! ## Common facts -/

/-- Register `k` of the save area `S - 8(k+1)`: `ra`, `s0`, `s1`, `s2`, …, `s11`. -/
def savedReg (k : Nat) : Fin 32 :=
  if k = 0 then 1 else if k = 1 then 8 else if k = 2 then 9 else Fin.ofNat 32 (k + 15)

/-- The caller's memory DTF owns or may change: the result, its stack, the scratch word. -/
def Owned (σ : Sig) (a : Word) : Prop :=
  InRange σ.res resultBytes a ∨ InRange (σ.S - w stackBytes) stackBytes a ∨ InRange TX.scratch 8 a

/-- The live list `L` is the caller's `g.L` and DTF's blocks `X`, each carved from `Priv g.L`. -/
def Live (σ : Sig) (m : Machine) (L X : List (Word × Nat)) : Prop :=
  σ.A.Heap L m ∧ L.Perm (σ.g.L ++ X) ∧
  ∀ b ∈ X, 0 < b.2 ∧ RamRange b.1 b.2 ∧ ∀ a, InRange b.1 b.2 a → σ.A.Priv σ.g.L a

/-- After the prologue. -/
def Common (σ : Sig) (m : Machine) : Prop :=
  σ.m.pc.toNat = entry ∧ Pre σ.A σ.g σ.m ∧ RodataLoaded zesuImage m ∧
  (∀ k < 13, m.load (σ.S - w (8 * (k + 1))) 8 = some (σ.m.reg (savedReg k))) ∧
  Present m (σ.S - w stackBytes) stackBytes ∧ Present m σ.res resultBytes ∧
  Present m TX.scratch 8 ∧
  SameOutside (fun a => Owned σ a ∨ σ.A.Priv σ.g.L a) σ.m m ∧
  ∃ L X, Live σ m L X

/-- The word a shape value stands for (`none`: a payload pointer or a slot base, which carry no
fact). -/
def Val.word (σ : Sig) : Val → Option Word
  | .fr k => some (σ.fr + w k)
  | .res k => some (σ.res + w k)
  | .ao k => some (σ.ao + w k)
  | .vt => some (w TX.vtable)
  | .inp => none
  | .slot => none

def ShapeOk (σ : Sig) (sh : Shape) (m : Machine) : Prop :=
  (∀ p ∈ sh.regs, ∀ v, p.2.word σ = some v → m.reg (Fin.ofNat 32 p.1) = v) ∧
  (∀ p ∈ sh.slots, ∀ v, p.2.word σ = some v → m.load (σ.fr + w p.1) 8 = some v)

/-- No arm before the dispatch. -/
def ArmOk (σ : Sig) (arms : List Nat) : Prop := arms = [] ∨ σ.t ∈ arms

/-- Bytes of the first `k` items of `b`, each a `decodeItem` success; an item consumes
`(h + p) mod 2^64` bytes (`TX.itemConsumed`), as the binary adds it to `rest` and as the reference
decoder's `item` drops it. -/
def skip : Nat → List Byte → Option Nat
  | 0, _ => some 0
  | k + 1, b =>
    match F2.decode b with
    | .success _ h p => (skip k (b.drop (TX.itemConsumed h p))).map (TX.itemConsumed h p + ·)
    | .error => none

def Loc.word (σ : Sig) (m : Machine) : Loc → Word
  | .reg i => m.reg (Fin.ofNat 32 i)
  | .slot o => TX.wordAt m (σ.fr + w o)

def RestOk (σ : Sig) (m : Machine) (rs : List RestLoc) : Prop :=
  ∀ r ∈ rs, ∃ c, skip r.k σ.payload = some c ∧
    r.loc.word σ m = if r.len then w σ.len - w c else σ.inp + w c

/-- A buffer slot of `n` bytes at `a0`, carved from the allocator's private memory. -/
def SlotOk (σ : Sig) (m : Machine) (n : Nat) : Prop :=
  RamRange (m.reg 10) n ∧ Present m (m.reg 10) n ∧ ∀ a, InRange (m.reg 10) n a → σ.A.Priv σ.g.L a

/-- The result is written: error code 3, or code 0 and the decoded transaction. -/
def Done (σ : Sig) (m : Machine) : Prop :=
  m.load (σ.res + w errOff) 2 = some 3 ∨
  ∃ tx, decode σ.t σ.payload = some tx ∧ m.load (σ.res + w errOff) 2 = some 0 ∧ TxAt m σ.res tx

def Extra (pc : Nat) (σ : Sig) (m : Machine) : Prop :=
  if pc = 0x80000574 then m.reg 10 = w (0x80110050 + 8 * σ.t)
  else if pc = 0x80002138 then SlotOk σ m 32
  else if pc = 0x80002434 then SlotOk σ m 0x90
  else if pc = 0x800011f8 then Done σ m
  else True

/-! ## Callees -/

/-- The index of every callee: the live list, the list bytes (F1, F4), TX's parameters. -/
abbrev Idx := List (Word × Nat) × List Byte × TX.Params

def famCallee (entry bound : Nat) (P : Sig → Idx → Machine → Prop)
    (Q : Sig → Idx → Machine → Machine → Prop)
    (h : ∀ σ x, Spec zesuImage entry bound (P σ x) (Q σ x)) : Callee Sig zesuImage where
  X := Idx
  entry := entry
  bound := bound
  Pre := P
  Post := fun σ x m m' => Q σ x m m' ∧ Preserved m m'
  spec := fun σ x m hpc hx => Reaches.preserve (h σ x m hpc hx)

def allocPre (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m : Machine) : Prop :=
  A.Heap L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧ (m.reg 12).toNat ≤ 3 ∧
    StackOk m 16 ∧ RetAligned m ∧ CalleeFrameFree (A.Priv L) m

def allocPost (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧ SameOutside (fun a => A.Priv L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
  ((m'.reg 10 = 0 ∧ A.Heap L m') ∨
   (m'.reg 10 ≠ 0 ∧ A.Heap (L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
    RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
    (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → A.Priv L a) ∧
    (∀ a, A.Priv (L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → A.Priv L a)))

def freePre (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m : Machine) : Prop :=
  A.Heap L m ∧ (m.reg 11, (m.reg 12).toNat) ∈ L ∧ 0 < (m.reg 12).toNat ∧
    (m.reg 12).toNat < 2 ^ 63 ∧ (m.reg 13).toNat ≤ 3 ∧ StackOk m 16 ∧ RetAligned m ∧
    CalleeFrameFree (A.Priv L) m

def freePost (A : AllocAssumptions zesuImage) (L : List (Word × Nat)) (m m' : Machine) : Prop :=
  Returns m m' ∧
  SameOutside (fun a => A.Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a ∨
    InRange (m.reg 2 - 16) 16 a) m m' ∧
  A.Heap (L.erase (m.reg 11, (m.reg 12).toNat)) m' ∧
  (∀ a, A.Priv (L.erase (m.reg 11, (m.reg 12).toNat)) a →
    A.Priv L a ∨ InRange (m.reg 11) (m.reg 12).toNat a)

def Kind.entry : Kind → Nat
  | .f2 => F2.entry | .f1 => F1.entry | .f4 => F4.entry | .memcpy => Layout.memcpyEntry
  | .tx => TX.entry | .alloc => allocEntry | .remap => F0.entry | .free => freeEntry

def Kind.bound : Kind → Nat
  | .f2 => F2.bound | .f1 => F1.bound | .f4 => F4.bound | .memcpy => 3
  | .tx => TX.bound | .alloc => 53 | .remap => F0.bound | .free => 42

def Kind.Pre : Kind → Sig → Idx → Machine → Prop
  | .f2, _, _ => F2.Pre
  | .f1, σ, x => F1.Pre σ.A x.1 x.2.1
  | .f4, σ, x => F4.Pre σ.A x.1 x.2.1
  | .memcpy, _, _ => MemcpyPre
  | .tx, σ, x => TX.Pre σ.A x.2.2
  | .alloc, σ, x => allocPre σ.A x.1
  | .remap, _, _ => F0.Pre
  | .free, σ, x => freePre σ.A x.1

def Kind.Post : Kind → Sig → Idx → Machine → Machine → Prop
  | .f2, _, _ => F2.Post
  | .f1, σ, x => F1.Post σ.A x.1 x.2.1
  | .f4, σ, x => F4.Post σ.A x.1 x.2.1
  | .memcpy, _, _ => MemcpyPost
  | .tx, σ, x => TX.Post σ.A x.2.2
  | .alloc, σ, x => allocPost σ.A x.1
  | .remap, _, _ => F0.Post
  | .free, σ, x => freePost σ.A x.1

theorem Kind.spec : ∀ (k : Kind) (σ : Sig) (x : Idx),
    Spec zesuImage k.entry k.bound (k.Pre σ x) (k.Post σ x)
  | .f2, _, _ => F2.f2_spec
  | .f1, σ, x => F1.f1_spec σ.A x.1 x.2.1
  | .f4, σ, x => F4.f4_spec σ.A x.1 x.2.1
  | .memcpy, _, _ => memcpy_spec zesuImage
  | .tx, σ, x => TX.tx_spec σ.A x.2.2
  | .alloc, σ, x => σ.A.alloc_spec x.1
  | .remap, _, _ => F0.f0_spec
  | .free, σ, x => σ.A.free_spec x.1

/-- Every callee has the index `Idx`, whatever its kind. -/
def calleeOf (k : Kind) : Callee Sig zesuImage :=
  famCallee k.entry k.bound k.Pre k.Post k.spec

/-- What the call site says about the callee's index: the callee's precondition, and the live list
is DTF's `Live` list (allocator calls, F1, F4, TX; TX's parameters carry it too). The return-site
cut lemmas need both (`Live` after an `alloc`, its size positive). -/
def IdxOk (k : Kind) (σ : Sig) (x : Idx) (m : Machine) : Prop :=
  k.Pre σ x m ∧
  match k with
  | .f2 | .memcpy | .remap => True
  | .tx => x.2.2.L = x.1 ∧ ∃ X, Live σ m x.1 X
  | _ => ∃ X, Live σ m x.1 X

/-! ## Assertions -/

def AEntry (σ : Sig) (m : Machine) : Prop := m = σ.m ∧ m.pc.toNat = entry ∧ Pre σ.A σ.g m

def PlainA (d : CutData) (σ : Sig) (m : Machine) : Prop :=
  m.pc.toNat = d.pc ∧ Common σ m ∧ ShapeOk σ d.shape m ∧ ArmOk σ d.arms ∧ RestOk σ m d.rest ∧
    Extra d.pc σ m

/-- The call-site predicate of the call returning to `r`. -/
def SiteA (s : Site) (r : Nat) (σ : Sig) (x : Idx) (m : Machine) : Prop :=
  m.reg 1 = w r ∧ Common σ m ∧ ShapeOk σ s.shape m ∧ ArmOk σ s.arms ∧ RestOk σ m s.rest ∧
    IdxOk s.kind σ x m

def RetA (s : Site) (r : Nat) (σ : Sig) (m : Machine) : Prop :=
  ∃ mc x, SiteA s r σ x mc ∧ (calleeOf s.kind).Post σ x mc m

def ACut (d : CutData) (σ : Sig) (m : Machine) : Prop :=
  (d.plain = true ∧ PlainA d σ m) ∨ ∃ s, d.site = some s ∧ RetA s d.pc σ m

/-! ## Budgets -/

/-- The variable part of a budget beyond the rest length. -/
inductive Inner
  | none
  /-- a byte loop: cursor and end registers -/
  | be (cur fin : Nat)
  /-- a list loop: the location of the list bytes left -/
  | list (l : Loc)
  deriving Inhabited

/-- `(pc, K, inner)` per cut point (generated from the leaves, `OPEN/DTF/CUTS.md`). -/
def budgetTable : List (Nat × Nat × Inner) := [
  (0x8000050c, 34359750421, .none),
  (0x80000574, 34359750395, .none),
  (0x80000588, 5649, .none),
  (0x8000059c, 5569, .none),
  (0x800005dc, 34359750390, .none),
  (0x800005f0, 34359750310, .none),
  (0x80000634, 34359749653, .be 10 11),
  (0x8000065c, 34359749568, .none),
  (0x8000069c, 34359745912, .none),
  (0x800006b0, 34359745832, .none),
  (0x800006f4, 34359745175, .be 10 11),
  (0x8000071c, 34359745090, .none),
  (0x8000075c, 34359747290, .none),
  (0x80000770, 34359747210, .none),
  (0x800007b4, 34359746553, .be 10 11),
  (0x800007dc, 34359746468, .none),
  (0x8000081c, 34359745161, .none),
  (0x80000830, 34359745081, .none),
  (0x80000874, 34359744424, .be 10 11),
  (0x8000089c, 34359744339, .none),
  (0x800008e8, 4912, .be 10 11),
  (0x80000910, 4827, .none),
  (0x80000960, 4167, .be 10 11),
  (0x80000994, 4079, .none),
  (0x800009d8, 3422, .be 10 11),
  (0x80000a00, 3337, .none),
  (0x80000a48, 34359748911, .be 10 11),
  (0x80000a70, 34359748826, .none),
  (0x80000ac4, 34359748165, .be 10 11),
  (0x80000af8, 34359748077, .none),
  (0x80000b4c, 34359747416, .be 10 11),
  (0x80000b80, 34359747328, .none),
  (0x80000bc4, 34359746671, .be 10 11),
  (0x80000bec, 34359746586, .none),
  (0x80000c34, 34359744433, .be 10 11),
  (0x80000c5c, 34359744348, .none),
  (0x80000cb0, 34359743687, .be 10 11),
  (0x80000ce4, 34359743599, .none),
  (0x80000d38, 34359742938, .be 10 11),
  (0x80000d6c, 34359742850, .none),
  (0x80000db0, 34359742193, .be 10 11),
  (0x80000dd8, 34359742108, .none),
  (0x80000e20, 34359745811, .be 10 11),
  (0x80000e48, 34359745726, .none),
  (0x80000e9c, 34359745065, .be 10 11),
  (0x80000ed0, 34359744977, .none),
  (0x80000f24, 34359744316, .be 10 11),
  (0x80000f58, 34359744228, .none),
  (0x80000f9c, 34359743571, .be 10 11),
  (0x80000fc4, 34359743486, .none),
  (0x8000100c, 34359743682, .be 10 11),
  (0x80001034, 34359743597, .none),
  (0x80001084, 34359742937, .be 10 11),
  (0x800010b8, 34359742849, .none),
  (0x800010fc, 34359742192, .be 10 11),
  (0x80001124, 34359742107, .none),
  (0x800011b4, 3232, .none),
  (0x800011f0, 17, .none),
  (0x800011f8, 15, .none),
  (0x80001254, 2569, .be 10 11),
  (0x800012f0, 34359742001, .none),
  (0x8000134c, 34359741338, .be 10 11),
  (0x800013c8, 2466, .none),
  (0x800013fc, 19, .none),
  (0x80001400, 18, .none),
  (0x80001468, 34359746479, .none),
  (0x800014bc, 34359745818, .be 10 11),
  (0x8000155c, 34359742001, .none),
  (0x800015b0, 34359741340, .be 10 11),
  (0x80001650, 34359743379, .none),
  (0x800016a4, 34359742718, .be 10 11),
  (0x80001708, 2392, .none),
  (0x80001748, 34359741236, .none),
  (0x800017a0, 34359741161, .none),
  (0x800017c4, 2382, .none),
  (0x800017d8, 2302, .none),
  (0x80001828, 1642, .be 10 11),
  (0x800018a4, 34359745715, .none),
  (0x800018fc, 34359745640, .none),
  (0x80001940, 34359741237, .none),
  (0x80001998, 34359741162, .none),
  (0x800019dc, 34359742615, .none),
  (0x80001a34, 34359742540, .none),
  (0x80001a5c, 34359741151, .none),
  (0x80001a70, 2354, .none),
  (0x80001aa4, 2266, .none),
  (0x80001ae8, 1609, .be 10 11),
  (0x80001b10, 1524, .none),
  (0x80001b60, 864, .be 10 11),
  (0x80001bcc, 1545, .none),
  (0x80001c24, 883, .be 10 11),
  (0x80001c84, 34359745630, .none),
  (0x80001c98, 6833, .none),
  (0x80001ccc, 6745, .none),
  (0x80001d40, 34359741152, .none),
  (0x80001d54, 2355, .none),
  (0x80001d88, 2267, .none),
  (0x80001dcc, 1610, .be 10 11),
  (0x80001df4, 1525, .none),
  (0x80001e48, 864, .be 10 11),
  (0x80001eb0, 34359742530, .none),
  (0x80001ec4, 3733, .none),
  (0x80001ef8, 3645, .none),
  (0x80001f54, 2982, .be 10 11),
  (0x80001fac, 785, .none),
  (0x80002004, 123, .be 14 15),
  (0x80002064, 2889, .none),
  (0x800020ac, 2871, .list (.reg 22)),
  (0x800020c0, 2791, .list (.reg 22)),
  (0x8000211c, 2571, .list (.reg 22)),
  (0x80002138, 2564, .list (.reg 22)),
  (0x80002180, 2352, .none),
  (0x800021b0, 2265, .none),
  (0x800021f4, 1608, .be 10 11),
  (0x8000221c, 1523, .none),
  (0x80002274, 861, .be 10 11),
  (0x800022e4, 2484, .none),
  (0x800022f0, 2346, .none),
  (0x8000230c, 2264, .none),
  (0x80002350, 1607, .be 10 11),
  (0x80002378, 1522, .none),
  (0x800023cc, 861, .be 10 11),
  (0x8000241c, 2568, .list (.slot 0x68)),
  (0x80002420, 2567, .list (.slot 0x68)),
  (0x80002434, 2562, .list (.slot 0x68)),
  (0x800024d0, 6723, .list (.slot 0x68)),
  (0x800024ec, 6641, .list (.slot 0x68)),
  (0x8000252c, 6552, .list (.slot 0x68)),
  (0x80002574, 5897, .be 10 11),
  (0x80002600, 5791, .list (.slot 0x68)),
  (0x80002654, 5698, .list (.slot 0x68)),
  (0x80002690, 5046, .be 10 11),
  (0x800026d4, 4955, .list (.slot 0x68)),
  (0x80002710, 4303, .be 10 11),
  (0x80002754, 4212, .list (.slot 0x68)),
  (0x8000279c, 3557, .be 10 11),
  (0x80002820, 3453, .list (.slot 0x68)),
  (0x80002868, 2798, .be 10 11),
  (0x800029a8, 2714, .list (.slot 0x68)),
  (0x800029c4, 2708, .list (.slot 0x68)),
  (0x800029c8, 2707, .list (.slot 0x68)),
  (0x80002a08, 2639, .list (.slot 0x68)),
  (0x80002a1c, 2637, .list (.slot 0x68)),
  (0x80002a38, 2627, .list (.slot 0x68)),
  (0x80002a6c, 2572, .list (.slot 0x68)),
  (0x80002b50, 765, .none),
  (0x80002bb4, 103, .be 14 15),
  (0x80002c68, 2412, .none),
  (0x80002c94, 765, .none),
  (0x80002cfc, 102, .be 14 15),
  (0x80002db8, 82, .none),
  (0x80002dbc, 81, .none),
  (0x80002dc4, 79, .none),
  (0x80002ecc, 2410, .none),
  (0x80002ee0, 2402, .none),
  (0x80002f14, 2347, .none),
  (0x80002f54, 2491, .none),
  (0x80002f90, 762, .none),
  (0x80002ff0, 101, .be 15 16),
  (0x80003064, 762, .none),
  (0x800030d4, 97, .be 15 16)
]

def budgetAt (pc : Nat) : Nat × Inner := (budgetTable.lookup pc).getD (0, .none)

/-- The length of the `rest` slice at the cut (0 when no location holds it). -/
def restLen (d : CutData) (σ : Sig) (m : Machine) : Nat :=
  match d.rest.find? (·.len) with
  | some r => (r.loc.word σ m).toNat
  | none => 0

def innerOf (σ : Sig) (m : Machine) : Inner → Nat
  | .none => 0
  | .be cur fin => 20 * (m.reg (Fin.ofNat 32 fin) - m.reg (Fin.ofNat 32 cur)).toNat
  | .list l => 256 * (l.word σ m).toNat

/-- The budget at a cut. Deliberately not unfolded by `zesu_simp`: with `budgetAt` rows as
`zesu_simp` lemmas `budget_auto` passes on every leaf and `leaf_auto`'s exit stage (two rules and
`leaf_diag`) then runs and fails on all 486 leaves, `Vc.lean` 274 s → 897 s (LOG.md, S7). -/
def budgetOf (d : CutData) (σ : Sig) (m : Machine) : Nat :=
  (budgetAt d.pc).1 + 256 * restLen d σ m + innerOf σ m (budgetAt d.pc).2

/-! ## The plan -/

def mkCut (d : CutData) : Cut Sig where
  pc := d.pc
  S := d.shape.S
  A := if d.pc = entry then AEntry else ACut d
  env := envOf d.shape
  budget := budgetOf d

/-- The entry as a literal, so `if pc = entry` in a cut's assertion reduces (`leaf_auto`). -/
@[zesu_simp] theorem entry_eq : entry = 0x8000050c := rfl

def leavesTable : List (Nat × List Leaf) := [
  (0x8000050c, run_8000050c_leaves),
  (0x80000574, run_80000574_leaves),
  (0x80000588, run_80000588_leaves),
  (0x8000059c, run_8000059c_leaves),
  (0x800005dc, run_800005dc_leaves),
  (0x800005f0, run_800005f0_leaves),
  (0x80000634, run_80000634_leaves),
  (0x8000065c, run_8000065c_leaves),
  (0x8000069c, run_8000069c_leaves),
  (0x800006b0, run_800006b0_leaves),
  (0x800006f4, run_800006f4_leaves),
  (0x8000071c, run_8000071c_leaves),
  (0x8000075c, run_8000075c_leaves),
  (0x80000770, run_80000770_leaves),
  (0x800007b4, run_800007b4_leaves),
  (0x800007dc, run_800007dc_leaves),
  (0x8000081c, run_8000081c_leaves),
  (0x80000830, run_80000830_leaves),
  (0x80000874, run_80000874_leaves),
  (0x8000089c, run_8000089c_leaves),
  (0x800008e8, run_800008e8_leaves),
  (0x80000910, run_80000910_leaves),
  (0x80000960, run_80000960_leaves),
  (0x80000994, run_80000994_leaves),
  (0x800009d8, run_800009d8_leaves),
  (0x80000a00, run_80000a00_leaves),
  (0x80000a48, run_80000a48_leaves),
  (0x80000a70, run_80000a70_leaves),
  (0x80000ac4, run_80000ac4_leaves),
  (0x80000af8, run_80000af8_leaves),
  (0x80000b4c, run_80000b4c_leaves),
  (0x80000b80, run_80000b80_leaves),
  (0x80000bc4, run_80000bc4_leaves),
  (0x80000bec, run_80000bec_leaves),
  (0x80000c34, run_80000c34_leaves),
  (0x80000c5c, run_80000c5c_leaves),
  (0x80000cb0, run_80000cb0_leaves),
  (0x80000ce4, run_80000ce4_leaves),
  (0x80000d38, run_80000d38_leaves),
  (0x80000d6c, run_80000d6c_leaves),
  (0x80000db0, run_80000db0_leaves),
  (0x80000dd8, run_80000dd8_leaves),
  (0x80000e20, run_80000e20_leaves),
  (0x80000e48, run_80000e48_leaves),
  (0x80000e9c, run_80000e9c_leaves),
  (0x80000ed0, run_80000ed0_leaves),
  (0x80000f24, run_80000f24_leaves),
  (0x80000f58, run_80000f58_leaves),
  (0x80000f9c, run_80000f9c_leaves),
  (0x80000fc4, run_80000fc4_leaves),
  (0x8000100c, run_8000100c_leaves),
  (0x80001034, run_80001034_leaves),
  (0x80001084, run_80001084_leaves),
  (0x800010b8, run_800010b8_leaves),
  (0x800010fc, run_800010fc_leaves),
  (0x80001124, run_80001124_leaves),
  (0x800011b4, run_800011b4_leaves),
  (0x800011f0, run_800011f0_leaves),
  (0x800011f8, run_800011f8_leaves),
  (0x80001254, run_80001254_leaves),
  (0x800012f0, run_800012f0_leaves),
  (0x8000134c, run_8000134c_leaves),
  (0x800013c8, run_800013c8_leaves),
  (0x800013fc, run_800013fc_leaves),
  (0x80001400, run_80001400_leaves),
  (0x80001468, run_80001468_leaves),
  (0x800014bc, run_800014bc_leaves),
  (0x8000155c, run_8000155c_leaves),
  (0x800015b0, run_800015b0_leaves),
  (0x80001650, run_80001650_leaves),
  (0x800016a4, run_800016a4_leaves),
  (0x80001708, run_80001708_leaves),
  (0x80001748, run_80001748_leaves),
  (0x800017a0, run_800017a0_leaves),
  (0x800017c4, run_800017c4_leaves),
  (0x800017d8, run_800017d8_leaves),
  (0x80001828, run_80001828_leaves),
  (0x800018a4, run_800018a4_leaves),
  (0x800018fc, run_800018fc_leaves),
  (0x80001940, run_80001940_leaves),
  (0x80001998, run_80001998_leaves),
  (0x800019dc, run_800019dc_leaves),
  (0x80001a34, run_80001a34_leaves),
  (0x80001a5c, run_80001a5c_leaves),
  (0x80001a70, run_80001a70_leaves),
  (0x80001aa4, run_80001aa4_leaves),
  (0x80001ae8, run_80001ae8_leaves),
  (0x80001b10, run_80001b10_leaves),
  (0x80001b60, run_80001b60_leaves),
  (0x80001bcc, run_80001bcc_leaves),
  (0x80001c24, run_80001c24_leaves),
  (0x80001c84, run_80001c84_leaves),
  (0x80001c98, run_80001c98_leaves),
  (0x80001ccc, run_80001ccc_leaves),
  (0x80001d40, run_80001d40_leaves),
  (0x80001d54, run_80001d54_leaves),
  (0x80001d88, run_80001d88_leaves),
  (0x80001dcc, run_80001dcc_leaves),
  (0x80001df4, run_80001df4_leaves),
  (0x80001e48, run_80001e48_leaves),
  (0x80001eb0, run_80001eb0_leaves),
  (0x80001ec4, run_80001ec4_leaves),
  (0x80001ef8, run_80001ef8_leaves),
  (0x80001f54, run_80001f54_leaves),
  (0x80001fac, run_80001fac_leaves),
  (0x80002004, run_80002004_leaves),
  (0x80002064, run_80002064_leaves),
  (0x800020ac, run_800020ac_leaves),
  (0x800020c0, run_800020c0_leaves),
  (0x8000211c, run_8000211c_leaves),
  (0x80002138, run_80002138_leaves),
  (0x80002180, run_80002180_leaves),
  (0x800021b0, run_800021b0_leaves),
  (0x800021f4, run_800021f4_leaves),
  (0x8000221c, run_8000221c_leaves),
  (0x80002274, run_80002274_leaves),
  (0x800022e4, run_800022e4_leaves),
  (0x800022f0, run_800022f0_leaves),
  (0x8000230c, run_8000230c_leaves),
  (0x80002350, run_80002350_leaves),
  (0x80002378, run_80002378_leaves),
  (0x800023cc, run_800023cc_leaves),
  (0x8000241c, run_8000241c_leaves),
  (0x80002420, run_80002420_leaves),
  (0x80002434, run_80002434_leaves),
  (0x800024d0, run_800024d0_leaves),
  (0x800024ec, run_800024ec_leaves),
  (0x8000252c, run_8000252c_leaves),
  (0x80002574, run_80002574_leaves),
  (0x80002600, run_80002600_leaves),
  (0x80002654, run_80002654_leaves),
  (0x80002690, run_80002690_leaves),
  (0x800026d4, run_800026d4_leaves),
  (0x80002710, run_80002710_leaves),
  (0x80002754, run_80002754_leaves),
  (0x8000279c, run_8000279c_leaves),
  (0x80002820, run_80002820_leaves),
  (0x80002868, run_80002868_leaves),
  (0x800029a8, run_800029a8_leaves),
  (0x800029c4, run_800029c4_leaves),
  (0x800029c8, run_800029c8_leaves),
  (0x80002a08, run_80002a08_leaves),
  (0x80002a1c, run_80002a1c_leaves),
  (0x80002a38, run_80002a38_leaves),
  (0x80002a6c, run_80002a6c_leaves),
  (0x80002b50, run_80002b50_leaves),
  (0x80002bb4, run_80002bb4_leaves),
  (0x80002c68, run_80002c68_leaves),
  (0x80002c94, run_80002c94_leaves),
  (0x80002cfc, run_80002cfc_leaves),
  (0x80002db8, run_80002db8_leaves),
  (0x80002dbc, run_80002dbc_leaves),
  (0x80002dc4, run_80002dc4_leaves),
  (0x80002ecc, run_80002ecc_leaves),
  (0x80002ee0, run_80002ee0_leaves),
  (0x80002f14, run_80002f14_leaves),
  (0x80002f54, run_80002f54_leaves),
  (0x80002f90, run_80002f90_leaves),
  (0x80002ff0, run_80002ff0_leaves),
  (0x80003064, run_80003064_leaves),
  (0x800030d4, run_800030d4_leaves)
]

def leavesAt (pc : Nat) : List Leaf := (leavesTable.lookup pc).getD []

def calleeAt (r : Nat) : Option (Callee Sig zesuImage) :=
  ((table.find? (·.pc = r)).bind (·.site)).map (calleeOf ·.kind)

def vcPlan : Plan Sig zesuImage where
  cuts := table.map mkCut
  fuel := 300
  leaves := leavesAt
  callee := calleeAt
  Post := fun σ => Post σ.A σ.g σ.m

end ZesuExec.Fn.DTF
