import ZesuExec.Fn.Scratch.AllocRuns
import ZesuExec.Fn.Scratch.AllocSpec
import ZesuExec.Fn.Scratch.Vc
import ZesuExec.Fn.Stage

/-!
# `scratch_arena.alloc` in the obligation framework: assertions, plan, cut lemmas

Plan `SA` over `zesuImage` (the run reads the child's vtable from rodata), `σ = SigA`: the child
allocator's contract `A`, its live blocks `L`, the entry machine `e`. Cut points and regions as
in `Fn/Scratch/AllocRuns.lean`. Inside the frame every assertion states `FrRegs` (the registers
the prologue set: `sp`, `s0 = e.sp`, `s1 = len`, `s2 = align`, `s3 = ctx`) and `FrMem` (the saved
`ra`, `s0`–`s5` and the byte `align & 63 = align` at `e.sp - 59`). The call of the child's `alloc` returns
to `0x800db87c`; its callee contract is `A.alloc_spec L` with `Preserved` added
(`Reaches.preserve`).
-/

namespace ZesuExec.Fn.Scratch
open ZesuExec ZesuExec.Sym ZesuExec.Machine ZesuExec.Vc

structure SigA where
  A : AllocContract zesuImage
  L : List (Word × Nat)
  e : Machine

/-- `AllocPreS` with names. -/
structure EntryS (A : AllocContract zesuImage) (L : List (Word × Nat)) (m : Machine) : Prop where
  ro : RodataLoaded zesuImage m
  ra : RetAligned m
  stack : StackOk m 80
  ctxRam : RamRange (m.reg 10) 32
  ctxP : Present m (m.reg 10) 32
  vt : m.load (m.reg 10 + 8) 8 = some (BitVec.ofNat 64 allocVt)
  k64 : (m.reg 12).toNat < 64
  need : needN m ≤ 2 ^ 62
  last : (lastSize m).toNat < 2 ^ 62
  dctx : Fn.Disjoint (m.reg 10, 32) (m.reg 2 - 80, 80)
  heap : A.Heap L m
  priv : ∀ a, InRange (m.reg 10) 32 a ∨ InRange (m.reg 2 - 80) 80 a → ¬ A.Priv L a
  chunk : chunks m ≠ 0 → RamRange (chunks m) 24 ∧ Present m (chunks m + 8) 16 ∧ used m ≤ cap m ∧
    (chunks m).toNat + (cap m).toNat ≤ Layout.ramHi ∧
    Fn.Disjoint (chunks m + 8, 16) (m.reg 10, 32) ∧
    Fn.Disjoint (chunks m + 8, 16) (m.reg 2 - 80, 80) ∧
    ∀ a, InRange (chunks m + 8) 16 a → ¬ A.Priv L a

theorem EntryS.of {A : AllocContract zesuImage} {L : List (Word × Nat)} {m : Machine}
    (h : AllocPreS A L m) : EntryS A L m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- Frame offsets of the saved registers. -/
def savedRegs : List (Nat × Fin 32) :=
  [(0x38, 1), (0x30, 8), (0x28, 9), (0x20, 18), (0x18, 19), (0x10, 20), (8, 21)]

/-- The registers the prologue set. -/
def FrRegs (e m : Machine) : Prop :=
  m.reg 2 = e.reg 2 - 64 ∧ m.reg 8 = e.reg 2 ∧ m.reg 9 = e.reg 11 ∧ m.reg 18 = e.reg 12 ∧
    m.reg 19 = e.reg 10 ∧ ∀ i : Fin 32, i.val ∈ [22, 23, 24, 25, 26, 27] → m.reg i = e.reg i

/-- The saved registers and the alignment byte in the frame. -/
def FrMem (e m : Machine) : Prop :=
  (∀ p ∈ savedRegs, m.load (e.reg 2 - 64 + BitVec.ofNat 64 p.1) 8 = some (e.reg p.2)) ∧
    m.load (e.reg 2 - 64 + BitVec.ofNat 64 5) 1 = some (e.reg 12)

def Fr64 (e : Machine) (a : Word) : Prop := InRange (e.reg 2 - 64) 64 a
def Fr80 (e : Machine) (a : Word) : Prop := InRange (e.reg 2 - 80) 80 a

def AE (g : SigA) (m : Machine) : Prop :=
  m = g.e ∧ m.pc.toNat = 0x800db7a4 ∧ AllocPreS g.A g.L g.e

def AJ (g : SigA) (m : Machine) : Prop :=
  AllocPreS g.A g.L g.e ∧ m.pc.toNat = 0x800db7e4 ∧ FrRegs g.e m ∧ FrMem g.e m ∧
    m.reg 10 = chunks g.e ∧ chunks g.e ≠ 0 ∧ SameOutside (Fr64 g.e) g.e m ∧
    Present m (g.e.reg 2 - 80) 80

def AS (g : SigA) (m : Machine) : Prop :=
  AllocPreS g.A g.L g.e ∧ m.pc.toNat = 0x800db820 ∧ FrRegs g.e m ∧ FrMem g.e m ∧ ¬ Fits g.e ∧
    SameOutside (Fr64 g.e) g.e m ∧ Present m (g.e.reg 2 - 80) 80

/-- The child's answer, as `A.alloc_spec` gives it for `newSize` bytes. -/
def Out (g : SigA) (m : Machine) : Prop :=
  (m.reg 10 = 0 ∧ g.A.Heap g.L m) ∨
  (m.reg 10 ≠ 0 ∧ g.A.Heap (g.L ++ [(m.reg 10, newSize g.e)]) m ∧
    RamRange (m.reg 10) (newSize g.e) ∧ Present m (m.reg 10) (newSize g.e) ∧
    (∀ a, InRange (m.reg 10) (newSize g.e) a → g.A.Priv g.L a) ∧
    (∀ a, g.A.Priv (g.L ++ [(m.reg 10, newSize g.e)]) a → g.A.Priv g.L a))

def AR (g : SigA) (m : Machine) : Prop :=
  AllocPreS g.A g.L g.e ∧ m.pc.toNat = 0x800db87c ∧ FrRegs g.e m ∧ FrMem g.e m ∧ ¬ Fits g.e ∧
    m.reg 20 = BitVec.ofNat 64 (newSize g.e) ∧
    SameOutside (fun a => g.A.Priv g.L a ∨ Fr80 g.e a) g.e m ∧
    Present m (g.e.reg 2 - 80) 80 ∧ RodataLoaded zesuImage m ∧ Out g m

def AN (g : SigA) (m : Machine) : Prop :=
  AllocPreS g.A g.L g.e ∧ m.pc.toNat = 0x800db880 ∧ FrRegs g.e m ∧ FrMem g.e m ∧ ¬ Fits g.e ∧
    m.reg 20 = BitVec.ofNat 64 (newSize g.e) ∧
    SameOutside (fun a => g.A.Priv g.L a ∨ Fr80 g.e a) g.e m ∧
    Present m (g.e.reg 2 - 80) 80 ∧ RodataLoaded zesuImage m ∧ m.reg 10 ≠ 0 ∧ Out g m

def shapeAE (m : Machine) : Shape := [((m.reg 2 - 64, 64), frame64R), ((m.reg 10, 32), arenaR)]
def shapeIn (m : Machine) : Shape := [((m.reg 2, 64), frame64R), ((m.reg 19, 32), arenaR)]
def shapeAJ (m : Machine) : Shape := shapeIn m ++ [((m.reg 10 + 8, 16), capR)]
def shapeAN (m : Machine) : Shape := shapeIn m ++ [((m.reg 10, 24), hdrR)]

def envA (sh : Machine → Shape) (_ : SigA) (m : Machine) : Env := entryEnv m ((sh m).map (·.1))

theorem envA_var (sh : Machine → Shape) (g : SigA) (m : Machine) (i : Fin 32) :
    (envA sh g m).vars i.val = m.reg i := by simp [envA, entryEnv]

def cAE : Cut SigA := ⟨0x800db7a4, SAE, AE, envA shapeAE, fun _ _ => 133⟩
def cAJ : Cut SigA := ⟨0x800db7e4, SAJ, AJ, envA shapeAJ, fun _ _ => 117⟩
def cAS : Cut SigA := ⟨0x800db820, SAS, AS, envA shapeIn, fun _ _ => 105⟩
def cAR : Cut SigA := ⟨0x800db87c, SAS, AR, envA shapeIn, fun _ _ => 32⟩
def cAN : Cut SigA := ⟨0x800db880, SAN, AN, envA shapeAN, fun _ _ => 31⟩

/-- The child's `alloc` (`A.alloc_spec`), with `Preserved`. -/
def childAlloc : Callee SigA zesuImage where
  entry := Fn.allocEntry
  bound := 53
  Pre g _ m := g.A.Heap g.L m ∧ 0 < (m.reg 11).toNat ∧ (m.reg 11).toNat < 2 ^ 63 ∧
      (m.reg 12).toNat ≤ 4 ∧ StackOk m 16 ∧ RetAligned m ∧ Fn.CalleeFrameFree (g.A.Priv g.L) m
  Post g _ m m' := (Returns m m' ∧
      SameOutside (fun a => g.A.Priv g.L a ∨ InRange (m.reg 2 - 16) 16 a) m m' ∧
      ((m'.reg 10 = 0 ∧ g.A.Heap g.L m') ∨
       (m'.reg 10 ≠ 0 ∧ g.A.Heap (g.L ++ [(m'.reg 10, (m.reg 11).toNat)]) m' ∧
        RamRange (m'.reg 10) (m.reg 11).toNat ∧ Present m' (m'.reg 10) (m.reg 11).toNat ∧
        (∀ a, InRange (m'.reg 10) (m.reg 11).toNat a → g.A.Priv g.L a) ∧
        (∀ a, g.A.Priv (g.L ++ [(m'.reg 10, (m.reg 11).toNat)]) a → g.A.Priv g.L a)))) ∧
      Preserved m m'
  spec g _ := fun m hpc hpre => Reaches.preserve (g.A.alloc_spec g.L m hpc hpre)

def saPlan : Plan SigA zesuImage where
  cuts := [cAE, cAJ, cAS, cAR, cAN]
  fuel := 64
  leaves := fun pc => if pc = 0x800db7a4 then saRunE_leaves else if pc = 0x800db7e4 then saRunJ_leaves
    else if pc = 0x800db820 then saRunS_leaves else if pc = 0x800db87c then saRunR_leaves
    else if pc = 0x800db880 then saRunN_leaves else []
  callee := fun r => if r = 0x800db87c then some childAlloc else none
  Post g m' := AllocPostS g.A g.L g.e m'

zesu_plan SA := saPlan

/-! ## Cut lemmas -/

theorem cutOK_A {P : Plan SigA zesuImage} {pc : Nat} {ov : Nat → Option Sym}
    {rs : List Region} {A : SigA → Machine → Prop} {sh : Machine → Shape}
    {bud : SigA → Machine → Nat}
    (hrs : ∀ m, (sh m).map (·.2) = rs)
    (h : ∀ g m, A g m → (∀ p ∈ sh m, RegionOk p) ∧ ((sh m).map (·.1)).Pairwise Fn.Disjoint ∧
      (∀ i : Fin 32, i.val ≠ 0 → ∀ s, ov i.val = some s →
        s.eval (entryEnv m ((sh m).map (·.1))) = m.reg i) ∧
      (∀ r j, r < rs.length → j < (entryEnv m ((sh m).map (·.1))).size r →
        (m.mem ((entryEnv m ((sh m).map (·.1))).base r + BitVec.ofNat 64 j)).isSome) ∧
      m.load ((entryEnv m ((sh m).map (·.1))).base 1 + 8) 8 = some (BitVec.ofNat 64 allocVt) ∧
      RodataLoaded zesuImage m ∧ m.pc.toNat = pc) :
    CutOK P (⟨pc, Fn.entryState ov rs knownS, A, fun _ m => entryEnv m ((sh m).map (·.1)), bud⟩ :
      Cut SigA) := by
  intro g m hA
  obtain ⟨hok, hd, hov, hpres, hvt, hro, hpc⟩ := h g m hA
  have hwf := entry_wf (m := m) (ov := ov) (ks := knownS) (sh m) hok hd
  have hmt := entry_match (m := m) (regs := (sh m).map (·.1)) (ov := ov) (rs := rs) (ks := knownS)
    hov hpres (by
      intro k hk t ht
      simp only [knownS, List.mem_singleton] at hk; subst hk
      have := load_bytes hvt (by decide) t ht
      rw [show (entryEnv m ((sh m).map (·.1))).base 1 + 8 + BitVec.ofNat 64 t =
        (entryEnv m ((sh m).map (·.1))).base 1 + BitVec.ofNat 64 (8 + t) by bv_omega] at this
      simp [Env.byte0, entryEnv, this, Sym.eval] at *
      simp [Env.base] at this ⊢; rw [this]; rfl)
  rw [hrs m] at hwf
  exact ⟨hwf, hmt, hro, hpc⟩

/-! ## Facts the cuts share -/

section
variable {A : AllocContract zesuImage} {L : List (Word × Nat)} {e m : Machine}

theorem sp_facts (E : EntryS A L e) :
    (e.reg 2 - 64).toNat = (e.reg 2).toNat - 64 ∧ (e.reg 2 - 80).toNat = (e.reg 2).toNat - 80 ∧
    (e.reg 2).toNat % 16 = 0 ∧ Layout.ramLo + 80 ≤ (e.reg 2).toNat ∧
    (e.reg 2).toNat ≤ Layout.ramHi := by
  obtain ⟨hal, hlo, hhi, -⟩ := E.stack
  unfold Layout.ramLo at hlo
  refine ⟨?_, ?_, hal, hlo, hhi⟩ <;> (rw [BitVec.toNat_sub]; simp; omega)

theorem regionOk_fr (E : EntryS A L e) : RegionOk ((e.reg 2 - 64, 64), frame64R) := by
  obtain ⟨h64, -, hal, hlo, hhi⟩ := sp_facts E
  refine ⟨by simp [frame64R], by simp [frame64R, h64]; omega, ?_⟩
  simp [frame64R, writable, inRange, h64]; unfold Layout.ramLo Layout.ramHi at *; omega

theorem regionOk_ctx (E : EntryS A L e) : RegionOk ((e.reg 10, 32), arenaR) := by
  have := E.ctxRam
  refine ⟨by simp [arenaR], by simp [arenaR, Nat.mod_one], ?_⟩
  simp [arenaR, writable, inRange]; unfold RamRange at this; omega

theorem disj_fr_ctx (E : EntryS A L e) : Fn.Disjoint (e.reg 2 - 64, 64) (e.reg 10, 32) := by
  have := E.dctx; obtain ⟨h64, h80, -⟩ := sp_facts E
  unfold Fn.Disjoint at *; simp only at *; omega

theorem fr64_80 (E : EntryS A L e) {a : Word} (h : Fr64 e a) : Fr80 e a := by
  obtain ⟨h64, h80, -⟩ := sp_facts E
  unfold Fr64 Fr80 InRange at *; rw [h64] at h; rw [h80]; omega

theorem fr80_ram (E : EntryS A L e) {a : Word} (h : Fr80 e a) : Layout.ramLo ≤ a.toNat := by
  obtain ⟨-, h80, -, hlo, -⟩ := sp_facts E
  unfold Fr80 InRange at h; rw [h80] at h; omega

/-- Frame bytes from `Present m (e.sp - 80) 80`. -/
theorem fr_present (hp : Present m (e.reg 2 - 80) 80) {j : Nat} (hj : j < 64) :
    (m.mem (e.reg 2 - 64 + BitVec.ofNat 64 j)).isSome := by
  have := hp (16 + j) (by omega)
  rwa [show e.reg 2 - 80 + BitVec.ofNat 64 (16 + j) = e.reg 2 - 64 + BitVec.ofNat 64 j by
    bv_omega] at this

theorem ctx_in (E : EntryS A L e) {j : Nat} (hj : j < 32) :
    InRange (e.reg 10) 32 (e.reg 10 + BitVec.ofNat 64 j) := by
  have := E.ctxRam; unfold RamRange Layout.ramHi at this
  exact inRange_add (by omega) hj

theorem ctx_not_fr80 (E : EntryS A L e) {j : Nat} (hj : j < 32) :
    ¬ Fr80 e (e.reg 10 + BitVec.ofNat 64 j) := by
  have hd := E.dctx; have hc := ctx_in E hj
  unfold Fr80 InRange at *; unfold Fn.Disjoint at hd; simp only at hd; omega

/-- The arena's bytes are the entry's while changes stay in `Priv L` and the 80 frame bytes. -/
theorem ctx_mem (E : EntryS A L e) {R : Word → Prop} (hso : SameOutside R e m)
    (hR : ∀ a, R a → A.Priv L a ∨ Fr80 e a) {j : Nat} (hj : j < 32) :
    m.mem (e.reg 10 + BitVec.ofNat 64 j) = e.mem (e.reg 10 + BitVec.ofNat 64 j) :=
  hso _ fun h => (hR _ h).elim (E.priv _ (.inl (ctx_in E hj))) (ctx_not_fr80 E hj)

theorem vt_of (E : EntryS A L e) {R : Word → Prop} (hso : SameOutside R e m)
    (hR : ∀ a, R a → A.Priv L a ∨ Fr80 e a) :
    m.load (e.reg 10 + 8) 8 = some (BitVec.ofNat 64 allocVt) := by
  rw [load_congr fun t ht => ?_]
  · exact E.vt
  rw [show e.reg 10 + 8 + BitVec.ofNat 64 t = e.reg 10 + BitVec.ofNat 64 (8 + t) by bv_omega]
  exact ctx_mem E hso hR (by omega)

theorem ro_of (E : EntryS A L e) {R : Word → Prop} (hso : SameOutside R e m)
    (hR : ∀ a, R a → Layout.ramLo ≤ a.toNat) : RodataLoaded zesuImage m := by
  intro a b h
  have ha := zesu_rodata_range h
  unfold Layout.rodataHi at ha
  rw [hso _ fun hr => by have := hR _ hr; simp at this; unfold Layout.ramLo at this; omega]
  exact E.ro a b h

theorem c8 (E : EntryS A L e) (hne : chunks e ≠ 0) :
    (chunks e + 8).toNat = (chunks e).toNat + 8 := by
  have := (E.chunk hne).1; unfold RamRange Layout.ramHi at this
  rw [BitVec.toNat_add]; simp; omega

theorem hdr_not_fr80 (E : EntryS A L e) (hne : chunks e ≠ 0) {j : Nat} (hj : j < 16) :
    ¬ Fr80 e (chunks e + 8 + BitVec.ofNat 64 j) := by
  obtain ⟨hr, -, -, -, -, hd, -⟩ := E.chunk hne
  have h8 := c8 E hne
  unfold RamRange Layout.ramHi at hr
  have hin := inRange_add (b := chunks e + 8) (n := 16) (by omega) hj
  unfold Fr80 InRange at *; unfold Fn.Disjoint at hd; simp only at hd; omega

theorem hdr_mem (E : EntryS A L e) (hne : chunks e ≠ 0) (hso : SameOutside (Fr64 e) e m)
    {j : Nat} (hj : j < 16) :
    m.mem (chunks e + 8 + BitVec.ofNat 64 j) = e.mem (chunks e + 8 + BitVec.ofNat 64 j) :=
  hso _ fun h => hdr_not_fr80 E hne hj (fr64_80 E h)

theorem regionOk_hdr (E : EntryS A L e) (hne : chunks e ≠ 0) :
    RegionOk ((chunks e + 8, 16), capR) := by
  have := (E.chunk hne).1; have h8 := c8 E hne
  unfold RamRange at this
  exact regionOk_cap (by omega) (by omega)

theorem disj_fr_hdr (E : EntryS A L e) (hne : chunks e ≠ 0) :
    Fn.Disjoint (e.reg 2 - 64, 64) (chunks e + 8, 16) := by
  obtain ⟨-, -, -, -, -, hd, -⟩ := E.chunk hne
  obtain ⟨h64, h80, -⟩ := sp_facts E
  unfold Fn.Disjoint at *; simp only at *; omega

theorem disj_ctx_hdr (E : EntryS A L e) (hne : chunks e ≠ 0) :
    Fn.Disjoint (e.reg 10, 32) (chunks e + 8, 16) := by
  obtain ⟨-, -, -, -, hd, -, -⟩ := E.chunk hne
  unfold Fn.Disjoint at *; simp only at *; omega

end

/-! ## Cut lemmas -/

theorem SA.cut_800db7a4 : CutOK SA.plan SA.plan.cuts[0]! :=
  cutOK_A (sh := shapeAE) (fun _ => rfl) fun g m h => by
    obtain ⟨rfl, hpc, hpre⟩ := h
    have E := EntryS.of hpre
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, ?_, E.ro, hpc⟩
    · simp only [shapeAE, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl)
      · exact regionOk_fr E
      · exact regionOk_ctx E
    · simp only [shapeAE, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
        forall_eq, List.Pairwise.nil, and_true, List.not_mem_nil, false_implies, implies_true]
      exact disj_fr_ctx E
    · simp only [ovAE] at hs
      split at hs
      · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAE]; bv_omega
      · split at hs
        · next h => cases hs; have : i = 10 := Fin.ext h; subst this
                    simp [Sym.eval, Env.base, entryEnv, shapeAE]
        · simp at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl <;> simp [Env.size, Env.base, entryEnv, shapeAE] at hj ⊢
      · exact fr_present (fun j hj => by simpa using E.stack.2.2.2 j hj) hj
      · exact E.ctxP j hj
    · simpa [Env.base, entryEnv, shapeAE] using E.vt

/-- The obligations of a cut inside the frame, for the frame and the arena. -/
theorem in_frame {A : AllocContract zesuImage} {L : List (Word × Nat)} {e m : Machine}
    (E : EntryS A L e) (hfr : FrRegs e m) {R : Word → Prop} (hso : SameOutside R e m)
    (hR : ∀ a, R a → A.Priv L a ∨ Fr80 e a) (hp : Present m (e.reg 2 - 80) 80) :
    RegionOk ((m.reg 2, 64), frame64R) ∧ RegionOk ((m.reg 19, 32), arenaR) ∧
    Fn.Disjoint (m.reg 2, 64) (m.reg 19, 32) ∧
    (∀ j < 64, (m.mem (m.reg 2 + BitVec.ofNat 64 j)).isSome) ∧
    (∀ j < 32, (m.mem (m.reg 19 + BitVec.ofNat 64 j)).isSome) ∧
    m.load (m.reg 19 + 8) 8 = some (BitVec.ofNat 64 allocVt) ∧ m.reg 2 + 64 = m.reg 8 := by
  obtain ⟨r2, r8, -, -, r19, -⟩ := hfr
  rw [r2, r19, r8]
  refine ⟨regionOk_fr E, regionOk_ctx E, disj_fr_ctx E, fun j hj => fr_present hp hj,
    fun j hj => ?_, vt_of E hso hR, by bv_omega⟩
  rw [ctx_mem E hso hR hj]; exact E.ctxP j hj

theorem SA.cut_800db7e4 : CutOK SA.plan SA.plan.cuts[1]! :=
  cutOK_A (sh := shapeAJ) (fun _ => rfl) fun g m h => by
    obtain ⟨hpre, hpc, hfr, -, h10, hne, hso, hp⟩ := h
    have E := EntryS.of hpre
    have hR : ∀ a, Fr64 g.e a → g.A.Priv g.L a ∨ Fr80 g.e a := fun a h => .inr (fr64_80 E h)
    obtain ⟨o0, o1, d01, p0, p1, hvt, h28⟩ := in_frame E hfr hso hR hp
    obtain ⟨r2, -, -, -, r19, -⟩ := hfr
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, ?_,
      ro_of E hso (fun a h => fr80_ram E (fr64_80 E h)), hpc⟩
    · simp only [shapeAJ, shapeIn, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl)
      · exact o0
      · exact o1
      · rw [h10]; exact regionOk_hdr E hne
    · simp only [shapeAJ, shapeIn, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, List.not_mem_nil, false_implies, implies_true, or_false]
      rw [h10, r2, r19]; rw [r2, r19] at d01
      exact ⟨⟨d01, disj_fr_hdr E hne⟩, disj_ctx_hdr E hne⟩
    · simp only [ovAJ, ovIn] at hs
      split at hs
      · next h => cases hs; have : i = 10 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAJ, shapeIn]; bv_omega
      split at hs
      · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAJ, shapeIn]
      split at hs
      · next h => cases hs; have : i = 8 := Fin.ext h; subst this
                  simpa [Sym.eval, Env.base, entryEnv, shapeAJ, shapeIn] using h28
      split at hs
      · next h => cases hs; have : i = 19 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAJ, shapeIn]
      · simp at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr' with rfl | rfl | rfl <;>
        simp [Env.size, Env.base, entryEnv, shapeAJ, shapeIn] at hj ⊢
      · exact p0 j hj
      · exact p1 j hj
      · have h1 := hdr_mem E hne hso hj; have h2 := (E.chunk hne).2.1 j hj
        simp only [h10]; simp at h1 h2 ⊢; rw [h1]; exact h2
    · simpa [Env.base, entryEnv, shapeAJ, shapeIn] using hvt

/-- Cut lemma for the cuts whose shape is `shapeIn`. -/
theorem cut_in {P : Plan SigA zesuImage} {pc : Nat} {A : SigA → Machine → Prop}
    {bud : SigA → Machine → Nat}
    (h : ∀ g m, A g m → ∃ R : Word → Prop, EntryS g.A g.L g.e ∧ FrRegs g.e m ∧
      SameOutside R g.e m ∧ (∀ a, R a → g.A.Priv g.L a ∨ Fr80 g.e a) ∧
      Present m (g.e.reg 2 - 80) 80 ∧ RodataLoaded zesuImage m ∧ m.pc.toNat = pc) :
    CutOK P (⟨pc, SAS, A, envA shapeIn, bud⟩ : Cut SigA) :=
  cutOK_A (sh := shapeIn) (fun _ => rfl) fun g m hA => by
    obtain ⟨R, E, hfr, hso, hR, hp, hro, hpc⟩ := h g m hA
    obtain ⟨o0, o1, d01, p0, p1, hvt, h28⟩ := in_frame E hfr hso hR hp
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, ?_, hro, hpc⟩
    · simp only [shapeIn, List.mem_cons, List.mem_nil_iff, or_false]
      rintro p (rfl | rfl)
      · exact o0
      · exact o1
    · simp only [shapeIn, List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
        forall_eq, List.Pairwise.nil, and_true, List.not_mem_nil, false_implies, implies_true]
      exact d01
    · simp only [ovIn] at hs
      split at hs
      · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeIn]
      split at hs
      · next h => cases hs; have : i = 8 := Fin.ext h; subst this
                  simpa [Sym.eval, Env.base, entryEnv, shapeIn] using h28
      split at hs
      · next h => cases hs; have : i = 19 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeIn]
      · simp at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl <;> simp [Env.size, Env.base, entryEnv, shapeIn] at hj ⊢
      · exact p0 j hj
      · exact p1 j hj
    · simpa [Env.base, entryEnv, shapeIn] using hvt

theorem SA.cut_800db820 : CutOK SA.plan SA.plan.cuts[2]! :=
  cut_in fun g m h => by
    obtain ⟨hpre, hpc, hfr, -, -, hso, hp⟩ := h
    have E := EntryS.of hpre
    exact ⟨_, E, hfr, hso, fun a h => .inr (fr64_80 E h), hp,
      ro_of E hso (fun a h => fr80_ram E (fr64_80 E h)), hpc⟩

theorem SA.cut_800db87c : CutOK SA.plan SA.plan.cuts[3]! :=
  cut_in fun g m h => by
    obtain ⟨hpre, hpc, hfr, -, -, -, hso, hp, hro, -⟩ := h
    exact ⟨_, EntryS.of hpre, hfr, hso, fun a h => h, hp, hro, hpc⟩

theorem needN_ge (m : Machine) : 24 ≤ needN m := by
  unfold needN; have := Nat.one_le_two_pow (n := (m.reg 12).toNat); omega

theorem newSize_ge (m : Machine) : needN m ≤ newSize m := by
  unfold newSize; split <;> omega

theorem newSize_24 (m : Machine) : 24 ≤ newSize m := Nat.le_trans (needN_ge m) (newSize_ge m)

theorem newSize_lt {A : AllocContract zesuImage} {L : List (Word × Nat)} {e : Machine}
    (E : EntryS A L e) : newSize e < 2 ^ 63 := by
  have := E.need; have := E.last; unfold newSize; split <;> omega

/-- The child's new block, 24 header bytes at least, is in RAM, in `Priv L`, apart from the frame
and the arena. -/
theorem blk_facts {A : AllocContract zesuImage} {L : List (Word × Nat)} {e : Machine}
    (E : EntryS A L e) {b : Word} (hr : RamRange b (newSize e))
    (hpv : ∀ a, InRange b (newSize e) a → A.Priv L a) :
    RegionOk ((b, 24), hdrR) ∧ Fn.Disjoint (e.reg 2 - 64, 64) (b, 24) ∧
      Fn.Disjoint (e.reg 10, 32) (b, 24) := by
  have h24 := newSize_24 e
  unfold RamRange at hr
  have hin : ∀ a, InRange b 24 a → A.Priv L a := fun a h => hpv a ⟨h.1, by have := h.2; omega⟩
  refine ⟨⟨by simp [hdrR], by simp [hdrR, Nat.mod_one], ?_⟩, ?_, ?_⟩
  · simp [hdrR, writable, inRange]; omega
  · exact Alloc.disjoint_of_avoid (by decide) (by decide) fun a ha hb =>
      E.priv a (.inr (by unfold InRange at *; obtain ⟨h64, h80, -⟩ := sp_facts E; omega)) (hin a hb)
  · exact Alloc.disjoint_of_avoid (by decide) (by decide) fun a ha hb =>
      E.priv a (.inl ha) (hin a hb)

theorem SA.cut_800db880 : CutOK SA.plan SA.plan.cuts[4]! :=
  cutOK_A (sh := shapeAN) (fun _ => rfl) fun g m h => by
    obtain ⟨hpre, hpc, hfr, -, -, -, hso, hp, hro, hne, hout⟩ := h
    have E := EntryS.of hpre
    obtain ⟨o0, o1, d01, p0, p1, hvt, h28⟩ := in_frame E hfr hso (fun a h => h) hp
    obtain ⟨r2, -, -, -, r19, -⟩ := hfr
    obtain ⟨h0, -⟩ | ⟨-, -, hbr, hbp, hbpv, -⟩ := hout
    · exact absurd h0 hne
    obtain ⟨ob, dfb, dcb⟩ := blk_facts E hbr hbpv
    refine ⟨?_, ?_, fun i hi s hs => ?_, fun r j hr hj => ?_, ?_, hro, hpc⟩
    · simp only [shapeAN, shapeIn, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_nil_iff, or_false]
      rintro p (rfl | rfl | rfl)
      · exact o0
      · exact o1
      · exact ob
    · simp only [shapeAN, shapeIn, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, List.not_mem_nil, false_implies, implies_true, or_false]
      rw [r2, r19]; rw [r2, r19] at d01
      exact ⟨⟨d01, dfb⟩, dcb⟩
    · simp only [ovAN, ovIn] at hs
      split at hs
      · next h => cases hs; have : i = 10 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAN, shapeIn]
      split at hs
      · next h => cases hs; have : i = 2 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAN, shapeIn]
      split at hs
      · next h => cases hs; have : i = 8 := Fin.ext h; subst this
                  simpa [Sym.eval, Env.base, entryEnv, shapeAN, shapeIn] using h28
      split at hs
      · next h => cases hs; have : i = 19 := Fin.ext h; subst this
                  simp [Sym.eval, Env.base, entryEnv, shapeAN, shapeIn]
      · simp at hs
    · simp only [List.length_cons, List.length_nil] at hr
      have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
      rcases hr' with rfl | rfl | rfl <;>
        simp [Env.size, Env.base, entryEnv, shapeAN, shapeIn] at hj ⊢
      · exact p0 j hj
      · exact p1 j hj
      · exact hbp j (by have := newSize_24 g.e; omega)
    · simpa [Env.base, entryEnv, shapeAN, shapeIn] using hvt

/-! ## `alignUp` arithmetic -/

theorem mask_toNat {k : Nat} (hk : k < 64) :
    ((BitVec.allOnes 64) <<< k).toNat = 2 ^ 64 - 2 ^ k := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_allOnes, Nat.shiftLeft_eq]
  have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hK2 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  generalize 2 ^ k = K at *
  have : (2 ^ 64 - 1) * K = 2 ^ 64 * (K - 1) + (2 ^ 64 - K) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.one_mul, Nat.mul_one]; omega
  rw [this, Nat.mul_add_mod]; omega

theorem alignUp_toNat (x k : Word) (hk : k.toNat < 64)
    (hx : x.toNat + 2 ^ k.toNat - 1 < 2 ^ 64) :
    (alignUp x k).toNat = (x.toNat + 2 ^ k.toNat - 1) / 2 ^ k.toNat * 2 ^ k.toNat := by
  unfold alignUp maskW
  rw [Nat.mod_eq_of_lt hk, show (-1 : Word) = BitVec.allOnes 64 from by decide, BitVec.xor_allOnes,
    ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_not, mask_toNat hk]
  have hK : 1 ≤ 2 ^ k.toNat := Nat.one_le_two_pow
  have hK2 : 2 ^ k.toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have e1 : (x.toNat + (2 ^ 64 - 1 - (2 ^ 64 - 2 ^ k.toNat))) % 2 ^ 64 =
      x.toNat + 2 ^ k.toNat - 1 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [e1]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (by omega)

/-- Rounding up moves by less than `2^k`. -/
theorem alignUp_bounds (x k : Word) (hk : k.toNat < 64)
    (hx : x.toNat + 2 ^ k.toNat - 1 < 2 ^ 64) :
    x.toNat ≤ (alignUp x k).toNat ∧ (alignUp x k).toNat ≤ x.toNat + 2 ^ k.toNat - 1 := by
  rw [alignUp_toNat x k hk hx]
  have hK : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have h1 := Nat.div_mul_le_self (x.toNat + 2 ^ k.toNat - 1) (2 ^ k.toNat)
  have h2 := Nat.lt_div_mul_add (a := x.toNat + 2 ^ k.toNat - 1) hK
  omega

end ZesuExec.Fn.Scratch
