import ZesuExec.Service

/-!
# Program logic over `next`

`RunsIn img k m m'`: `m` reaches `m'` in `k` instructions of `next`. `Spec` is the contract
form every function theorem (`ZesuExec.Fn.<Id>.Proof`) states.
-/

namespace ZesuExec

inductive RunsIn (img : Image) : Nat → Machine → Machine → Prop
  | refl : RunsIn img 0 m m
  | step : next img m = some (m₁, c) → RunsIn img k m₁ m₂ → RunsIn img (c + k) m m₂

def Reaches (img : Image) (bound : Nat) (Q : Machine → Prop) (m : Machine) : Prop :=
  ∃ k m', k ≤ bound ∧ RunsIn img k m m' ∧ Q m'

def Spec (img : Image) (entry bound : Nat) (Pre : Machine → Prop)
    (Post : Machine → Machine → Prop) : Prop :=
  ∀ m, m.pc.toNat = entry → Pre m → Reaches img bound (Post m) m

theorem RunsIn.trans {img : Image} {k₁ k₂ : Nat} {m m₁ m₂ : Machine}
    (h₁ : RunsIn img k₁ m m₁) (h₂ : RunsIn img k₂ m₁ m₂) : RunsIn img (k₁ + k₂) m m₂ := by
  induction h₁ with
  | refl => simpa using h₂
  | step hn _ ih => rw [Nat.add_assoc]; exact .step hn (ih h₂)

theorem Reaches.mono {img : Image} {b b' : Nat} {Q Q' : Machine → Prop} {m : Machine}
    (h : Reaches img b Q m) (hb : b ≤ b') (hq : ∀ m', Q m' → Q' m') : Reaches img b' Q' m := by
  obtain ⟨k, m', hk, hr, hQ⟩ := h
  exact ⟨k, m', Nat.le_trans hk hb, hr, hq _ hQ⟩

theorem Reaches.done {img : Image} {b : Nat} {Q : Machine → Prop} {m : Machine} (h : Q m) :
    Reaches img b Q m := ⟨0, m, Nat.zero_le _, .refl, h⟩

theorem Reaches.trans {img : Image} {b₁ b₂ : Nat} {P Q : Machine → Prop} {m : Machine}
    (h₁ : Reaches img b₁ P m) (h₂ : ∀ m', P m' → Reaches img b₂ Q m') :
    Reaches img (b₁ + b₂) Q m := by
  obtain ⟨k₁, m₁, hk₁, hr₁, hP⟩ := h₁
  obtain ⟨k₂, m₂, hk₂, hr₂, hQ⟩ := h₂ m₁ hP
  exact ⟨k₁ + k₂, m₂, Nat.add_le_add hk₁ hk₂, hr₁.trans hr₂, hQ⟩

theorem Reaches.loop {img : Image} {Q : Machine → Prop} (I : Nat → Machine → Prop) (c : Nat)
    (h : ∀ μ m, I μ m → Reaches img c (fun m' => Q m' ∨ ∃ μ', μ' < μ ∧ I μ' m') m) :
    ∀ μ m, I μ m → Reaches img ((μ + 1) * c) Q m := by
  intro μ
  induction μ using Nat.strongRecOn with
  | ind μ ih =>
    intro m hI
    have h₁ := h μ m hI
    have : (μ + 1) * c = c + μ * c := by rw [Nat.succ_mul, Nat.add_comm]
    rw [this]
    refine Reaches.trans h₁ fun m' hm' => ?_
    rcases hm' with hQ | ⟨μ', hlt, hI'⟩
    · exact Reaches.done hQ
    · exact (ih μ' hlt m' hI').mono (Nat.mul_le_mul_right _ hlt) (fun _ h => h)

/-- `m'` differs from `m` in memory only inside `R`. -/
def SameOutside (R : Word → Prop) (m m' : Machine) : Prop := ∀ a, ¬ R a → m'.mem a = m.mem a

/-- The bytes `bs` are present at `a, a+1, …`. -/
def BytesAt (m : Machine) (a : Word) (bs : List Byte) : Prop :=
  ∀ i (h : i < bs.length), m.mem (a + BitVec.ofNat 64 i) = some bs[i]

/-- Callee-saved registers of the RISC-V ABI (`sp`, `s0`–`s11`). -/
def calleeSaved : List (Fin 32) := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- `m'` is a return from the call that started at `m`: `pc` is `x1` with bit 0 clear and
`sp`, `x8`, `x9`, `x18`–`x27` are restored. -/
def Returns (m m' : Machine) : Prop :=
  m'.pc = (m.reg 1 &&& ~~~(1 : Word)) ∧ ∀ i ∈ calleeSaved, m'.reg i = m.reg i

def RodataLoaded (img : Image) (m : Machine) : Prop :=
  ∀ a b, img.rodataByte? a = some b → m.mem (BitVec.ofNat 64 a) = some (BitVec.ofNat 8 b)

/-- `memcpy` contract: the domain of `ziskMemcpy` holds. -/
def MemcpyPre (m : Machine) : Prop := ziskMemcpyDomain m = true

/-- `memcpy` contract: the result is `ziskMemcpy`'s. -/
def MemcpyPost (m m' : Machine) : Prop := ziskMemcpy m = some m'

theorem memcpy_spec (img : Image) : Spec img Layout.memcpyEntry 3 MemcpyPre MemcpyPost := by
  intro m hpc hpre
  have hn : next img m = some ({ m with mem := ziskMemcpyMem m, pc := m.reg 1 &&& ~~~(1 : Word) }, 3) := by
    simp [next, hpc, ziskMemcpy, show ziskMemcpyDomain m = true from hpre]
  exact ⟨3, _, Nat.le_refl _, by simpa using RunsIn.step hn .refl,
    by simp [MemcpyPost, ziskMemcpy, show ziskMemcpyDomain m = true from hpre]⟩

end ZesuExec
