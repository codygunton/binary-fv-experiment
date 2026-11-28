import ZesuExec.Sym.Exec

/-!
# Executor tests (plan S4 step 4)

For each of the 33 forms, `stepI` on a symbolic state with literal registers and one 64-byte
RAM region agrees with `Machine.exec` on the matching concrete machine (registers, `pc`, and
the region's bytes). Then the refusals: `csrrs` does not run, a store one past the end of a
region and a two-byte load at an odd offset return `none`.
-/

namespace ZesuExec.Test.SymTest
open ZesuExec ZesuExec.Sym ZesuExec.Machine

def ramBase : Nat := 0xa0000000
def pc0 : Nat := 0x800d6960

/-- Concrete register values: `x5` points 8 bytes into the region, the rest are literals. -/
def regVal (i : Nat) : Nat :=
  if i = 0 then 0 else if i = 5 then ramBase + 8 else 0x1234567 * i + 0xff00000000000000 * (i % 3)

def mem0Byte (j : Nat) : Nat := (j * 37 + 11) % 256

def env : Env where
  vars := fun _ => 0
  regions := [(BitVec.ofNat 64 ramBase, 64)]
  mem0 := fun _ j => BitVec.ofNat 8 (mem0Byte j)

def S0 : SState where
  regs := (List.range 32).map fun i => if i = 5 then .ptr 0 8 else .lit (regVal i)
  mem := []
  known := []
  regions := [⟨some 64, 16, true⟩]
  steps := 0

def m0 : Machine where
  regs := fun i => BitVec.ofNat 64 (regVal i.val)
  pc := BitVec.ofNat 64 pc0
  mem := fun a =>
    if ramBase ≤ a.toNat ∧ a.toNat < ramBase + 64 then some (BitVec.ofNat 8 (mem0Byte (a.toNat - ramBase)))
    else none

/-- `stepI` and `exec` agree on registers, `pc` (when the exit is a known address) and the
region's bytes. -/
def agrees (i : Instr) : Bool :=
  match stepI zesuEmpty pc0 i S0, m0.exec i with
  | some (S', e, _), some m' =>
    (List.range 32).all (fun j => (S'.reg j).eval env == m'.reg ⟨j % 32, Nat.mod_lt _ (by decide)⟩) &&
    (List.range 64).all (fun j => some (memByte env S'.mem 0 j) == m'.mem (BitVec.ofNat 64 (ramBase + j))) &&
    (match e with
     | .next p => m'.pc.toNat == p
     | .branch c t f => m'.pc.toNat == if c.eval env then t else f
     | .call t _ => m'.pc.toNat == t
     | .callInd t _ | .ret t | .jumpInd t => m'.pc == t.eval env)
  | _, _ => false
where zesuEmpty : Image := ⟨[], []⟩

def forms : List Instr :=
  [.lui 7 0x12345, .auipc 7 0x00012, .jal 1 0x00100, .jalr 1 5 (-8), .beq 6 6 16, .bne 6 7 16,
   .blt 6 7 (-16), .bltu 6 7 16, .bgeu 6 7 16, .lb 7 5 3, .lbu 7 5 3, .lhu 7 5 2, .lw 7 5 4,
   .ld 7 5 8, .sb 5 9 1, .sh 5 9 2, .sw 5 9 4, .sd 5 9 (-8), .addi 7 6 (-1), .andi 7 6 0x0f0,
   .xori 7 6 (-1), .sltiu 7 6 5, .slli 7 6 13, .srli 7 6 61, .add 7 6 8, .sub 7 6 8, .and 7 6 8,
   .or 7 6 8, .sll 7 6 8, .sltu 7 6 8, .mul 7 6 8, .mulhu 7 6 8, .xor 7 6 8, .addiw 7 6 (-1)]

theorem forms_count : forms.length = 34 := by decide

/-- `jalr` to a literal target (`x5` replaced by a literal) exercises the literal branch. -/
theorem jalr_literal_agrees :
    agrees (.jalr 0 6 0) = false ∧ agrees (.jalr 0 0 0x100) = true := by decide +kernel

theorem all_forms_agree : forms.all agrees = true := by decide +kernel

/-- The `csrrs` word of `memcpy` does not decode, so `run` refuses it. -/
theorem csrrs_refused :
    run ⟨[⟨0x800e06c4, [0x8135a073]⟩], []⟩ [] 4 0x800e06c4 S0 = none := by decide +kernel

/-- A store at `ptr r (size r)` is refused. -/
theorem store_past_end_refused : storeSym S0 (.ptr 0 64) 1 (.lit 0) = none := by decide +kernel

/-- A two-byte load at an odd offset is accepted (`Machine.load` takes misaligned ranges). -/
theorem odd_halfword_accepted : (loadSym ⟨[], []⟩ S0 (.ptr 0 9) 2).isSome = true := by decide +kernel

/-- A two-byte load that runs past the region's end is refused. -/
theorem halfword_past_end_refused : loadSym ⟨[], []⟩ S0 (.ptr 0 63) 2 = none := by decide +kernel

end ZesuExec.Test.SymTest
