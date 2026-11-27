import ZesuExec.Sym.Env

/-!
# Obligation framework: plans (programme plan S2 step 1)

A function proof is a `Plan`: cut points with an assertion, a symbolic start state, an `Env`
and an instruction budget each; the leaves `sym_run` computed from every cut point; the callees
by return address; the postcondition. `σ` carries the entry machine and the logical parameters
every assertion may mention. `ZesuExec.Vc.vc_sound` turns the per-cut and per-leaf goals of
`ZesuExec.Vc.Goals` into `Reaches` from every cut point.
-/

namespace ZesuExec.Vc
open ZesuExec ZesuExec.Sym

/-- A function the plan calls, with its contract. `Pre` and `Post` may mention the plan's
parameters `σ`. -/
structure Callee (σ : Type) (img : Image) where
  entry : Nat
  bound : Nat
  Pre   : σ → Machine → Prop
  Post  : σ → Machine → Machine → Prop
  spec  : ∀ g, Spec img entry bound (Pre g) (Post g)

/-- A cut point: where a symbolic run starts and an assertion is stated. -/
structure Cut (σ : Type) where
  pc     : Nat
  /-- symbolic state its run starts from -/
  S      : SState
  /-- the assertion -/
  A      : σ → Machine → Prop
  env    : σ → Machine → Env
  /-- instructions still allowed from here -/
  budget : σ → Machine → Nat

/-- Only for `cuts[i]!` in the generated statements; never a cut of a plan. -/
instance {σ : Type} : Inhabited (Cut σ) :=
  ⟨{ pc := 0, S := default, A := fun _ _ => False,
     env := fun _ _ => { vars := fun _ => 0, regions := [], mem0 := fun _ _ => 0 },
     budget := fun _ _ => 0 }⟩

structure Plan (σ : Type) (img : Image) where
  cuts   : List (Cut σ)
  fuel   : Nat
  /-- by cut pc; filled from `sym_run` constants -/
  leaves : Nat → List Leaf
  /-- by return address of the call site -/
  callee : Nat → Option (Callee σ img)
  Post   : σ → Machine → Prop

/-- The `memcpy` service as a callee (`memcpy_spec`). -/
def Callee.memcpy (σ : Type) (img : Image) : Callee σ img where
  entry := Layout.memcpyEntry
  bound := 3
  Pre := fun _ => MemcpyPre
  Post := fun _ => MemcpyPost
  spec := fun _ => memcpy_spec img

end ZesuExec.Vc
