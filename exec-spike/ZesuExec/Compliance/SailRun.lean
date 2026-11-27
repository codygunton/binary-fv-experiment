import Evm.Lib.Rlp.Decoding

/-!
# Running EVM-Sail functions

The vendored EVM-Sail model (`vendor/evm-sail-lean`, EVM-Sail `d0e4aabd`) runs its functions in
`Evm.SailM = StateT Evm.HostState Evm.Defs.SailM`: the host state carries the byte regions (the
stateless input is `inputBytes`), and `Evm.Defs.SailM` is Sail's register monad
(`EStateM (Sail.Error Unit) SailRegs`). A function's result on host state `hs` and register state
`σ` is `((f ...).run hs).run σ`. The lemmas below evaluate `pure`, `throw`, `<$>` and `>>=`
through that double run.
-/

namespace ZesuExec.Compliance
open Sail

/-- The Sail register state of the EVM-Sail model. -/
abbrev SailRegs := PreSail.SequentialState Evm.Defs.RegisterType trivialChoiceSource

/-- The host state whose stateless-input region holds `input`, every other region empty. -/
def hostOf (input : List (BitVec 8)) : Evm.HostState :=
  { Evm.initialHostState with inputBytes := input.toArray }

@[simp] theorem run_throw {α : Type} (e : Error Unit) (hs : Evm.HostState) (σ : SailRegs) :
    EStateM.run (StateT.run (throw e : Evm.SailM α) hs) σ = .error e σ := rfl

@[simp] theorem run_pure {α : Type} (a : α) (hs : Evm.HostState) (σ : SailRegs) :
    EStateM.run (StateT.run (pure a : Evm.SailM α) hs) σ = .ok (a, hs) σ := rfl

theorem run_map_ok {α β : Type} (f : α → β) (x : Evm.SailM α) (hs : Evm.HostState) (σ : SailRegs)
    (a : α) (h : EStateM.run (StateT.run x hs) σ = .ok (a, hs) σ) :
    EStateM.run (StateT.run (f <$> x) hs) σ = .ok (f a, hs) σ := by
  rw [StateT.run_map]
  simp only [EStateM.run, Functor.map, EStateM.map] at h ⊢
  rw [h]

theorem run_bind_ok {α β : Type} (x : Evm.SailM α) (f : α → Evm.SailM β) (hs : Evm.HostState)
    (σ : SailRegs) (a : α) (h : EStateM.run (StateT.run x hs) σ = .ok (a, hs) σ) :
    EStateM.run (StateT.run (x >>= f) hs) σ = EStateM.run (StateT.run (f a) hs) σ := by
  rw [StateT.run_bind]
  simp only [EStateM.run, bind, EStateM.bind] at h ⊢
  rw [h]

theorem run_bind_error {α β : Type} (x : Evm.SailM α) (f : α → Evm.SailM β)
    (hs : Evm.HostState) (σ : SailRegs) (e : Error Unit)
    (h : EStateM.run (StateT.run x hs) σ = .error e σ) :
    EStateM.run (StateT.run (x >>= f) hs) σ = .error e σ := by
  rw [StateT.run_bind]
  simp only [EStateM.run, bind, EStateM.bind] at h ⊢
  rw [h]

end ZesuExec.Compliance
