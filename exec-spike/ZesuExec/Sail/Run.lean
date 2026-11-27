import ZesuExec.Sail.Step
import ZesuExec.Logic

/-!
# `sail_reaches`: machine-level reachability transfers to the Sail model

`SailReaches img b Q s`: from `s`, the Sail model reaches a state satisfying `Q` within `b`
instructions, where each step is a retiring `try_step`, except at the `memcpy` entry, where the
assumed ZisK service (`ziskMemcpy`) acts on a related machine state (cost 3). `sail_reaches`
follows by induction on `RunsIn`, with `sail_step_sim` for ordinary steps; for the service it
builds the Sail state `sailMemcpy m s` that holds the service's effect.
-/

namespace ZesuExec.SailLink

open BinaryFv.RiscV (State Runs)
open LeanRV64DExecutable.Functions
open Register

inductive SailReaches (img : Image) : Nat → (State → Prop) → State → Prop
  | done {b : Nat} {Q : State → Prop} {s : State} : Q s → SailReaches img b Q s
  | step {b : Nat} {Q : State → Prop} {s s' : State} (n : Nat) :
      Runs (try_step n false) s s' false → SailReaches img b Q s' → SailReaches img (b + 1) Q s
  | service {b : Nat} {Q : State → Prop} {s s' : State} {m m' : Machine} :
      Rel img m s → m.pc.toNat = Layout.memcpyEntry → ziskMemcpy m = some m' → Rel img m' s' →
      SailReaches img b Q s' → SailReaches img (b + 3) Q s

theorem SailReaches.mono {img : Image} {b b' : Nat} {Q : State → Prop} {s : State}
    (h : SailReaches img b Q s) (hb : b ≤ b') : SailReaches img b' Q s := by
  induction h generalizing b' with
  | done hq => exact .done hq
  | step n hr _ ih =>
    obtain ⟨c, rfl⟩ : ∃ c, b' = c + 1 := ⟨b' - 1, by omega⟩
    exact .step n hr (ih (by omega))
  | service hR hpc hz hR' _ ih =>
    obtain ⟨c, rfl⟩ : ∃ c, b' = c + 3 := ⟨b' - 3, by omega⟩
    exact .service hR hpc hz hR' (ih (by omega))

/-! ## The Sail state after the `memcpy` service -/

/-- The addresses the service writes: the 8 bytes at `Layout.extraParams`, then the destination. -/
def memcpyAddrs (m : Machine) : List Nat :=
  (List.range 8).map (Layout.extraParams + ·) ++
    (List.range (m.reg 12).toNat).map ((m.reg 10).toNat + ·)

/-- Overwrite each address of `as` with the post-service byte there. -/
def memcpyFold (m : Machine) (as : List Nat) (mem : Std.ExtHashMap Nat (BitVec 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  as.foldl (fun mem a => match ziskMemcpyMem m (BitVec.ofNat 64 a) with
    | some b => mem.insert a b
    | none => mem) mem

/-- The Sail state that holds the service's effect on `m`, starting from `s`. -/
def sailMemcpy (m : Machine) (s : State) : State :=
  { s with mem := memcpyFold m (memcpyAddrs m) s.mem,
           regs := s.regs.insert PC (m.reg 1 &&& ~~~(1 : Word)) }

theorem memcpyFold_spec (m : Machine) :
    ∀ (as : List Nat) (mem : Std.ExtHashMap Nat (BitVec 8)) (x : Nat),
      (x ∈ as → ∀ b, ziskMemcpyMem m (BitVec.ofNat 64 x) = some b →
        (memcpyFold m as mem).get? x = some b) ∧
      (x ∉ as → (memcpyFold m as mem).get? x = mem.get? x)
  | [], mem, x => by simp [memcpyFold]
  | a :: as, mem, x => by
    have ih := fun mem => memcpyFold_spec m as mem x
    have hstep : memcpyFold m (a :: as) mem = memcpyFold m as
        (match ziskMemcpyMem m (BitVec.ofNat 64 a) with
          | some b => mem.insert a b
          | none => mem) := rfl
    rw [hstep]
    constructor
    · intro hx b hb
      by_cases hr : x ∈ as
      · exact (ih _).1 hr b hb
      · have hxa : x = a := by simpa [hr] using hx
        subst hxa
        rw [(ih _).2 hr, hb]
        simp [Std.ExtHashMap.get?_eq_getElem?]
    · intro hx
      have hr : x ∉ as := fun h => hx (List.mem_cons_of_mem _ h)
      have hxa : x ≠ a := fun h => hx (h ▸ List.mem_cons_self)
      rw [(ih _).2 hr]
      split
      · simp [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, Ne.symm hxa]
      · rfl

/-- Outside the written addresses the service leaves memory alone. -/
theorem ziskMemcpyMem_outside (m : Machine) (x : Word) (hx : x.toNat ∉ memcpyAddrs m) :
    ziskMemcpyMem m x = m.mem x := by
  simp only [memcpyAddrs, List.mem_append, List.mem_map, List.mem_range, not_or, not_exists,
    not_and] at hx
  obtain ⟨h1, h2⟩ := hx
  unfold ziskMemcpyMem
  simp only
  rw [if_neg (fun h => h2 (x.toNat - (m.reg 10).toNat) (by omega) (by omega))]
  rw [if_neg (fun h => h1 (x.toNat - Layout.extraParams) (by omega) (by omega))]
  simp

/-- Every written address lies in RAM. -/
theorem memcpyAddrs_ram {m : Machine} (hd : ziskMemcpyDomain m = true) {x : Nat}
    (hx : x ∈ memcpyAddrs m) : Layout.ramLo ≤ x := by
  simp only [ziskMemcpyDomain, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨_, hep⟩, _⟩, hn⟩ := hd
  simp only [Machine.writable, Machine.inRange, Bool.and_eq_true, decide_eq_true_eq] at hep hn
  simp only [memcpyAddrs, List.mem_append, List.mem_map, List.mem_range] at hx
  simp only [Layout.ramLo, Layout.ramHi, Layout.extraParams] at hep hn ⊢
  rcases hx with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Layout.extraParams]; omega
  · rcases hn with hn | ⟨⟨⟨_, _⟩, hw⟩, _⟩
    · omega
    · omega

theorem sailMemcpy_rel {img : Image} {m m' : Machine} {s : State} (h : Rel img m s)
    (hz : ziskMemcpy m = some m') : Rel img m' (sailMemcpy m s) := by
  unfold ziskMemcpy at hz
  split at hz
  · rename_i hd
    simp only [Option.some.injEq] at hz
    subst hz
    have hfin : ∀ r, r ≠ PC → (sailMemcpy m s).regs.get? r = s.regs.get? r :=
      fun r hr => get?_insert_ne _ hr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Configured.of_agree h.conf (fun r _ h2 _ _ _ => hfin r h2)
        (by rw [hfin _ (by decide)]; exact h.conf.instret)
    · intro j hj; rw [hfin _ (xreg_ne_PC j)]; exact h.regs j hj
    · exact get?_insert_self _
    · intro x b hb
      change (memcpyFold m (memcpyAddrs m) s.mem).get? x.toNat = some b
      by_cases hx : x.toNat ∈ memcpyAddrs m
      · exact (memcpyFold_spec m _ s.mem x.toNat).1 hx b (by
          change ziskMemcpyMem m x = some b at hb; simpa using hb)
      · rw [(memcpyFold_spec m _ s.mem x.toNat).2 hx]
        change ziskMemcpyMem m x = some b at hb
        rw [ziskMemcpyMem_outside m x hx] at hb
        exact h.mem x b hb
    · intro seg hseg k w hk h1 h2 j hj
      change (memcpyFold m (memcpyAddrs m) s.mem).get? _ = _
      have hnot : seg.base + 4 * k + j ∉ memcpyAddrs m := fun hx => by
        have := memcpyAddrs_ram hd hx
        simp only [Layout.ramLo, Layout.textHi] at this h2; omega
      rw [(memcpyFold_spec m _ s.mem _).2 hnot]
      exact h.code seg hseg k w hk h1 h2 j hj
  · cases hz

/-! ## Transfer -/

theorem sail_runsIn {img : Image} {k : Nat} {m m₂ : Machine} (hr : RunsIn img k m m₂)
    {Q : Machine → Prop} :
    Q m₂ → ∀ s, Rel img m s → SailReaches img k (fun s' => ∃ m', Rel img m' s' ∧ Q m') s := by
  induction hr with
  | refl => exact fun hq s h => .done ⟨_, h, hq⟩
  | @step m m₁ c k m₂ hn _ ih =>
    intro hq s h
    unfold next at hn
    split at hn
    · rename_i hpc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hn
      obtain ⟨m', hz, rfl, rfl⟩ := hn
      rw [Nat.add_comm]
      exact .service h hpc hz (sailMemcpy_rel h hz) (ih hq (sailMemcpy m s) (sailMemcpy_rel h hz))
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hn
      obtain ⟨m', hs, rfl, rfl⟩ := hn
      obtain ⟨s', hrun, hrel⟩ := sail_step_sim h hs 0
      rw [Nat.add_comm]
      exact .step 0 hrun (ih hq s' hrel)

theorem sail_reaches {img : Image} {b : Nat} {Q : Machine → Prop} {m : Machine} {s : State}
    (h : Rel img m s) (hr : Reaches img b Q m) :
    SailReaches img b (fun s' => ∃ m', Rel img m' s' ∧ Q m') s := by
  obtain ⟨k, m', hk, hrun, hq⟩ := hr
  exact (sail_runsIn hrun hq s h).mono hk

end ZesuExec.SailLink
