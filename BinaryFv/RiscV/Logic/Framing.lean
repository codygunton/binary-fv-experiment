import BinaryFv.RiscV.Logic.ImageMemory
import BinaryFv.RiscV.Model.State

namespace BinaryFv.RiscV

open BinaryFv.Binary

open PreSail
open LeanRV64DExecutable.Functions
open Register

def MemoryEqualOutside (before after : State) (address : Nat) : Prop :=
  ∀ observed, observed ≠ address → before.mem.get? observed = after.mem.get? observed

/-- A generated Sail action has completed normally from `before` to `after`. -/
def Runs (action : SailM α) (before after : State) (result : α) : Prop :=
  action.run before = .ok result after

theorem Runs.bind {first : SailM α} {next : α → SailM β}
    {before middle after : State} {value : α} {result : β}
    (hFirst : Runs first before middle value) (hNext : Runs (next value) middle after result) :
    Runs (first >>= next) before after result := by
  change EStateM.bind first next before = .ok result after
  unfold EStateM.bind
  rw [show first before = .ok value middle from hFirst]
  exact hNext

def RegisterEqualOutside (before after : State) (written : Register) : Prop :=
  ∀ observed, observed ≠ written → before.regs.get? observed = after.regs.get? observed

theorem writeByte_run (state : State) (address : Nat) (value : BitVec 8) :
    (writeByte address value : SailM PUnit).run state =
      .ok PUnit.unit { state with mem := state.mem.insert address value } := by
  rfl

theorem writeByte_run_memory_get (state : State) (address observed : Nat) (value : BitVec 8) :
    (match (writeByte address value : SailM PUnit).run state with
    | .ok _ state' => state'.mem.get? observed
    | .error _ state' => state'.mem.get? observed) =
      if address == observed then some value else state.mem.get? observed := by
  change (state.mem.insert address value).get? observed = _
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]

theorem readByte_run (state : State) (address : Nat) (value : BitVec 8)
    (memory : state.mem.get? address = some value) :
    (readByte address : SailM (BitVec 8)).run state = .ok value state := by
  simp only [simp_sail]
  simp only [EStateM.run, EStateM.instMonad, EStateM.bind, instMonadStateOfMonadStateOf,
    EStateM.instMonadStateOf, EStateM.instMonadExceptOfOfBacktrackable, getThe]
  unfold EStateM.get
  simp only
  rw [memory]
  rfl

theorem readByte_of_image (image : ProgramImage) (state : State) (address : Nat) (byte : UInt8)
    (loaded : image.matchesMemory state.mem) (source : image.readByte? address = some byte) :
    (readByte address : SailM (BitVec 8)).run state =
      .ok (BitVec.ofNat 8 byte.toNat) state :=
  readByte_run state address (BitVec.ofNat 8 byte.toNat) (loaded address byte source)

theorem readReg_run (state : State) (register : Register) (value : RegisterType register)
    (stored : state.regs.get? register = some value) :
    (readReg register : SailM (RegisterType register)).run state = .ok value state := by
  simp [PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
    EStateM.instMonad, EStateM.instMonadStateOf, instMonadStateOfMonadStateOf,
    EStateM.instMonadExceptOfOfBacktrackable, getThe, stored]

/-- Register-presence and delegation facts sufficient to exclude generated interrupt dispatch. -/
def InterruptDisabled (state : State) : Prop :=
  ∃ (misaBits mstatusBits mipBits : BitVec 64) (meip : BitVec 1),
    state.regs.get? misa = some misaBits ∧
      state.regs.get? mip = some mipBits ∧
        state.regs.get? mie = some (0 : BitVec 64) ∧
          state.regs.get? mideleg = some (0 : BitVec 64) ∧
            state.regs.get? sig_meip = some meip ∧ state.regs.get? mstatus = some mstatusBits

theorem dispatchInterrupt_disabled (state : State) (priv : Privilege)
    (disabled : InterruptDisabled state) :
    (dispatchInterrupt priv).run state = .ok none state := by
  rcases disabled with ⟨misaBits, mstatusBits, mipBits, meip, misaRead, mipRead, mieRead,
    midelegRead, meipRead, mstatusRead⟩
  simp [dispatchInterrupt, getPendingSet, read_mip, external_interrupts_pending, currentlyEnabled,
    hartSupports, zeros, PreSail.assert, PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.pure, EStateM.instMonad, MonadState.get, MonadStateOf.get, getThe, misaRead, mipRead,
    mieRead, midelegRead, meipRead, mstatusRead]

theorem writeByte_preserves_registers (state : State) (address : Nat) (value : BitVec 8) :
    (match (writeByte address value : SailM PUnit).run state with
    | .ok _ state' => state'.regs
    | .error _ state' => state'.regs) = state.regs := by
  rfl

theorem writeByte_preserves_memory_outside (state : State) (address observed : Nat)
    (value : BitVec 8) (distinct : observed ≠ address) :
    (match (writeByte address value : SailM PUnit).run state with
    | .ok _ state' => state'.mem.get? observed
    | .error _ state' => state'.mem.get? observed) = state.mem.get? observed := by
  rw [writeByte_run_memory_get]
  by_cases same : address = observed
  · exact (distinct same.symm).elim
  · simp [same]

theorem writeByte_memory_frame (state : State) (address : Nat) (value : BitVec 8) :
    MemoryEqualOutside state { state with mem := state.mem.insert address value } address := by
  intro observed distinct
  symm
  change (state.mem.insert address value).get? observed = state.mem.get? observed
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases same : address = observed
  · exact (distinct same.symm).elim
  · simp [same]

theorem writeReg_run (state : State) (written : Register) (value : RegisterType written) :
    (writeReg written value : SailM PUnit).run state =
      .ok PUnit.unit { state with regs := state.regs.insert written value } := by
  rfl

theorem writeReg_register_frame (state : State) (written : Register)
    (value : RegisterType written) :
    RegisterEqualOutside state { state with regs := state.regs.insert written value } written := by
  intro observed distinct
  change state.regs.get? observed = (state.regs.insert written value).get? observed
  rw [Std.ExtDHashMap.get?_insert]
  simp [Ne.symm distinct]

/-- A generated register update leaves every distinct register's observed value unchanged. -/
theorem writeReg_read_unchanged (state : State) (written observed : Register)
    (value : RegisterType written) (distinct : observed ≠ written) :
    ({ state with regs := state.regs.insert written value }.regs.get? observed) =
      state.regs.get? observed := by
  symm
  exact writeReg_register_frame state written value observed distinct

theorem writeReg_preserves_memory (state : State) (written : Register)
    (value : RegisterType written) :
    (match (writeReg written value : SailM PUnit).run state with
    | .ok _ state' => state'.mem
    | .error _ state' => state'.mem) = state.mem := by
  rfl

/-! ## Inverting binds, and `writeBytes` register preservation -/

/-- Inverting a deterministic first action out of a `Runs` bind. -/
theorem runs_bind_inv {α β : Type} {first : SailM α} {next : α → SailM β}
    {s smid s' : State} {v : α} {r : β}
    (hfirst : Runs first s smid v) (hbind : Runs (first >>= next) s s' r) :
    Runs (next v) smid s' r := by
  have key : (first >>= next).run s = (next v).run smid := by
    show EStateM.bind first next s = (next v).run smid
    unfold EStateM.bind
    rw [show first s = EStateM.Result.ok v smid from hfirst]; rfl
  unfold Runs at hbind ⊢
  rw [← key]; exact hbind

/-- A `Runs` bind whose continuation is a state-preserving `pure` inverts to the first action,
running to the same final state. -/
theorem runs_bind_pure_inv {α β : Type} {first : SailM α} {b : β} {s s' : State}
    (hbind : Runs (first >>= fun _ => (pure b : SailM β)) s s' b) :
    ∃ v, Runs first s s' v := by
  cases hf : first.run s with
  | error e smid =>
    exfalso
    have hbad : (first >>= fun _ => (pure b : SailM β)).run s = EStateM.Result.error e smid := by
      show EStateM.bind first _ s = _
      unfold EStateM.bind
      rw [show first s = EStateM.Result.error e smid from hf]
    unfold Runs at hbind; rw [hbad] at hbind
    exact EStateM.Result.noConfusion hbind
  | ok val smid =>
    refine ⟨val, ?_⟩
    have hok : (first >>= fun _ => (pure b : SailM β)).run s = EStateM.Result.ok b smid := by
      show EStateM.bind first _ s = _
      unfold EStateM.bind
      rw [show first s = EStateM.Result.ok val smid from hf]; rfl
    unfold Runs at hbind; rw [hok] at hbind
    injection hbind with _ hss
    unfold Runs; rw [hf, hss]

/-- The generated `writeBytes` only mutates `.mem`, so it leaves the register file unchanged. -/
theorem writeBytes_preserves_regs {n : Nat} (addr : Nat) (data : BitVec (8 * n))
    (s s' : State) (h : Runs (PreSail.writeBytes addr data) s s' true) :
    s'.regs = s.regs := by
  have hforM : ∀ (list : List (Nat × BitVec 8)) (s s' : State),
      Runs (List.forM list (fun p => PreSail.writeByte p.1 p.2) : SailM PUnit) s s' () →
      s'.regs = s.regs := by
    intro list
    induction list with
    | nil =>
      intro s s' h
      have hh : EStateM.run (pure () : SailM PUnit) s = .ok () s' := by
        simpa only [List.forM, Runs] using h
      simp only [EStateM.run] at hh
      injection hh with _ hs2
      rw [hs2]
    | cons p rest ih =>
      intro s s' h
      have hstep : Runs
          (PreSail.writeByte p.1 p.2 >>= fun _ =>
            List.forM rest (fun p => PreSail.writeByte p.1 p.2)) s s' () := by
        simpa only [List.forM] using h
      have hfirst : Runs (PreSail.writeByte p.1 p.2) s
          { s with mem := s.mem.insert p.1 p.2 } () := by
        unfold Runs; exact writeByte_run s p.1 p.2
      have hcont := runs_bind_inv hfirst hstep
      have := ih { s with mem := s.mem.insert p.1 p.2 } s' hcont
      rw [this]
  have hstep : Runs
      (List.forM (List.ofFn (fun i : Fin n => (addr + i.val, data.extractLsb' (8 * i.val) 8)))
        (fun p => PreSail.writeByte p.1 p.2) >>= fun _ => (pure true : SailM Bool)) s s' true := by
    unfold PreSail.writeBytes at h; exact h
  obtain ⟨v, hforMrun⟩ := runs_bind_pure_inv hstep
  cases v
  exact hforM _ s s' hforMrun

end BinaryFv.RiscV
