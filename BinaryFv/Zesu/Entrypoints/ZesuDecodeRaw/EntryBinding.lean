import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.StateBuilder
import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Platform.PhysicalAccess
import BinaryFv.RiscV.Proof.ImageLoadCorrectness
import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.ExportedDecoder

/-!
# Proving the constructed state is a valid decoder entry

`buildZesuEntryState` creates the Sail state used to call `zesu_decode_raw`. This module proves that
running the builder establishes the exported contract's entry predicate: input bytes are present,
file-backed code and constants are intact, private globals represent a fresh decoder, and `a0`, `a1`,
`ra`, and `PC` contain the C ABI values.

The threading splits at the one input-independent seam. `configureZesuMachine` is a closed program
(machine setup: `sail_model_init` + M-extension + the pinned PMA region), so its success is a finite
evaluation `native_decide` settles — this is the SSZ layer, where that is permitted, and it sidesteps
hand-threading `sail_model_init`'s ~40 register writes and its `misa`-dependent `legalize_*` reads.
Everything after configuration is input-dependent and is threaded with the establishment lemmas in
`ImageLoadCorrectness`: each loader sets its own addresses and frames the complement, so the
earlier-established facts survive because the runner's ranges are pairwise disjoint.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.Zesu
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.DecodedValue
open BinaryFv.Zesu.Elflings

/-! ## The machine configuration succeeds -/

/-- Whether the configuration program runs to a normal (non-error) result from the empty initial
state. A closed finite computation, so `native_decide` settles it. -/
def configureSucceedsB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ _ => true
  | .error _ _ => false

theorem configure_succeeds : configureSucceedsB = true := by native_decide

/-- Whether a PMA region has exactly the runner's main-memory fields. Each field is checked directly
rather than comparing `PMA_Region`s, which do not have a `DecidableEq` instance. -/
private def zesuMainMemoryRegionB (region : PMA_Region) : Bool :=
  (region.base == BitVec.ofNat 64 zesuPmaRange.start) &&
  (region.size == BitVec.ofNat 64 zesuPmaRange.size) &&
  (match region.attributes.mem_type with | .MainMemory => true | _ => false) &&
  region.attributes.cacheable && region.attributes.coherent && region.attributes.executable &&
  region.attributes.readable && region.attributes.writable && region.attributes.read_idempotent &&
  region.attributes.write_idempotent &&
  (match region.attributes.misaligned_exceptions.load_store with
    | none => true
    | some _ => false) &&
  (match region.attributes.misaligned_exceptions.vector with | none => true | some _ => false) &&
  (match region.attributes.misaligned_exceptions.amo with | .AccessFault => true | _ => false) &&
  (match region.attributes.atomic_support with | .AMOCASQ => true | _ => false) &&
  (match region.attributes.reservability with | .RsrvEventual => true | _ => false) &&
  region.attributes.supports_cbo_zero && region.attributes.supports_pte_read &&
  region.attributes.supports_pte_write && !region.include_in_device_tree

private theorem zesuMainMemoryRegion_of_check {region : PMA_Region}
    (h : zesuMainMemoryRegionB region = true) : region = zesuMainMemoryRegion := by
  rcases region with ⟨base, size, attributes, deviceTree⟩
  rcases attributes with ⟨memType, cacheable, coherent, executable, readable, writable,
    readIdempotent, writeIdempotent, misaligned, atomicSupport, reservability, cboZero, pteRead,
    pteWrite⟩
  rcases misaligned with ⟨loadStore, vector, amo⟩
  cases memType <;> cases loadStore <;> cases vector <;> cases amo <;> cases atomicSupport <;>
    cases reservability <;>
    simp_all [zesuMainMemoryRegionB, zesuMainMemoryRegion, zesuMainMemoryAttributes, zesuPmaRange]

private def zesuMainMemoryRegionsB (regions : List PMA_Region) : Bool :=
  match regions with
  | [region] => zesuMainMemoryRegionB region
  | _ => false

private theorem zesuMainMemoryRegions_of_check {regions : List PMA_Region}
    (h : zesuMainMemoryRegionsB regions = true) : regions = [zesuMainMemoryRegion] := by
  cases regions with
  | nil => simp [zesuMainMemoryRegionsB] at h
  | cons region regions =>
    cases regions with
    | nil => exact congrArg (fun region => [region]) (zesuMainMemoryRegion_of_check h)
    | cons next rest => simp [zesuMainMemoryRegionsB] at h

/-- Whether the closed configuration computation installs the intended PMA table. -/
private def configurePmaRegionsB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ s =>
    match s.regs.get? pma_regions with
    | some regions => zesuMainMemoryRegionsB regions
    | none => false
  | .error _ _ => false

private theorem configure_pma_regions_check : configurePmaRegionsB = true := by native_decide

/-- The configuration action installs exactly the runner's main-memory PMA table. -/
theorem configure_pma_regions {s : State}
    (h : configureZesuMachine.run initialState = .ok () s) :
    s.regs.get? pma_regions = some [zesuMainMemoryRegion] := by
  have hcheck := configure_pma_regions_check
  unfold configurePmaRegionsB at hcheck
  rw [h] at hcheck
  cases hpma : s.regs.get? pma_regions with
  | none => simp [hpma] at hcheck
  | some regions =>
    have hregions : zesuMainMemoryRegionsB regions = true := by
      simpa [hpma] using hcheck
    exact congrArg some (zesuMainMemoryRegions_of_check hregions)

/-- Whether the closed configuration leaves the three wrapper-saved registers readable. The wrapper
stores `s0`, `s1`, and `s2` before writing any of them, so the canonical entry must expose their
actual initialized values rather than postulate an ABI value. -/
private def configureSavedRegistersPresentB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ state => (state.regs.get? x8).isSome && (state.regs.get? x9).isSome &&
      (state.regs.get? x18).isSome
  | .error _ _ => false

private theorem configure_saved_registers_present_check : configureSavedRegistersPresentB = true := by
  native_decide

/-- The configured machine provides the three live registers the wrapper saves in its frame. -/
theorem configure_saved_registers_present {s : State}
    (h : configureZesuMachine.run initialState = .ok () s) :
    (∃ value, s.regs.get? x8 = some value) ∧
      (∃ value, s.regs.get? x9 = some value) ∧
        ∃ value, s.regs.get? x18 = some value := by
  have hcheck := configure_saved_registers_present_check
  unfold configureSavedRegistersPresentB at hcheck
  rw [h] at hcheck
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2, hcheck.2⟩

/-- The production setup also materializes the wrapper's remaining callee-saved registers. -/
def CalleeSavedRegistersPresent (s : State) : Prop :=
  (∃ value, s.regs.get? x19 = some value) ∧
    (∃ value, s.regs.get? x20 = some value) ∧
      (∃ value, s.regs.get? x21 = some value) ∧
        (∃ value, s.regs.get? x22 = some value) ∧
          (∃ value, s.regs.get? x23 = some value) ∧
            (∃ value, s.regs.get? x24 = some value) ∧
              (∃ value, s.regs.get? x25 = some value) ∧
                (∃ value, s.regs.get? x26 = some value) ∧
                  ∃ value, s.regs.get? x27 = some value

private def configureCalleeSavedRegistersPresentB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ state =>
      (state.regs.get? x19).isSome && (state.regs.get? x20).isSome &&
        (state.regs.get? x21).isSome && (state.regs.get? x22).isSome &&
          (state.regs.get? x23).isSome && (state.regs.get? x24).isSome &&
            (state.regs.get? x25).isSome && (state.regs.get? x26).isSome &&
              (state.regs.get? x27).isSome
  | _ => false

private theorem configure_callee_saved_registers_present_check :
    configureCalleeSavedRegistersPresentB = true := by native_decide

theorem configure_callee_saved_registers_present {s : State}
    (h : configureZesuMachine.run initialState = .ok () s) :
    CalleeSavedRegistersPresent s := by
  have hcheck := configure_callee_saved_registers_present_check
  unfold configureCalleeSavedRegistersPresentB at hcheck
  rw [h] at hcheck
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hcheck
  rcases hcheck with ⟨⟨⟨⟨⟨⟨⟨⟨h19, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩
  exact ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27⟩

/-! ### The configured machine is a *normal* execution state

`NormalExecutionState` (`RiscV/Platform/NormalState.lean`) bundles the twelve platform reads a
retiring step depends on: hart state, privilege, `satp`, the delegation/interrupt words, the PMP
tables, the two counter-control CSRs, the landing-pad expectation, and the `misa` bit that enables
compressed instructions. Until now it was a predicate **no theorem in the tree mentioned**, so
nothing established that any state the runner produces satisfies it.

It matters because it is exactly the hypothesis set `Step/ControlFlow.lean`'s retirement lemmas take
apart — `tryStepRetRetires` alone wants `hartRead`, `inhibitRead`, `configRead`, `notInhibited`,
`machineEnabled`, `InterruptDisabled`, `FetchBasePlatform`, `FetchMemoryNoMMIO`,
`LandingPadNotExpected` and the `Zca` read, every one of which is a consequence of these twelve. So
"the machine is configured normally" is the missing currency between the state builder and the single
`ret` that the sentinel bridge needs, and this section makes it a proved fact about the state the
runner really calls `zesu_decode_raw` from rather than an assumption. -/

/-- `NormalExecutionState` as a decidable check. Written out rather than `decide`d because three of
its conjuncts have no `Decidable` instance: `HartState` and `Privilege` carry no `DecidableEq`, and
the `misa` conjunct is a `match` on an `Option`, not an equation. -/
def normalExecutionB (s : State) : Bool :=
  (match s.regs.get? hart_state with | some (HartState.HART_ACTIVE ()) => true | _ => false) &&
  (match s.regs.get? cur_privilege with | some Privilege.Machine => true | _ => false) &&
  decide (s.regs.get? satp = some (0 : BitVec 64)) &&
  decide (s.regs.get? mideleg = some (0 : BitVec 64)) &&
  decide (s.regs.get? mie = some (0 : BitVec 64)) &&
  decide (s.regs.get? mip = some (0 : BitVec 64)) &&
  decide (s.regs.get? pmpcfg_n = some (default : Vector (BitVec 8) 64)) &&
  decide (s.regs.get? pmpaddr_n = some (default : Vector (BitVec 64) 64)) &&
  decide (s.regs.get? mcountinhibit = some (0 : BitVec 32)) &&
  decide (s.regs.get? minstretcfg = some (0 : BitVec 64)) &&
  decide (s.regs.get? elp = some
    (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED)) &&
  (match s.regs.get? misa with
    | some m => decide (Sail.BitVec.access m 12 = 1#1)
    | none => false)

/-- The check discharges the predicate. The three `match` conjuncts are inverted by case analysis on
the register read: every branch but the intended one reduces the check to `false = true`. -/
theorem normalExecutionState_of_check {s : State} (h : normalExecutionB s = true) :
    NormalExecutionState s := by
  unfold normalExecutionB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhart, hpriv⟩, hsatp⟩, hmideleg⟩, hmie⟩, hmip⟩, hpmpcfg⟩, hpmpaddr⟩,
    hinhibit⟩, hcfg⟩, help⟩, hmisa⟩ := h
  refine ⟨?_, ?_, hsatp, hmideleg, hmie, hmip, hpmpcfg, hpmpaddr, hinhibit, hcfg, help, ?_⟩
  · cases hread : s.regs.get? hart_state with
    | none => rw [hread] at hhart; simp at hhart
    | some hs =>
      cases hs with
      | HART_ACTIVE u => cases u; rfl
      | HART_WAITING w => rw [hread] at hhart; simp at hhart
  · cases hread : s.regs.get? cur_privilege with
    | none => rw [hread] at hpriv; simp at hpriv
    | some p =>
      cases p <;> first | rfl | (rw [hread] at hpriv; simp at hpriv)
  · cases hread : s.regs.get? misa with
    | none => rw [hread] at hmisa; simp at hmisa
    | some m => rw [hread] at hmisa; exact of_decide_eq_true hmisa

/-! ### The five machine registers a retiring *fetch* needs that `NormalExecutionState` omits

`NormalExecutionState` pins twelve registers. Working backwards from `tryStepRetRetires` through its
premises turns up **five more**, and not one of them is among the twelve:

* `minstret` — `retiredRead`, the counter the retirement increments;
* `mstatus` and `sig_meip` — `InterruptDisabled` (`RiscV/Logic/Framing.lean`);
* `mstatus` again and `pma_regions` — `FetchBasePlatform` (`RiscV/Platform/Fetch.lean`), through
  `FetchPmaAllows`;
* `mseccfg` — `Elfling.returnExit_fetch_and_decode`, which needs it to decode the exit instruction.

They are *presence* claims at existentially bound values, not value pins, which is why they cannot be
conjuncts of `NormalExecutionState` — every conjunct there fixes a value. So they are a separate
predicate. Grouping all five is deliberate: `minstret` is not special. It sits in exactly the same
category as the other four — a machine register that exists at the state the runner builds and that
no contract clause says still exists after the call — and splitting it out would suggest four of them
are settled when none is.

This module proves the predicate holds at the state `zesu_decode_raw` is entered from. It does **not**
hold at the exit for anything proved anywhere: that is the remaining gap, and it is a contract
question, not a runner question. -/

/-- The five registers `tryStepRetRetires` and its premises read that `NormalExecutionState` does not
mention. Presence, not value: each is consumed at an existentially bound value. -/
def FetchPlatformPresent (state : State) : Prop :=
  (∃ v, state.regs.get? minstret = some v) ∧
  (∃ v, state.regs.get? mstatus = some v) ∧
  (∃ v, state.regs.get? sig_meip = some v) ∧
  (∃ v, state.regs.get? pma_regions = some v) ∧
  (∃ v, state.regs.get? mseccfg = some v)

/-- The decidable form. -/
def fetchPlatformPresentB (state : State) : Bool :=
  (state.regs.get? minstret).isSome && (state.regs.get? mstatus).isSome &&
  (state.regs.get? sig_meip).isSome && (state.regs.get? pma_regions).isSome &&
  (state.regs.get? mseccfg).isSome

theorem fetchPlatformPresent_of_check {s : State} (h : fetchPlatformPresentB s = true) :
    FetchPlatformPresent s := by
  unfold fetchPlatformPresentB at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `FetchPlatformPresent` reads none of the six registers the builder's ABI block writes. -/
theorem fetchPlatformPresent_frame {s s' : State}
    (hframe : ∀ r : Register, r ≠ x1 → r ≠ x2 → r ≠ x10 → r ≠ x11 → r ≠ PC → r ≠ nextPC →
      s'.regs.get? r = s.regs.get? r)
    (h : FetchPlatformPresent s) : FetchPlatformPresent s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
    assumption

/-! ### The two registers the exit fetch reads *at their value*

For four of `FetchPlatformPresent`'s five registers presence is the whole story: the premise binds
the contents existentially and never inspects them. Two registers are not like that, and a presence
claim about either is worth nothing to a fetch:

* `pma_regions` — `FetchPmaAllows` **evaluates** `matching_pma_region` on the table;
* `htif_tohost_base` — `FetchMemoryNoMMIO` **evaluates** `within_htif_readable` on it, and the `none`
  branch is the one that makes the dispatch miss MMIO.

So they get a predicate of their own rather than a sixth and seventh conjunct of a predicate whose
name promises presence. It is parameterized by the fetch addresses because the PMA lookup is
per-address, and *which* addresses matter is not this module's business: the check is closed once the
list is, so a caller supplies a `native_decide` at its own addresses and no exit address is named
here.

The check never compares two `PMA_Region`s — they carry no `DecidableEq`, which is why pinning the
table by equation is not available — it reads the matched region's `executable` flag instead, which
is exactly what the premise consumes.

`FetchPmaAllows` (`RiscV/Platform/Fetch.lean`) is spelled out rather than imported: this module sits
below the fetch layer and pulling it in would enlarge the root's import closure for one definition.
The two are the same conjunction, and `ReturnToSentinel.lean` re-packs one into the other in a
line. -/

/-- Whether a PMA table grants an executable four-byte instruction fetch at `pc`. Phrased on the
matched region's `executable` flag rather than on an equation between regions: `PMA_Region` carries
no `DecidableEq`, so pinning the table itself is not something a check can do — and the flag is what
the premise consumes anyway. -/
def pmaExecutableAtB (regions : List PMA_Region) (pc : Nat) : Bool :=
  match matching_pma_region regions (physaddr.Physaddr (BitVec.ofNat 64 pc)) 4 with
  | some region => region.attributes.executable
  | none => false

theorem pmaExecutableAt_of_check {regions : List PMA_Region} {pc : Nat}
    (h : pmaExecutableAtB regions pc = true) :
    ∃ region, matching_pma_region regions (physaddr.Physaddr (BitVec.ofNat 64 pc)) 4 = some region ∧
      region.attributes.executable = true := by
  unfold pmaExecutableAtB at h
  split at h
  · next region hmatch => exact ⟨region, hmatch, h⟩
  · next => exact absurd h (by simp)

/-- The generated PMA lookup at `pc`, read off the state. -/
def fetchPmaAllowsB (state : State) (pc : Nat) : Bool :=
  match state.regs.get? pma_regions with
  | some regions => pmaExecutableAtB regions pc
  | none => false

/-- The two value dependencies of a four-byte instruction fetch, at the addresses a caller fetches
from. The first conjunct is `FetchPmaAllows state (BitVec.ofNat 64 pc)` written out. -/
def FetchPlatformPinned (state : State) (addresses : List Nat) : Prop :=
  (∀ pc ∈ addresses, ∃ (regions : List PMA_Region) (region : PMA_Region),
      state.regs.get? pma_regions = some regions ∧
        matching_pma_region regions (physaddr.Physaddr (BitVec.ofNat 64 pc)) 4 = some region ∧
          region.attributes.executable = true) ∧
    state.regs.get? htif_tohost_base = some none

/-- The decidable form. The `htif_tohost_base` conjunct is a `match` rather than a `decide` for the
same reason three of `normalExecutionB`'s are: its register type is an `Option`, not an equation
type with an instance to hand. -/
def fetchPlatformPinnedB (state : State) (addresses : List Nat) : Bool :=
  addresses.all (fetchPmaAllowsB state) &&
    (match state.regs.get? htif_tohost_base with | some none => true | _ => false)

theorem fetchPlatformPinned_of_check {s : State} {addresses : List Nat}
    (h : fetchPlatformPinnedB s addresses = true) : FetchPlatformPinned s addresses := by
  unfold fetchPlatformPinnedB at h
  simp only [Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · intro pc hpc
    have hrow := List.all_eq_true.mp h.1 pc hpc
    unfold fetchPmaAllowsB at hrow
    split at hrow
    · next regions hregions =>
        obtain ⟨region, hmatch, hexec⟩ := pmaExecutableAt_of_check hrow
        exact ⟨regions, region, hregions, hmatch, hexec⟩
    · next => exact absurd hrow (by simp)
  · have hhtif := h.2
    split at hhtif
    · next base hbase => exact hbase
    · next => exact absurd hhtif (by simp)

/-- `FetchPlatformPinned` reads none of the six registers the builder's ABI block writes. -/
theorem fetchPlatformPinned_frame {s s' : State} {addresses : List Nat}
    (hframe : ∀ r : Register, r ≠ x1 → r ≠ x2 → r ≠ x10 → r ≠ x11 → r ≠ PC → r ≠ nextPC →
      s'.regs.get? r = s.regs.get? r)
    (h : FetchPlatformPinned s addresses) : FetchPlatformPinned s' addresses := by
  obtain ⟨hpma, hhtif⟩ := h
  refine ⟨?_, ?_⟩
  · intro pc hpc
    obtain ⟨regions, region, hregions, hmatch, hexec⟩ := hpma pc hpc
    exact ⟨regions, region,
      (hframe pma_regions (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans hregions, hmatch, hexec⟩
  · rw [hframe htif_tohost_base (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hhtif

def pmaReadableAtB (regions : List PMA_Region) (address width : Nat) : Bool :=
  match matching_pma_region regions (physaddr.Physaddr (BitVec.ofNat 64 address)) width with
  | some region => region.attributes.readable
  | none => false

def loadPmaAllowsB (state : State) (access : Nat × Nat) : Bool :=
  match state.regs.get? pma_regions with
  | some regions => pmaReadableAtB regions access.1 access.2
  | none => false

structure LoadPlatformPinned (state : State) (accesses : List (Nat × Nat)) : Prop where
  mstatus : ∃ bits, state.regs.get? mstatus = some bits ∧ _get_Mstatus_MPRV bits = 0#1
  mseccfg : ∃ bits, state.regs.get? mseccfg = some bits ∧
    pmm_mode_backwards (_get_Seccfg_PMM bits) = .PMM_Disabled
  allows : ∀ access ∈ accesses,
    LoadPmaAllows state (BitVec.ofNat 64 access.1) access.2

def loadPlatformPinnedB (state : State) (accesses : List (Nat × Nat)) : Bool :=
  (match state.regs.get? mstatus with
    | some bits => _get_Mstatus_MPRV bits == 0#1
    | none => false) &&
  (match state.regs.get? mseccfg with
    | some bits => match pmm_mode_backwards (_get_Seccfg_PMM bits) with
      | .PMM_Disabled => true
      | _ => false
    | none => false) && accesses.all (loadPmaAllowsB state)

theorem loadPlatformPinned_of_check {state : State} {accesses : List (Nat × Nat)}
    (h : loadPlatformPinnedB state accesses = true) : LoadPlatformPinned state accesses := by
  simp only [loadPlatformPinnedB, Bool.and_eq_true] at h
  rcases hmstatus : state.regs.get? mstatus with _ | mstatusBits
  · simp [hmstatus] at h
  rcases hmseccfg : state.regs.get? mseccfg with _ | mseccfgBits
  · simp [hmstatus, hmseccfg] at h
  simp only [hmstatus, hmseccfg, beq_iff_eq] at h
  have hpmm : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) = .PMM_Disabled := by
    cases hp : pmm_mode_backwards (_get_Seccfg_PMM mseccfgBits) <;> simp_all
  refine ⟨⟨mstatusBits, hmstatus, h.1.1⟩, ⟨mseccfgBits, hmseccfg, hpmm⟩, ?_⟩
  intro access haccess
  have hrow := List.all_eq_true.mp h.2 access haccess
  unfold loadPmaAllowsB at hrow
  split at hrow
  · next regions hregions =>
      unfold pmaReadableAtB at hrow
      split at hrow
      · next region hmatch => exact ⟨regions, region, hregions, hmatch, hrow⟩
      · next => exact absurd hrow (by simp)
  · next => exact absurd hrow (by simp)

theorem loadPlatformPinned_frame {s s' : State} {accesses : List (Nat × Nat)}
    (mstatusFrame : s'.regs.get? mstatus = s.regs.get? mstatus)
    (mseccfgFrame : s'.regs.get? mseccfg = s.regs.get? mseccfg)
    (pmaFrame : s'.regs.get? pma_regions = s.regs.get? pma_regions)
    (h : LoadPlatformPinned s accesses) : LoadPlatformPinned s' accesses := by
  rcases h.mstatus with ⟨mstatusBits, mstatusRead, mprvZero⟩
  rcases h.mseccfg with ⟨mseccfgBits, mseccfgRead, pmmDisabled⟩
  refine ⟨⟨mstatusBits, mstatusFrame.trans mstatusRead, mprvZero⟩,
    ⟨mseccfgBits, mseccfgFrame.trans mseccfgRead, pmmDisabled⟩, ?_⟩
  intro access haccess
  obtain ⟨regions, region, regionsRead, matching, readable⟩ := h.allows access haccess
  exact ⟨regions, region, pmaFrame.trans regionsRead, matching, readable⟩

/-- Whether the configured machine's PMA table grants an executable four-byte instruction fetch at
every listed address and leaves the HTIF window disabled. Closed and finite once `addresses` is. -/
def configureFetchPinnedB (addresses : List Nat) : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ s => fetchPlatformPinnedB s addresses
  | .error _ _ => false

def configureLoadPinnedB (accesses : List (Nat × Nat)) : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ state => loadPlatformPinnedB state accesses
  | .error _ _ => false

/-- Whether the configuration program both succeeds and leaves a normal execution state with the five
fetch registers present. Closed and finite, like `configureSucceedsB`, so `native_decide` settles
it. -/
def configureNormalB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ s => normalExecutionB s && fetchPlatformPresentB s
  | .error _ _ => false

theorem configure_normal : configureNormalB = true := by native_decide

/-- **The machine configuration runs to a normal execution state.**

Its ABI register values are still deliberately left abstract — the builder's final `writeReg` block
pins the ones the entry binding reads. What is *no longer* abstract is the platform state, because
nothing downstream can retire a single instruction without it.

The last conjunct is an implication rather than a fact because the addresses are the caller's: this
module proves the configured machine's PMA table and HTIF base are whatever `configureZesuMachine`
left them, and hands back the consequence for any address list a caller can `native_decide`. -/
theorem configure_runs : ∃ mid, Runs configureZesuMachine initialState mid () ∧
    NormalExecutionState mid ∧ FetchPlatformPresent mid ∧
    (∀ addresses : List Nat, configureFetchPinnedB addresses = true →
      FetchPlatformPinned mid addresses) ∧
    (∀ accesses : List (Nat × Nat), configureLoadPinnedB accesses = true →
      LoadPlatformPinned mid accesses) := by
  have h := configure_normal
  unfold configureNormalB at h
  cases hr : configureZesuMachine.run initialState with
  | error e s => rw [hr] at h; simp at h
  | ok u s =>
    rw [hr] at h
    simp only [Bool.and_eq_true] at h
    refine ⟨s, ?_, normalExecutionState_of_check h.1, fetchPlatformPresent_of_check h.2, ?_, ?_⟩
    · show configureZesuMachine.run initialState = .ok () s
      rw [hr]
    · intro addresses hchecked
      unfold configureFetchPinnedB at hchecked
      rw [hr] at hchecked
      exact fetchPlatformPinned_of_check hchecked
    · intro accesses hchecked
      unfold configureLoadPinnedB at hchecked
      rw [hr] at hchecked
      exact loadPlatformPinned_of_check hchecked

/-- **`NormalExecutionState` reads none of the six registers the builder's ABI block writes**, so it
transports across that block verbatim. The six disequalities are the whole content: `x1`, `x2`,
`x10`, `x11`, `PC` and `nextPC` are general-purpose or program-counter registers, and every register
this predicate names is a platform CSR or the hart/privilege state. -/
theorem normalExecutionState_frame {s s' : State}
    (hframe : ∀ r : Register, r ≠ x1 → r ≠ x2 → r ≠ x10 → r ≠ x11 → r ≠ PC → r ≠ nextPC →
      s'.regs.get? r = s.regs.get? r)
    (h : NormalExecutionState s) : NormalExecutionState s' := by
  obtain ⟨hhart, hpriv, hsatp, hmideleg, hmie, hmip, hpmpcfg, hpmpaddr, hinhibit, hcfg, help,
    hmisa⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hframe _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
    assumption

/-! ## Loader helpers -/

/-- The canonical image is a single load segment, so the file loader reduces to one `loadFileSegment`
(`loadFileBackedImage_single_establishes`). -/
theorem programImage_single : ∃ seg, Artifacts.programImage.segments = #[seg] := by
  have h : Artifacts.programImage.segments.toList.length = 1 := by native_decide
  obtain ⟨seg, hseg⟩ := List.length_eq_one_iff.mp h
  exact ⟨seg, by apply Array.toList_inj.mp; simpa using hseg⟩

/-- **`storeU64` frames outside its eight-byte window.** The runtime-globals writes only need to be
threaded and shown to leave the earlier-established facts (code, input, decoder globals) untouched;
the concrete stored value is irrelevant to the entry binding, so only the frame is exposed. -/
theorem storeU64_establishes (addr value : Nat) (s0 : State) :
    ∃ s, Runs (storeU64 addr value) s0 s () ∧
      s.regs = s0.regs ∧
      (∀ a, a < addr ∨ addr + 8 ≤ a → s.mem.get? a = s0.mem.get? a) := by
  obtain ⟨s, hrun, hregs, hframe, _hwin⟩ :=
    forIn_writeBytes_establishes (fun i => addr + i)
      (fun i => BitVec.ofNat 8 ((value / 256 ^ i) % 256))
      (List.range' 0 8 1) s0 (range'_map_add_nodup addr 8)
  have hrun' : Runs (storeU64 addr value) s0 s () := by
    show Runs (forIn [:8] PUnit.unit _ >>= fun _ => pure PUnit.unit) s0 s ()
    rw [Std.Range.forIn_eq_forIn_range']
    exact Runs.bind (by simpa using hrun) (by show (pure PUnit.unit : SailM Unit).run s = .ok () s; rfl)
  refine ⟨s, hrun', hregs, ?_⟩
  intro a ha
  apply hframe
  simp only [List.mem_map, List.mem_range']
  rintro ⟨i, ⟨_, hi⟩, rfl⟩; omega

/-- **Every file-backed byte of the canonical image lies below `86028`** — the single load segment's
`initialEndAddress`. The runner adds its input (`0x2000…`), decoder globals (`0x421D…`), and heap
globals (`0x1503…`) strictly above every file byte, so a file-backed address is outside every runner
window and each loader's frame preserves `fileBytesLoadedFaithfully`. -/
theorem file_addr_lt {addr : Nat} {byte : UInt8}
    (h : Artifacts.programImage.readFileByte? addr = some byte) : addr < 86028 := by
  obtain ⟨seg, hmem, _, hlt⟩ := ProgramImage.readFileByte?_mem_segment h
  have hb : ∀ s ∈ Artifacts.programImage.segments.toList, s.initialEndAddress ≤ 86028 := by
    native_decide
  exact Nat.lt_of_lt_of_le hlt (hb seg hmem)

/-! ## The entry binding

The built state satisfies the exported function instance's entry binding at the canonical parameters and the
fresh incoming globals model. Threaded through the whole builder: configure (via `configure_runs`),
the file loader, the input loader, the zeroed decoder globals, and the two runtime-globals writes,
then the ABI register block. The three memory facts (`MemoryBytes`, `CodeIntact`, the fresh
`DecoderGlobalsRep`) each survive the later loaders because the runner's ranges are pairwise disjoint:
file bytes below `86028`, the input at `0x2000…`, and the decoder globals in `[0x421D1A0, 0x421D4E0)`,
all disjoint from the heap-global windows at `[0x1503?, …)`. -/

set_option maxRecDepth 10000 in
/-- **The built state is a valid decoder entry, and the runner's own ABI registers are exposed.**

**The four ABI registers the builder writes are exposed, not merely used.** `preZesuDecodeRaw` pins
only `a0` and `a1`, because those are the two the *decoder's* contract reads. The builder also writes
`ra := canonicalRunnerLayout.sentinel`, `sp := stackStop`, and `PC`/`nextPC := zesu_decode_raw`, and
those three are what the **runner's** side of the proof needs: the sentinel bridge
(`RiscV/Elfling/SentinelBridge.lean`) can only turn a function trace into a `TraceToSentinel` if the
final `ret` lands on the sentinel, which is a fact about `ra`; and the entry `FunctionTrace` starts at
the entry pc, which is a fact about `PC`. Both were already *proved* here — they are literal `insert`s
in the state this proof constructs — and were simply discarded by the old conclusion, so a caller had
to re-derive facts this theorem had in hand. `buildZesuEntryState_entry_binding` below is the old
statement, derived from this one, so the three existing callers are untouched.

This exposes the register values **at the entry state only**; the exit-side half is now supplied from
the other end. `Contracts/ExportedDecoder.lean`'s `postZesuDecodeRaw` and `Contracts/Runtime.lean`'s
two accessor postconditions carry `Agree platformPreserved before after` and
`RetiredCounterPresent after` — the frame clause composes with the `x1 := sentinel` exposed here to
give the bridge's `linkIsSentinel` (`platformPreserved_link`) and with `NormalExecutionState s` to
give it at the exit (`normalExecutionState_of_platformPreserved`), and it additionally carries the
five registers `NormalExecutionState` omits. The counter is separate because the machine writes
`minstret` on every retirement, so preservation of it would be false of every function instance.

(An earlier version of this note said no `post*` in `Contracts/` mentioned `x1`, and a later one said
those postconditions carry `x1 = x1` and `NormalExecutionState after`. Both are superseded;
`CalleeFrame` still has no SSZ call site, and `ExportedDecoderAudit.calleeFrame_is_not_the_vocabulary`
records why the clause was not spelled with it.)

**One entry-side gap this leaves, and one that is now closed.** `FetchPlatformPresent` above and
`platformPreserved` are not the same list, deliberately:

* `htif_tohost_base` is in `platformPreserved` (the MMIO dispatch is a run of `within_mmio_readable`,
  which reads exactly that register) and is **not** in `FetchPlatformPresent`. That gap is now closed
  from the other side: `FetchPlatformPinned` carries it at its *value*, `some none`, which is what
  `Platform/FetchMmio.lean`'s `fetchMemoryNoMMIO_of_state_layout_excluded` consumes, and it is
  discharged by the same `native_decide` over `configureZesuMachine.run initialState` the other five
  registers got. `pma_regions` moved with it, for the sharper reason that its *presence* was never
  enough — `FetchPmaAllows` evaluates `matching_pma_region` on the table.
* `minstret` is in `FetchPlatformPresent`, which is right *here* — the entry state does have it — but
  it cannot be carried across the call by agreement, which is why the contract asks for
  `RetiredCounterPresent` at the exit instead. That one is still open by design, not by omission. -/
theorem buildZesuEntryState_entry_binding_abi (input : ByteArray) :
    ∃ s, Runs (buildZesuEntryState input) initialState s () ∧
      preZesuDecodeRaw canonicalEnvironment canonicalDecoderGlobalsLayout canonicalResultBuffer
        canonicalStatelessInputRep DecoderGlobalsModel.fresh ⟨canonicalRunnerLayout.inputBase, input⟩ s ∧
      s.regs.get? x1 = some (BitVec.ofNat 64 canonicalRunnerLayout.sentinel) ∧
      s.regs.get? x2 = some (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) ∧
      NormalExecutionState s ∧ FetchPlatformPresent s ∧
      (∀ addresses : List Nat, configureFetchPinnedB addresses = true →
        FetchPlatformPinned s addresses) ∧
      (∀ accesses : List (Nat × Nat), configureLoadPinnedB accesses = true →
        LoadPlatformPinned s accesses) ∧
      ∃ entrySym, Artifacts.zesuDecodeRaw.toOption = some entrySym ∧
        s.regs.get? PC = some (BitVec.ofNat 64 entrySym.value) ∧
        s.regs.get? nextPC = some (BitVec.ofNat 64 entrySym.value) ∧
          s.regs.get? pma_regions = some [zesuMainMemoryRegion] ∧
            (∃ value, s.regs.get? x8 = some value) ∧
              (∃ value, s.regs.get? x9 = some value) ∧
                (∃ value, s.regs.get? x18 = some value) ∧
                  CalleeSavedRegistersPresent s := by
  -- Stage the loaders.
  obtain ⟨seg, hsingle⟩ := programImage_single
  obtain ⟨s1, hrun1, hnormal1, hfetch1, hpinned1, hloadPinned1⟩ := configure_runs
  have hrun1' : configureZesuMachine.run initialState = .ok () s1 := hrun1
  have hpma1 : s1.regs.get? pma_regions = some [zesuMainMemoryRegion] :=
    configure_pma_regions hrun1'
  have hsaved1 := configure_saved_registers_present hrun1'
  have hcallee1 := configure_callee_saved_registers_present hrun1'
  obtain ⟨s2, hrun2, hregs2, _hlow2, _hhigh2, hfile2⟩ :=
    loadFileBackedImage_single_establishes hsingle s1
  obtain ⟨sstack, hrunstack, hregsstack, hframestack, _hwinstack⟩ :=
    loadZeroBytes_establishes canonicalRunnerLayout.stackBase canonicalRunnerLayout.stackSize s2
  obtain ⟨s3, hrun3, hregs3, hframe3, hwin3⟩ :=
    loadBytes_establishes canonicalRunnerLayout.inputBase input sstack
  obtain ⟨s4, hrun4, hregs4, hframe4, hwin4⟩ :=
    loadZeroBytes_establishes decoderBssBase GeneratedDecoderGlobals.bssSize s3
  obtain ⟨s5, hrun5, hregs5, hframe5⟩ :=
    storeU64_establishes zkvmHeapPos
      ((GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "heap")).elim 0 (·.2.1)) s4
  obtain ⟨s6, hrun6, hregs6, hframe6⟩ :=
    storeU64_establishes zkvmHeapTop
      ((GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "heap")).elim 0 (fun g => g.2.1 + g.2.2)) s5
  -- The entry symbol resolves, so the builder's final match reduces to the two PC writes.
  obtain ⟨entrySym, hentry⟩ : ∃ sym, Artifacts.zesuDecodeRaw.toOption = some sym := by
    match h : Artifacts.zesuDecodeRaw.toOption with
    | some sym => exact ⟨sym, rfl⟩
    | none => exact absurd h (by native_decide)
  -- The concrete numeric landscape of the runner's ranges.
  have hzt : zkvmHeapTop = 86032 := by native_decide
  have hzp : zkvmHeapPos = 86040 := by native_decide
  have hbb : decoderBssBase = 69292064 := by native_decide
  have hbs : GeneratedDecoderGlobals.bssSize = 864 := by native_decide
  have hib : (69292928 : Nat) ≤ canonicalRunnerLayout.inputBase := by native_decide
  -- Memory-frame transports through the post-input loaders (the two heap-globals writes and the
  -- zeroed decoder globals), each justified because the runner's ranges are pairwise disjoint.
  have hmem_high : ∀ a, 69292928 ≤ a → s6.mem.get? a = s3.mem.get? a := fun a ha =>
    (hframe6 a (Or.inr (by omega))).trans ((hframe5 a (Or.inr (by omega))).trans
      (hframe4 a (Or.inr (by omega))))
  -- File bytes are below every runner range, the zeroed stack included, so they survive all of them.
  have hstackBase : (86028 : Nat) ≤ canonicalRunnerLayout.stackBase := by decide
  have hmem_low : ∀ a, a < 86028 → s6.mem.get? a = s2.mem.get? a := fun a ha =>
    (hframe6 a (Or.inl (by omega))).trans ((hframe5 a (Or.inl (by omega))).trans
      ((hframe4 a (Or.inl (by omega))).trans ((hframe3 a (Or.inl (by omega))).trans
        (hframestack a (Or.inl (by omega))))))
  have hmem_glob : ∀ a, 86048 ≤ a → s6.mem.get? a = s4.mem.get? a := fun a ha =>
    (hframe6 a (Or.inr (by omega))).trans (hframe5 a (Or.inr (by omega)))
  have hregs6_1 : s6.regs = s1.regs := by
    rw [hregs6, hregs5, hregs4, hregs3, hregsstack, hregs2]
  -- Build the entry state, threading `Runs`, and read off the memory and the ABI registers.
  have hbuilt : ∃ sf, Runs (buildZesuEntryState input) initialState sf () ∧
      sf.mem = s6.mem ∧
      sf.regs.get? x10 = some (BitVec.ofNat 64 canonicalRunnerLayout.inputBase) ∧
      sf.regs.get? x11 = some (BitVec.ofNat 64 input.size) ∧
      sf.regs.get? x1 = some (BitVec.ofNat 64 canonicalRunnerLayout.sentinel) ∧
      sf.regs.get? x2 = some (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) ∧
      sf.regs.get? PC = some (BitVec.ofNat 64 entrySym.value) ∧
      sf.regs.get? nextPC = some (BitVec.ofNat 64 entrySym.value) ∧
      NormalExecutionState sf ∧ FetchPlatformPresent sf ∧
      (∀ addresses : List Nat, configureFetchPinnedB addresses = true →
        FetchPlatformPinned sf addresses) ∧
      (∀ accesses : List (Nat × Nat), configureLoadPinnedB accesses = true →
        LoadPlatformPinned sf accesses) ∧
      sf.regs.get? pma_regions = some [zesuMainMemoryRegion] ∧
      (∃ value, sf.regs.get? x8 = some value) ∧
        (∃ value, sf.regs.get? x9 = some value) ∧
          (∃ value, sf.regs.get? x18 = some value) ∧
            CalleeSavedRegistersPresent sf := by
    have hrunR : Runs
        (writeReg x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase) >>= fun _ =>
         writeReg x11 (BitVec.ofNat 64 input.size) >>= fun _ =>
         writeReg x1 (BitVec.ofNat 64 canonicalRunnerLayout.sentinel) >>= fun _ =>
         writeReg x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) >>= fun _ =>
         writeReg PC (BitVec.ofNat 64 entrySym.value) >>= fun _ =>
         writeReg nextPC (BitVec.ofNat 64 entrySym.value))
        s6 { s6 with regs := ((((( s6.regs.insert x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase)).insert x11 (BitVec.ofNat 64 input.size)).insert x1 (BitVec.ofNat 64 canonicalRunnerLayout.sentinel)).insert x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)).insert PC (BitVec.ofNat 64 entrySym.value)).insert nextPC (BitVec.ofNat 64 entrySym.value) } () :=
      Runs.bind (by rw [Runs, writeReg_run]) (Runs.bind (by rw [Runs, writeReg_run])
        (Runs.bind (by rw [Runs, writeReg_run]) (Runs.bind (by rw [Runs, writeReg_run])
          (Runs.bind (by rw [Runs, writeReg_run]) (by rw [Runs, writeReg_run])))))
    refine ⟨{ s6 with regs := ((((( s6.regs.insert x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase)).insert x11 (BitVec.ofNat 64 input.size)).insert x1 (BitVec.ofNat 64 canonicalRunnerLayout.sentinel)).insert x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)).insert PC (BitVec.ofNat 64 entrySym.value)).insert nextPC (BitVec.ofNat 64 entrySym.value) }, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold buildZesuEntryState initStack
      simp only [hentry]
      exact Runs.bind hrun1 (Runs.bind hrun2 (Runs.bind hrunstack (Runs.bind hrun3 (Runs.bind hrun4
        (Runs.bind (Runs.bind hrun5 hrun6) hrunR)))))
    · simp [Std.ExtDHashMap.get?_insert]
    · simp [Std.ExtDHashMap.get?_insert]
    · simp [Std.ExtDHashMap.get?_insert]
    · simp [Std.ExtDHashMap.get?_insert]
    · simp [Std.ExtDHashMap.get?_insert]
    · -- `nextPC` is the outermost write, so no frame step is needed.
      simp
    · -- The platform state survives every loader (each frames `regs`) and the ABI block (which
      -- writes only general-purpose registers and the two program counters).
      have hchain : s6.regs = s1.regs := by
        rw [hregs6, hregs5, hregs4, hregs3, hregsstack, hregs2]
      refine normalExecutionState_frame (fun r h1 h2 h10 h11 hpc hnext => ?_) hnormal1
      simp [Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h10, Ne.symm h11,
        Ne.symm hpc, Ne.symm hnext, hchain]
    · -- The same frame, for the five registers the fetch reads.
      have hchain : s6.regs = s1.regs := by
        rw [hregs6, hregs5, hregs4, hregs3, hregsstack, hregs2]
      refine fetchPlatformPresent_frame (fun r h1 h2 h10 h11 hpc hnext => ?_) hfetch1
      simp [Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h10, Ne.symm h11,
        Ne.symm hpc, Ne.symm hnext, hchain]
    · -- And once more for the two registers the fetch reads at their value.
      have hchain : s6.regs = s1.regs := by
        rw [hregs6, hregs5, hregs4, hregs3, hregsstack, hregs2]
      intro addresses hchecked
      refine fetchPlatformPinned_frame (fun r h1 h2 h10 h11 hpc hnext => ?_) (hpinned1 addresses hchecked)
      simp [Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2, Ne.symm h10, Ne.symm h11,
        Ne.symm hpc, Ne.symm hnext, hchain]
    · have hchain : s6.regs = s1.regs := by
        rw [hregs6, hregs5, hregs4, hregs3, hregsstack, hregs2]
      intro accesses hchecked
      refine loadPlatformPinned_frame ?_ ?_ ?_ (hloadPinned1 accesses hchecked) <;>
        simp [Std.ExtDHashMap.get?_insert, hchain]
    · simp [Std.ExtDHashMap.get?_insert, hregs6_1, hpma1]
    · obtain ⟨value, hvalue⟩ := hsaved1.1
      exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
    · obtain ⟨value, hvalue⟩ := hsaved1.2.1
      exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
    · obtain ⟨value, hvalue⟩ := hsaved1.2.2
      exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
    · rcases hcallee1 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
      constructor
      · rcases h19 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h20 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h21 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h22 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h23 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h24 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h25 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      constructor
      · rcases h26 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
      · rcases h27 with ⟨value, hvalue⟩
        exact ⟨value, by simp [Std.ExtDHashMap.get?_insert, hregs6_1, hvalue]⟩
  obtain ⟨sf, hrunsf, hmemsf, hx10, hx11, hx1, hx2, hpc, hnextpc, hnormal, hfetchsf,
    hpinnedsf, hloadPinnedsf, hpmasf, hx8sf, hx9sf, hx18sf, hcalleesf⟩ :=
    hbuilt
  refine ⟨sf, hrunsf, ?_, hx1, hx2, hnormal, hfetchsf, hpinnedsf, hloadPinnedsf,
    entrySym, hentry, hpc, hnextpc, hpmasf, hx8sf, hx9sf, hx18sf, hcalleesf⟩
  -- Reduce the argument projections once, then discharge each entry-binding conjunct.
  show MemoryBytes sf canonicalRunnerLayout.inputBase input ∧
      canonicalEnvironment.CodeIntact sf ∧
      sf.regs.get? x10 = some (BitVec.ofNat 64 canonicalRunnerLayout.inputBase) ∧
      sf.regs.get? x11 = some (BitVec.ofNat 64 input.size) ∧
      DecoderGlobalsRep canonicalDecoderGlobalsLayout canonicalStatelessInputRep
        canonicalRunnerLayout.inputBase input canonicalResultBuffer DecoderGlobalsModel.fresh sf
  refine ⟨?_, ?_, hx10, hx11, ?_, ?_⟩
  · -- MemoryBytes: the input reads back.
    intro i hi
    rw [hmemsf, hmem_high (canonicalRunnerLayout.inputBase + i) (by omega)]
    exact hwin3 i hi
  · -- CodeIntact: fileBytesLoadedFaithfully transports from `s2`. Rewrite `env.image` to the artifact
    -- image with a syntactic projection lemma — reducing it by `whnf` would force the ELF parse.
    have hcanimg : canonicalEnvironment.image = Artifacts.programImage := by
      simp only [canonicalEnvironment]
    show canonicalEnvironment.image.fileBytesLoadedFaithfully sf.mem
    rw [hcanimg]
    intro addr byte hread
    rw [hmemsf, hmem_low addr (file_addr_lt hread)]
    exact hfile2 addr byte hread
  · -- DecoderGlobalsScalarRep: attempted flag and status word are zero.
    refine ⟨?_, ?_⟩
    · -- FlagRep attempted false.
      show sf.mem.get? canonicalDecoderGlobalsLayout.attempted
        = some (BitVec.ofNat 8 (if DecoderGlobalsModel.fresh.attempted then 1 else 0))
      have haddr : canonicalDecoderGlobalsLayout.attempted = decoderBssBase + 0 := by native_decide
      rw [hmemsf, haddr, hmem_glob (decoderBssBase + 0) (by omega)]
      simpa [DecoderGlobalsModel.fresh] using hwin4 0 (by omega)
    · -- Word32LERep status 0.
      intro index hidx
      show sf.mem.get? (canonicalDecoderGlobalsLayout.status + index)
        = some (BitVec.ofNat 8 ((DecoderGlobalsModel.fresh.status.code / 256 ^ index) % 256))
      have haddr : canonicalDecoderGlobalsLayout.status + index = decoderBssBase + (4 + index) := by
        have hst : canonicalDecoderGlobalsLayout.status = decoderBssBase + 4 := by native_decide
        omega
      rw [hmemsf, haddr, hmem_glob (decoderBssBase + (4 + index)) (by omega),
        hwin4 (4 + index) (by omega)]
      simp [DecoderGlobalsModel.fresh, DecodeStatus.code]
  · -- StoredResultRep: the discriminant is zero (absent), no payload.
    refine ⟨?_, ?_⟩
    · -- StoredResultDiscriminantRep: OptionTagRep discriminant false.
      show sf.mem.get? (canonicalDecoderGlobalsLayout.storedResult
          + canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset)
        = some (BitVec.ofNat 8 (if DecoderGlobalsModel.fresh.stored.isSome then 1 else 0))
      have haddr : canonicalDecoderGlobalsLayout.storedResult
          + canonicalDecoderGlobalsLayout.storedResultObject.discriminantOffset
          = decoderBssBase + 848 := by native_decide
      rw [hmemsf, haddr, hmem_glob (decoderBssBase + 848) (by omega)]
      simpa [DecoderGlobalsModel.fresh] using hwin4 848 (by omega)
    · -- No stored value.
      simp [DecoderGlobalsModel.fresh]

/-- The entry binding alone, which is what the three satisfiability callers consume. Derived from
`buildZesuEntryState_entry_binding_abi` rather than proved again, so there is one construction of the
entry state and one place a change to the builder has to be reflected. -/
theorem buildZesuEntryState_entry_binding (input : ByteArray) :
    ∃ s, Runs (buildZesuEntryState input) initialState s () ∧
      preZesuDecodeRaw canonicalEnvironment canonicalDecoderGlobalsLayout canonicalResultBuffer
        canonicalStatelessInputRep DecoderGlobalsModel.fresh ⟨canonicalRunnerLayout.inputBase, input⟩ s := by
  obtain ⟨s, hrun, hbind, -⟩ := buildZesuEntryState_entry_binding_abi input
  exact ⟨s, hrun, hbind⟩

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
