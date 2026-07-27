import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.StateBuilder
import BinaryFv.RiscV.Logic.Framing
import BinaryFv.RiscV.Proof.ImageLoadFrame
import BinaryFv.SSZ.Zesu.Contracts.CanonicalParams
import BinaryFv.SSZ.Zesu.Contracts.ExportedDecoder

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
Everything after configuration is input-dependent and is threaded with the `ImageLoadFrame` establishment
lemmas: each loader sets its own addresses and frames the complement, so the earlier-established facts
survive because the runner's ranges are pairwise disjoint.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Elfling

/-! ## The machine configuration succeeds -/

/-- Whether the configuration program runs to a normal (non-error) result from the empty initial
state. A closed finite computation, so `native_decide` settles it. -/
def configureSucceedsB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ _ => true
  | .error _ _ => false

theorem configure_succeeds : configureSucceedsB = true := by native_decide

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

/-- Whether the configuration program both succeeds and leaves a normal execution state. Closed and
finite, like `configureSucceedsB`, so `native_decide` settles it. -/
def configureNormalB : Bool :=
  match configureZesuMachine.run initialState with
  | .ok _ s => normalExecutionB s
  | .error _ _ => false

theorem configure_normal : configureNormalB = true := by native_decide

/-- **The machine configuration runs to a normal execution state.**

Its ABI register values are still deliberately left abstract — the builder's final `writeReg` block
pins the ones the entry binding reads. What is *no longer* abstract is the platform state, because
nothing downstream can retire a single instruction without it. -/
theorem configure_runs : ∃ mid, Runs configureZesuMachine initialState mid () ∧
    NormalExecutionState mid := by
  have h := configure_normal
  unfold configureNormalB at h
  cases hr : configureZesuMachine.run initialState with
  | error e s => rw [hr] at h; simp at h
  | ok u s =>
    refine ⟨s, ?_, normalExecutionState_of_check (by rw [hr] at h; exact h)⟩
    show configureZesuMachine.run initialState = .ok () s
    rw [hr]

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
theorem programImage_single : ∃ seg, Artifact.programImage.segments = #[seg] := by
  have h : Artifact.programImage.segments.toList.length = 1 := by native_decide
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
window and each loader's frame preserves `fileBytesMatchMemory`. -/
theorem file_addr_lt {addr : Nat} {byte : UInt8}
    (h : Artifact.programImage.readFileByte? addr = some byte) : addr < 86028 := by
  obtain ⟨seg, hmem, _, hlt⟩ := ProgramImage.readFileByte?_mem_segment h
  have hb : ∀ s ∈ Artifact.programImage.segments.toList, s.initialEndAddress ≤ 86028 := by
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

This exposes the register values **at the entry state only**. It does *not* say `ra` survives the
call: nothing in the contract layer constrains callee-saved registers (`CalleeFrame` exists in
`RiscV/Elfling/Contract.lean` and is used by no SSZ contract, and no `post*` in `Contracts/` mentions
`x1`), so the exit-side half of the bridge's obligation remains open. -/
theorem buildZesuEntryState_entry_binding_abi (input : ByteArray) :
    ∃ s, Runs (buildZesuEntryState input) initialState s () ∧
      preZesuDecodeRaw canonicalEnvironment canonicalDecoderGlobalsLayout canonicalResultBuffer
        canonicalRepRawV4 DecoderGlobalsModel.fresh ⟨canonicalRunnerLayout.inputBase, input⟩ s ∧
      s.regs.get? x1 = some (BitVec.ofNat 64 canonicalRunnerLayout.sentinel) ∧
      s.regs.get? x2 = some (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) ∧
      NormalExecutionState s ∧
      ∃ entrySym, Artifact.zesuDecodeRaw.toOption = some entrySym ∧
        s.regs.get? PC = some (BitVec.ofNat 64 entrySym.value) ∧
        s.regs.get? nextPC = some (BitVec.ofNat 64 entrySym.value) := by
  -- Stage the loaders.
  obtain ⟨seg, hsingle⟩ := programImage_single
  obtain ⟨s1, hrun1, hnormal1⟩ := configure_runs
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
  obtain ⟨entrySym, hentry⟩ : ∃ sym, Artifact.zesuDecodeRaw.toOption = some sym := by
    match h : Artifact.zesuDecodeRaw.toOption with
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
  -- Build the entry state, threading `Runs`, and read off the memory and the ABI registers.
  have hbuilt : ∃ sf, Runs (buildZesuEntryState input) initialState sf () ∧
      sf.mem = s6.mem ∧
      sf.regs.get? x10 = some (BitVec.ofNat 64 canonicalRunnerLayout.inputBase) ∧
      sf.regs.get? x11 = some (BitVec.ofNat 64 input.size) ∧
      sf.regs.get? x1 = some (BitVec.ofNat 64 canonicalRunnerLayout.sentinel) ∧
      sf.regs.get? x2 = some (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) ∧
      sf.regs.get? PC = some (BitVec.ofNat 64 entrySym.value) ∧
      sf.regs.get? nextPC = some (BitVec.ofNat 64 entrySym.value) ∧
      NormalExecutionState sf := by
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
    refine ⟨{ s6 with regs := ((((( s6.regs.insert x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase)).insert x11 (BitVec.ofNat 64 input.size)).insert x1 (BitVec.ofNat 64 canonicalRunnerLayout.sentinel)).insert x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)).insert PC (BitVec.ofNat 64 entrySym.value)).insert nextPC (BitVec.ofNat 64 entrySym.value) }, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  obtain ⟨sf, hrunsf, hmemsf, hx10, hx11, hx1, hx2, hpc, hnextpc, hnormal⟩ := hbuilt
  refine ⟨sf, hrunsf, ?_, hx1, hx2, hnormal, entrySym, hentry, hpc, hnextpc⟩
  -- Reduce the argument projections once, then discharge each entry-binding conjunct.
  show MemoryBytes sf canonicalRunnerLayout.inputBase input ∧
      canonicalEnvironment.CodeIntact sf ∧
      sf.regs.get? x10 = some (BitVec.ofNat 64 canonicalRunnerLayout.inputBase) ∧
      sf.regs.get? x11 = some (BitVec.ofNat 64 input.size) ∧
      DecoderGlobalsRep canonicalDecoderGlobalsLayout canonicalRepRawV4
        canonicalRunnerLayout.inputBase input canonicalResultBuffer DecoderGlobalsModel.fresh sf
  refine ⟨?_, ?_, hx10, hx11, ?_, ?_⟩
  · -- MemoryBytes: the input reads back.
    intro i hi
    rw [hmemsf, hmem_high (canonicalRunnerLayout.inputBase + i) (by omega)]
    exact hwin3 i hi
  · -- CodeIntact: fileBytesMatchMemory transports from `s2`. Rewrite `env.image` to the artifact
    -- image with a syntactic projection lemma — reducing it by `whnf` would force the ELF parse.
    have hcanimg : canonicalEnvironment.image = Artifact.programImage := by
      simp only [canonicalEnvironment]
    show canonicalEnvironment.image.fileBytesMatchMemory sf.mem
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
        canonicalRepRawV4 DecoderGlobalsModel.fresh ⟨canonicalRunnerLayout.inputBase, input⟩ s := by
  obtain ⟨s, hrun, hbind, -⟩ := buildZesuEntryState_entry_binding_abi input
  exact ⟨s, hrun, hbind⟩

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
