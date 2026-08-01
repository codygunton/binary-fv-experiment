import BinaryFv.RiscV.Elfling.SentinelBridge
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Execution
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.EntryBinding
import BinaryFv.Zesu.Contracts.Runtime
import BinaryFv.Zesu.Contracts.Footprint
import BinaryFv.Zesu.Elflings.GeneratedReturnExits

/-!
# The exported accessors' calling sequence, threaded

`runAccessorsIfReached` (`Runner.lean`) is the only part of the executable runner about which nothing
was proved: `SuccessfulRun.accessors` and `RejectedRun.accessors` each demand a
`Runs (runAccessorsIfReached …)` and no lemma produced one. This module supplies everything in that
gap that does **not** depend on machine execution, and names the exact residue that does.

The split is clean because `runAccessor` has exactly two halves:

* a **prologue** of four `writeReg`s — `ra` at the sentinel, `sp` at the top of the runner's stack,
  `PC`/`nextPC` at the accessor's entry — which is pure state update and is settled here in full
  (`accessorSetup`, and the frame lemmas below);
* a **body**, `runToOutcome` from that state, which is real execution and is settled only by a trace.

So every theorem here takes the trace as a premise and does the rest. `runToOutcome_of_traceToSentinel`
already turns a `TraceToSentinel` into a `Runs` of the body; what was missing was the prologue, the
inversion of `a0` into `AccessorOutcome.returned`, and the sequencing of the two calls.
`accessorReachesSentinel_of_enteredFunctionTrace` joins this to
`Elfling.traceToSentinel_of_enteredFunctionTrace`, so an accessor contract's own
`ImplementsFunctionInstance` obligation plus its `ret` is all that
`AcceptedAccessorTraces`/`RejectedAccessorTraces` still want, and the two accessor fields are then
constructed with no further machine reasoning.

## What is *not* here, deliberately

No accessor trace is constructed, and none can be at this layer: `TraceToSentinel.step` carries
`Runs (try_step …)`, which only real execution produces. That is not an omission that a reader has to
take on trust — `zero_length_accessor_traces_force_equal_codes` below *proves* that the degenerate
zero-step traces cannot even distinguish the two accessors' return codes, so the accepted path's
obligation genuinely requires retired steps.

## Trust surface

The threading itself is compiler-free: `runAccessor_returned_of_trace`,
`runAccessorsIfReached_returned_of_traces`, `zero_length_accessor_traces_force_equal_codes` and both
satisfiability witnesses reach only `propext`/`Classical.choice`/`Quot.sound`. Three doors enter
elsewhere and each is inherited rather than opened here: `resolvedSymbols` (Runner's
`runnerSymbols_isSome`) in everything phrased at the pinned symbols, `raw_stateless_input_layout` (the
ABI manifest) in `rawV4Rep_accessorSetup`, and the builder's own `native_decide`s in
`accessor_entry_bindings_satisfiable`.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.Zesu
open BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.MemoryRepresentation

/-! ## The prologue's post-state

`runAccessor`'s four `writeReg`s are a single record update on `regs`. Naming it makes both halves of
what the assembly needs statable: which registers the accessor is entered with, and — the part the
surrounding proof depends on — that *memory is untouched*, so every fact established at the decode's
final state survives into the accessor call. -/

/-- The state `runAccessor entryPc` enters its accessor from: the decode's final state with `ra`, `sp`,
`PC` and `nextPC` set to the C ABI values `runAccessor` writes, and nothing else changed. -/
def accessorSetup (entryPc : Nat) (state : State) : State :=
  { state with
      regs := (((state.regs.insert x1 sentinelWord).insert x2
        (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)).insert PC
        (BitVec.ofNat 64 entryPc)).insert nextPC (BitVec.ofNat 64 entryPc) }

/-- **The prologue runs, and lands exactly there.** The four `writeReg`s of `runAccessor`, threaded. -/
theorem accessorSetup_runs (entryPc : Nat) (state : State) :
    Runs (writeReg x1 sentinelWord >>= fun _ =>
          writeReg x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) >>= fun _ =>
          writeReg PC (BitVec.ofNat 64 entryPc) >>= fun _ =>
          writeReg nextPC (BitVec.ofNat 64 entryPc))
      state (accessorSetup entryPc state) () :=
  Runs.bind (writeReg_run state x1 sentinelWord)
    (Runs.bind (writeReg_run _ x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop))
      (Runs.bind (writeReg_run _ PC (BitVec.ofNat 64 entryPc))
        (writeReg_run _ nextPC (BitVec.ofNat 64 entryPc))))

/-- **The prologue writes no memory.** This is the load-bearing half: every memory predicate
established at the decode's final state — `MemoryBytes`, `CodeIntact`, the decoder globals, the
stored `RawV4` — holds verbatim at the accessor's entry state, because the two states have the *same*
memory, not merely agreeing memory. -/
@[simp] theorem accessorSetup_mem (entryPc : Nat) (state : State) :
    (accessorSetup entryPc state).mem = state.mem := rfl

@[simp] theorem accessorSetup_nextPC (entryPc : Nat) (state : State) :
    (accessorSetup entryPc state).regs.get? nextPC = some (BitVec.ofNat 64 entryPc) := by
  simp [accessorSetup]

@[simp] theorem accessorSetup_pc (entryPc : Nat) (state : State) :
    (accessorSetup entryPc state).regs.get? PC = some (BitVec.ofNat 64 entryPc) := by
  simp [accessorSetup, Std.ExtDHashMap.get?_insert]

/-- `ra` holds the return sentinel, which is what makes the accessor's return observable at all. -/
@[simp] theorem accessorSetup_ra (entryPc : Nat) (state : State) :
    (accessorSetup entryPc state).regs.get? x1 = some sentinelWord := by
  simp [accessorSetup, Std.ExtDHashMap.get?_insert]

/-- `sp` is the top of the runner's stack, freshly, rather than whatever the previous call left. -/
@[simp] theorem accessorSetup_sp (entryPc : Nat) (state : State) :
    (accessorSetup entryPc state).regs.get? x2 =
      some (BitVec.ofNat 64 canonicalRunnerLayout.stackStop) := by
  simp [accessorSetup, Std.ExtDHashMap.get?_insert]

/-- Every register the prologue does not write reads back unchanged. -/
theorem accessorSetup_regs_frame (entryPc : Nat) (state : State) (observed : Register)
    (hra : observed ≠ x1) (hsp : observed ≠ x2) (hpc : observed ≠ PC) (hnext : observed ≠ nextPC) :
    (accessorSetup entryPc state).regs.get? observed = state.regs.get? observed := by
  simp [accessorSetup, Std.ExtDHashMap.get?_insert, Ne.symm hra, Ne.symm hsp, Ne.symm hpc,
    Ne.symm hnext]

/-- **The prologue cannot manufacture a return code.** `a0` is not one of the four registers it
writes, so the value `runAccessor` eventually reports is the accessor's own, never a leftover the
setup installed. -/
@[simp] theorem accessorSetup_observeReturnCode (entryPc : Nat) (state : State) :
    observeReturnCode? (accessorSetup entryPc state) = observeReturnCode? state := by
  unfold observeReturnCode?
  rw [accessorSetup_regs_frame entryPc state x10 (by decide) (by decide) (by decide) (by decide)]

/-! ## Memory facts survive the prologue

Each of these is `rfl`-cheap because the predicate reads only `.mem`, and each is stated anyway: the
assembly consumes them by name, and a predicate that quietly stopped being memory-only would break
here rather than at the point of use. `RawV4Rep` is the exception — it is a nest of structures, so it
transports through the footprint machinery rather than definitionally. -/

/-- The input window the decode preserved is still there when the accessor is entered. -/
theorem memoryBytes_accessorSetup {state : State} {base : Nat} {bytes : ByteArray}
    (entryPc : Nat) (h : MemoryBytes state base bytes) :
    MemoryBytes (accessorSetup entryPc state) base bytes := h

/-- The file-backed code and rodata are still intact when the accessor is entered — which is exactly
the `CodeIntact` conjunct both accessor contracts' entry bindings open with. -/
theorem codeIntact_accessorSetup {env : DecoderEnvironment} {state : State}
    (entryPc : Nat) (h : env.CodeIntact state) : env.CodeIntact (accessorSetup entryPc state) := h

/-- The scalar decoder globals still represent the same ghost model. -/
theorem decoderGlobalsScalarRep_accessorSetup {layout : DecoderGlobalsLayout}
    {model : DecoderGlobalsModel} {state : State} (entryPc : Nat)
    (h : DecoderGlobalsScalarRep layout model state) :
    DecoderGlobalsScalarRep layout model (accessorSetup entryPc state) := h

/-- The inline `stored_result` discriminant still represents the same ghost model. -/
theorem storedResultDiscriminantRep_accessorSetup {layout : DecoderGlobalsLayout}
    {model : DecoderGlobalsModel} {state : State} (entryPc : Nat)
    (h : StoredResultDiscriminantRep layout model state) :
    StoredResultDiscriminantRep layout model (accessorSetup entryPc state) := h

/-- The option-tag observer reads the same byte, so the runner's own discriminant observation is
unchanged by entering an accessor. -/
@[simp] theorem observeOptionTag_accessorSetup (entryPc : Nat) (state : State) (base : Nat) :
    observeOptionTag? (accessorSetup entryPc state) base = observeOptionTag? state base := rfl

/-- **The decoded value's representation survives the prologue.** `RawV4Rep` is a nest of structures
rather than a memory-reading `def`, so this goes through the root's footprint transport with the
memory agreement discharged by `rfl` — the two states share one `mem`, so every address agrees. -/
theorem rawV4Rep_accessorSetup {state : State} {inputBase rootBase : Nat} {input : ByteArray}
    {value : BinaryFv.Specs.SSZ.RawV4} (entryPc : Nat)
    (h : RawV4Rep state inputBase input rootBase value) :
    RawV4Rep (accessorSetup entryPc state) inputBase input rootBase value := by
  obtain ⟨_, htransport⟩ :=
    Footprint.rawV4_footprint_abi inputBase input rootBase value state
      BinaryFv.Zesu.Artifacts.raw_stateless_input_layout.1 h
  exact htransport _ (fun _ _ => rfl)

/-! ## Entry bindings for the two accessor contracts

`contractRawResult` and `contractRawError` are source-shaped contracts, so the entry binding an
`ImplementsFunctionInstance` consumes is their `pre` (`FunctionContract.toBinding`). Both `pre`s are
memory-only, which is why they are dischargeable here at all: the prologue is invisible to them, and
what remains is the memory content the decode's final state must supply. -/

/-- The entry binding of a source-shaped contract is its `pre`; recorded so the lemmas below can be
stated in the `pre` form a reader can check against `Contracts/Runtime.lean` and still be consumed
where the function-instance obligation expects `binding.entry`. -/
theorem functionInstance_entry_eq_pre {Error Args Result : Type}
    (contract : BinaryFv.RiscV.Elfling.FunctionContract Error Args Result) (args : Args)
    (state : State) :
    contract.toFunctionInstance.binding.entry args state = contract.pre args state := rfl

/-- **`zesu_raw_error`'s entry binding, at the state it is actually called from.** Both conjuncts are
transported from the decode's final state; neither is re-derived. -/
theorem contractRawError_entry_accessorSetup {env : DecoderEnvironment}
    {layout : DecoderGlobalsLayout} {model : DecoderGlobalsModel} {state : State} (entryPc : Nat)
    (hcode : env.CodeIntact state) (hglobals : DecoderGlobalsScalarRep layout model state) :
    (contractRawError env layout).pre model (accessorSetup entryPc state) :=
  ⟨codeIntact_accessorSetup entryPc hcode, decoderGlobalsScalarRep_accessorSetup entryPc hglobals⟩

/-- **`zesu_raw_result`'s entry binding, at the state it is actually called from.** -/
theorem contractRawResult_entry_accessorSetup {env : DecoderEnvironment}
    {layout : DecoderGlobalsLayout} {resultBuffer : Nat} {model : DecoderGlobalsModel}
    {state : State} (entryPc : Nat) (hcode : env.CodeIntact state)
    (hstored : StoredResultDiscriminantRep layout model state) :
    (contractRawResult env layout resultBuffer).pre model (accessorSetup entryPc state) :=
  ⟨codeIntact_accessorSetup entryPc hcode,
    storedResultDiscriminantRep_accessorSetup entryPc hstored⟩

/-- **Neither entry binding is vacuous at the state the runner actually calls from.** Both are
satisfied at the accessor setup over the state `buildZesuEntryState` really produces, with the fresh
globals model — so the two lemmas above are not conditional on an impossible premise.

The witness is the builder's own state rather than one written to suit: `CodeIntact` demands roughly
twenty kilobytes of file-backed image bytes, which cannot be written down by hand. -/
theorem accessor_entry_bindings_satisfiable :
    ∃ (state : State) (model : DecoderGlobalsModel),
      (contractRawError canonicalEnvironment Elflings.canonicalDecoderGlobalsLayout).pre model
        (accessorSetup resolvedSymbols.rawError state) ∧
      (contractRawResult canonicalEnvironment Elflings.canonicalDecoderGlobalsLayout
        Elflings.canonicalResultBuffer).pre model
        (accessorSetup resolvedSymbols.rawResult state) := by
  obtain ⟨state, _, binding⟩ := buildZesuEntryState_entry_binding ByteArray.empty
  exact ⟨state, DecoderGlobalsModel.fresh,
    contractRawError_entry_accessorSetup _ binding.2.1 binding.2.2.2.2.1,
    contractRawResult_entry_accessorSetup _ binding.2.1 binding.2.2.2.2.2.1⟩

/-! ### Getting `StoredResultDiscriminantRep` from what the runner already observes

The runner's witnesses (`SuccessfulRun.storedPresent`, `RejectedRun.storedAbsent`) record the
discriminant as an *observation* — `observeOptionTag? … = some b` — while the contract wants the
*representation*. `observe_option_tag_of_rep` goes one way only; this is the converse, which the
observer's own definition supports because it rejects every byte other than `0` and `1`. -/

/-- **The option-tag observer's converse.** A successful observation forces the representation, so an
observed discriminant is as good as a represented one. -/
theorem optionTagRep_of_observeOptionTag {state : State} {base : Nat} {present : Bool}
    (h : observeOptionTag? state base = some present) : OptionTagRep state base present := by
  unfold observeOptionTag? at h
  match hbyte : state.mem.get? base with
  | none => rw [hbyte] at h; exact absurd h (by simp)
  | some byte =>
    rw [hbyte] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    by_cases hone : byte = BitVec.ofNat 8 1
    · simp only [hone] at h
      simp at h
      subst h
      show state.mem.get? base = some (BitVec.ofNat 8 1)
      rw [hbyte, hone]
    · simp only [if_neg hone] at h
      by_cases hzero : byte = BitVec.ofNat 8 0
      · simp only [hzero] at h
        simp at h
        subst h
        show state.mem.get? base = some (BitVec.ofNat 8 0)
        rw [hbyte, hzero]
      · simp only [if_neg hzero] at h
        exact absurd h (by simp)

/-- The runner's discriminant observation, in the shape `contractRawResult`'s entry binding wants.
`storedResultDiscriminantAddr` is by definition the address the layout puts the discriminant at, so
no address is re-derived here. -/
theorem storedResultDiscriminantRep_of_observation {model : DecoderGlobalsModel} {state : State}
    (h : observeOptionTag? state storedResultDiscriminantAddr = some model.stored.isSome) :
    StoredResultDiscriminantRep Elflings.canonicalDecoderGlobalsLayout model state :=
  optionTagRep_of_observeOptionTag h

/-! ## From a contract's postcondition to the runner's observation

Both accessor postconditions pin `a0` as a 64-bit word; the runner reads it back through
`observeReturnCode?`, which is `BitVec.toNat`. These two lemmas are the join, and they are where the
`< 2 ^ 64` side condition is discharged once instead of at each use. -/

/-- **A pinned `a0` is a readable return code.** -/
theorem observeReturnCode_of_a0 {state : State} {value : Nat} (hbound : value < 2 ^ 64)
    (h : state.regs.get? x10 = some (BitVec.ofNat 64 value)) :
    observeReturnCode? state = some value := by
  unfold observeReturnCode?
  rw [h]
  simpa using Nat.mod_eq_of_lt hbound

/-- `zesu_raw_result`'s postcondition, read as the runner reads it. -/
theorem observeReturnCode_of_postRawResult {env : DecoderEnvironment} {resultBuffer : Nat}
    {model : DecoderGlobalsModel} {result : Except Contracts.DecodeError Nat} {before after : State}
    {pointer : Nat} (hbound : pointer < 2 ^ 64) (hresult : result = .ok pointer)
    (h : postRawResult env resultBuffer model result before after) :
    observeReturnCode? after = some pointer := by
  subst hresult
  -- code, allocation, ownership, the register frame, the retired counter, the pointer value,
  -- then `a0`.
  obtain ⟨-, -, -, -, -, -, ha0⟩ := h
  exact observeReturnCode_of_a0 hbound ha0

/-- `zesu_raw_error`'s postcondition, read as the runner reads it. -/
theorem observeReturnCode_of_postRawError {env : DecoderEnvironment} {model : DecoderGlobalsModel}
    {result : Except Contracts.DecodeError Nat} {before after : State} {code : Nat}
    (hbound : code < 2 ^ 64) (hresult : result = .ok code)
    (h : postRawError env model result before after) :
    observeReturnCode? after = some code := by
  subst hresult
  -- code, allocation, ownership, the register frame, the retired counter, the status value,
  -- then `a0`.
  obtain ⟨-, -, -, -, -, -, ha0⟩ := h
  exact observeReturnCode_of_a0 hbound ha0

/-! ## One accessor call, threaded end to end -/

/-- **`runAccessor` follows a trace to a return code.** The prologue is discharged here; the body is
the premise. The fuel premise is `count < fuel` because that is what `runToOutcome_of_traceToSentinel`
requires — `accessorFuel_exceeds_bound` supplies it from the accessor's own contract bound, so the
budget is never a free parameter. -/
theorem runAccessor_returned_of_trace (entryPc fuel : Nat) {before exit : State} {count code : Nat}
    (htrace : TraceToSentinel sentinelWord 0 count (accessorSetup entryPc before) exit)
    (hfuel : count < fuel) (hcode : observeReturnCode? exit = some code) :
    Runs (runAccessor entryPc fuel) before exit (.returned code) := by
  have hbody : Runs (runToOutcome sentinelWord fuel 0) (accessorSetup entryPc before) exit
      (.reached count) := by
    have := runToOutcome_of_traceToSentinel sentinelWord count fuel 0
      (accessorSetup entryPc before) exit htrace hfuel
    simpa using this
  unfold runAccessor
  refine Runs.bind (writeReg_run before x1 sentinelWord) ?_
  refine Runs.bind (writeReg_run _ x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)) ?_
  refine Runs.bind (writeReg_run _ PC (BitVec.ofNat 64 entryPc)) ?_
  refine Runs.bind (writeReg_run _ nextPC (BitVec.ofNat 64 entryPc)) ?_
  refine Runs.bind hbody ?_
  refine Runs.bind (get_runs exit) ?_
  rw [Runs, hcode]
  rfl

/-- The same, with the fuel premise supplied from the accessor's own contract step bound rather than
from a free number. This is the form the assembly uses.

**The premise is `stepBound + 1`, not `stepBound`, and the `+ 1` is not slack taken for comfort.** A
contract's `EnteredFunctionTrace` retires `count ≤ stepBound` steps and stops *on* the exit; the
sentinel is only reached by the `ret` that follows, and `traceToSentinel_of_functionTrace` accordingly
returns a trace of length `count + 1`. So the tighter premise would not compose with the bridge at
all. `accessorFuel stepBound = stepBound + 2` was sized for exactly this — one step to retire the
return onto the sentinel, one to keep the budget strictly greater — and this is where the first of
those two is spent. The tighter `count ≤ stepBound` is a special case, so nothing is lost. -/
theorem runAccessor_returned_of_bound (entryPc stepBound : Nat) {before exit : State}
    {count code : Nat}
    (htrace : TraceToSentinel sentinelWord 0 count (accessorSetup entryPc before) exit)
    (hbound : count ≤ stepBound + 1) (hcode : observeReturnCode? exit = some code) :
    Runs (runAccessor entryPc (accessorFuel stepBound)) before exit (.returned code) :=
  runAccessor_returned_of_trace entryPc (accessorFuel stepBound) htrace
    (by have := accessorFuel_exceeds_bound stepBound; unfold accessorFuel at *; omega) hcode

/-! ## Both accessor calls, sequenced

This is the shape `SuccessfulRun.accessors` and `RejectedRun.accessors` are stated in. Note the
threading: `zesu_raw_error` is called from the state `zesu_raw_result` *returned in*, not from the
decode's final state, so the second trace starts at `accessorSetup … middle`. -/

/-- **The two accessor calls, run in sequence from the decode's final state.** -/
theorem runAccessorsIfReached_returned_of_traces (symbols : RunnerSymbols) (steps : Nat)
    {final middle after : State} {resultCount errorCount resultCode errorCode : Nat}
    (hresultTrace : TraceToSentinel sentinelWord 0 resultCount
      (accessorSetup symbols.rawResult final) middle)
    (hresultBound : resultCount ≤ rawResultStepBound + 1)
    (hresultCode : observeReturnCode? middle = some resultCode)
    (herrorTrace : TraceToSentinel sentinelWord 0 errorCount
      (accessorSetup symbols.rawError middle) after)
    (herrorBound : errorCount ≤ rawErrorStepBound + 1)
    (herrorCode : observeReturnCode? after = some errorCode) :
    Runs (runAccessorsIfReached symbols (.reached steps)) final after
      (.returned resultCode, .returned errorCode) := by
  unfold runAccessorsIfReached
  refine Runs.bind (runAccessor_returned_of_bound symbols.rawResult rawResultStepBound
    hresultTrace hresultBound hresultCode) ?_
  exact Runs.bind (runAccessor_returned_of_bound symbols.rawError rawErrorStepBound
    herrorTrace herrorBound herrorCode) rfl

/-! ## The residue: what the sentinel bridge must supply

Everything above takes the accessor traces as premises. These are the premises, named — as `Prop`
definitions rather than `sorry`s, following `Contracts/Options.lean`'s rule that an unfinished
obligation must exist as a statement before it exists as a proof.

The generic `traceToSentinel_of_enteredFunctionTrace` bridge, plus the two accessor contracts'
`ImplementsFunctionInstance` obligations, are what discharge them —
`accessorReachesSentinel_of_enteredFunctionTrace` below is that join, so what is left is per-accessor
and target-specific. Note precisely what it demands, because it is not merely "a trace exists":

* the trace must start at `accessorSetup entryPc before` — the state *after* the runner's prologue,
  not at the accessor's entry with arbitrary registers, so the contract's entry binding has to be
  established at a state whose `ra`/`sp`/`PC`/`nextPC` are the runner's. That is exactly what
  `contractRawResult_entry_accessorSetup` / `contractRawError_entry_accessorSetup` do;
* its length must be within the accessor's **own contract** step bound (`rawResultStepBound = 32`,
  `rawErrorStepBound = 16`, by `accessor_step_bounds`) plus the single `ret` the bridge appends —
  never within some other budget;
* the exit state's `a0` must read back as the expected code, which
  `observeReturnCode_of_postRawResult` / `observeReturnCode_of_postRawError` supply from the
  contracts' own postconditions;
* the bridge's two avoidance conditions must hold of the accessor's own address set: no address it
  executes at is the sentinel. `Layout.lean`'s `loaded_disjoint_from_runner` is the fact that settles
  it, and supplying it is a per-accessor obligation this module does not attempt.
-/

/-- **One accessor's residual obligation.** The exported accessor at `entryPc`, entered from `before`
by the runner's own prologue, reaches the return sentinel in `after` within its contract's step bound
plus the one `ret` that lands on the sentinel. This is exactly `runAccessor_returned_of_bound`'s two
trace premises, packaged; see its docstring for why the bound is `stepBound + 1`. -/
def AccessorReachesSentinel (entryPc stepBound : Nat) (before after : State) : Prop :=
  ∃ count, count ≤ stepBound + 1 ∧
    TraceToSentinel sentinelWord 0 count (accessorSetup entryPc before) after

/-- **The join with the generic sentinel bridge, in one step.** An `EnteredFunctionTrace` of the
accessor from the runner's own setup state — which is what its `ImplementsFunctionInstance`
obligation produces once `contractRawResult_entry_accessorSetup` /
`contractRawError_entry_accessorSetup` discharge the entry binding — plus the `ret` that lands on the
sentinel, *is* the residual obligation.

This is the seam, and the arithmetic is the whole content of it: the contract bounds the function's
own retirements by `stepBound`, `traceToSentinel_of_enteredFunctionTrace` appends the `ret`, and the
result is admitted because `AccessorReachesSentinel` allows `stepBound + 1`. -/
theorem accessorReachesSentinel_of_enteredFunctionTrace {region exit : BitVec 64 → Prop}
    {entryPc stepBound count : Nat} {before atExit after : State}
    (regionAvoidsSentinel : ∀ pc, region pc → pc ≠ sentinelWord)
    (exitAvoidsSentinel : ∀ pc, exit pc → pc ≠ sentinelWord)
    (run : Elfling.EnteredFunctionTrace region exit (BitVec.ofNat 64 entryPc) 0 count
      (accessorSetup entryPc before) atExit)
    (hbound : count ≤ stepBound)
    (ret : Runs (try_step (0 + count) false) atExit after false)
    (landed : after.regs.get? PC = some sentinelWord) :
    AccessorReachesSentinel entryPc stepBound before after :=
  ⟨count + 1, by omega,
    (Elfling.traceToSentinel_of_enteredFunctionTrace regionAvoidsSentinel exitAvoidsSentinel run ret
      landed).1⟩

/-- The packaged obligation is enough: an `AccessorReachesSentinel` plus the exit code is a complete
`runAccessor` run. -/
theorem runAccessor_returned_of_reaches {entryPc stepBound : Nat} {before after : State}
    {code : Nat} (h : AccessorReachesSentinel entryPc stepBound before after)
    (hcode : observeReturnCode? after = some code) :
    Runs (runAccessor entryPc (accessorFuel stepBound)) before after (.returned code) := by
  obtain ⟨count, hbound, htrace⟩ := h
  exact runAccessor_returned_of_bound entryPc stepBound htrace hbound hcode

/-- **The accepted path's residual obligation, in full.** Both exported accessors reach their
sentinels from the runner's prologue within their own contract bounds, `zesu_raw_result` returning
the canonical result buffer and `zesu_raw_error` returning `ok`. -/
def AcceptedAccessorTraces (final : State) : Prop :=
  ∃ middle after : State,
    AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound final middle ∧
    observeReturnCode? middle = some Elflings.canonicalResultBuffer ∧
    AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound middle after ∧
    observeReturnCode? after = some DecodeStatus.ok.code

/-- **The rejected path's residual obligation, in full.** Same shape, with a null `zesu_raw_result`
and the recorded status. -/
def RejectedAccessorTraces (status : Nat) (final : State) : Prop :=
  ∃ middle after : State,
    AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound final middle ∧
    observeReturnCode? middle = some 0 ∧
    AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound middle after ∧
    observeReturnCode? after = some status

/-- **The accepted path's obligation is exactly `SuccessfulRun.accessors`.** Given the residue, the
field is constructed with no further machine reasoning — which is the whole point of naming it. -/
theorem accessors_accepted_of_traces {final : State} (steps : Nat)
    (h : AcceptedAccessorTraces final) :
    ∃ after : State, Runs (runAccessorsIfReached resolvedSymbols (.reached steps)) final after
      (.returned Elflings.canonicalResultBuffer, .returned DecodeStatus.ok.code) := by
  obtain ⟨middle, after, ⟨rc, rbound, rtrace⟩, rcode, ⟨ec, ebound, etrace⟩, ecode⟩ := h
  exact ⟨after, runAccessorsIfReached_returned_of_traces resolvedSymbols steps rtrace rbound rcode
    etrace ebound ecode⟩

/-- **The rejected path's obligation is exactly `RejectedRun.accessors`.** -/
theorem accessors_rejected_of_traces {final : State} {status : Nat} (steps : Nat)
    (h : RejectedAccessorTraces status final) :
    ∃ after : State, Runs (runAccessorsIfReached resolvedSymbols (.reached steps)) final after
      (.returned 0, .returned status) := by
  obtain ⟨middle, after, ⟨rc, rbound, rtrace⟩, rcode, ⟨ec, ebound, etrace⟩, ecode⟩ := h
  exact ⟨after, runAccessorsIfReached_returned_of_traces resolvedSymbols steps rtrace rbound rcode
    etrace ebound ecode⟩

/-! ## The two witnesses, assembled

The point of the residue being *only* the two accessor trace obligations is checkable rather than
asserted: here are `SuccessfulRun` and `RejectedRun` built from the decode-side facts plus
`AcceptedAccessorTraces`/`RejectedAccessorTraces` and nothing else. `Assembly.lean`'s
`accessorTraces_of_locals` is what discharges that pair, from the two accessors' own contract
obligations. -/

/-- **A successful run, assembled.** Every field but the accessors comes from the decode; the
accessors come from the named residue. -/
theorem successfulRun_of_acceptedAccessorTraces (input : ByteArray) (value : BinaryFv.Specs.SSZ.RawV4)
    {entryState finalState : State} {stepCount : Nat}
    (hbuild : Runs (buildZesuEntryState input) initialState entryState ())
    (htrace : TraceToSentinel sentinelWord 0 stepCount entryState finalState)
    (hbound : stepCount ≤ entryStepBound input.size + 1)
    (hcode : observeReturnCode? finalState = some 1)
    (htag : observeOptionTag? finalState storedResultDiscriminantAddr = some true)
    (hinput : MemoryBytes finalState canonicalRunnerLayout.inputBase input)
    (hvalue : RawV4Rep finalState canonicalRunnerLayout.inputBase input
      Elflings.canonicalResultBuffer value)
    (haccessors : AcceptedAccessorTraces finalState) :
    Nonempty (SuccessfulRun input value) := by
  obtain ⟨after, hruns⟩ := accessors_accepted_of_traces stepCount haccessors
  refine ⟨{ entryState := entryState
            finalState := finalState
            afterAccessors := after
            stepCount := stepCount
            builds := hbuild
            trace := htrace
            withinStepBound := hbound
            returnCode := hcode
            storedPresent := htag
            inputPreserved := hinput
            storedValue := hvalue
            accessors := hruns }⟩

/-- **A rejected run, assembled.** -/
theorem rejectedRun_of_rejectedAccessorTraces (input : ByteArray)
    {entryState finalState : State} {stepCount status : Nat}
    (hbuild : Runs (buildZesuEntryState input) initialState entryState ())
    (htrace : TraceToSentinel sentinelWord 0 stepCount entryState finalState)
    (hbound : stepCount ≤ entryStepBound input.size + 1)
    (hcode : observeReturnCode? finalState = some 0)
    (htag : observeOptionTag? finalState storedResultDiscriminantAddr = some false)
    (hstatus : statusCategory status = .specRejection)
    (haccessors : RejectedAccessorTraces status finalState) :
    Nonempty (RejectedRun input) := by
  obtain ⟨after, hruns⟩ := accessors_rejected_of_traces stepCount haccessors
  refine ⟨{ entryState := entryState
            finalState := finalState
            afterAccessors := after
            stepCount := stepCount
            status := status
            builds := hbuild
            trace := htrace
            withinStepBound := hbound
            returnCode := hcode
            storedAbsent := htag
            specRejection := hstatus
            accessors := hruns }⟩

/-! ## Where each accessor's sentinel trace ends

The bridge attaches at one pc per call, and which pc that is has to be a definite description rather
than a choice among exits — the same requirement `entry_function_instance_exit_is_its_return` settles
for the wrapper. These are its two accessor analogues, and they hold for the same reason: after the
exit rule was corrected so that a resolved call is an exit only in tail position, each exported
accessor's whole exit inventory collapsed to its own `ret`.

Checked for exactly the two instances the runner calls, selected by their **pinned entry addresses**
rather than by function instance name, because it is the address `runAccessor` writes into `PC` that decides
which instance executes. -/

/-- The two accessor instances exist and are distinct, so the theorem below is not a statement about
an empty selection. Stated first because a `List.all` over nothing is `true`. -/
theorem accessor_function_instances_found :
    (BinaryFv.Zesu.Elflings.Generated.generatedProgram.functionInstances.filter
      (fun i => i.entryPc == resolvedSymbols.rawResult || i.entryPc == resolvedSymbols.rawError)).size
      = 2 := by native_decide

/-- **Each exported accessor has exactly one exit, and it is its `ret`.**

So `runAccessor`'s `EnteredFunctionTrace` ends on the return, `returnExit_fetch_and_decode` applies
there, and `accessorReachesSentinel_of_enteredFunctionTrace` has a definite pc to attach at — the
accessor half of what the wrapper already has. Without it the accessor traces could halt at some
other exit where there is no `ret` to retire, which is exactly the defect the exit-rule fix removed
from the entry. -/
theorem accessor_function_instances_exit_is_their_return :
    ∀ nodes, BinaryFv.Zesu.ControlFlow.controlFlow? = some nodes →
      (BinaryFv.Zesu.Elflings.Generated.generatedProgram.functionInstances.filter
        (fun i => i.entryPc == resolvedSymbols.rawResult
          || i.entryPc == resolvedSymbols.rawError)).all
        (fun i => (i.exitPcs.size == 1) &&
          (BinaryFv.Zesu.Elflings.Validation.returnExitPcs nodes i == i.exitPcs)) = true := by
  intro nodes hn
  have h : (BinaryFv.Zesu.ControlFlow.controlFlow?.map fun ns =>
      (BinaryFv.Zesu.Elflings.Generated.generatedProgram.functionInstances.filter
        (fun i => i.entryPc == resolvedSymbols.rawResult
          || i.entryPc == resolvedSymbols.rawError)).all
        (fun i => (i.exitPcs.size == 1) &&
          (BinaryFv.Zesu.Elflings.Validation.returnExitPcs ns i == i.exitPcs))).getD false
      = true := by native_decide
  rw [hn] at h
  simpa using h

/-! ## Anti-vacuity

Two questions, both of which have bitten this project: are the trace premises above satisfiable at
all, and can they be satisfied *degenerately*, making the composed theorem worthless?

The answers are yes and no respectively, and both are proved rather than asserted. -/

/-- The state the satisfiability witness starts from: nothing but a readable `a0`. -/
def witnessAccessorState : State :=
  { initialState with regs := initialState.regs.insert x10 (BitVec.ofNat 64 7) }

/-- **The trace premises are satisfiable, and the conclusion is inhabited.** A genuine
`Runs (runAccessor …)` ending in `.returned`, produced by the theorem above rather than by hand.

The witness enters the accessor *at the sentinel itself*, so the trace is `TraceToSentinel.done` and
no machine step is needed. That is the honest form of this check: it shows the hypothesis set is
consistent and the theorem's plumbing is exercised. It does **not** show the pinned accessors reach
their sentinels — that is the bridge's obligation, and the next theorem shows why no witness of this
shape could ever stand in for it. -/
theorem runAccessor_returned_of_trace_satisfiable :
    ∃ (entryPc fuel : Nat) (before exit : State) (count code : Nat),
      TraceToSentinel sentinelWord 0 count (accessorSetup entryPc before) exit ∧
      count < fuel ∧ observeReturnCode? exit = some code ∧
      Runs (runAccessor entryPc fuel) before exit (.returned code) := by
  have hpc : (accessorSetup canonicalRunnerLayout.sentinel witnessAccessorState).regs.get? PC =
      some sentinelWord := accessorSetup_pc _ _
  have htrace : TraceToSentinel sentinelWord 0 0
      (accessorSetup canonicalRunnerLayout.sentinel witnessAccessorState)
      (accessorSetup canonicalRunnerLayout.sentinel witnessAccessorState) :=
    TraceToSentinel.done 0 _ hpc
  have hcode : observeReturnCode? (accessorSetup canonicalRunnerLayout.sentinel
      witnessAccessorState) = some 7 := by
    rw [accessorSetup_observeReturnCode]
    exact observeReturnCode_of_a0 (by decide) (by simp [witnessAccessorState])
  exact ⟨canonicalRunnerLayout.sentinel, 1, witnessAccessorState,
    accessorSetup canonicalRunnerLayout.sentinel witnessAccessorState, 0, 7, htrace,
    Nat.zero_lt_one, hcode,
    runAccessor_returned_of_trace _ 1 htrace Nat.zero_lt_one hcode⟩

/-- Symbols whose two "accessors" *are* the return sentinel. Only the satisfiability witness below
uses them; they are not the pinned symbols and no theorem about the real decoder mentions them. -/
def sentinelSymbols : RunnerSymbols where
  decodeEntry := canonicalRunnerLayout.sentinel
  rawResult := canonicalRunnerLayout.sentinel
  rawError := canonicalRunnerLayout.sentinel

/-- **The sequencing theorem's premises are jointly satisfiable too, and its conclusion inhabited.**
Both accessor calls, run one after the other from a common state, producing exactly the pair shape
`SuccessfulRun.accessors`/`RejectedRun.accessors` carry.

The codes coincide, necessarily — the next theorem proves that no zero-length witness can do
otherwise. -/
theorem runAccessorsIfReached_returned_of_traces_satisfiable (steps : Nat) :
    ∃ final after : State,
      Runs (runAccessorsIfReached sentinelSymbols (.reached steps)) final after
        (.returned 7, .returned 7) := by
  have hmiddle : observeReturnCode? (accessorSetup sentinelSymbols.rawResult
      witnessAccessorState) = some 7 := by
    rw [accessorSetup_observeReturnCode]
    exact observeReturnCode_of_a0 (by decide) (by simp [witnessAccessorState])
  have hafter : observeReturnCode? (accessorSetup sentinelSymbols.rawError
      (accessorSetup sentinelSymbols.rawResult witnessAccessorState)) = some 7 := by
    rw [accessorSetup_observeReturnCode]; exact hmiddle
  exact ⟨witnessAccessorState, _,
    runAccessorsIfReached_returned_of_traces sentinelSymbols steps
      (TraceToSentinel.done 0 _ (accessorSetup_pc _ _)) (Nat.zero_le _) hmiddle
      (TraceToSentinel.done 0 _ (accessorSetup_pc _ _)) (Nat.zero_le _) hafter⟩

/-- **The degenerate witness cannot stand in for the real one.** If both accessor traces have length
zero, the two calls necessarily report the *same* return code — because the prologue does not write
`a0` and no step retires, so neither call can change it.

The accepted path demands `zesu_raw_result` return `canonicalResultBuffer` and `zesu_raw_error`
return `DecodeStatus.ok.code`, which are different numbers
(`accepted_accessor_codes_differ`). So `AcceptedAccessorTraces` cannot be discharged by zero-length
traces: it genuinely requires retired machine steps, which is precisely the bridge's job. This is the
measurement that stops the residue above from being a `Prop` that something trivial could satisfy. -/
theorem zero_length_accessor_traces_force_equal_codes {symbols : RunnerSymbols}
    {final middle after : State} {resultCode errorCode : Nat}
    (hresultTrace : TraceToSentinel sentinelWord 0 0 (accessorSetup symbols.rawResult final) middle)
    (herrorTrace : TraceToSentinel sentinelWord 0 0 (accessorSetup symbols.rawError middle) after)
    (hresultCode : observeReturnCode? middle = some resultCode)
    (herrorCode : observeReturnCode? after = some errorCode) :
    resultCode = errorCode := by
  cases hresultTrace with
  | done _ _ _ =>
    cases herrorTrace with
    | done _ _ _ =>
      rw [accessorSetup_observeReturnCode] at herrorCode
      rw [herrorCode] at hresultCode
      exact (Option.some.inj hresultCode).symm

/-- The two codes the accepted path demands really are different, so the previous theorem bites. -/
theorem accepted_accessor_codes_differ :
    Elflings.canonicalResultBuffer ≠ DecodeStatus.ok.code := by native_decide

/-- **`AcceptedAccessorTraces` is not degenerately satisfiable.** At least one of the two accessor
runs it demands must retire a machine step. Stated over an arbitrary `final` because the conclusion is
about the obligation's shape, not about any particular state. -/
theorem acceptedAccessorTraces_needs_a_step {final : State} (h : AcceptedAccessorTraces final) :
    ∃ middle after : State,
      AccessorReachesSentinel resolvedSymbols.rawResult rawResultStepBound final middle ∧
      AccessorReachesSentinel resolvedSymbols.rawError rawErrorStepBound middle after ∧
      ¬ (TraceToSentinel sentinelWord 0 0 (accessorSetup resolvedSymbols.rawResult final) middle ∧
         TraceToSentinel sentinelWord 0 0 (accessorSetup resolvedSymbols.rawError middle) after) := by
  obtain ⟨middle, after, hresult, rcode, herror, ecode⟩ := h
  refine ⟨middle, after, hresult, herror, ?_⟩
  rintro ⟨rzero, ezero⟩
  exact accepted_accessor_codes_differ
    (zero_length_accessor_traces_force_equal_codes rzero ezero rcode ecode)

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
