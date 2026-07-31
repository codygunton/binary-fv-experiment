import BinaryFv.SSZ.Zesu.Contracts.Runtime

namespace BinaryFv.SSZ.Zesu.Contracts

open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register

/-!
# Exported-decoder vertical tests

Row A's binding-level checks on the exported wrapper and its accessors, stated as theorems so a
regression cannot silently revert them. These are definitional facts about the bindings — they do
not depend on Sail execution, the runner, or the concrete contract parameters.

The "old wrapper binding" the plan contrasts against is gone: it required the internal convention
`x10 = resultBase`, so a caller that set only the real C ABI registers `a0 = input`, `a1 = len`
would not have satisfied it. The two `wrapper_entry_requires_*` theorems pin that the new binding is
stated against exactly those real registers, which is the correction.
-/

/-- **The wrapper entry binds the input pointer in `a0`.** A state whose `a0` is not the input base
does not satisfy the entry binding — so a mutated argument register fails. -/
theorem wrapper_entry_requires_input_in_a0 (env : DecoderEnvironment)
    (globals : DecoderGlobalsLayout) (resultBuffer : Nat)
    (rep : ContainerRepresentation SszBridge.RawV4) (incoming : DecoderGlobalsModel)
    (args : ZesuDecodeRawArgs)
    (state : State) (hbad : state.regs.get? x10 ≠ some (BitVec.ofNat 64 args.inputBase)) :
    ¬ preZesuDecodeRaw env globals resultBuffer rep incoming args state := by
  intro h
  exact hbad h.2.2.1

/-- **The wrapper entry binds the length in `a1`.** A state whose `a1` is not the input length does
not satisfy the entry binding. -/
theorem wrapper_entry_requires_length_in_a1 (env : DecoderEnvironment)
    (globals : DecoderGlobalsLayout) (resultBuffer : Nat)
    (rep : ContainerRepresentation SszBridge.RawV4) (incoming : DecoderGlobalsModel)
    (args : ZesuDecodeRawArgs)
    (state : State) (hbad : state.regs.get? x11 ≠ some (BitVec.ofNat 64 args.bytes.size)) :
    ¬ preZesuDecodeRaw env globals resultBuffer rep incoming args state := by
  intro h
  exact hbad h.2.2.2.1

/-- **Relocation leaves the `RoutineSpec` untouched.** The exported wrapper's shared specification is
independent of the global locations and result-buffer address, so relinking the binary (which moves
those addresses) changes bindings but never what the routine means. -/
theorem wrapper_spec_is_relocation_invariant (env : DecoderEnvironment)
    (g₁ g₂ : DecoderGlobalsLayout) (rb₁ rb₂ : Nat)
    (rep : ContainerRepresentation SszBridge.RawV4) (incoming : DecoderGlobalsModel) :
    (functionInstanceZesuDecodeRaw env g₁ rb₁ rep incoming).spec
      = (functionInstanceZesuDecodeRaw env g₂ rb₂ rep incoming).spec :=
  rfl

/-- The accessor `zesu_raw_error` means exactly the status the ghost globals model records. -/
theorem raw_error_reads_model_status (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (model : DecoderGlobalsModel) :
    (contractRawError env globals).meaning model = .ok model.status.code :=
  rfl

/-- The accessor `zesu_raw_result` means the canonical buffer pointer exactly when the ghost globals
model has a stored value, and null otherwise. -/
theorem raw_result_reads_model_pointer (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (model : DecoderGlobalsModel) :
    (contractRawResult env globals resultBuffer).meaning model
      = .ok (if model.stored.isSome then resultBuffer else 0) :=
  rfl

/-- **A fresh successful call feeds the accessors a non-null result of the exact status.** After the
wrapper stores a decoded value, `zesu_raw_result` yields the canonical buffer and `zesu_raw_error`
yields `ok`. -/
theorem accessors_after_fresh_success (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (value : SszBridge.RawV4) :
    (contractRawResult env globals resultBuffer).meaning
        (resultingGlobals DecoderGlobalsModel.fresh (.ok value)) = .ok resultBuffer ∧
    (contractRawError env globals).meaning
        (resultingGlobals DecoderGlobalsModel.fresh (.ok value)) = .ok DecodeStatus.ok.code := by
  constructor <;>
    simp [contractRawResult, contractRawError, resultingGlobals, callOutcome,
      DecodeCallOutcome.status, DecodeCallOutcome.stored, DecoderGlobalsModel.fresh]

/-- **A fresh rejected call feeds the accessors a null result.** After the wrapper rejects,
`zesu_raw_result` yields null. -/
theorem accessors_after_fresh_rejection (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (error : SszDecodeError) :
    (contractRawResult env globals resultBuffer).meaning
        (resultingGlobals DecoderGlobalsModel.fresh (.error error)) = .ok 0 := by
  simp [contractRawResult, resultingGlobals, callOutcome, DecodeCallOutcome.stored,
    DecoderGlobalsModel.fresh]

/-! ## The stored result against the actual 848-byte object layout -/

/-- **A fresh success populates the inline object.** When the wrapper's outgoing stored-result
representation holds after a fresh successful decode, the `stored_result` discriminant byte is present
(at the reflected offset within the object) and the payload buffer holds the value under the container
representation — the value lives in the 848-byte object, not behind a pointer. -/
theorem stored_object_holds_value_after_fresh_success (globals : DecoderGlobalsLayout)
    (rep : ContainerRepresentation SszBridge.RawV4) (inputBase : Nat) (input : ByteArray)
    (resultBase : Nat) (incoming : DecoderGlobalsModel) (value : SszBridge.RawV4) (state : State)
    (hfresh : incoming.attempted = false)
    (h : StoredResultRep globals rep inputBase input resultBase
          (resultingGlobals incoming (.ok value)) state) :
    OptionTagRep state (globals.storedResult + globals.storedResultObject.discriminantOffset) true ∧
      rep inputBase input value state resultBase := by
  have hstored : (resultingGlobals incoming (.ok value)).stored = some value :=
    (fresh_success_stores_value incoming value hfresh).2.2.2
  obtain ⟨hdisc, hval⟩ := h
  rw [hstored] at hval
  refine ⟨?_, hval⟩
  unfold StoredResultDiscriminantRep at hdisc
  rw [hstored] at hdisc
  simpa using hdisc

/-- **A fresh rejection clears the discriminant.** After a fresh rejected decode, the outgoing
stored-result discriminant byte is absent. -/
theorem stored_object_absent_after_fresh_rejection (globals : DecoderGlobalsLayout)
    (rep : ContainerRepresentation SszBridge.RawV4) (inputBase : Nat) (input : ByteArray)
    (resultBase : Nat) (incoming : DecoderGlobalsModel) (error : SszDecodeError) (state : State)
    (hfresh : incoming.attempted = false)
    (h : StoredResultRep globals rep inputBase input resultBase
          (resultingGlobals incoming (.error error)) state) :
    OptionTagRep state (globals.storedResult + globals.storedResultObject.discriminantOffset) false := by
  have hnone : (resultingGlobals incoming (.error error)).stored = none :=
    (fresh_rejection_stores_nothing incoming error hfresh).2.2
  obtain ⟨hdisc, _⟩ := h
  unfold StoredResultDiscriminantRep at hdisc
  rw [hnone] at hdisc
  simpa using hdisc

/-- **A second call leaves the object untouched.** Once `attempted` is set the globals are unchanged,
so the outgoing stored-result representation is exactly the incoming one. -/
theorem stored_object_unchanged_after_second_call (globals : DecoderGlobalsLayout)
    (rep : ContainerRepresentation SszBridge.RawV4) (inputBase : Nat) (input : ByteArray)
    (resultBase : Nat) (incoming : DecoderGlobalsModel)
    (result : Except SszDecodeError SszBridge.RawV4) (state : State) (h : incoming.attempted = true)
    (hrep : StoredResultRep globals rep inputBase input resultBase
              (resultingGlobals incoming result) state) :
    StoredResultRep globals rep inputBase input resultBase incoming state := by
  rwa [(second_call_is_alreadyDecoded incoming result h).2.2.2] at hrep

/-! ## The callee-frame clauses, exhibited

`postZesuDecodeRaw`, `postRawResult` and `postRawError` each carry `Agree platformPreserved before
after` and `RetiredCounterPresent after`. Elaboration alone does not show those clauses are
satisfiable. This row has already had one proposed clause turn out to be false of every allocating
routine; a false exported-contract premise makes the root vacuous rather than merely under-specified.

So each strengthened predicate gets a run here that satisfies it, and then **four** clobbering runs
that the predicate refuses. One run breaking everything at once would prove less than it appears to:
every refutation would be discharged from every other clause, so none would be tested. Each clobber
below therefore disturbs exactly one register and leaves the rest of the frame intact.

The four are one per distinguishable capability of the clause:

| clobber | register | what it tests |
| --- | --- | --- |
| `raClobberRegs` | `x1` | the callee returned to the wrong address |
| `platformClobberRegs` | `mie` | it came back with interrupts enabled — a `NormalExecutionState` register |
| `fetchClobberRegs` | `pma_regions` | one of the **five** `NormalExecutionState` never mentioned, at its *value*, which is the form `FetchPmaAllows` consumes |
| `mmioClobberRegs` | `htif_tohost_base` | the MMIO dispatch's only register — the one whose coverage was not obvious from `FetchMemoryNoMMIO`'s shape |

The last two are the ones that make this change have content. The clause it replaced was
`after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after`, written down here as
`postRawErrorTwoClause` and `postZesuDecodeRawTwoClause` so that "the previous form permitted this
run" is a checkable statement rather than a claim about what the source used to say. Both clobbers
satisfy that previous form — so it **permitted** a callee that rewrote the PMA table or turned on the
HTIF window under its caller, and the exit `ret` would then have been unprovable at a state the
contract certified. `accessor_fetch_and_mmio_clobbers_permitted_by_the_old_pair` and its wrapper
counterpart say exactly that.

The three `post*_eq_historical_and_clauses` equivalences close the loop by proving that each
`…Historical` predicate is the live one *minus exactly these two conjuncts*, so a refutation
identifies which clause did the refusing rather than leaving it to be read off the source.

The runs are shaped like the routines they stand for rather than doing nothing. Each writes its stack
frame — a routine that touched no memory would satisfy the memory clauses for a reason having nothing
to do with these clauses — and **advances `minstret`**, which every retired instruction does. That
last detail is load-bearing in the other direction: it is what makes a future edit that folds the
retired counter into `platformPreserved` fail here instead of silently making all three
postconditions false. The wrapper's run additionally writes the two decoder globals a rejected decode
really writes. Deliberately the *rejection* path: it is a real path of the real wrapper, and its
stored-result arm is `True`, so the witness holds for **every** container representation rather than
for a convenient one. The success arm would additionally have to realise a `RawV4` in memory, which
is orthogonal to the clauses under test.
-/

namespace CalleeFrameExhibit

open BinaryFv.Binary

/-- The environment the exhibits are stated at.

Shaped like the real one where the shape matters: a single load segment with no file-backed bytes and
a 2000-byte zero-fill tail, which is the pinned image's own arrangement (code and rodata from the
file, the decoder's mutable globals in the BSS tail). The tail is what makes
`calleeFrame_is_not_the_vocabulary` a statement about this decoder rather than about an arbitrary
image. -/
def calleeFrameEnv : DecoderEnvironment where
  image := ⟨#[⟨0, ByteArray.empty, 2000, 0⟩]⟩
  allocatorState := range 900 8
  heapPosAddr := 900
  arenaBase := 0
  optionalBlobSchedule := default
  blobSchedule := ⟨0, 0, 0⟩
  optionalU64 := default
  record := default
  stack := range 1000 64

theorem calleeFrameEnv_readFileByte (address : Nat) :
    calleeFrameEnv.image.readFileByte? address = none := by
  cases h : calleeFrameEnv.image.readFileByte? address with
  | none => rfl
  | some byte =>
    obtain ⟨seg, hmem, _, hlt⟩ := ProgramImage.readFileByte?_mem_segment h
    have hseg : seg = ⟨0, ByteArray.empty, 2000, 0⟩ := by simpa [calleeFrameEnv] using hmem
    subst hseg
    exact absurd hlt (by simp [LoadSegment.initialEndAddress, LoadSegment.fileSize])

theorem calleeFrameEnv_codeIntact (state : State) : calleeFrameEnv.CodeIntact state := by
  intro address byte h
  rw [calleeFrameEnv_readFileByte address] at h
  exact absurd h (by simp)

/-- Every address of the zero-fill tail reads zero from the *image*, which is the fact the full-image
frame would pin and the decoder's globals contradict. -/
theorem calleeFrameEnv_readByte {address : Nat} (h : address < 2000) :
    calleeFrameEnv.image.readByte? address = some 0 := by
  show (ProgramImage.mk #[⟨0, ByteArray.empty, 2000, 0⟩]).readByte? address = some 0
  simp [ProgramImage.readByte?, ProgramImage.segmentAt?, LoadSegment.readByte?,
    LoadSegment.containsMemoryByte, LoadSegment.endAddress, h]

/-- The three private globals, all inside the zero-fill tail as they are in the real binary. The
option layout is the pinned one: an 848-byte object with the discriminant at 832. -/
def calleeFrameGlobals : DecoderGlobalsLayout where
  attempted := 10
  status := 20
  storedResult := 30
  storedResultObject := { size := 848, discriminantOffset := 832, payloadOffset := 0 }

/-- The caller's return address, sitting in `x1` on entry. Any value does: the clause is
preservation, and naming a *particular* value here would be the mistake the contract avoids. -/
def calleeLink : BitVec 64 := BitVec.ofNat 64 4660

/-! ### The register files

Three layers, because each is doing a different job. `normalRegs` is the twelve
`NormalExecutionState` demands plus `x1`. `machineRegs` adds the six a retiring `ret` reads that
`NormalExecutionState` never mentions — the five plus the HTIF base. `returnedRegs` is what a
well-behaved callee hands back: `machineRegs` with a return value in `a0` and the retired counter
advanced. -/

/-- The twelve platform registers at the values `NormalExecutionState` demands, plus `x1`. -/
def normalRegs (ra : BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  (default : State).regs
    |>.insert hart_state (HartState.HART_ACTIVE ())
    |>.insert cur_privilege Privilege.Machine
    |>.insert satp (0 : BitVec 64)
    |>.insert mideleg (0 : BitVec 64)
    |>.insert mie (0 : BitVec 64)
    |>.insert mip (0 : BitVec 64)
    |>.insert pmpcfg_n (default : Vector (BitVec 8) 64)
    |>.insert pmpaddr_n (default : Vector (BitVec 64) 64)
    |>.insert mcountinhibit (0 : BitVec 32)
    |>.insert minstretcfg (0 : BitVec 64)
    |>.insert elp (landing_pad_bits_backwards landing_pad_expectation.NO_LP_EXPECTED)
    |>.insert misa (BitVec.ofNat 64 4096)
    |>.insert x1 ra

theorem normalRegs_misa (ra : BitVec 64) :
    (normalRegs ra).get? misa = some (BitVec.ofNat 64 4096) := by
  unfold normalRegs
  simp [Std.ExtDHashMap.get?_insert]

theorem normalRegs_x1 (ra : BitVec 64) : (normalRegs ra).get? x1 = some ra := by
  unfold normalRegs
  simp

set_option maxHeartbeats 1000000 in
/-- **A state satisfying `NormalExecutionState` exists**, built rather than assumed. Twelve register
writes, one per conjunct; the `misa` conjunct is separate because it is a `match` on the read rather
than an equation. -/
theorem normalRegs_normal (ra : BitVec 64) :
    NormalExecutionState { (default : State) with regs := normalRegs ra } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?misa⟩
  case misa =>
    show match (normalRegs ra).get? misa with
      | some misaBits => Sail.BitVec.access misaBits 12 = 1#1
      | none => False
    rw [normalRegs_misa]
    decide
  all_goals
    · show (normalRegs ra).get? _ = _
      unfold normalRegs
      simp [Std.ExtDHashMap.get?_insert]

/-- The retired-instruction counter as the caller left it. -/
def retiredBefore : BitVec 64 := BitVec.ofNat 64 7

/-- …and after the callee ran. Different, deliberately: see `returnedRegs`. -/
def retiredAfter : BitVec 64 := BitVec.ofNat 64 10

/-- `normalRegs` plus the six registers a retiring `ret` reads that `NormalExecutionState` never
mentions: `minstret`, `mstatus`, `sig_meip`, `pma_regions`, `mseccfg`, and the HTIF base its MMIO
dispatch consults. The values are arbitrary-but-fixed — the clause under test is agreement, so a
witness that pinned *meaningful* values would be exercising something else. -/
def machineRegs (ra : BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  (normalRegs ra)
    |>.insert minstret retiredBefore
    |>.insert mstatus (0 : BitVec 64)
    |>.insert sig_meip (0 : BitVec 1)
    |>.insert pma_regions ([] : List PMA_Region)
    |>.insert mseccfg (0 : BitVec 64)
    |>.insert htif_tohost_base (none : Option physaddrbits)

/-- **The register file a well-behaved callee hands back**: the caller's whole platform frame, the
return value in `a0`, and `minstret` *advanced*.

The advance is not decoration. The machine writes `minstret` on every retirement, so a witness that
left it alone would be a witness for a routine that executed nothing — and, worse, it would satisfy a
`platformPreserved` that wrongly included the counter, hiding the fact that such a clause is false of
every real routine. With the advance in place, adding `minstret` to `platformPreserved` breaks
`raw_error_run_satisfies_the_clauses` rather than passing quietly. -/
def returnedRegs (code : Nat) : Std.ExtDHashMap Register RegisterType :=
  ((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret retiredAfter

theorem machineRegs_x1 (ra : BitVec 64) : (machineRegs ra).get? x1 = some ra := by
  unfold machineRegs
  simp [Std.ExtDHashMap.get?_insert, normalRegs_x1]

theorem machineRegs_pmaRegions (ra : BitVec 64) :
    (machineRegs ra).get? pma_regions = some ([] : List PMA_Region) := by
  unfold machineRegs
  simp [Std.ExtDHashMap.get?_insert]

theorem machineRegs_htifBase (ra : BitVec 64) :
    (machineRegs ra).get? htif_tohost_base = some (none : Option physaddrbits) := by
  unfold machineRegs
  simp

theorem machineRegs_minstret (ra : BitVec 64) :
    (machineRegs ra).get? minstret = some retiredBefore := by
  unfold machineRegs
  simp [Std.ExtDHashMap.get?_insert]

/-- The six extra writes touch none of `NormalExecutionState`'s twelve, so the bigger register file is
still a normal machine. -/
theorem machineRegs_normal (ra : BitVec 64) :
    NormalExecutionState { (default : State) with regs := machineRegs ra } := by
  refine normalExecutionState_of_agree (before := { (default : State) with regs := normalRegs ra })
    ?_ (normalRegs_normal ra)
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show (machineRegs ra).get? _ = (normalRegs ra).get? _
      unfold machineRegs
      simp [Std.ExtDHashMap.get?_insert]

/-- **The callee returned the whole frame.** Eighteen registers, checked one at a time. -/
theorem returnedRegs_agree (code : Nat) :
    ∀ r : Register, platformPreserved r →
      (returnedRegs code).get? r = (machineRegs calleeLink).get? r := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl) <;>
    · show (((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
        retiredAfter).get? _ = (machineRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

theorem returnedRegs_x10 (code : Nat) :
    (returnedRegs code).get? x10 = some (BitVec.ofNat 64 code) := by
  unfold returnedRegs
  simp [Std.ExtDHashMap.get?_insert]

theorem returnedRegs_minstret (code : Nat) :
    (returnedRegs code).get? minstret = some retiredAfter := by
  unfold returnedRegs
  simp

/-- **The retired counter moved**, which is why the contract asks for its presence rather than its
preservation. -/
theorem returnedRegs_minstret_moved (code : Nat) :
    (returnedRegs code).get? minstret ≠ (machineRegs calleeLink).get? minstret := by
  rw [returnedRegs_minstret, machineRegs_minstret]
  show ¬ (some retiredAfter = some retiredBefore)
  simp [retiredAfter, retiredBefore]

/-! ### The four clobbered register files

Each disturbs exactly one register of the frame and leaves the other seventeen alone. That is what
makes each refutation below a statement about the register it names. -/

/-- A callee that returns to the wrong address. -/
def raClobberRegs (code : Nat) : Std.ExtDHashMap Register RegisterType :=
  (returnedRegs code).insert x1 (BitVec.ofNat 64 5)

/-- A callee that comes back with interrupts enabled — a `NormalExecutionState` register. -/
def platformClobberRegs (code : Nat) : Std.ExtDHashMap Register RegisterType :=
  (returnedRegs code).insert mie (1 : BitVec 64)

/-- A callee that rewrites the PMA table. `NormalExecutionState` says nothing about `pma_regions`,
and `FetchPmaAllows` reads it at its *value*. -/
def fetchClobberRegs (code : Nat) : Std.ExtDHashMap Register RegisterType :=
  (returnedRegs code).insert pma_regions [(default : PMA_Region)]

/-- A callee that turns on the HTIF window under its caller — the one register the MMIO dispatch
reads. -/
def mmioClobberRegs (code : Nat) : Std.ExtDHashMap Register RegisterType :=
  (returnedRegs code).insert htif_tohost_base (some (0 : physaddrbits))

theorem raClobberRegs_x10 (code : Nat) :
    (raClobberRegs code).get? x10 = some (BitVec.ofNat 64 code) := by
  unfold raClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_x10]

theorem platformClobberRegs_x10 (code : Nat) :
    (platformClobberRegs code).get? x10 = some (BitVec.ofNat 64 code) := by
  unfold platformClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_x10]

theorem fetchClobberRegs_x10 (code : Nat) :
    (fetchClobberRegs code).get? x10 = some (BitVec.ofNat 64 code) := by
  unfold fetchClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_x10]

theorem mmioClobberRegs_x10 (code : Nat) :
    (mmioClobberRegs code).get? x10 = some (BitVec.ofNat 64 code) := by
  unfold mmioClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_x10]

theorem raClobberRegs_minstret (code : Nat) :
    (raClobberRegs code).get? minstret = some retiredAfter := by
  unfold raClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_minstret]

theorem platformClobberRegs_minstret (code : Nat) :
    (platformClobberRegs code).get? minstret = some retiredAfter := by
  unfold platformClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_minstret]

theorem fetchClobberRegs_minstret (code : Nat) :
    (fetchClobberRegs code).get? minstret = some retiredAfter := by
  unfold fetchClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_minstret]

theorem mmioClobberRegs_minstret (code : Nat) :
    (mmioClobberRegs code).get? minstret = some retiredAfter := by
  unfold mmioClobberRegs
  simp [Std.ExtDHashMap.get?_insert, returnedRegs_minstret]

/-- **The `ra` clobber leaves the machine perfectly normal**, so the old platform clause could not
have been what refused it. -/
theorem raClobberRegs_normalAgree (code : Nat) :
    ∀ r : Register, normalRegisters r →
      (raClobberRegs code).get? r = (machineRegs calleeLink).get? r := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show ((((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
        retiredAfter).insert x1 (BitVec.ofNat 64 5)).get? _ = (machineRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

/-- The PMA clobber is normal too: `pma_regions` is one of the five `NormalExecutionState` omits. -/
theorem fetchClobberRegs_normalAgree (code : Nat) :
    ∀ r : Register, normalRegisters r →
      (fetchClobberRegs code).get? r = (machineRegs calleeLink).get? r := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show ((((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
        retiredAfter).insert pma_regions [(default : PMA_Region)]).get? _
        = (machineRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

/-- And so is the HTIF clobber. -/
theorem mmioClobberRegs_normalAgree (code : Nat) :
    ∀ r : Register, normalRegisters r →
      (mmioClobberRegs code).get? r = (machineRegs calleeLink).get? r := by
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show ((((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
        retiredAfter).insert htif_tohost_base (some (0 : physaddrbits))).get? _
        = (machineRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

/-- The PMA and HTIF clobbers both return to the right address, so the old `x1` clause could not have
been what refused them either. -/
theorem fetchClobberRegs_x1 (code : Nat) :
    (fetchClobberRegs code).get? x1 = (machineRegs calleeLink).get? x1 := by
  show ((((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
    retiredAfter).insert pma_regions [(default : PMA_Region)]).get? x1
    = (machineRegs calleeLink).get? x1
  simp [Std.ExtDHashMap.get?_insert]

theorem mmioClobberRegs_x1 (code : Nat) :
    (mmioClobberRegs code).get? x1 = (machineRegs calleeLink).get? x1 := by
  show ((((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
    retiredAfter).insert htif_tohost_base (some (0 : physaddrbits))).get? x1
    = (machineRegs calleeLink).get? x1
  simp [Std.ExtDHashMap.get?_insert]

theorem platformClobberRegs_x1 (code : Nat) :
    (platformClobberRegs code).get? x1 = (machineRegs calleeLink).get? x1 := by
  show ((((machineRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert minstret
    retiredAfter).insert mie (1 : BitVec 64)).get? x1 = (machineRegs calleeLink).get? x1
  simp [Std.ExtDHashMap.get?_insert]

theorem platformClobberRegs_mie (code : Nat) :
    (platformClobberRegs code).get? mie = some (1 : BitVec 64) := by
  unfold platformClobberRegs
  simp

theorem raClobberRegs_x1 (code : Nat) :
    (raClobberRegs code).get? x1 = some (BitVec.ofNat 64 5) := by
  unfold raClobberRegs
  simp

theorem fetchClobberRegs_pmaRegions (code : Nat) :
    (fetchClobberRegs code).get? pma_regions = some [(default : PMA_Region)] := by
  unfold fetchClobberRegs
  simp

theorem mmioClobberRegs_htifBase (code : Nat) :
    (mmioClobberRegs code).get? htif_tohost_base = some (some (0 : physaddrbits)) := by
  unfold mmioClobberRegs
  simp

/-! ### The accessors

`zesu_raw_result` and `zesu_raw_error` are leaves: no prologue, no store. The run below is the
strongest thing that is still shaped like a compiled routine — it touches exactly one byte, in its
own stack frame, returns a value in `a0`, and retires instructions. -/

def accessorBefore : State :=
  { (default : State) with
    regs := machineRegs calleeLink
    mem := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0) }

/-- The accessor returned: `a0` holds the code, `minstret` has advanced, one byte of its stack frame
changed, and every register of the frame is untouched. -/
def accessorAfter (code : Nat) : State :=
  { (default : State) with
    regs := returnedRegs code
    mem := ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0)).insert 1016
      (BitVec.ofNat 8 9) }

def accessorRaClobber (code : Nat) : State :=
  { accessorAfter code with regs := raClobberRegs code }

def accessorPlatformClobber (code : Nat) : State :=
  { accessorAfter code with regs := platformClobberRegs code }

def accessorFetchClobber (code : Nat) : State :=
  { accessorAfter code with regs := fetchClobberRegs code }

def accessorMmioClobber (code : Nat) : State :=
  { accessorAfter code with regs := mmioClobberRegs code }

theorem accessorBefore_frame : accessorBefore.mem.get? 1016 = some (BitVec.ofNat 8 0) := by
  simp [accessorBefore]

theorem accessorAfter_frame (code : Nat) :
    (accessorAfter code).mem.get? 1016 = some (BitVec.ofNat 8 9) := by
  simp [accessorAfter]

theorem accessorAfter_mem_of_ne {code address : Nat} (h : address ≠ 1016) :
    (accessorAfter code).mem.get? address = accessorBefore.mem.get? address := by
  show (((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0)).insert 1016
      (BitVec.ofNat 8 9)).get? address
    = ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0)).get? address
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  rw [if_neg (fun heq => h heq.symm)]

theorem accessorRaClobber_mem (code address : Nat) :
    (accessorRaClobber code).mem.get? address = (accessorAfter code).mem.get? address := rfl

theorem accessorPlatformClobber_mem (code address : Nat) :
    (accessorPlatformClobber code).mem.get? address = (accessorAfter code).mem.get? address := rfl

theorem accessorFetchClobber_mem (code address : Nat) :
    (accessorFetchClobber code).mem.get? address = (accessorAfter code).mem.get? address := rfl

theorem accessorMmioClobber_mem (code address : Nat) :
    (accessorMmioClobber code).mem.get? address = (accessorAfter code).mem.get? address := rfl

theorem accessorBefore_normal : NormalExecutionState accessorBefore := machineRegs_normal calleeLink

theorem accessorAfter_agree (code : Nat) :
    Agree platformPreserved accessorBefore (accessorAfter code) := returnedRegs_agree code

theorem accessorAfter_retired (code : Nat) : RetiredCounterPresent (accessorAfter code) :=
  ⟨retiredAfter, returnedRegs_minstret code⟩

theorem accessorAfter_x10 (code : Nat) :
    (accessorAfter code).regs.get? x10 = some (BitVec.ofNat 64 code) := returnedRegs_x10 code

/-- Away from its stack frame the accessor changed nothing — the content of both memory clauses at
this environment. -/
theorem accessor_writes_only_its_frame (code : Nat) :
    calleeFrameEnv.NoAllocation accessorBefore (accessorAfter code) ∧
      calleeFrameEnv.WritesOnlyWithinOwnRecord 0 0 accessorBefore (accessorAfter code) := by
  refine ⟨?_, ?_⟩
  · intro address haddr
    obtain ⟨hlo, hhi⟩ : (900 : Nat) ≤ address ∧ address < 900 + 8 := haddr
    exact accessorAfter_mem_of_ne (by omega)
  · intro address houtside
    refine accessorAfter_mem_of_ne ?_
    rintro rfl
    exact houtside (Or.inr (show (1000 : Nat) ≤ 1016 ∧ (1016 : Nat) < 1000 + 64 by omega))

/-- **`zesu_raw_error`'s strengthened postcondition is satisfiable by a run shaped like the compiled
routine.** It wrote its stack frame, returned the status in `a0`, retired instructions, and came back
with the caller's whole register frame intact. -/
theorem raw_error_run_satisfies_the_clauses (model : DecoderGlobalsModel) :
    postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorAfter model.status.code) ∧
      -- it really wrote its frame: not a routine that does nothing
      accessorBefore.mem.get? 1016 ≠ (accessorAfter model.status.code).mem.get? 1016 ∧
      calleeFrameEnv.stack 1016 ∧
      -- it really retired instructions, so the counter is *not* preserved
      (accessorAfter model.status.code).regs.get? minstret ≠ accessorBefore.regs.get? minstret ∧
      -- and the caller's platform state, `ra` included, came back
      NormalExecutionState (accessorAfter model.status.code) ∧
      (accessorAfter model.status.code).regs.get? x1 = some calleeLink := by
  obtain ⟨hnoalloc, howned⟩ := accessor_writes_only_its_frame model.status.code
  refine ⟨⟨calleeFrameEnv_codeIntact _, hnoalloc, howned, accessorAfter_agree _,
      accessorAfter_retired _, rfl, accessorAfter_x10 _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [accessorBefore_frame, accessorAfter_frame]
    simp
  · show (1000 : Nat) ≤ 1016 ∧ (1016 : Nat) < 1000 + 64
    omega
  · exact returnedRegs_minstret_moved _
  · exact normalExecutionState_of_platformPreserved (accessorAfter_agree _) accessorBefore_normal
  · rw [platformPreserved_link (accessorAfter_agree _)]
    exact machineRegs_x1 _

/-- **`zesu_raw_result`'s strengthened postcondition is satisfiable**, by the same run at the pointer
its meaning prescribes. -/
theorem raw_result_run_satisfies_the_clauses (resultBuffer : Nat) (model : DecoderGlobalsModel) :
    postRawResult calleeFrameEnv resultBuffer model
        (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
        (accessorAfter (if model.stored.isSome then resultBuffer else 0)) ∧
      accessorBefore.mem.get? 1016
        ≠ (accessorAfter (if model.stored.isSome then resultBuffer else 0)).mem.get? 1016 ∧
      (accessorAfter (if model.stored.isSome then resultBuffer else 0)).regs.get? minstret
        ≠ accessorBefore.regs.get? minstret ∧
      (accessorAfter (if model.stored.isSome then resultBuffer else 0)).regs.get? x1
        = some calleeLink := by
  obtain ⟨hnoalloc, howned⟩ :=
    accessor_writes_only_its_frame (if model.stored.isSome then resultBuffer else 0)
  refine ⟨⟨calleeFrameEnv_codeIntact _, hnoalloc, howned, accessorAfter_agree _,
      accessorAfter_retired _, rfl, accessorAfter_x10 _⟩, ?_, ?_, ?_⟩
  · rw [accessorBefore_frame, accessorAfter_frame]
    simp
  · exact returnedRegs_minstret_moved _
  · rw [platformPreserved_link (accessorAfter_agree _)]
    exact machineRegs_x1 _

/-- **`postRawError` as it stood before the callee-frame clauses.** Kept verbatim so the clobbers
below remain countermodels to *the predicate that had the gap*, rather than being quietly re-pointed
at a different claim. Deliberately local: nothing outside this section may state an obligation in
terms of it. -/
def postRawErrorHistorical (env : DecoderEnvironment) (model : DecoderGlobalsModel)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  env.CodeIntact after ∧ env.NoAllocation before after ∧
  env.WritesOnlyWithinOwnRecord 0 0 before after ∧
  match result with
  | .ok code => code = model.status.code ∧ after.regs.get? x10 = some (BitVec.ofNat 64 code)
  | .error _ => False

/-- **`postRawResult` as it stood before the callee-frame clauses.** -/
def postRawResultHistorical (env : DecoderEnvironment) (resultBuffer : Nat)
    (model : DecoderGlobalsModel) (result : Except SszDecodeError Nat)
    (before after : State) : Prop :=
  env.CodeIntact after ∧ env.NoAllocation before after ∧
  env.WritesOnlyWithinOwnRecord 0 0 before after ∧
  match result with
  | .ok pointer =>
      pointer = (if model.stored.isSome then resultBuffer else 0) ∧
      after.regs.get? x10 = some (BitVec.ofNat 64 pointer)
  | .error _ => False

/-- **`postRawError` as it stood under the two clauses this change replaced**: the historical
predicate plus `ra` preserved and `NormalExecutionState after`.

This is a named object rather than an inlined conjunction on purpose. The claim the clobbers below
make is *the previous form permitted this run*, and that claim is only checkable if the previous form
is written down; spelled inline it would be a claim about the reader's memory of what the source used
to say. -/
def postRawErrorTwoClause (env : DecoderEnvironment) (model : DecoderGlobalsModel)
    (result : Except SszDecodeError Nat) (before after : State) : Prop :=
  postRawErrorHistorical env model result before after ∧
    after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after

/-! **The historical predicates really are the live ones minus exactly the two clauses**, and that is
a theorem rather than a claim about how the copies were made.

It is what turns each clobber below into a proof about a *named* clause. "All the old conjuncts hold,
the counter is present, and the strengthened predicate fails" pins the failure on the `Agree` clause
only if nothing else was added; these equivalences are what say nothing else was. They are also the
guard against the trap `DECISIONS.md` records as *restating in place is silent*: edit either copy and
they stop compiling. -/

theorem postRawError_eq_historical_and_clauses (env : DecoderEnvironment)
    (model : DecoderGlobalsModel) (result : Except SszDecodeError Nat) (before after : State) :
    postRawError env model result before after ↔
      postRawErrorHistorical env model result before after ∧
        Agree platformPreserved before after ∧ RetiredCounterPresent after := by
  constructor
  · rintro ⟨hcode, hnoalloc, howned, hagree, hretired, hrest⟩
    exact ⟨⟨hcode, hnoalloc, howned, hrest⟩, hagree, hretired⟩
  · rintro ⟨⟨hcode, hnoalloc, howned, hrest⟩, hagree, hretired⟩
    exact ⟨hcode, hnoalloc, howned, hagree, hretired, hrest⟩

theorem postRawResult_eq_historical_and_clauses (env : DecoderEnvironment) (resultBuffer : Nat)
    (model : DecoderGlobalsModel) (result : Except SszDecodeError Nat) (before after : State) :
    postRawResult env resultBuffer model result before after ↔
      postRawResultHistorical env resultBuffer model result before after ∧
        Agree platformPreserved before after ∧ RetiredCounterPresent after := by
  constructor
  · rintro ⟨hcode, hnoalloc, howned, hagree, hretired, hrest⟩
    exact ⟨⟨hcode, hnoalloc, howned, hrest⟩, hagree, hretired⟩
  · rintro ⟨⟨hcode, hnoalloc, howned, hrest⟩, hagree, hretired⟩
    exact ⟨hcode, hnoalloc, howned, hagree, hretired, hrest⟩

/-- The historical predicates hold of *any* after-state that writes what `accessorAfter` writes and
returns the same code. All four clobbers do, which is what leaves the register frame as the only
difference. -/
theorem accessor_historical_of_same_memory {code : Nat} {after : State}
    (hmem : ∀ address, after.mem.get? address = (accessorAfter code).mem.get? address) :
    calleeFrameEnv.CodeIntact after ∧
      calleeFrameEnv.NoAllocation accessorBefore after ∧
      calleeFrameEnv.WritesOnlyWithinOwnRecord 0 0 accessorBefore after := by
  obtain ⟨hnoalloc, howned⟩ := accessor_writes_only_its_frame code
  exact ⟨calleeFrameEnv_codeIntact _,
    fun address ha => (hmem address).trans (hnoalloc address ha),
    fun address ha => (hmem address).trans (howned address ha)⟩

/-- **The accessor contracts used to permit a callee that returned to the wrong address**, and the
strengthened ones refuse that very run.

This is the half a satisfiability witness cannot supply. `accessorRaClobber` writes exactly what
`accessorAfter` writes, so every memory conjunct of both predicates is satisfied identically; its
retired counter has advanced, so the counter clause is satisfied too; and it is a
`NormalExecutionState`, so the *old* platform clause is satisfied as well. The only difference from
the good run is the one register that carries the return address. -/
theorem accessor_ra_clobber_permitted_historical (resultBuffer : Nat)
    (model : DecoderGlobalsModel) :
    postRawErrorHistorical calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorRaClobber model.status.code) ∧
      postRawResultHistorical calleeFrameEnv resultBuffer model
        (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
        (accessorRaClobber (if model.stored.isSome then resultBuffer else 0)) ∧
      -- it returned to a different address …
      (accessorRaClobber model.status.code).regs.get? x1 ≠ accessorBefore.regs.get? x1 ∧
      -- … while leaving the machine entirely normal, so no platform clause is what bites …
      NormalExecutionState (accessorRaClobber model.status.code) ∧
      -- … and the counter clause is satisfied too …
      RetiredCounterPresent (accessorRaClobber model.status.code) ∧
      -- … and yet both strengthened postconditions refuse it.
      ¬ postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
          (accessorRaClobber model.status.code) ∧
      ¬ postRawResult calleeFrameEnv resultBuffer model
          (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
          (accessorRaClobber (if model.stored.isSome then resultBuffer else 0)) := by
  have hne : ∀ code : Nat,
      (accessorRaClobber code).regs.get? x1 ≠ accessorBefore.regs.get? x1 := by
    intro code
    rw [show (accessorRaClobber code).regs.get? x1 = some (BitVec.ofNat 64 5) from
        raClobberRegs_x1 code,
      show accessorBefore.regs.get? x1 = some calleeLink from machineRegs_x1 _]
    show ¬ (some (BitVec.ofNat 64 5) = some calleeLink)
    simp [calleeLink]
  have hnormal : ∀ code : Nat, NormalExecutionState (accessorRaClobber code) := fun code =>
    normalExecutionState_of_agree (before := accessorBefore) (raClobberRegs_normalAgree code)
      accessorBefore_normal
  obtain ⟨hcode, hnoalloc, howned⟩ :=
    accessor_historical_of_same_memory (accessorRaClobber_mem model.status.code)
  obtain ⟨hcode', hnoalloc', howned'⟩ :=
    accessor_historical_of_same_memory
      (accessorRaClobber_mem (if model.stored.isSome then resultBuffer else 0))
  exact ⟨⟨hcode, hnoalloc, howned, rfl, raClobberRegs_x10 _⟩,
    ⟨hcode', hnoalloc', howned', rfl, raClobberRegs_x10 _⟩, hne _, hnormal _,
    ⟨retiredAfter, raClobberRegs_minstret _⟩,
    fun h => hne _ (platformPreserved_link
      ((postRawError_eq_historical_and_clauses _ _ _ _ _).mp h).2.1),
    fun h => hne _ (platformPreserved_link
      ((postRawResult_eq_historical_and_clauses _ _ _ _ _ _).mp h).2.1)⟩

/-- **The accessor contracts used to permit a callee that came back with interrupts enabled**, and
the strengthened ones refuse that run too — through a different register of the same frame.

`ra` is preserved here, so the return-address half of the frame is satisfied and cannot be what
refuses the run; the refutation comes from `mie`. -/
theorem accessor_platform_clobber_permitted_historical (resultBuffer : Nat)
    (model : DecoderGlobalsModel) :
    postRawErrorHistorical calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorPlatformClobber model.status.code) ∧
      postRawResultHistorical calleeFrameEnv resultBuffer model
        (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
        (accessorPlatformClobber (if model.stored.isSome then resultBuffer else 0)) ∧
      -- `ra` is intact, so the return address is not what bites …
      (accessorPlatformClobber model.status.code).regs.get? x1 = accessorBefore.regs.get? x1 ∧
      -- … the machine is not one a `ret` can be shown to retire from …
      ¬ NormalExecutionState (accessorPlatformClobber model.status.code) ∧
      -- … and both strengthened postconditions refuse it.
      ¬ postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
          (accessorPlatformClobber model.status.code) ∧
      ¬ postRawResult calleeFrameEnv resultBuffer model
          (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
          (accessorPlatformClobber (if model.stored.isSome then resultBuffer else 0)) := by
  have hnotnormal : ∀ code : Nat, ¬ NormalExecutionState (accessorPlatformClobber code) := by
    intro code hnormal
    have hread := hnormal.2.2.2.2.1
    rw [show (accessorPlatformClobber code).regs.get? mie = some (1 : BitVec 64) from
      platformClobberRegs_mie code] at hread
    exact absurd hread (by simp)
  obtain ⟨hcode, hnoalloc, howned⟩ :=
    accessor_historical_of_same_memory (accessorPlatformClobber_mem model.status.code)
  obtain ⟨hcode', hnoalloc', howned'⟩ :=
    accessor_historical_of_same_memory
      (accessorPlatformClobber_mem (if model.stored.isSome then resultBuffer else 0))
  exact ⟨⟨hcode, hnoalloc, howned, rfl, platformClobberRegs_x10 _⟩,
    ⟨hcode', hnoalloc', howned', rfl, platformClobberRegs_x10 _⟩,
    platformClobberRegs_x1 _, hnotnormal _,
    fun h => hnotnormal _ (normalExecutionState_of_platformPreserved
      ((postRawError_eq_historical_and_clauses _ _ _ _ _).mp h).2.1 accessorBefore_normal),
    fun h => hnotnormal _ (normalExecutionState_of_platformPreserved
      ((postRawResult_eq_historical_and_clauses _ _ _ _ _ _).mp h).2.1 accessorBefore_normal)⟩

/-- **The two clauses this change replaced permitted a callee that rewrote the PMA table, and one
that opened the HTIF window** — and the frame clause refuses both.

This is the theorem that gives the change its content, and it is stated against the *old pair* rather
than against the pre-clause predicate: for each run, `after.regs.get? x1 = before.regs.get? x1` and
`NormalExecutionState after` are listed as explicit conjuncts and are proved. So neither of the two
clauses that used to be here could have refused these runs, and both would have certified an exit
state at which `tryStepRetRetires` is not provable — `FetchPmaAllows` evaluates `matching_pma_region`
on `pma_regions`, and `FetchMemoryNoMMIO` runs `within_htif_readable` on `htif_tohost_base`.

The two are kept in one theorem because they are the same claim about two registers; they are
separate *runs* because a single run breaking both would make each refutation derivable from the
other. -/
theorem accessor_fetch_and_mmio_clobbers_permitted_by_the_old_pair (model : DecoderGlobalsModel) :
    -- the PMA clobber: the previous form of the contract accepts it …
    postRawErrorTwoClause calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorFetchClobber model.status.code) ∧
      RetiredCounterPresent (accessorFetchClobber model.status.code) ∧
      -- … and yet the frame clause refuses it, at `pma_regions`
      (accessorFetchClobber model.status.code).regs.get? pma_regions
        ≠ accessorBefore.regs.get? pma_regions ∧
      ¬ postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
          (accessorFetchClobber model.status.code) ∧
    -- the HTIF clobber: the previous form accepts it too …
    postRawErrorTwoClause calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorMmioClobber model.status.code) ∧
      RetiredCounterPresent (accessorMmioClobber model.status.code) ∧
      -- … and yet the frame clause refuses it, at `htif_tohost_base`
      (accessorMmioClobber model.status.code).regs.get? htif_tohost_base
        ≠ accessorBefore.regs.get? htif_tohost_base ∧
      ¬ postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
          (accessorMmioClobber model.status.code) := by
  have hpma : (accessorFetchClobber model.status.code).regs.get? pma_regions
      ≠ accessorBefore.regs.get? pma_regions := by
    rw [show (accessorFetchClobber model.status.code).regs.get? pma_regions
        = some [(default : PMA_Region)] from fetchClobberRegs_pmaRegions _,
      show accessorBefore.regs.get? pma_regions = some ([] : List PMA_Region) from
        machineRegs_pmaRegions _]
    simp
  have hhtif : (accessorMmioClobber model.status.code).regs.get? htif_tohost_base
      ≠ accessorBefore.regs.get? htif_tohost_base := by
    rw [show (accessorMmioClobber model.status.code).regs.get? htif_tohost_base
        = some (some (0 : physaddrbits)) from mmioClobberRegs_htifBase _,
      show accessorBefore.regs.get? htif_tohost_base = some (none : Option physaddrbits) from
        machineRegs_htifBase _]
    simp
  obtain ⟨hcode, hnoalloc, howned⟩ :=
    accessor_historical_of_same_memory (accessorFetchClobber_mem model.status.code)
  obtain ⟨hcode', hnoalloc', howned'⟩ :=
    accessor_historical_of_same_memory (accessorMmioClobber_mem model.status.code)
  exact ⟨⟨⟨hcode, hnoalloc, howned, rfl, fetchClobberRegs_x10 _⟩,
      fetchClobberRegs_x1 _,
      normalExecutionState_of_agree (before := accessorBefore) (fetchClobberRegs_normalAgree _)
        accessorBefore_normal⟩,
    ⟨retiredAfter, fetchClobberRegs_minstret _⟩,
    hpma,
    (fun h => hpma (platformPreserved_pmaRegions
      ((postRawError_eq_historical_and_clauses _ _ _ _ _).mp h).2.1)),
    ⟨⟨hcode', hnoalloc', howned', rfl, mmioClobberRegs_x10 _⟩,
      mmioClobberRegs_x1 _,
      normalExecutionState_of_agree (before := accessorBefore) (mmioClobberRegs_normalAgree _)
        accessorBefore_normal⟩,
    ⟨retiredAfter, mmioClobberRegs_minstret _⟩,
    hhtif,
    (fun h => hhtif (platformPreserved_htifBase
      ((postRawError_eq_historical_and_clauses _ _ _ _ _).mp h).2.1))⟩

/-! ### The wrapper

`zesu_decode_raw` is not a leaf: it writes its stack frame *and* two of the three private globals.
The run below is its rejection path — `attempted` set, `last_status` recorded, the stored-result
discriminant left absent, `0` in `a0` — with the register frame restored, which is what the compiled
wrapper does with a conventional save/restore. -/

def wrapperMemBefore : Std.ExtHashMap Nat (BitVec 8) :=
  (∅ : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 10 (BitVec.ofNat 8 0)
    |>.insert 20 (BitVec.ofNat 8 0)
    |>.insert 21 (BitVec.ofNat 8 0)
    |>.insert 22 (BitVec.ofNat 8 0)
    |>.insert 23 (BitVec.ofNat 8 0)
    |>.insert 862 (BitVec.ofNat 8 0)
    |>.insert 1016 (BitVec.ofNat 8 0)

/-- `attempted := 1`, `last_status := 2` (`invalidSsz`), and one byte of stack frame. -/
def wrapperMemAfter : Std.ExtHashMap Nat (BitVec 8) :=
  wrapperMemBefore
    |>.insert 10 (BitVec.ofNat 8 1)
    |>.insert 20 (BitVec.ofNat 8 2)
    |>.insert 1016 (BitVec.ofNat 8 9)

def wrapperBefore : State :=
  { (default : State) with regs := machineRegs calleeLink, mem := wrapperMemBefore }

def wrapperAfter : State :=
  { (default : State) with regs := returnedRegs 0, mem := wrapperMemAfter }

/-- The wrapper's `ra` clobber: same globals, same return code, same frame, wrong return address —
and a perfectly normal machine, so only the return-address register can refuse it. -/
def wrapperRaClobber : State := { wrapperAfter with regs := raClobberRegs 0 }

/-- The wrapper's platform clobber: `ra` faithfully restored, interrupts enabled. -/
def wrapperPlatformClobber : State := { wrapperAfter with regs := platformClobberRegs 0 }

/-- The wrapper's PMA clobber: `ra` restored *and* a normal machine, so the two clauses this change
replaced both hold of it. -/
def wrapperFetchClobber : State := { wrapperAfter with regs := fetchClobberRegs 0 }

/-- The wrapper's HTIF clobber, likewise. -/
def wrapperMmioClobber : State := { wrapperAfter with regs := mmioClobberRegs 0 }

theorem wrapperAfter_attempted : wrapperAfter.mem.get? 10 = some (BitVec.ofNat 8 1) := by
  show wrapperMemAfter.get? 10 = _
  unfold wrapperMemAfter wrapperMemBefore
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp

theorem wrapperAfter_status0 : wrapperAfter.mem.get? 20 = some (BitVec.ofNat 8 2) := by
  show wrapperMemAfter.get? 20 = _
  unfold wrapperMemAfter wrapperMemBefore
  simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp

theorem wrapperAfter_zero {address : Nat}
    (h : address = 21 ∨ address = 22 ∨ address = 23 ∨ address = 862) :
    wrapperAfter.mem.get? address = some (BitVec.ofNat 8 0) := by
  show wrapperMemAfter.get? address = _
  unfold wrapperMemAfter wrapperMemBefore
  rcases h with rfl | rfl | rfl | rfl <;>
    · simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      simp

theorem wrapperBefore_normal : NormalExecutionState wrapperBefore := machineRegs_normal calleeLink

theorem wrapperAfter_agree : Agree platformPreserved wrapperBefore wrapperAfter :=
  returnedRegs_agree 0

theorem wrapperAfter_retired : RetiredCounterPresent wrapperAfter :=
  ⟨retiredAfter, returnedRegs_minstret 0⟩

theorem wrapperAfter_x10 : wrapperAfter.regs.get? x10 = some (BitVec.ofNat 64 0) :=
  returnedRegs_x10 0

/-- **The wrapper's strengthened postcondition is satisfiable by its own rejection path**, and it
holds for every container representation because the rejected arm stores no value.

The conjuncts after the postcondition are what make the run non-degenerate: it wrote its record (the
`attempted` byte moved) and its stack frame, it retired instructions (so `minstret` moved), and the
caller's frame — `ra` and the platform state included — came back. -/
theorem wrapper_run_satisfies_the_clauses (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase resultBuffer : Nat) :
    postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep DecoderGlobalsModel.fresh
        ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz) wrapperBefore wrapperAfter ∧
      -- it wrote the `attempted` global …
      wrapperBefore.mem.get? 10 ≠ wrapperAfter.mem.get? 10 ∧
      -- … and its stack frame …
      wrapperBefore.mem.get? 1016 ≠ wrapperAfter.mem.get? 1016 ∧
      -- … and retired instructions, so the counter is not preserved …
      wrapperAfter.regs.get? minstret ≠ wrapperBefore.regs.get? minstret ∧
      -- … and still came back with the caller's platform state and `ra`.
      NormalExecutionState wrapperAfter ∧
      wrapperAfter.regs.get? x1 = some calleeLink := by
  refine ⟨⟨?_, calleeFrameEnv_codeIntact _, ?_, wrapperAfter_agree, wrapperAfter_retired,
    ⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro index hindex; exact absurd hindex (by simp)
  · show wrapperAfter.regs.get? x10 = some (BitVec.ofNat 64 0)
    exact wrapperAfter_x10
  · -- the `attempted` flag reads `true`
    show wrapperAfter.mem.get? calleeFrameGlobals.attempted = some (BitVec.ofNat 8 1)
    exact wrapperAfter_attempted
  · -- `last_status` reads `invalidSsz = 2`, little-endian
    intro index hindex
    have hcase : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · exact wrapperAfter_status0
    · exact wrapperAfter_zero (Or.inl rfl)
    · exact wrapperAfter_zero (Or.inr (Or.inl rfl))
    · exact wrapperAfter_zero (Or.inr (Or.inr (Or.inl rfl)))
  · -- the stored-result discriminant reads absent
    show wrapperAfter.mem.get? 862 = some (BitVec.ofNat 8 0)
    exact wrapperAfter_zero (Or.inr (Or.inr (Or.inr rfl)))
  · trivial
  · rw [wrapperAfter_attempted]
    show ¬ (wrapperMemBefore.get? 10 = some (BitVec.ofNat 8 1))
    unfold wrapperMemBefore
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp
  · show ¬ (wrapperMemBefore.get? 1016 = wrapperMemAfter.get? 1016)
    unfold wrapperMemAfter wrapperMemBefore
    simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    simp
  · exact returnedRegs_minstret_moved 0
  · exact normalExecutionState_of_platformPreserved wrapperAfter_agree wrapperBefore_normal
  · rw [platformPreserved_link wrapperAfter_agree]
    exact machineRegs_x1 _

/-- **`postZesuDecodeRaw` as it stood before the callee-frame clauses.** -/
def postZesuDecodeRawHistorical (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (result : Except SszDecodeError SszBridge.RawV4) (_before after : State) : Prop :=
  MemoryBytes after args.inputBase args.bytes ∧
  env.CodeIntact after ∧
  after.regs.get? x10 = some (BitVec.ofNat 64 (callOutcome incoming result).returnCode) ∧
  DecoderGlobalsRep globals rep args.inputBase args.bytes resultBuffer
    (resultingGlobals incoming result) after

/-- **`postZesuDecodeRaw` as it stood under the two clauses this change replaced**, named for the
reason `postRawErrorTwoClause` is. -/
def postZesuDecodeRawTwoClause (env : DecoderEnvironment) (globals : DecoderGlobalsLayout)
    (resultBuffer : Nat) (rep : ContainerRepresentation SszBridge.RawV4)
    (incoming : DecoderGlobalsModel) (args : ZesuDecodeRawArgs)
    (result : Except SszDecodeError SszBridge.RawV4) (before after : State) : Prop :=
  postZesuDecodeRawHistorical env globals resultBuffer rep incoming args result before after ∧
    after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after

/-- The wrapper's historical predicate is likewise the live one minus exactly the two clauses. -/
theorem postZesuDecodeRaw_eq_historical_and_clauses (env : DecoderEnvironment)
    (globals : DecoderGlobalsLayout) (resultBuffer : Nat)
    (rep : ContainerRepresentation SszBridge.RawV4) (incoming : DecoderGlobalsModel)
    (args : ZesuDecodeRawArgs) (result : Except SszDecodeError SszBridge.RawV4)
    (before after : State) :
    postZesuDecodeRaw env globals resultBuffer rep incoming args result before after ↔
      postZesuDecodeRawHistorical env globals resultBuffer rep incoming args result before after ∧
        Agree platformPreserved before after ∧ RetiredCounterPresent after := by
  constructor
  · rintro ⟨hbytes, hcode, ha0, hagree, hretired, hglobals⟩
    exact ⟨⟨hbytes, hcode, ha0, hglobals⟩, hagree, hretired⟩
  · rintro ⟨⟨hbytes, hcode, ha0, hglobals⟩, hagree, hretired⟩
    exact ⟨hbytes, hcode, ha0, hagree, hretired, hglobals⟩

/-- The historical wrapper postcondition holds of any after-state with `wrapperAfter`'s memory and
return code — which all four clobbers have. -/
theorem wrapper_historical_of_same_memory (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase resultBuffer : Nat) {after : State}
    (hmem : ∀ address, after.mem.get? address = wrapperAfter.mem.get? address)
    (hx10 : after.regs.get? x10 = some (BitVec.ofNat 64 0)) :
    postZesuDecodeRawHistorical calleeFrameEnv calleeFrameGlobals resultBuffer rep
      DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
      wrapperBefore after := by
  obtain ⟨⟨hbytes, -, -, -, -, hglobals⟩, -, -, -, -, -⟩ :=
    wrapper_run_satisfies_the_clauses rep inputBase resultBuffer
  obtain ⟨⟨hflag, hstatus⟩, hdisc, hstored⟩ := hglobals
  exact ⟨fun index hindex => (hmem _).trans (hbytes index hindex), calleeFrameEnv_codeIntact _,
    hx10, ⟨⟨(hmem _).trans hflag, fun index hi => (hmem _).trans (hstatus index hi)⟩,
      (hmem _).trans hdisc, hstored⟩⟩

/-- **The wrapper contract used to permit a decode that never came back to its caller.**

Same globals, same return code, same stack frame, an advanced counter, and a normal machine — the old
postcondition cannot tell `wrapperRaClobber` from `wrapperAfter`, and neither can the platform
clause. Only the return-address register refuses it. -/
theorem wrapper_ra_clobber_permitted_historical (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase resultBuffer : Nat) :
    postZesuDecodeRawHistorical calleeFrameEnv calleeFrameGlobals resultBuffer rep
        DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
        wrapperBefore wrapperRaClobber ∧
      wrapperRaClobber.regs.get? x1 ≠ wrapperBefore.regs.get? x1 ∧
      NormalExecutionState wrapperRaClobber ∧
      RetiredCounterPresent wrapperRaClobber ∧
      ¬ postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep
          DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
          wrapperBefore wrapperRaClobber := by
  have hne : wrapperRaClobber.regs.get? x1 ≠ wrapperBefore.regs.get? x1 := by
    rw [show wrapperRaClobber.regs.get? x1 = some (BitVec.ofNat 64 5) from raClobberRegs_x1 0,
      show wrapperBefore.regs.get? x1 = some calleeLink from machineRegs_x1 _]
    show ¬ (some (BitVec.ofNat 64 5) = some calleeLink)
    simp [calleeLink]
  exact ⟨wrapper_historical_of_same_memory rep inputBase resultBuffer (fun _ => rfl)
      (raClobberRegs_x10 0),
    hne,
    normalExecutionState_of_agree (before := wrapperBefore) (raClobberRegs_normalAgree 0)
      wrapperBefore_normal,
    ⟨retiredAfter, raClobberRegs_minstret 0⟩,
    fun h => hne (platformPreserved_link
      ((postZesuDecodeRaw_eq_historical_and_clauses _ _ _ _ _ _ _ _ _).mp h).2.1)⟩

/-- **The wrapper contract used to permit a decode that came back with interrupts enabled**, refused
through a different register of the same frame. `ra` is intact here, so the return-address half is
satisfied and the refutation can only come from `mie`. -/
theorem wrapper_platform_clobber_permitted_historical
    (rep : ContainerRepresentation SszBridge.RawV4) (inputBase resultBuffer : Nat) :
    postZesuDecodeRawHistorical calleeFrameEnv calleeFrameGlobals resultBuffer rep
        DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
        wrapperBefore wrapperPlatformClobber ∧
      wrapperPlatformClobber.regs.get? x1 = wrapperBefore.regs.get? x1 ∧
      ¬ NormalExecutionState wrapperPlatformClobber ∧
      ¬ postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep
          DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
          wrapperBefore wrapperPlatformClobber := by
  have hnotnormal : ¬ NormalExecutionState wrapperPlatformClobber := by
    intro hnormal
    have hread := hnormal.2.2.2.2.1
    rw [show wrapperPlatformClobber.regs.get? mie = some (1 : BitVec 64) from
      platformClobberRegs_mie 0] at hread
    exact absurd hread (by simp)
  exact ⟨wrapper_historical_of_same_memory rep inputBase resultBuffer (fun _ => rfl)
      (platformClobberRegs_x10 0),
    platformClobberRegs_x1 0, hnotnormal,
    fun h => hnotnormal (normalExecutionState_of_platformPreserved
      ((postZesuDecodeRaw_eq_historical_and_clauses _ _ _ _ _ _ _ _ _).mp h).2.1
      wrapperBefore_normal)⟩

/-- **The wrapper contract, under the two clauses this change replaced, permitted a decode that
rewrote the PMA table or opened the HTIF window** — and the frame clause refuses both.

The wrapper counterpart of `accessor_fetch_and_mmio_clobbers_permitted_by_the_old_pair`, and it is
here rather than delegated to the accessors because `postZesuDecodeRaw` is a different predicate:
`postZesuDecodeRaw_eq_historical_and_clauses` is what names the clause in *its* conjunction, and a
theorem about `postRawError` says nothing about it. -/
theorem wrapper_fetch_and_mmio_clobbers_permitted_by_the_old_pair
    (rep : ContainerRepresentation SszBridge.RawV4) (inputBase resultBuffer : Nat) :
    postZesuDecodeRawTwoClause calleeFrameEnv calleeFrameGlobals resultBuffer rep
        DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
        wrapperBefore wrapperFetchClobber ∧
      ¬ postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep
          DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
          wrapperBefore wrapperFetchClobber ∧
    postZesuDecodeRawTwoClause calleeFrameEnv calleeFrameGlobals resultBuffer rep
        DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
        wrapperBefore wrapperMmioClobber ∧
      ¬ postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep
          DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
          wrapperBefore wrapperMmioClobber := by
  have hpma : wrapperFetchClobber.regs.get? pma_regions ≠ wrapperBefore.regs.get? pma_regions := by
    rw [show wrapperFetchClobber.regs.get? pma_regions = some [(default : PMA_Region)] from
        fetchClobberRegs_pmaRegions 0,
      show wrapperBefore.regs.get? pma_regions = some ([] : List PMA_Region) from
        machineRegs_pmaRegions _]
    simp
  have hhtif : wrapperMmioClobber.regs.get? htif_tohost_base
      ≠ wrapperBefore.regs.get? htif_tohost_base := by
    rw [show wrapperMmioClobber.regs.get? htif_tohost_base = some (some (0 : physaddrbits)) from
        mmioClobberRegs_htifBase 0,
      show wrapperBefore.regs.get? htif_tohost_base = some (none : Option physaddrbits) from
        machineRegs_htifBase _]
    simp
  exact ⟨⟨wrapper_historical_of_same_memory rep inputBase resultBuffer (fun _ => rfl)
        (fetchClobberRegs_x10 0),
      fetchClobberRegs_x1 0,
      normalExecutionState_of_agree (before := wrapperBefore) (fetchClobberRegs_normalAgree 0)
        wrapperBefore_normal⟩,
    (fun h => hpma (platformPreserved_pmaRegions
      ((postZesuDecodeRaw_eq_historical_and_clauses _ _ _ _ _ _ _ _ _).mp h).2.1)),
    ⟨wrapper_historical_of_same_memory rep inputBase resultBuffer (fun _ => rfl)
        (mmioClobberRegs_x10 0),
      mmioClobberRegs_x1 0,
      normalExecutionState_of_agree (before := wrapperBefore) (mmioClobberRegs_normalAgree 0)
        wrapperBefore_normal⟩,
    (fun h => hhtif (platformPreserved_htifBase
      ((postZesuDecodeRaw_eq_historical_and_clauses _ _ _ _ _ _ _ _ _).mp h).2.1))⟩

/-! ### `CalleeFrame` is not the vocabulary for these clauses

`RiscV/Elfling/Contract.lean` defines `CalleeFrame preserved image before after :=
Agree preserved before after ∧ image.matchesMemory after.mem`, and it has **no call site tree-wide**.
The register half is exactly right and is now what the clause is spelled with. The memory half is the
retired defect: `image.matchesMemory` is the *full*-image match that `DecoderEnvironment.CodeIntact`
was corrected away from, because it pins every BSS byte to its static zero and the decoder's globals
are in the BSS.

So writing the clause as `CalleeFrame` would not have been a tidier spelling of the same thing — it
would have added a conjunct that the wrapper's own rejection path makes **false**, on a predicate
consumed only through an assumed hypothesis. That is the vacuous-root failure mode, and the theorem
below is it in one line: the same run that satisfies the strengthened `postZesuDecodeRaw` refutes
`CalleeFrame` at any register set whatsoever — `platformPreserved` included. -/

theorem calleeFrame_is_not_the_vocabulary (preserved : Register → Prop)
    (rep : ContainerRepresentation SszBridge.RawV4) (inputBase resultBuffer : Nat) :
    postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep DecoderGlobalsModel.fresh
        ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz) wrapperBefore wrapperAfter ∧
      ¬ CalleeFrame preserved calleeFrameEnv.image wrapperBefore wrapperAfter := by
  refine ⟨(wrapper_run_satisfies_the_clauses rep inputBase resultBuffer).1, ?_⟩
  rintro ⟨-, hmatch⟩
  have himage : wrapperAfter.mem.get? 10 = some (BitVec.ofNat 8 (0 : UInt8).toNat) :=
    hmatch 10 0 (calleeFrameEnv_readByte (by omega))
  rw [wrapperAfter_attempted] at himage
  exact absurd himage (by simp)

end CalleeFrameExhibit

end BinaryFv.SSZ.Zesu.Contracts
