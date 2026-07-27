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

/-! ## `NormalExecutionState` transports to an exit state

`ExportedDecoder`'s callee-frame note asserts `NormalExecutionState after`, and the only place the
tree establishes that predicate at all is `EntryBinding.configure_runs`, at the state the runner
*builds*. Those are not the same claim, and the gap between them is exactly this lemma: the predicate
reads twelve platform registers and nothing else, so it survives any step that leaves those twelve
alone — every memory write, and every write to a general-purpose register or program counter.

Stated with `Agree`, which is the register half of `RiscV/Elfling/Contract.lean`'s `CalleeFrame`.
That is the reuse question answered in the affirmative for one half; the other half is answered in
the negative at the end of this file. -/

/-- The twelve registers `NormalExecutionState` reads. -/
def platformRegisters : Register → Prop := fun r =>
  r = hart_state ∨ r = cur_privilege ∨ r = satp ∨ r = mideleg ∨ r = mie ∨ r = mip ∨
    r = pmpcfg_n ∨ r = pmpaddr_n ∨ r = mcountinhibit ∨ r = minstretcfg ∨ r = elp ∨ r = misa

/-- **`NormalExecutionState` transports across any step that preserves the twelve platform
registers.** This is what carries the predicate from the state where it is established to the `after`
state the three postconditions assert it of. -/
theorem normalExecutionState_of_agree {before after : State}
    (agree : Agree platformRegisters before after) (h : NormalExecutionState before) :
    NormalExecutionState after := by
  obtain ⟨hhart, hpriv, hsatp, hmideleg, hmie, hmip, hpmpcfg, hpmpaddr, hinhibit, hcfg, help,
    hmisa⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?misa⟩
  case misa =>
    rw [agree misa (by simp [platformRegisters])]
    exact hmisa
  all_goals
    first
      | (rw [agree hart_state (by simp [platformRegisters])]; exact hhart)
      | (rw [agree cur_privilege (by simp [platformRegisters])]; exact hpriv)
      | (rw [agree satp (by simp [platformRegisters])]; exact hsatp)
      | (rw [agree mideleg (by simp [platformRegisters])]; exact hmideleg)
      | (rw [agree mie (by simp [platformRegisters])]; exact hmie)
      | (rw [agree mip (by simp [platformRegisters])]; exact hmip)
      | (rw [agree pmpcfg_n (by simp [platformRegisters])]; exact hpmpcfg)
      | (rw [agree pmpaddr_n (by simp [platformRegisters])]; exact hpmpaddr)
      | (rw [agree mcountinhibit (by simp [platformRegisters])]; exact hinhibit)
      | (rw [agree minstretcfg (by simp [platformRegisters])]; exact hcfg)
      | (rw [agree elp (by simp [platformRegisters])]; exact help)

/-! ## The callee-frame clauses, exhibited

`postZesuDecodeRaw`, `postRawResult` and `postRawError` each gained `after.regs.get? x1 =
before.regs.get? x1` and `NormalExecutionState after`. They are consumed only through the **assumed**
`LocalContractAssumptions`, so the build stays green whatever they say — which is precisely why the
build is not evidence. This row has already had one clause approved on that reasoning turn out to be
*false* of every allocating routine, and a false conjunct inside an assumed hypothesis makes the root
vacuous rather than merely under-specified.

So each strengthened predicate gets a run here that satisfies it, and then **two** clobbering runs
that the unstrengthened predicate accepted and the strengthened one refuses — one per clause, because
a single run breaking both would leave each refutation derivable from the other clause and so would
test neither. The clobbers are what stop a redundant clause from looking exactly like a load-bearing
one: satisfiability alone would prove just as easily if the clauses said nothing.

The three `post*_eq_historical_and_clauses` equivalences close the loop by proving that each
`…Historical` predicate is the live one *minus exactly these two conjuncts*, so "all the old
conjuncts hold, the other new one holds, and the strengthened predicate fails" identifies which
clause did the refusing rather than leaving it to be read off the source.

The runs are shaped like the routines they stand for rather than doing nothing. Each writes its stack
frame — a routine that touched no memory would satisfy the memory clauses for a reason having nothing
to do with these two — and the wrapper's additionally writes the two decoder globals a rejected
decode really writes. Deliberately the *rejection* path: it is a real path of the real wrapper, and
its stored-result arm is `True`, so the witness holds for **every** container representation rather
than for a convenient one. The success arm would additionally have to realise a `RawV4` in memory,
which is orthogonal to the two clauses under test.
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

/-! ### The accessors

`zesu_raw_result` and `zesu_raw_error` are leaves: no prologue, no store. The run below is the
strongest thing that is still shaped like a compiled routine — it touches exactly one byte, in its
own stack frame, and returns a value in `a0`. -/

def accessorBefore : State :=
  { (default : State) with
    regs := normalRegs calleeLink
    mem := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0) }

/-- The accessor returned: `a0` holds the code, one byte of its stack frame changed, `x1` and every
platform register are untouched. -/
def accessorAfter (code : Nat) : State :=
  { (default : State) with
    regs := (normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)
    mem := ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0)).insert 1016
      (BitVec.ofNat 8 9) }

/-! Two clobbering runs, and they are deliberately **separate**.

A single run that broke both clauses at once would prove less than it appears to: the refutation
could be discharged from either conjunct, so deleting one clause would leave the exhibit compiling
and guarding the other. Each run below therefore violates exactly one of the two clauses and
satisfies the other, which makes each `¬ post…` conclusion derivable **only** from the clause it is
about. Delete either clause and the corresponding theorem stops compiling. -/

/-- A callee that returns to the wrong address. Memory-wise, and platform-wise, it is
indistinguishable from `accessorAfter`: `NormalExecutionState` still holds of it. -/
def accessorRaClobber (code : Nat) : State :=
  { (default : State) with
    regs := ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert x1
      (BitVec.ofNat 64 5)
    mem := ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0)).insert 1016
      (BitVec.ofNat 8 9) }

/-- A callee that restores `ra` faithfully but comes back with interrupts enabled — a state no `ret`
can be shown to retire from, because `InterruptDisabled` is one of `tryStepRetRetires`' hypotheses. -/
def accessorPlatformClobber (code : Nat) : State :=
  { (default : State) with
    regs := ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert mie (1 : BitVec 64)
    mem := ((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 1016 (BitVec.ofNat 8 0)).insert 1016
      (BitVec.ofNat 8 9) }

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

theorem accessorAfter_x10 (code : Nat) :
    (accessorAfter code).regs.get? x10 = some (BitVec.ofNat 64 code) := by
  simp [accessorAfter]

theorem accessorRaClobber_x10 (code : Nat) :
    (accessorRaClobber code).regs.get? x10 = some (BitVec.ofNat 64 code) := by
  show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert x1
    (BitVec.ofNat 64 5)).get? x10 = _
  simp [Std.ExtDHashMap.get?_insert]

theorem accessorPlatformClobber_x10 (code : Nat) :
    (accessorPlatformClobber code).regs.get? x10 = some (BitVec.ofNat 64 code) := by
  show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert
    mie (1 : BitVec 64)).get? x10 = _
  simp [Std.ExtDHashMap.get?_insert]

theorem accessorRaClobber_x1 (code : Nat) :
    (accessorRaClobber code).regs.get? x1 = some (BitVec.ofNat 64 5) := by
  show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert x1
    (BitVec.ofNat 64 5)).get? x1 = _
  simp

/-- **The `ra` clobber leaves the machine perfectly normal**, so the platform clause cannot be what
refuses it. This is what makes `accessor_ra_clobber_permitted_historical`'s last conjunct a test of
the `x1` clause specifically. -/
theorem accessorRaClobber_normal (code : Nat) : NormalExecutionState (accessorRaClobber code) := by
  refine normalExecutionState_of_agree (before := accessorBefore) ?_ (normalRegs_normal calleeLink)
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert x1
        (BitVec.ofNat 64 5)).get? _ = (normalRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

/-- **The platform clobber returns to the right address**, so the `x1` clause cannot be what refuses
it. The mirror of `accessorRaClobber_normal`. -/
theorem accessorPlatformClobber_x1 (code : Nat) :
    (accessorPlatformClobber code).regs.get? x1 = accessorBefore.regs.get? x1 := by
  show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert
    mie (1 : BitVec 64)).get? x1 = (normalRegs calleeLink).get? x1
  simp [Std.ExtDHashMap.get?_insert]

theorem accessorPlatformClobber_mie (code : Nat) :
    (accessorPlatformClobber code).regs.get? mie = some (1 : BitVec 64) := by
  show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).insert
    mie (1 : BitVec 64)).get? mie = _
  simp

theorem accessorAfter_x1 (code : Nat) :
    (accessorAfter code).regs.get? x1 = accessorBefore.regs.get? x1 := by
  show ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).get? x1
    = (normalRegs calleeLink).get? x1
  simp [Std.ExtDHashMap.get?_insert]

theorem accessorAfter_normal (code : Nat) : NormalExecutionState (accessorAfter code) := by
  refine normalExecutionState_of_agree (before := accessorBefore) ?_ (normalRegs_normal calleeLink)
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 code)).get? _
        = (normalRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

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
routine.** It wrote its stack frame, returned the status in `a0`, and came back with the caller's
`ra` and a normal machine. -/
theorem raw_error_run_satisfies_the_clauses (model : DecoderGlobalsModel) :
    postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorAfter model.status.code) ∧
      -- it really wrote its frame: not a routine that does nothing
      accessorBefore.mem.get? 1016 ≠ (accessorAfter model.status.code).mem.get? 1016 ∧
      calleeFrameEnv.stack 1016 ∧
      -- and `ra` came back holding the caller's value
      (accessorAfter model.status.code).regs.get? x1 = some calleeLink := by
  obtain ⟨hnoalloc, howned⟩ := accessor_writes_only_its_frame model.status.code
  refine ⟨⟨calleeFrameEnv_codeIntact _, hnoalloc, howned, accessorAfter_x1 _,
      accessorAfter_normal _, rfl, accessorAfter_x10 _⟩, ?_, ?_, ?_⟩
  · rw [accessorBefore_frame, accessorAfter_frame]
    simp
  · show (1000 : Nat) ≤ 1016 ∧ (1016 : Nat) < 1000 + 64
    omega
  · rw [accessorAfter_x1]; exact normalRegs_x1 _

/-- **`zesu_raw_result`'s strengthened postcondition is satisfiable**, by the same run at the pointer
its meaning prescribes. -/
theorem raw_result_run_satisfies_the_clauses (resultBuffer : Nat) (model : DecoderGlobalsModel) :
    postRawResult calleeFrameEnv resultBuffer model
        (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
        (accessorAfter (if model.stored.isSome then resultBuffer else 0)) ∧
      accessorBefore.mem.get? 1016
        ≠ (accessorAfter (if model.stored.isSome then resultBuffer else 0)).mem.get? 1016 ∧
      (accessorAfter (if model.stored.isSome then resultBuffer else 0)).regs.get? x1
        = some calleeLink := by
  obtain ⟨hnoalloc, howned⟩ :=
    accessor_writes_only_its_frame (if model.stored.isSome then resultBuffer else 0)
  refine ⟨⟨calleeFrameEnv_codeIntact _, hnoalloc, howned, accessorAfter_x1 _,
      accessorAfter_normal _, rfl, accessorAfter_x10 _⟩, ?_, ?_⟩
  · rw [accessorBefore_frame, accessorAfter_frame]
    simp
  · rw [accessorAfter_x1]; exact normalRegs_x1 _

/-- **`postRawError` as it stood before the callee-frame clauses.** Kept verbatim so the clobber
below remains a countermodel to *the predicate that had the gap*, rather than being quietly
re-pointed at a different claim. Deliberately local: nothing outside this section may state an
obligation in terms of it. -/
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

/-! **The historical predicates really are the live ones minus exactly the two clauses**, and that is
a theorem rather than a claim about how the copies were made.

It is what turns each clobber below into a proof about a *named* clause. "All the old conjuncts hold,
`NormalExecutionState` holds, and the strengthened predicate fails" pins the failure on the `x1`
clause only if nothing else was added; these equivalences are what say nothing else was. They are
also the guard against the trap `DECISIONS.md` records as *restating in place is silent*: edit either
copy and they stop compiling. -/

theorem postRawError_eq_historical_and_clauses (env : DecoderEnvironment)
    (model : DecoderGlobalsModel) (result : Except SszDecodeError Nat) (before after : State) :
    postRawError env model result before after ↔
      postRawErrorHistorical env model result before after ∧
        after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after := by
  constructor
  · rintro ⟨hcode, hnoalloc, howned, hx1, hnormal, hrest⟩
    exact ⟨⟨hcode, hnoalloc, howned, hrest⟩, hx1, hnormal⟩
  · rintro ⟨⟨hcode, hnoalloc, howned, hrest⟩, hx1, hnormal⟩
    exact ⟨hcode, hnoalloc, howned, hx1, hnormal, hrest⟩

theorem postRawResult_eq_historical_and_clauses (env : DecoderEnvironment) (resultBuffer : Nat)
    (model : DecoderGlobalsModel) (result : Except SszDecodeError Nat) (before after : State) :
    postRawResult env resultBuffer model result before after ↔
      postRawResultHistorical env resultBuffer model result before after ∧
        after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after := by
  constructor
  · rintro ⟨hcode, hnoalloc, howned, hx1, hnormal, hrest⟩
    exact ⟨⟨hcode, hnoalloc, howned, hrest⟩, hx1, hnormal⟩
  · rintro ⟨⟨hcode, hnoalloc, howned, hrest⟩, hx1, hnormal⟩
    exact ⟨hcode, hnoalloc, howned, hx1, hnormal, hrest⟩

/-- The historical predicates hold of *any* after-state that writes what `accessorAfter` writes.
Both clobbers do, which is what leaves the register clauses as the only difference. -/
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
`accessorAfter` writes, so every memory conjunct of both predicates is satisfied identically — and it
is `NormalExecutionState` too, so the *other* new clause is satisfied as well. The only difference
from the good run is the one register the old form said nothing about, which is what makes the last
two conjuncts a test of the `x1` clause and of nothing else. -/
theorem accessor_ra_clobber_permitted_historical (resultBuffer : Nat)
    (model : DecoderGlobalsModel) :
    postRawErrorHistorical calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorRaClobber model.status.code) ∧
      postRawResultHistorical calleeFrameEnv resultBuffer model
        (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
        (accessorRaClobber (if model.stored.isSome then resultBuffer else 0)) ∧
      -- it returned to a different address …
      (accessorRaClobber model.status.code).regs.get? x1 ≠ accessorBefore.regs.get? x1 ∧
      -- … while leaving the machine entirely normal, so the platform clause is not what bites …
      NormalExecutionState (accessorRaClobber model.status.code) ∧
      -- … and yet both strengthened postconditions refuse it.
      ¬ postRawError calleeFrameEnv model (.ok model.status.code) accessorBefore
          (accessorRaClobber model.status.code) ∧
      ¬ postRawResult calleeFrameEnv resultBuffer model
          (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
          (accessorRaClobber (if model.stored.isSome then resultBuffer else 0)) := by
  have hne : ∀ code : Nat,
      (accessorRaClobber code).regs.get? x1 ≠ accessorBefore.regs.get? x1 := by
    intro code
    rw [accessorRaClobber_x1, show accessorBefore.regs.get? x1 = some calleeLink from normalRegs_x1 _]
    show ¬ (some (BitVec.ofNat 64 5) = some calleeLink)
    simp [calleeLink]
  obtain ⟨hcode, hnoalloc, howned⟩ :=
    accessor_historical_of_same_memory (accessorRaClobber_mem model.status.code)
  obtain ⟨hcode', hnoalloc', howned'⟩ :=
    accessor_historical_of_same_memory
      (accessorRaClobber_mem (if model.stored.isSome then resultBuffer else 0))
  exact ⟨⟨hcode, hnoalloc, howned, rfl, accessorRaClobber_x10 _⟩,
    ⟨hcode', hnoalloc', howned', rfl, accessorRaClobber_x10 _⟩, hne _,
    accessorRaClobber_normal _,
    fun h => hne _ ((postRawError_eq_historical_and_clauses _ _ _ _ _).mp h).2.1,
    fun h => hne _ ((postRawResult_eq_historical_and_clauses _ _ _ _ _ _).mp h).2.1⟩

/-- **The accessor contracts used to permit a callee that came back with interrupts enabled**, and
the strengthened ones refuse that run too — through the *other* clause.

The mirror of the theorem above, and the pair is the point. Here `ra` is preserved, so the `x1`
clause is satisfied and cannot be what refuses the run; the refutation can only come from
`NormalExecutionState after`. Delete either clause and exactly one of these two theorems stops
compiling. -/
theorem accessor_platform_clobber_permitted_historical (resultBuffer : Nat)
    (model : DecoderGlobalsModel) :
    postRawErrorHistorical calleeFrameEnv model (.ok model.status.code) accessorBefore
        (accessorPlatformClobber model.status.code) ∧
      postRawResultHistorical calleeFrameEnv resultBuffer model
        (.ok (if model.stored.isSome then resultBuffer else 0)) accessorBefore
        (accessorPlatformClobber (if model.stored.isSome then resultBuffer else 0)) ∧
      -- `ra` is intact, so the `x1` clause is not what bites …
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
    rw [accessorPlatformClobber_mie] at hread
    exact absurd hread (by simp)
  obtain ⟨hcode, hnoalloc, howned⟩ :=
    accessor_historical_of_same_memory (accessorPlatformClobber_mem model.status.code)
  obtain ⟨hcode', hnoalloc', howned'⟩ :=
    accessor_historical_of_same_memory
      (accessorPlatformClobber_mem (if model.stored.isSome then resultBuffer else 0))
  exact ⟨⟨hcode, hnoalloc, howned, rfl, accessorPlatformClobber_x10 _⟩,
    ⟨hcode', hnoalloc', howned', rfl, accessorPlatformClobber_x10 _⟩,
    accessorPlatformClobber_x1 _, hnotnormal _,
    fun h => hnotnormal _ ((postRawError_eq_historical_and_clauses _ _ _ _ _).mp h).2.2,
    fun h => hnotnormal _ ((postRawResult_eq_historical_and_clauses _ _ _ _ _ _).mp h).2.2⟩

/-! ### The wrapper

`zesu_decode_raw` is not a leaf: it writes its stack frame *and* two of the three private globals.
The run below is its rejection path — `attempted` set, `last_status` recorded, the stored-result
discriminant left absent, `0` in `a0` — with `ra` restored, which is what the compiled wrapper does
with a conventional save/restore. -/

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
  { (default : State) with regs := normalRegs calleeLink, mem := wrapperMemBefore }

def wrapperAfter : State :=
  { (default : State) with
    regs := (normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)
    mem := wrapperMemAfter }

/-- The wrapper's `ra` clobber: same globals, same return code, same frame, wrong return address —
and a perfectly normal machine, so only the `x1` clause can refuse it. -/
def wrapperRaClobber : State :=
  { (default : State) with
    regs := ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert x1
      (BitVec.ofNat 64 5)
    mem := wrapperMemAfter }

/-- The wrapper's platform clobber: `ra` faithfully restored, interrupts enabled — so only the
`NormalExecutionState` clause can refuse it. -/
def wrapperPlatformClobber : State :=
  { (default : State) with
    regs := ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert mie (1 : BitVec 64)
    mem := wrapperMemAfter }

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

theorem wrapperAfter_x1 : wrapperAfter.regs.get? x1 = wrapperBefore.regs.get? x1 := by
  show ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).get? x1
    = (normalRegs calleeLink).get? x1
  simp [Std.ExtDHashMap.get?_insert]

theorem wrapperAfter_x10 : wrapperAfter.regs.get? x10 = some (BitVec.ofNat 64 0) := by
  simp [wrapperAfter]

theorem wrapperAfter_normal : NormalExecutionState wrapperAfter := by
  refine normalExecutionState_of_agree (before := wrapperBefore) ?_ (normalRegs_normal calleeLink)
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · show ((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).get? _
        = (normalRegs calleeLink).get? _
      simp [Std.ExtDHashMap.get?_insert]

/-- **The wrapper's strengthened postcondition is satisfiable by its own rejection path**, and it
holds for every container representation because the rejected arm stores no value.

The conjuncts after the postcondition are what make the run non-degenerate: it wrote its record (the
`attempted` byte moved) and its stack frame, and `ra` still holds the caller's address. -/
theorem wrapper_run_satisfies_the_clauses (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase resultBuffer : Nat) :
    postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep DecoderGlobalsModel.fresh
        ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz) wrapperBefore wrapperAfter ∧
      -- it wrote the `attempted` global …
      wrapperBefore.mem.get? 10 ≠ wrapperAfter.mem.get? 10 ∧
      -- … and its stack frame …
      wrapperBefore.mem.get? 1016 ≠ wrapperAfter.mem.get? 1016 ∧
      -- … and still came back with the caller's `ra`.
      wrapperAfter.regs.get? x1 = some calleeLink := by
  refine ⟨⟨?_, calleeFrameEnv_codeIntact _, ?_, wrapperAfter_x1, wrapperAfter_normal, ⟨?_, ?_⟩,
    ?_, ?_⟩, ?_, ?_, ?_⟩
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
  · rw [wrapperAfter_x1]; exact normalRegs_x1 _

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

/-- The wrapper's historical predicate is likewise the live one minus exactly the two clauses. -/
theorem postZesuDecodeRaw_eq_historical_and_clauses (env : DecoderEnvironment)
    (globals : DecoderGlobalsLayout) (resultBuffer : Nat)
    (rep : ContainerRepresentation SszBridge.RawV4) (incoming : DecoderGlobalsModel)
    (args : ZesuDecodeRawArgs) (result : Except SszDecodeError SszBridge.RawV4)
    (before after : State) :
    postZesuDecodeRaw env globals resultBuffer rep incoming args result before after ↔
      postZesuDecodeRawHistorical env globals resultBuffer rep incoming args result before after ∧
        after.regs.get? x1 = before.regs.get? x1 ∧ NormalExecutionState after := by
  constructor
  · rintro ⟨hbytes, hcode, ha0, hx1, hnormal, hglobals⟩
    exact ⟨⟨hbytes, hcode, ha0, hglobals⟩, hx1, hnormal⟩
  · rintro ⟨⟨hbytes, hcode, ha0, hglobals⟩, hx1, hnormal⟩
    exact ⟨hbytes, hcode, ha0, hx1, hnormal, hglobals⟩

/-- The historical wrapper postcondition holds of any after-state with `wrapperAfter`'s memory and
return code — which both clobbers have. -/
theorem wrapper_historical_of_same_memory (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase resultBuffer : Nat) {after : State}
    (hmem : ∀ address, after.mem.get? address = wrapperAfter.mem.get? address)
    (hx10 : after.regs.get? x10 = some (BitVec.ofNat 64 0)) :
    postZesuDecodeRawHistorical calleeFrameEnv calleeFrameGlobals resultBuffer rep
      DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
      wrapperBefore after := by
  obtain ⟨⟨hbytes, -, -, -, -, hglobals⟩, -, -, -⟩ :=
    wrapper_run_satisfies_the_clauses rep inputBase resultBuffer
  obtain ⟨⟨hflag, hstatus⟩, hdisc, hstored⟩ := hglobals
  exact ⟨fun index hindex => (hmem _).trans (hbytes index hindex), calleeFrameEnv_codeIntact _,
    hx10, ⟨⟨(hmem _).trans hflag, fun index hi => (hmem _).trans (hstatus index hi)⟩,
      (hmem _).trans hdisc, hstored⟩⟩

/-- **The wrapper contract used to permit a decode that never came back to its caller.**

Same globals, same return code, same stack frame, and a normal machine — the old postcondition
cannot tell `wrapperRaClobber` from `wrapperAfter`, and neither can the platform clause. Only the
`x1` clause refuses it. -/
theorem wrapper_ra_clobber_permitted_historical (rep : ContainerRepresentation SszBridge.RawV4)
    (inputBase resultBuffer : Nat) :
    postZesuDecodeRawHistorical calleeFrameEnv calleeFrameGlobals resultBuffer rep
        DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
        wrapperBefore wrapperRaClobber ∧
      wrapperRaClobber.regs.get? x1 ≠ wrapperBefore.regs.get? x1 ∧
      NormalExecutionState wrapperRaClobber ∧
      ¬ postZesuDecodeRaw calleeFrameEnv calleeFrameGlobals resultBuffer rep
          DecoderGlobalsModel.fresh ⟨inputBase, ByteArray.empty⟩ (.error .invalidSsz)
          wrapperBefore wrapperRaClobber := by
  have hx10 : wrapperRaClobber.regs.get? x10 = some (BitVec.ofNat 64 0) := by
    show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert x1
      (BitVec.ofNat 64 5)).get? x10 = _
    simp [Std.ExtDHashMap.get?_insert]
  have hne : wrapperRaClobber.regs.get? x1 ≠ wrapperBefore.regs.get? x1 := by
    have hx1 : wrapperRaClobber.regs.get? x1 = some (BitVec.ofNat 64 5) := by
      show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert x1
        (BitVec.ofNat 64 5)).get? x1 = _
      simp
    rw [hx1, show wrapperBefore.regs.get? x1 = some calleeLink from normalRegs_x1 _]
    show ¬ (some (BitVec.ofNat 64 5) = some calleeLink)
    simp [calleeLink]
  have hnormal : NormalExecutionState wrapperRaClobber := by
    refine normalExecutionState_of_agree (before := wrapperBefore) ?_ (normalRegs_normal calleeLink)
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      · show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert x1
          (BitVec.ofNat 64 5)).get? _ = (normalRegs calleeLink).get? _
        simp [Std.ExtDHashMap.get?_insert]
  exact ⟨wrapper_historical_of_same_memory rep inputBase resultBuffer (fun _ => rfl) hx10,
    hne, hnormal,
    fun h => hne ((postZesuDecodeRaw_eq_historical_and_clauses _ _ _ _ _ _ _ _ _).mp h).2.1⟩

/-- **The wrapper contract used to permit a decode that came back with interrupts enabled**, refused
by the other clause. `ra` is intact here, so the `x1` clause is satisfied and the refutation can only
come from `NormalExecutionState after`. -/
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
  have hx10 : wrapperPlatformClobber.regs.get? x10 = some (BitVec.ofNat 64 0) := by
    show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert
      mie (1 : BitVec 64)).get? x10 = _
    simp [Std.ExtDHashMap.get?_insert]
  have hx1 : wrapperPlatformClobber.regs.get? x1 = wrapperBefore.regs.get? x1 := by
    show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert
      mie (1 : BitVec 64)).get? x1 = (normalRegs calleeLink).get? x1
    simp [Std.ExtDHashMap.get?_insert]
  have hnotnormal : ¬ NormalExecutionState wrapperPlatformClobber := by
    intro hnormal
    have hread := hnormal.2.2.2.2.1
    rw [show wrapperPlatformClobber.regs.get? mie = some (1 : BitVec 64) by
      show (((normalRegs calleeLink).insert x10 (BitVec.ofNat 64 0)).insert
        mie (1 : BitVec 64)).get? mie = _
      simp] at hread
    exact absurd hread (by simp)
  exact ⟨wrapper_historical_of_same_memory rep inputBase resultBuffer (fun _ => rfl) hx10,
    hx1, hnotnormal,
    fun h => hnotnormal ((postZesuDecodeRaw_eq_historical_and_clauses _ _ _ _ _ _ _ _ _).mp h).2.2⟩

/-! ### `CalleeFrame` is not the vocabulary for these clauses

`RiscV/Elfling/Contract.lean` defines `CalleeFrame preserved image before after :=
Agree preserved before after ∧ image.matchesMemory after.mem`, and it has **no call site tree-wide**.
The register half is right and is reused above (`normalExecutionState_of_agree` is stated with
`Agree`). The memory half is the retired defect: `image.matchesMemory` is the *full*-image match that
`DecoderEnvironment.CodeIntact` was corrected away from, because it pins every BSS byte to its static
zero and the decoder's globals are in the BSS.

So writing the `ra` clause as `CalleeFrame` would not have been a tidier spelling of the same thing —
it would have added a conjunct that the wrapper's own rejection path makes **false**, on a predicate
consumed only through an assumed hypothesis. That is the vacuous-root failure mode, and the theorem
below is it in one line: the same run that satisfies the strengthened `postZesuDecodeRaw` refutes
`CalleeFrame` at any register set whatsoever. -/

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
