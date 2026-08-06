import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.Catalog.Dispatch
import GeneratedProgram
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.MachineExecution.MemcpyProof

/-!
# Compiled contract for the emitted `memcpy`

The source contract says which bytes `memcpy` copies. Executing its RISC-V body additionally needs
facts about the configured machine: executable instruction fetches, retirement counters, address
translation, PMA permission, and non-MMIO data access. `MemcpyMachinePre` is that compiled-instance
interface. It strengthens only the entry binding; the source meaning, postcondition, and step bound
remain exactly `contractMemcpy`.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV
open BinaryFv.RiscV.Elfling BinaryFv.Zesu.Contracts
open BinaryFv.Zesu.Elflings.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- Machine facts needed to execute this particular emitted body. Runtime addresses and lengths
remain arguments; only the instruction placement is fixed by the generated function instance. -/
structure MemcpyMachinePre (env : DecoderEnvironment) (args : CopyArgs) (state : State) : Prop where
  normal : NormalExecutionState state
  entry : state.regs.get? PC = some (BitVec.ofNat 64 0x13eb8)
  returnAddress : ∃ address : BitVec 64,
    state.regs.get? x1 = some address ∧ Sail.BitVec.access address 1 = 0#1
  currentPrivilege : state.regs.get? cur_privilege = some Privilege.Machine
  mstatus : ∃ bits : BitVec 64,
    state.regs.get? mstatus = some bits ∧ _get_Mstatus_MPRV bits = 0#1
  mseccfg : ∃ bits : BitVec 64, state.regs.get? mseccfg = some bits
  inhibit : ∃ bits : BitVec 32,
    state.regs.get? mcountinhibit = some bits ∧ _get_Counterin_IR bits = 0#1
  counterConfig : ∃ bits : BitVec 64,
    state.regs.get? minstretcfg = some bits ∧ _get_CountSmcntrpmf_MINH bits = 0#1
  hartActive : state.regs.get? hart_state = some (.HART_ACTIVE ())
  retiredCounter : ∃ value, state.regs.get? minstret = some value
  imageIsZesu : env.image = Artifacts.programImage
  lengthFits : args.length < 2 ^ 64
  sourceAddressFits : args.source < 2 ^ 64
  destinationAddressFits : args.destination < 2 ^ 64
  sourceFits : args.source + args.length ≤ 2 ^ 64
  destinationFits : args.destination + args.length ≤ 2 ^ 64
  destinationNotFile : ∀ index, index < args.length →
    env.image.readFileByte? (args.destination + index) = none
  destinationNotAllocatorState : ∀ address, env.allocatorState address →
    address < args.destination ∨ args.destination + args.length ≤ address
  platform : AbstractPlatform state
  dataAccess : AbstractDataAccess (BitVec.ofNat 64 args.length)
    (BitVec.ofNat 64 args.destination) (BitVec.ofNat 64 args.source) state
  landingPad : AbstractElp state

/-- Machine frame retained at the generated `ret`, so a caller can execute that instruction. -/
structure MemcpyMachinePost (before after : State) : Prop where
  frame : StableAgree before after
  retiredCounter : RetiredCounterPresent after

/-- The source `memcpy` contract with the machine premises for this emitted body made explicit at
entry. Its semantic specification and exit binding are unchanged. -/
def compiledMemcpyContract (env : DecoderEnvironment) :
    FunctionInstanceContract CopyArgs (Except Contracts.DecodeError ByteArray) :=
  let source := (contractMemcpy env).toFunctionInstance
  { spec := source.spec
    binding :=
      { entry := fun args state => source.binding.entry args state ∧
          MemcpyMachinePre env args state
        exit := fun args result before after => source.binding.exit args result before after ∧
          MemcpyMachinePost before after
        stepBound := source.binding.stepBound } }

theorem compiledMemcpyContract_spec (env : DecoderEnvironment) :
    (compiledMemcpyContract env).spec = (contractMemcpy env).toFunctionInstance.spec := rfl

theorem compiledMemcpyContract_exit (env : DecoderEnvironment) :
    (compiledMemcpyContract env).binding.exit =
      fun args result before after =>
        (contractMemcpy env).toFunctionInstance.binding.exit args result before after ∧
          MemcpyMachinePost before after := rfl

theorem compiledMemcpyContract_stepBound (env : DecoderEnvironment) :
    (compiledMemcpyContract env).binding.stepBound =
      (contractMemcpy env).toFunctionInstance.binding.stepBound := rfl

/-- The closed correctness statement Level 2 requires for the selected emitted body. -/
abbrev CompiledMemcpyInstanceContract : Prop :=
  (compiledMemcpyContract canonicalContractParams.env).ImplementsFunctionInstance
    functionInstance_memcpy
    (functionInstanceReachedPcs generatedProgram functionInstance_memcpy)
    (functionInstanceEntryWord functionInstance_memcpy)
    (functionInstanceExitPred functionInstance_memcpy)

/-- The exact typed summary consumed at each generated call site. -/
def compiledMemcpySummary (child : FunctionInstanceId) (fromStep used : Nat)
    (before after : State) : Prop :=
  child = functionInstance_memcpyId ∧
    (compiledMemcpyContract canonicalContractParams.env).summary
      (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
      (functionInstanceExitPred functionInstance_memcpy)
      (functionInstanceEntryWord functionInstance_memcpy) fromStep used before after

/-- Applying the closed compiled contract yields the exact caller-side summary. -/
theorem compiledMemcpySummary_of_contract (contract : CompiledMemcpyInstanceContract)
    (args : CopyArgs) (fromStep : Nat) (before : State)
    (entry : (compiledMemcpyContract canonicalContractParams.env).binding.entry args before) :
    ∃ used after,
      used ≤ (compiledMemcpyContract canonicalContractParams.env).binding.stepBound args ∧
      compiledMemcpySummary functionInstance_memcpyId fromStep used before after := by
  obtain ⟨used, after, bound, trace, post⟩ := contract args fromStep before entry
  exact ⟨used, after, bound, rfl, args, entry, bound, trace, post⟩

/-! ## Connecting the Sail loop result to the source contract -/

private theorem memcpy_entry_word :
    functionInstanceEntryWord functionInstance_memcpy = BitVec.ofNat 64 0x13eb8 := by
  native_decide

private theorem memcpy_exit_pred (pc : BitVec 64) :
    functionInstanceExitPred functionInstance_memcpy pc ↔ pc = BitVec.ofNat 64 0x13ec0 := by
  simp only [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa using h
  · rintro rfl
    native_decide

private theorem memcpy_body_pc_in_generated_region (pc : BitVec 64) (h : IsBodyPc pc) :
    functionInstanceExecutionPcs generatedProgram functionInstance_memcpy pc := by
  left
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨{ start := 81592, size := 36 }, ?_, ?_, ?_⟩ <;>
    simp [functionInstance_memcpy, BinaryFv.Binary.AddressRange.stop]

/-- A runtime window address reads back as plain arithmetic: `(ofNat base + ofNat index).toNat` is
`base + index` whenever the whole window `[base, base + limit)` fits the address space.  The
source/destination index conversions below need exactly this six times, each previously spelled as a
`windowAddr_toNat` rewrite plus a separate `toNat_ofNat` fact and a separate in-range side lemma. -/
private theorem windowNat {base limit index : Nat} (baseFits : base < 2 ^ 64)
    (windowFits : base + limit ≤ 2 ^ 64) (inBounds : index < limit) :
    (BitVec.ofNat 64 base + BitVec.ofNat 64 index).toNat = base + index := by
  have hbase : (BitVec.ofNat 64 base).toNat = base := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseFits]
  rw [windowAddr_toNat _ _ (by rw [hbase]; omega), hbase]

private def copySourceByte (contents : ByteArray) (index : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (contents.get! index).toNat

private theorem copySourceByte_eq (contents : ByteArray) (index : Nat)
    (inBounds : index < contents.size) :
    copySourceByte contents index = BitVec.ofNat 8 (contents[index]'inBounds).toNat := by
  simp only [copySourceByte]
  show BitVec.ofNat 8 (contents.data[index]!).toNat = _
  rw [getElem!_pos contents.data index inBounds]
  rfl

/-- The exact Sail run already proves the source-level `memcpy` postcondition. This theorem stops
at the generated `ret` exit, so it is the semantic half of the compiled-instance proof; only the
conversion of its exact trace to `EnteredFunctionTrace` remains separate. -/
theorem memcpy_body_satisfies_source_post (args : CopyArgs) (fromStep : Nat) (state : State)
    (sourcePre : (contractMemcpy canonicalContractParams.env).pre args state)
    (machine : MemcpyMachinePre canonicalContractParams.env args state) :
    ∃ count final,
      count = 1 + args.length * 7 + 1 ∧
      Trace fromStep count state final ∧
      EnteredFunctionTrace
        (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
        (functionInstanceExitPred functionInstance_memcpy)
        (functionInstanceEntryWord functionInstance_memcpy) fromStep count state final ∧
      final.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) ∧
      (contractMemcpy canonicalContractParams.env).post args
        ((contractMemcpy canonicalContractParams.env).meaning args) state final ∧
      MemcpyMachinePost state final := by
  rcases sourcePre with ⟨⟨sourceMemory, contentsLength, code, destinationRead, sourceRead,
    lengthRead⟩, nonoverlap⟩
  rcases machine.returnAddress with ⟨returnAddress, returnRead, returnAligned⟩
  rcases machine.mstatus with ⟨mstatusBits, mstatusRead, mprvDisabled⟩
  rcases machine.mseccfg with ⟨mseccfgBits, mseccfgRead⟩
  rcases machine.inhibit with ⟨inhibit, inhibitRead, retirementEnabled⟩
  rcases machine.counterConfig with
    ⟨counterConfig, counterConfigRead, machineCounterEnabled⟩
  have destinationNat : (BitVec.ofNat 64 args.destination).toNat = args.destination := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt machine.destinationAddressFits]
  have sourceNat : (BitVec.ofNat 64 args.source).toNat = args.source := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt machine.sourceAddressFits]
  have lengthNat : (BitVec.ofNat 64 args.length).toNat = args.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt machine.lengthFits]
  have sourceBytes : ∀ index : Nat, index < (BitVec.ofNat 64 args.length).toNat →
      state.mem.get? (BitVec.ofNat 64 args.source + BitVec.ofNat 64 index).toNat =
        some (copySourceByte args.contents index) := by
    intro index inBounds
    rw [lengthNat] at inBounds
    have contentsBounds : index < args.contents.size := contentsLength ▸ inBounds
    rw [windowNat machine.sourceAddressFits machine.sourceFits inBounds,
      copySourceByte_eq args.contents index contentsBounds]
    exact sourceMemory index contentsBounds
  have destinationNotFile : ∀ index : Nat,
      index < (BitVec.ofNat 64 args.length).toNat →
      canonicalContractParams.env.image.readFileByte?
        (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 index).toNat = none := by
    intro index inBounds
    rw [lengthNat] at inBounds
    rw [windowNat machine.destinationAddressFits machine.destinationFits inBounds]
    exact machine.destinationNotFile index inBounds
  have disjoint : ∀ j k : Nat,
      j < (BitVec.ofNat 64 args.length).toNat →
      k < (BitVec.ofNat 64 args.length).toNat →
      (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 j).toNat ≠
        (BitVec.ofNat 64 args.source + BitVec.ofNat 64 k).toNat := by
    intro j k jBounds kBounds equal
    rw [lengthNat] at jBounds kBounds
    rw [windowNat machine.destinationAddressFits machine.destinationFits jBounds,
      windowNat machine.sourceAddressFits machine.sourceFits kBounds] at equal
    rcases nonoverlap with before | after <;> omega
  have destinationFits : (BitVec.ofNat 64 args.destination).toNat
      + (BitVec.ofNat 64 args.length).toNat ≤ 2 ^ 64 := by
    simpa [destinationNat, lengthNat] using machine.destinationFits
  obtain ⟨final, run, confined, atExit, copied, _, _, _, _, codeFinal, stable, stackPreserved,
    frame, sourcePreserved, finalCounter⟩ :=
    memcpy_body (BitVec.ofNat 64 args.destination) (BitVec.ofNat 64 args.source)
      (BitVec.ofNat 64 args.length) returnAddress canonicalContractParams.env.image
      mseccfgBits mstatusBits inhibit counterConfig (copySourceByte args.contents) fromStep state
      machine.entry
      destinationRead sourceRead lengthRead returnRead machine.currentPrivilege mstatusRead
      mprvDisabled mseccfgRead machine.hartActive inhibitRead retirementEnabled counterConfigRead
      machineCounterEnabled machine.retiredCounter machine.imageIsZesu code sourceBytes
      (by simpa [lengthNat] using machine.lengthFits)
      (by simpa [sourceNat, lengthNat] using machine.sourceFits)
      destinationFits destinationNotFile disjoint machine.platform machine.dataAccess
      machine.landingPad
  -- Every memory-frame consequence below reads the same frame off outside the same window.
  have unchanged := frame.mem_unchanged_outside destinationFits
  have noAllocation : canonicalContractParams.env.NoAllocation state final :=
    fun address allocatorAddress => unchanged address
      (by simpa [destinationNat, lengthNat] using
        machine.destinationNotAllocatorState address allocatorAddress)
  have writesOnly : canonicalContractParams.env.WritesOnlyWithinOwnRecord
      args.destination args.length state final := by
    intro address outside
    apply unchanged address
    have notRange : ¬ Contracts.range args.destination args.length address :=
      fun inRange => outside (Or.inl (Or.inl inRange))
    simp only [Contracts.range] at notRange
    omega
  have exactFrame : CopyDestinationFrame args state final := fun address outside =>
    unchanged address (by simpa [destinationNat, lengthNat] using outside)
  have destinationMemory : MemoryRepresentation.MemoryBytes final args.destination
      args.contents := by
    intro index inBounds
    have argsBounds : index < args.length := by simpa [contentsLength] using inBounds
    have copiedIndex := copied index (by rw [lengthNat]; exact argsBounds)
    rw [windowNat machine.destinationAddressFits machine.destinationFits argsBounds,
      copySourceByte_eq args.contents index inBounds] at copiedIndex
    exact copiedIndex
  have sourceMemoryFinal : MemoryRepresentation.MemoryBytes final args.source args.contents := by
    intro index inBounds
    have argsBounds : index < args.length := by simpa [contentsLength] using inBounds
    have preserved := sourcePreserved index (by rw [lengthNat]; exact argsBounds)
    rw [windowNat machine.sourceAddressFits machine.sourceFits argsBounds] at preserved
    rw [preserved]
    exact sourceMemory index inBounds
  have generatedTrace : FunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
      (functionInstanceExitPred functionInstance_memcpy)
      fromStep (1 + args.length * 7 + 1) state final := by
    have widened := confined.mono_region memcpy_body_pc_in_generated_region
    have exitEq : (fun pc : BitVec 64 => pc = BitVec.ofNat 64 0x13ec0) =
        functionInstanceExitPred functionInstance_memcpy := by
      funext pc
      exact propext (memcpy_exit_pred pc).symm
    rw [exitEq] at widened
    simpa [lengthNat] using widened
  have entered : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
      (functionInstanceExitPred functionInstance_memcpy)
      (functionInstanceEntryWord functionInstance_memcpy)
      fromStep (1 + args.length * 7 + 1) state final := by
    refine ⟨?_, memcpy_body_pc_in_generated_region _ ?_, ?_, generatedTrace⟩
    · simpa [memcpy_entry_word] using machine.entry
    · rw [memcpy_entry_word]
      simp [IsBodyPc]
    · rw [memcpy_exit_pred]
      decide
  refine ⟨1 + args.length * 7 + 1, final, rfl, ?_, entered, atExit, ?_, ⟨stable, finalCounter⟩⟩
  · simpa [lengthNat] using run
  · refine ⟨?_, noAllocation, writesOnly, exactFrame, sourceMemoryFinal, ?_⟩
    · simpa [DecoderEnvironment.CodeIntact, canonicalContractParams,
        canonicalEnvironment] using codeFinal
    · simpa [meaningCopy] using destinationMemory

/-- The emitted `memcpy` instance satisfies its compiled contract. Every owned instruction is
executed by the generated Sail semantics; the runtime loop is discharged by induction. -/
theorem compiledMemcpyInstanceContract_proved : CompiledMemcpyInstanceContract := by
  intro args fromStep state entry
  rcases entry with ⟨sourcePre, machinePre⟩
  obtain ⟨count, final, countEq, _, entered, _, post, machinePost⟩ :=
    memcpy_body_satisfies_source_post args fromStep state sourcePre machinePre
  refine ⟨count, final, ?_, entered, ?_⟩
  · rw [countEq]
    change 1 + args.length * 7 + 1 ≤ 64 + 8 * args.length
    omega
  · exact ⟨post, machinePost⟩

def memcpyReturnAfter (returnPc : BitVec 64) (state : State) (retired : BitVec 64) : State :=
  tryStepControlFlowAfterRetired
    (controlFlowJumpState (tryStepControlFlowAfterIncrement state)
      (BitVec.ofNat 64 0x13ec0) returnPc)
    returnPc retired

/-- Execute the emitted `memcpy` instance's real `ret` from its proved machine postcondition. -/
theorem memcpy_return_step (stepNo : Nat) (args : CopyArgs) (returnPc : BitVec 64)
    (childEntry childExit : State) {childFrom childUsed : Nat}
    (returnTarget : Sail.BitVec.update returnPc 0 0#1 = returnPc)
    (returnBit1 : Sail.BitVec.access returnPc 1 = 0#1)
    (childPre : (compiledMemcpyContract canonicalContractParams.env).binding.entry args childEntry)
    (childTrace : EnteredFunctionTrace
      (functionInstanceExecutionPcs generatedProgram functionInstance_memcpy)
      (functionInstanceExitPred functionInstance_memcpy)
      (functionInstanceEntryWord functionInstance_memcpy)
      childFrom childUsed childEntry childExit)
    (entryLink : childEntry.regs.get? x1 = some returnPc)
    (childPost : (compiledMemcpyContract canonicalContractParams.env).binding.exit args
      ((compiledMemcpyContract canonicalContractParams.env).spec.meaning args)
      childEntry childExit) :
    ∃ retired,
      Runs (try_step stepNo false) childExit (memcpyReturnAfter returnPc childExit retired) false ∧
      (memcpyReturnAfter returnPc childExit retired).regs.get? PC = some returnPc := by
  rcases childPre with ⟨sourcePre, machine⟩
  rcases childPost with ⟨sourcePost, machinePost⟩
  rcases sourcePost with ⟨code, -, -, -, -, -⟩
  obtain ⟨exitPc, atExit, isExit⟩ := childTrace.trace.final_at_exit
  have exitPcEq : exitPc = BitVec.ofNat 64 0x13ec0 := by
    apply BitVec.eq_of_toNat_eq
    simpa [functionInstanceExitPred, FunctionInstance.isExit, functionInstance_memcpy] using isExit
  subst exitPc
  have stableAtExit : StableAgree childEntry childExit := machinePost.frame
  have loaded : Artifacts.programImage.fileBytesMatchMemory childExit.mem := by
    unfold DecoderEnvironment.CodeIntact at code
    rw [machine.imageIsZesu] at code
    exact code
  have fetchBytes : FetchBytesAt (tryStepControlFlowAfterIncrement childExit)
      (BitVec.ofNat 64 0x13ec0) 0x67#8 0x80#8 0x00#8 0x00#8 :=
    BinaryFv.Binary.ProgramImage.fetchBytesAt_of_file_bytes Artifacts.programImage
      (tryStepControlFlowAfterIncrement childExit) 0x13ec0 (by decide)
      (by simpa [tryStepControlFlowAfterIncrement] using loaded)
      0x67 0x80 0x00 0x00
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨mseccfgBits, mseccfgReadEntry⟩ := machine.mseccfg
  have stepPlatform : StepPlatform childExit (BitVec.ofNat 64 0x13ec0)
      0x67#8 0x80#8 0x00#8 0x00#8 mseccfgBits :=
    mkStepPlatform childExit mseccfgBits (BitVec.ofNat 64 0x13ec0)
      0x67#8 0x80#8 0x00#8 0x00#8 machine.platform machine.currentPrivilege
      mseccfgReadEntry stableAtExit (by
        change (childExit.regs.insert minstret_increment true).get? PC = _
        rw [Std.ExtDHashMap.get?_insert]
        simp [atExit])
      (by simp [IsBodyPc]) fetchBytes
  obtain ⟨retired, retiredRead⟩ := machinePost.retiredCounter
  have hartRead : childExit.regs.get? hart_state = some (.HART_ACTIVE ()) :=
    (stableAtExit hart_state (by simp [NonW])).trans machine.hartActive
  obtain ⟨inhibit, inhibitReadEntry, retirementEnabled⟩ := machine.inhibit
  have inhibitRead : childExit.regs.get? mcountinhibit = some inhibit :=
    (stableAtExit mcountinhibit (by simp [NonW])).trans inhibitReadEntry
  obtain ⟨config, configReadEntry, machineEnabled⟩ := machine.counterConfig
  have configRead : childExit.regs.get? minstretcfg = some config :=
    (stableAtExit minstretcfg (by simp [NonW])).trans configReadEntry
  have stepCounters : StepCounters childExit retired inhibit config :=
    ⟨hartRead, inhibitRead, configRead, retirementEnabled, machineEnabled, retiredRead⟩
  have exitLink : childExit.regs.get? x1 = some returnPc :=
    (stableAtExit x1 (by simp [NonW])).trans entryLink
  let executeState := coreControlFlowNextState (tryStepControlFlowAfterIncrement childExit)
    (BitVec.ofNat 64 0x13ec0)
  have w2 : WritesOnlyRegs stepBookkeeping childExit executeState :=
    stepPremiseState_writes childExit (BitVec.ofNat 64 0x13ec0)
  have executeStable : StableAgree childExit executeState := w2.agree nonW_disjoint_bookkeeping
  have landingPadAtExit : AbstractElp childExit := machine.landingPad.mono stableAtExit
  have helpElp : Runs (update_elp_state (.Regidx 1#5)) executeState executeState () :=
    landingPadAtExit executeState (.Regidx 1#5) rfl executeStable
  have linkRead : executeState.regs.get? nextPC = some (BitVec.ofNat 64 0x13ec4) := by
    change ((tryStepControlFlowAfterIncrement childExit).regs.insert nextPC
      (Sail.BitVec.addInt (BitVec.ofNat 64 0x13ec0) 4)).get? nextPC = _
    rw [Std.ExtDHashMap.get?_insert]
    simp
    decide
  have sourceRead : executeState.regs.get? x1 = some returnPc := by grind
  obtain ⟨misaBits, misaReadEntry, misaBit⟩ : ∃ misaBits,
      childEntry.regs.get? misa = some misaBits ∧ Sail.BitVec.access misaBits 12 = 1#1 := by
    have normalMisa := machine.normal.2.2.2.2.2.2.2.2.2.2.2
    match read : childEntry.regs.get? misa with
    | none => simp [read] at normalMisa
    | some bits => exact ⟨bits, rfl, by simpa [read] using normalMisa⟩
  have misaRead : childExit.regs.get? misa = some misaBits := by
    calc
      childExit.regs.get? misa = childEntry.regs.get? misa :=
        stableAtExit misa (by simp [NonW])
      _ = some misaBits := misaReadEntry
  have misaExecute : executeState.regs.get? misa = some misaBits := by grind
  have retRun := memcpy_step_ret stepNo childExit returnPc retired mseccfgBits misaBits inhibit config
    stepPlatform stepCounters (rX_bits_run_x1 executeState _ sourceRead) returnBit1 helpElp misaExecute
  refine ⟨retired, ?_, ?_⟩
  · simpa [memcpyReturnAfter, returnTarget] using retRun
  · simp [memcpyReturnAfter, tryStepControlFlowAfterRetired, tryStepControlFlowAfterTick,
      Std.ExtDHashMap.get?_insert]

end BinaryFv.Zesu.MachineExecution
