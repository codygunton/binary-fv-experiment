import BinaryFv.Zesu.Contracts.CanonicalParams
import BinaryFv.Zesu.Contracts.Catalog.Dispatch
import GeneratedProgram
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

/-- The source `memcpy` contract with the machine premises for this emitted body made explicit at
entry. Its semantic specification and exit binding are unchanged. -/
def compiledMemcpyContract (env : DecoderEnvironment) :
    FunctionInstanceContract CopyArgs (Except Contracts.DecodeError ByteArray) :=
  let source := (contractMemcpy env).toFunctionInstance
  { spec := source.spec
    binding :=
      { entry := fun args state => source.binding.entry args state ∧
          MemcpyMachinePre env args state
        exit := source.binding.exit
        stepBound := source.binding.stepBound } }

theorem compiledMemcpyContract_spec (env : DecoderEnvironment) :
    (compiledMemcpyContract env).spec = (contractMemcpy env).toFunctionInstance.spec := rfl

theorem compiledMemcpyContract_exit (env : DecoderEnvironment) :
    (compiledMemcpyContract env).binding.exit =
      (contractMemcpy env).toFunctionInstance.binding.exit := rfl

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
      final.regs.get? PC = some (BitVec.ofNat 64 0x13ec0) ∧
      (contractMemcpy canonicalContractParams.env).post args
        ((contractMemcpy canonicalContractParams.env).meaning args) state final := by
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
  have sourceIndexFits (index : Nat) (inBounds : index < args.length) :
      (BitVec.ofNat 64 args.source).toNat + index < 2 ^ 64 := by
    have fits := machine.sourceFits
    rw [sourceNat]
    omega
  have destinationIndexFits (index : Nat) (inBounds : index < args.length) :
      (BitVec.ofNat 64 args.destination).toNat + index < 2 ^ 64 := by
    have fits := machine.destinationFits
    rw [destinationNat]
    omega
  have sourceBytes : ∀ index : Nat, index < (BitVec.ofNat 64 args.length).toNat →
      state.mem.get? (BitVec.ofNat 64 args.source + BitVec.ofNat 64 index).toNat =
        some (copySourceByte args.contents index) := by
    intro index inBounds
    rw [lengthNat] at inBounds
    have contentsBounds : index < args.contents.size := contentsLength ▸ inBounds
    rw [windowAddr_toNat (BitVec.ofNat 64 args.source) index
      (sourceIndexFits index inBounds),
      sourceNat, copySourceByte_eq args.contents index contentsBounds]
    exact sourceMemory index contentsBounds
  have destinationNotFile : ∀ index : Nat,
      index < (BitVec.ofNat 64 args.length).toNat →
      canonicalContractParams.env.image.readFileByte?
        (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 index).toNat = none := by
    intro index inBounds
    rw [lengthNat] at inBounds
    rw [windowAddr_toNat (BitVec.ofNat 64 args.destination) index
      (destinationIndexFits index inBounds), destinationNat]
    exact machine.destinationNotFile index inBounds
  have disjoint : ∀ j k : Nat,
      j < (BitVec.ofNat 64 args.length).toNat →
      k < (BitVec.ofNat 64 args.length).toNat →
      (BitVec.ofNat 64 args.destination + BitVec.ofNat 64 j).toNat ≠
        (BitVec.ofNat 64 args.source + BitVec.ofNat 64 k).toNat := by
    intro j k jBounds kBounds equal
    rw [lengthNat] at jBounds kBounds
    rw [windowAddr_toNat (BitVec.ofNat 64 args.destination) j
      (destinationIndexFits j jBounds), destinationNat,
      windowAddr_toNat (BitVec.ofNat 64 args.source) k (sourceIndexFits k kBounds),
      sourceNat] at equal
    rcases nonoverlap with before | after <;> omega
  obtain ⟨final, run, atExit, copied, _, _, _, _, codeFinal, _, stackPreserved, frame,
    _⟩ :=
    memcpy_body (BitVec.ofNat 64 args.destination) (BitVec.ofNat 64 args.source)
      (BitVec.ofNat 64 args.length) returnAddress canonicalContractParams.env.image
      mseccfgBits mstatusBits inhibit counterConfig (copySourceByte args.contents) fromStep state
      machine.entry
      destinationRead sourceRead lengthRead returnRead machine.currentPrivilege mstatusRead
      mprvDisabled mseccfgRead machine.hartActive inhibitRead retirementEnabled counterConfigRead
      machineCounterEnabled machine.retiredCounter machine.imageIsZesu code sourceBytes
      (by simpa [lengthNat] using machine.lengthFits)
      (by simpa [sourceNat, lengthNat] using machine.sourceFits)
      (by simpa [destinationNat, lengthNat] using machine.destinationFits)
      destinationNotFile disjoint machine.platform machine.dataAccess machine.landingPad
  have noAllocation : canonicalContractParams.env.NoAllocation state final := by
    intro address allocatorAddress
    exact frame.mem_unchanged_outside (by simpa [destinationNat, lengthNat] using
      machine.destinationFits) address
        (by simpa [destinationNat, lengthNat] using
          machine.destinationNotAllocatorState address allocatorAddress)
  have writesOnly : canonicalContractParams.env.WritesOnlyWithinOwnRecord
      args.destination args.length state final := by
    intro address outside
    apply frame.mem_unchanged_outside (by simpa [destinationNat, lengthNat] using
      machine.destinationFits) address
    have notRange : ¬ Contracts.range args.destination args.length address := by
      intro inRange
      exact outside (Or.inl (Or.inl inRange))
    simp only [Contracts.range] at notRange
    omega
  have destinationMemory : MemoryRepresentation.MemoryBytes final args.destination
      args.contents := by
    intro index inBounds
    have argsBounds : index < args.length := by simpa [contentsLength] using inBounds
    have copiedIndex := copied index (by rw [lengthNat]; exact argsBounds)
    rw [windowAddr_toNat (BitVec.ofNat 64 args.destination) index
      (destinationIndexFits index argsBounds), destinationNat,
      copySourceByte_eq args.contents index inBounds] at copiedIndex
    exact copiedIndex
  refine ⟨1 + args.length * 7 + 1, final, rfl, ?_, atExit, ?_⟩
  · simpa [lengthNat] using run
  · refine ⟨?_, noAllocation, writesOnly, ?_⟩
    · simpa [DecoderEnvironment.CodeIntact, canonicalContractParams,
        canonicalEnvironment] using codeFinal
    · simpa [meaningCopy] using destinationMemory

end BinaryFv.Zesu.MachineExecution
