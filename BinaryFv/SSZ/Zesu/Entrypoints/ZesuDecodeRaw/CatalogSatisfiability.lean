import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.EntryBinding
import BinaryFv.SSZ.Zesu.Elfling.NonLocalPremises

/-!
# No cataloged precondition is impossible

`Implements` is vacuously true for a contract whose entry predicate no state satisfies, and Sail
memory is sparse enough that writing such a predicate by accident is easy — an entry that forgets to
materialize an address the routine reads is contradictory, not merely strict. Every cataloged routine
therefore carries a companion `PreSatisfiable` claim, and `catalogSatisfiability` is all of them at
once. This module discharges it.

The load-bearing clause is `CodeIntact`: it demands roughly twenty kilobytes of file-backed image
bytes present in memory, so a witness state cannot be written down. It does not have to be. The
runner already builds one — `buildZesuEntryState_entry_binding` proves the constructed state
satisfies the exported wrapper's entry binding, which contains `CodeIntact` and the complete fresh
decoder-globals representation. Every other cataloged precondition is that same memory content plus
some ABI registers, and registers are the one part of the state that can be set by hand.

So the proof has exactly two moving parts: one state obtained from the builder, and a register
overwrite that provably cannot disturb it. Note what is *not* here — no execution, no trace, and no
appeal to any routine's correctness. Satisfiability is a claim about the contract's entry predicate
alone, and proving it any other way would make the anti-vacuity argument circular.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open BinaryFv.SSZ.Zesu.Elfling

/-! ## One state, from the builder -/

/-- **A state with the canonical memory content every precondition needs.**

Both clauses come straight from the entry-binding theorem at the empty input: the file-backed image
is intact, and the three private decoder globals represent a fresh decoder. Nothing else about the
state is claimed, and nothing else is needed — every remaining precondition clause is either about
registers or about a `MemoryBytes` window the witness gets to choose empty. -/
theorem exists_canonical_memory_state :
    ∃ state : State,
      canonicalEnvironment.CodeIntact state ∧
        DecoderGlobalsRep canonicalDecoderGlobalsLayout canonicalRepRawV4
          canonicalRunnerLayout.inputBase ByteArray.empty canonicalResultBuffer
          DecoderGlobalsModel.fresh state := by
  obtain ⟨state, _, binding⟩ := buildZesuEntryState_entry_binding ByteArray.empty
  exact ⟨state, binding.2.1, binding.2.2.2.2⟩

/-! ## Registers, set by hand

Every precondition below constrains at most the four ABI argument registers. Overwriting them is a
record update on `regs`, which memory predicates cannot see. -/

/-- The witness state with the four ABI argument registers holding chosen values. -/
def withArgumentRegisters (state : State) (a0 a1 a2 a3 : Nat) : State :=
  { state with
      regs := (((state.regs.insert x10 (BitVec.ofNat 64 a0)).insert x11 (BitVec.ofNat 64 a1)).insert
        x12 (BitVec.ofNat 64 a2)).insert x13 (BitVec.ofNat 64 a3) }

@[simp] theorem withArgumentRegisters_mem (state : State) (a0 a1 a2 a3 : Nat) :
    (withArgumentRegisters state a0 a1 a2 a3).mem = state.mem := rfl

@[simp] theorem withArgumentRegisters_x10 (state : State) (a0 a1 a2 a3 : Nat) :
    (withArgumentRegisters state a0 a1 a2 a3).regs.get? x10 = some (BitVec.ofNat 64 a0) := by
  simp [withArgumentRegisters, Std.ExtDHashMap.get?_insert]

@[simp] theorem withArgumentRegisters_x11 (state : State) (a0 a1 a2 a3 : Nat) :
    (withArgumentRegisters state a0 a1 a2 a3).regs.get? x11 = some (BitVec.ofNat 64 a1) := by
  simp [withArgumentRegisters, Std.ExtDHashMap.get?_insert]

@[simp] theorem withArgumentRegisters_x12 (state : State) (a0 a1 a2 a3 : Nat) :
    (withArgumentRegisters state a0 a1 a2 a3).regs.get? x12 = some (BitVec.ofNat 64 a2) := by
  simp [withArgumentRegisters, Std.ExtDHashMap.get?_insert]

@[simp] theorem withArgumentRegisters_x13 (state : State) (a0 a1 a2 a3 : Nat) :
    (withArgumentRegisters state a0 a1 a2 a3).regs.get? x13 = some (BitVec.ofNat 64 a3) := by
  simp [withArgumentRegisters, Std.ExtDHashMap.get?_insert]

/-- A memory-only predicate cannot tell the argument registers were overwritten. -/
theorem codeIntact_withArgumentRegisters {state : State} {a0 a1 a2 a3 : Nat}
    (h : canonicalEnvironment.CodeIntact state) :
    canonicalEnvironment.CodeIntact (withArgumentRegisters state a0 a1 a2 a3) := h

/-- An empty `MemoryBytes` window is satisfied by every state, at every base. This is what lets each
witness pick the empty input and leave the memory content to `CodeIntact`. -/
theorem memoryBytes_empty (state : State) (base : Nat) :
    MemoryBytes state base ByteArray.empty := by
  intro index h
  exact absurd h (by simp)

/-! ## The witness

One state, named once. Every routine below is satisfied by it with its argument registers set; no
routine gets a state built to suit it. -/

/-- The state every satisfiability witness below is built from. -/
noncomputable def canonicalWitnessState : State := exists_canonical_memory_state.choose

theorem canonicalWitnessState_codeIntact :
    canonicalEnvironment.CodeIntact canonicalWitnessState :=
  exists_canonical_memory_state.choose_spec.1

theorem canonicalWitnessState_globals :
    DecoderGlobalsRep canonicalDecoderGlobalsLayout canonicalRepRawV4
      canonicalRunnerLayout.inputBase ByteArray.empty canonicalResultBuffer
      DecoderGlobalsModel.fresh canonicalWitnessState :=
  exists_canonical_memory_state.choose_spec.2

/-- The witness with all four argument registers zeroed. Every precondition below is stated at the
empty input based at address zero, so zero is the value each of them wants. -/
noncomputable def zeroArgumentWitness : State := withArgumentRegisters canonicalWitnessState 0 0 0 0

theorem zeroArgumentWitness_codeIntact :
    canonicalEnvironment.CodeIntact zeroArgumentWitness :=
  codeIntact_withArgumentRegisters canonicalWitnessState_codeIntact

/-! ## The precondition shapes

Ten shapes cover the thirty-eight cataloged routines. Each is discharged once here and then reused,
so a change to any shared precondition surfaces as one failure rather than a dozen. -/

theorem readAt_satisfiable :
    preReadAt canonicalEnvironment { base := 0, bytes := ByteArray.empty, offset := 0 }
      zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem slice_satisfiable :
    preSlice canonicalEnvironment { base := 0, bytes := ByteArray.empty } zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness]⟩

theorem sliceToResult_satisfiable :
    preSliceToResult canonicalEnvironment
      { base := 0, bytes := ByteArray.empty, resultBase := 0 } zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem canonicalOffsets_satisfiable :
    preCanonicalOffsets canonicalEnvironment
      { base := 0, bytes := ByteArray.empty, fixedSize := 0, offsets := [] } zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem collection_satisfiable :
    preCollection canonicalEnvironment
      { base := 0, bytes := ByteArray.empty, allocatorBase := 0, resultBase := 0 }
      zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem container_satisfiable :
    preContainer canonicalEnvironment
      { base := 0, bytes := ByteArray.empty, allocatorBase := 0, resultBase := 0 }
      zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem entry_satisfiable :
    preEntry canonicalEnvironment
      { base := 0, bytes := ByteArray.empty, allocatorBase := 0, resultBase := 0 }
      zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem alloc_satisfiable :
    preAlloc canonicalEnvironment { allocatorBase := 0, bytes := 0, alignment := 0 }
      zeroArgumentWitness :=
  ⟨zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

theorem copy_satisfiable :
    preCopy canonicalEnvironment
      { destination := 0, source := 0, length := 0, contents := ByteArray.empty }
      zeroArgumentWitness :=
  ⟨memoryBytes_empty _ _, rfl, zeroArgumentWitness_codeIntact, by simp [zeroArgumentWitness],
    by simp [zeroArgumentWitness], by simp [zeroArgumentWitness]⟩

/-! ## The thirty-eight routines

Each is `ValidEnvironment → PreSatisfiable`. The antecedent is genuinely unused here — the witness
carries a real image rather than a layout-shaped assumption — but it stays in the statement because
it is what makes the obligation meaningful for a *hypothetical* environment. -/

theorem satisfiable_zesuDecodeRaw :
    satisfiableZesuDecodeRaw canonicalEnvironment canonicalDecoderGlobalsLayout
      canonicalResultBuffer canonicalRepRawV4 := fun _ => by
  obtain ⟨state, _, binding⟩ := buildZesuEntryState_entry_binding ByteArray.empty
  exact ⟨⟨canonicalRunnerLayout.inputBase, ByteArray.empty⟩, state, binding⟩

theorem satisfiable_decodeRaw : satisfiableDecodeRaw canonicalEnvironment canonicalRepRawV4 :=
  fun _ => ⟨_, _, entry_satisfiable⟩

theorem satisfiable_decode : satisfiableDecode canonicalEnvironment canonicalRepRawV4 :=
  fun _ => ⟨_, _, entry_satisfiable⟩

theorem satisfiable_newPayloadRequest :
    satisfiableNewPayloadRequest canonicalEnvironment canonicalRepNewPayloadRequest :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_executionPayload :
    satisfiableExecutionPayload canonicalEnvironment canonicalRepExecutionPayload :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_executionRequests :
    satisfiableExecutionRequests canonicalEnvironment canonicalRepExecutionRequests :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_executionWitness :
    satisfiableExecutionWitness canonicalEnvironment canonicalRepExecutionWitness :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_chainConfig :
    satisfiableChainConfig canonicalEnvironment canonicalRepChainConfig :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_forkConfig : satisfiableForkConfig canonicalEnvironment canonicalRepForkConfig :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_forkActivation :
    satisfiableForkActivation canonicalEnvironment canonicalRepForkActivation :=
  fun _ => ⟨_, _, container_satisfiable⟩

theorem satisfiable_optionalU64 : satisfiableOptionalU64 canonicalEnvironment :=
  fun _ => ⟨_, _, sliceToResult_satisfiable⟩

theorem satisfiable_optionalBlobSchedule : satisfiableOptionalBlobSchedule canonicalEnvironment :=
  fun _ => ⟨_, _, sliceToResult_satisfiable⟩

theorem satisfiable_versionedHashes : satisfiableVersionedHashes canonicalEnvironment :=
  fun _ => ⟨_, _, collection_satisfiable⟩

theorem satisfiable_withdrawals : satisfiableWithdrawals canonicalEnvironment :=
  fun _ => ⟨_, _, collection_satisfiable⟩

theorem satisfiable_depositRequests : satisfiableDepositRequests canonicalEnvironment :=
  fun _ => ⟨_, _, collection_satisfiable⟩

theorem satisfiable_withdrawalRequests : satisfiableWithdrawalRequests canonicalEnvironment :=
  fun _ => ⟨_, _, collection_satisfiable⟩

theorem satisfiable_consolidationRequests : satisfiableConsolidationRequests canonicalEnvironment :=
  fun _ => ⟨_, _, collection_satisfiable⟩

theorem satisfiable_publicKeys : satisfiablePublicKeys canonicalEnvironment :=
  fun _ => ⟨_, _, collection_satisfiable⟩

theorem satisfiable_byteListList : satisfiableByteListList canonicalEnvironment :=
  fun _ => ⟨⟨⟨0, ByteArray.empty, 0, 0⟩, 0, 0⟩, _, collection_satisfiable⟩

theorem satisfiable_requireCanonicalOffsets :
    satisfiableRequireCanonicalOffsets canonicalEnvironment :=
  fun _ => ⟨_, _, canonicalOffsets_satisfiable⟩

theorem satisfiable_requireU32Length : satisfiableRequireU32Length canonicalEnvironment :=
  fun _ => ⟨_, _, slice_satisfiable⟩

theorem satisfiable_hasExactErePrefix : satisfiableHasExactErePrefix canonicalEnvironment :=
  fun _ => ⟨_, _, slice_satisfiable⟩

theorem satisfiable_readOffset : satisfiableReadOffset canonicalEnvironment :=
  fun _ => ⟨_, _, readAt_satisfiable⟩

theorem satisfiable_readU32 : satisfiableReadU32 canonicalEnvironment :=
  fun _ => ⟨_, _, readAt_satisfiable⟩

theorem satisfiable_readU64 : satisfiableReadU64 canonicalEnvironment :=
  fun _ => ⟨_, _, readAt_satisfiable⟩

theorem satisfiable_readU256 : satisfiableReadU256 canonicalEnvironment :=
  fun _ => ⟨⟨⟨0, ByteArray.empty, 0⟩, 0⟩, _, readAt_satisfiable⟩

theorem satisfiable_readArray (length : Nat) :
    satisfiableReadArray canonicalEnvironment length :=
  fun _ => ⟨⟨⟨0, ByteArray.empty, 0⟩, 0⟩, _, readAt_satisfiable⟩

theorem satisfiable_bytesAt : satisfiableBytesAt canonicalEnvironment :=
  fun _ => ⟨⟨⟨0, ByteArray.empty, 0⟩, 0⟩, _, readAt_satisfiable⟩

theorem satisfiable_alloc : satisfiableAlloc canonicalEnvironment canonicalHeap :=
  fun _ => ⟨_, _, alloc_satisfiable⟩

theorem satisfiable_allocatorAlloc :
    satisfiableAllocatorAlloc canonicalEnvironment canonicalHeap :=
  fun _ => ⟨_, _, alloc_satisfiable⟩

theorem satisfiable_memcpy : satisfiableMemcpy canonicalEnvironment :=
  fun _ => ⟨_, _, ⟨copy_satisfiable, Or.inl (by simp)⟩⟩

theorem satisfiable_memmove : satisfiableMemmove canonicalEnvironment :=
  fun _ => ⟨_, _, copy_satisfiable⟩

theorem satisfiable_rawResult :
    satisfiableRawResult canonicalEnvironment canonicalDecoderGlobalsLayout canonicalResultBuffer :=
  fun _ => ⟨DecoderGlobalsModel.fresh, canonicalWitnessState,
    canonicalWitnessState_codeIntact, canonicalWitnessState_globals.2.1⟩

theorem satisfiable_rawError :
    satisfiableRawError canonicalEnvironment canonicalDecoderGlobalsLayout :=
  fun _ => ⟨DecoderGlobalsModel.fresh, canonicalWitnessState,
    canonicalWitnessState_codeIntact, canonicalWitnessState_globals.1⟩

theorem satisfiable_allocatorResize : satisfiableAllocatorResize canonicalEnvironment :=
  fun _ => ⟨(), canonicalWitnessState, canonicalWitnessState_codeIntact⟩

theorem satisfiable_allocatorRemap : satisfiableAllocatorRemap canonicalEnvironment :=
  fun _ => ⟨(), canonicalWitnessState, canonicalWitnessState_codeIntact⟩

theorem satisfiable_allocatorFree : satisfiableAllocatorFree canonicalEnvironment :=
  fun _ => ⟨(), canonicalWitnessState, canonicalWitnessState_codeIntact⟩

theorem satisfiable_allocatorCtor : satisfiableAllocatorCtor canonicalEnvironment :=
  fun _ => ⟨{ contextBase := 0, vtableBase := 0, resultBase := 0 }, canonicalWitnessState,
    canonicalWitnessState_codeIntact⟩

/-! ## The obligation -/

/-- **No cataloged routine's precondition is impossible.**

The dispatch is total over `RoutineTag`, so this is a case analysis with no default arm: adding a
routine to the catalog without a witness is a compile error rather than a silent gap. Nothing here
depends on the entry being live or on which function instance carries it — satisfiability is a property of
the contract. -/
theorem canonical_catalog_satisfiability :
    catalogSatisfiability canonicalContractParams := by
  intro entry _ _
  unfold routineSatisfiable
  cases entry.tag with
  | zesuDecodeRaw => exact satisfiable_zesuDecodeRaw
  | decode => exact satisfiable_decode
  | decodeRaw => exact satisfiable_decodeRaw
  | newPayloadRequest => exact satisfiable_newPayloadRequest
  | executionPayload => exact satisfiable_executionPayload
  | executionRequests => exact satisfiable_executionRequests
  | executionWitness => exact satisfiable_executionWitness
  | chainConfig => exact satisfiable_chainConfig
  | forkConfig => exact satisfiable_forkConfig
  | forkActivation => exact satisfiable_forkActivation
  | optionalU64 => exact satisfiable_optionalU64
  | optionalBlobSchedule => exact satisfiable_optionalBlobSchedule
  | versionedHashes => exact satisfiable_versionedHashes
  | withdrawals => exact satisfiable_withdrawals
  | depositRequests => exact satisfiable_depositRequests
  | withdrawalRequests => exact satisfiable_withdrawalRequests
  | consolidationRequests => exact satisfiable_consolidationRequests
  | publicKeys => exact satisfiable_publicKeys
  | byteListList => exact satisfiable_byteListList
  | requireCanonicalOffsets => exact satisfiable_requireCanonicalOffsets
  | requireU32Length => exact satisfiable_requireU32Length
  | readOffset => exact satisfiable_readOffset
  | readU32 => exact satisfiable_readU32
  | readU64 => exact satisfiable_readU64
  | readU256 => exact satisfiable_readU256
  | readArray => exact satisfiable_readArray _
  | bytesAt => exact satisfiable_bytesAt
  | hasExactErePrefix => exact satisfiable_hasExactErePrefix
  | rawAlloc => exact satisfiable_alloc
  | memcpy => exact satisfiable_memcpy
  | memmove => exact satisfiable_memmove
  | rawResult => exact satisfiable_rawResult
  | rawError => exact satisfiable_rawError
  | allocatorAlloc => exact satisfiable_allocatorAlloc
  | allocatorResize => exact satisfiable_allocatorResize
  | allocatorRemap => exact satisfiable_allocatorRemap
  | allocatorFree => exact satisfiable_allocatorFree
  | allocatorCtor => exact satisfiable_allocatorCtor

/-- **The residue, with satisfiability removed.**

`Elfling.NonLocalPremises.sszComplianceObligations_of_residue` had to take
`catalogSatisfiability` as a premise because it sits below the runner's state builder, which is where
a state carrying real code lives. This restates it without that premise.

What remains: **exactly one premise, `LocalContractAssumptions`.** No oracle-agreement fact at all —
all four (`v3ShapeExcludesCanonicalV4`, `sourceShapedDecodeAgreesWithOracle`,
`sourceShapedContainersAgreeWithOracle` and `zeroFirstOffsetAliasRejected`) are proved rather than
assumed; no satisfiability premise, discharged by `canonical_catalog_satisfiability` in this module;
and no divergence premise either, since `knownDivergences_holds` proves that outright.

**Plus — not visible in this signature and not reduced by it — the two live-run scaffolds in
`Execution.lean`**, which the root theorem consumes alongside this obligation. That gap is the reason
the root is not yet `root_compliance_of_local_contracts assumedAllLocalContracts`: this signature
being down to one premise says the *obligation* half of the root's dependency is conditional on the
local proofs alone, and says nothing about the *run* half. -/
theorem sszComplianceObligations_of_residue
    (locals : Elfling.Validation.LocalContractAssumptions) :
    sszComplianceObligations Elfling.Generated.generatedProgram :=
  Elfling.Validation.sszComplianceObligations_of_residue
    canonical_catalog_satisfiability locals

/-- **The pair the two `Execution.lean` scaffolds each claim before the run**, from the local proofs
alone: a canonical generated program, and the compliance obligation for it.

This is `Elfling.Validation.canonicalProgram_and_obligations_of_residue` with satisfiability
discharged, so it is the exact shape of the scaffolds' first two conjuncts. What is left of those
scaffolds after this is `Nonempty (SuccessfulRun …)` / `Nonempty (RejectedRun …)` and nothing else. -/
theorem canonicalProgram_and_obligations_of_residue
    (locals : Elfling.Validation.LocalContractAssumptions) :
    Contracts.IsCanonicalGeneratedProgram Elfling.Generated.generatedProgram ∧
      sszComplianceObligations Elfling.Generated.generatedProgram :=
  Elfling.Validation.canonicalProgram_and_obligations_of_residue
    canonical_catalog_satisfiability locals

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
