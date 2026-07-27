import BinaryFv.SSZ.Zesu.Validation.LocalObligationRefutations

/-!
# The five remaining child-summary premises

The first ledger pass proves 120 `ChildSummariesAvailable` premises inhabited, 16 uninhabited, and
leaves five unknown. This module closes those five against the actual generated callee consumer.

Three parents call only pure leaf contracts whose exits can be constructed from every pre-state:
`decodeOptionalBlobSchedule`, `decodeOptionalU64`, and `decodeByteListList`. The other two call
allocating collection contracts. Empty input is accepted by those callees, but their unconstrained
result descriptor may overlap file-backed byte `0x10444 = 19`. The required empty-array count writes
zero at that byte while `CodeIntact` requires 19, so no child-summary relation can exist.

This is a complete join, not a list of ingredients: the positive theorems construct the exact
`ChildSummariesAvailable` relation, the negative theorems refute every relation, and both sets are
pinned by stable ledger key.
-/

namespace BinaryFv.SSZ.Zesu.Validation.RemainingSummaryPremises

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedManifest generatedProgram)
open BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
open BinaryFv.SSZ.Zesu.MemoryRepresentation
open LeanRV64DExecutable.Functions Register
open LocalObligationRefutations

/-! ## Realizable leaf exits -/

private theorem leafFrame_withArgumentRegisters
    {env : DecoderEnvironment} {base : Nat} {bytes : ByteArray}
    {before : State} (hbytes : MemoryBytes before base bytes)
    (hcode : env.CodeIntact before) (a0 a1 a2 a3 : Nat) :
    LeafFrame env base bytes 0 0 before
      (withArgumentRegisters before a0 a1 a2 a3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index hindex
    simpa only [withArgumentRegisters_mem] using hbytes index hindex
  · simpa only [DecoderEnvironment.CodeIntact, withArgumentRegisters_mem] using hcode
  · intro address haddress
    simp only [withArgumentRegisters_mem]
  · intro address haddress
    simp only [withArgumentRegisters_mem]

/-- `readOffset` has a realizable exit for both its value and error meanings. -/
theorem readOffset_exit_realizable (env : DecoderEnvironment) :
    ∀ (args : ReadAtArgs) (before : State),
      (contractReadOffset env).pre args before →
        ∃ after,
          (contractReadOffset env).post args ((contractReadOffset env).meaning args) before after := by
  intro args before hpre
  rcases hpre with ⟨hbytes, hcode, _⟩
  cases hmeaning : meaningReadU32 args.bytes args.offset with
  | ok value =>
      let after := withArgumentRegisters before value.toNat 0 0 0
      refine ⟨after, ?_⟩
      change postScalarRead env args 32
        ((meaningReadU32 args.bytes args.offset).map UInt32.toNat) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          UInt32.toNat_lt value, by simp [after]⟩
  | error error =>
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postScalarRead env args 32
        ((meaningReadU32 args.bytes args.offset).map UInt32.toNat) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          meaningReadU32_onlyInvalid args.bytes args.offset error hmeaning⟩

/-- `readU64` has a realizable exit for both its value and error meanings. -/
theorem readU64_exit_realizable (env : DecoderEnvironment) :
    ∀ (args : ReadAtArgs) (before : State),
      (contractReadU64 env).pre args before →
        ∃ after,
          (contractReadU64 env).post args ((contractReadU64 env).meaning args) before after := by
  intro args before hpre
  rcases hpre with ⟨hbytes, hcode, _⟩
  cases hmeaning : meaningReadU64 args.bytes args.offset with
  | ok value =>
      let after := withArgumentRegisters before value.toNat 0 0 0
      refine ⟨after, ?_⟩
      change postScalarRead env args 64
        ((meaningReadU64 args.bytes args.offset).map UInt64.toNat) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          UInt64.toNat_lt value, by simp [after]⟩
  | error error =>
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postScalarRead env args 64
        ((meaningReadU64 args.bytes args.offset).map UInt64.toNat) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          meaningReadU64_onlyInvalid args.bytes args.offset error hmeaning⟩

/-- `requireU32Length` has a realizable status exit on both arms. -/
theorem requireU32Length_exit_realizable (env : DecoderEnvironment) :
    ∀ (args : SliceArgs) (before : State),
      (contractRequireU32Length env).pre args before →
        ∃ after,
          (contractRequireU32Length env).post args
            ((contractRequireU32Length env).meaning args) before after := by
  intro args before hpre
  rcases hpre with ⟨hbytes, hcode, _⟩
  cases hmeaning : meaningRequireU32Length args.bytes with
  | ok value =>
      cases value
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postRequireU32Length env args (meaningRequireU32Length args.bytes) before after
      rw [hmeaning]
      exact ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _, by simp [after]⟩
  | error error =>
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postRequireU32Length env args (meaningRequireU32Length args.bytes) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          meaningRequireU32Length_onlyInvalid args.bytes error hmeaning⟩

/-- `requireCanonicalOffsets` has a realizable status exit on both arms. -/
theorem requireCanonicalOffsets_exit_realizable (env : DecoderEnvironment) :
    ∀ (args : CanonicalOffsetsArgs) (before : State),
      (contractRequireCanonicalOffsets env).pre args before →
        ∃ after,
          (contractRequireCanonicalOffsets env).post args
            ((contractRequireCanonicalOffsets env).meaning args) before after := by
  intro args before hpre
  rcases hpre with ⟨hbytes, hcode, _⟩
  cases hmeaning :
      meaningRequireCanonicalOffsets args.bytes args.fixedSize args.offsets with
  | ok value =>
      cases value
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postCanonicalOffsets env args
        (meaningRequireCanonicalOffsets args.bytes args.fixedSize args.offsets) before after
      rw [hmeaning]
      exact ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _, by simp [after]⟩
  | error error =>
      let after := withArgumentRegisters before 0 0 0 0
      refine ⟨after, ?_⟩
      change postCanonicalOffsets env args
        (meaningRequireCanonicalOffsets args.bytes args.fixedSize args.offsets) before after
      rw [hmeaning]
      exact
        ⟨leafFrame_withArgumentRegisters hbytes hcode _ _ _ _,
          meaningRequireCanonicalOffsets_onlyInvalid args.bytes args.fixedSize args.offsets error
            hmeaning⟩

private theorem routine_readOffset_exit_realizable
    (p : ContractParams) (function : FunctionId) :
    ExitRealizable (routineContract p function .readOffset) := by
  intro args before hpre
  exact readOffset_exit_realizable p.env args before hpre

private theorem routine_readU64_exit_realizable
    (p : ContractParams) (function : FunctionId) :
    ExitRealizable (routineContract p function .readU64) := by
  intro args before hpre
  exact readU64_exit_realizable p.env args before hpre

private theorem routine_requireU32Length_exit_realizable
    (p : ContractParams) (function : FunctionId) :
    ExitRealizable (routineContract p function .requireU32Length) := by
  intro args before hpre
  exact requireU32Length_exit_realizable p.env args before hpre

private theorem routine_requireCanonicalOffsets_exit_realizable
    (p : ContractParams) (function : FunctionId) :
    ExitRealizable (routineContract p function .requireCanonicalOffsets) := by
  intro args before hpre
  exact requireCanonicalOffsets_exit_realizable p.env args before hpre

private def realizableLeafTagB (tag : RoutineTag) : Bool :=
  tag == .bytesAt || tag == .readU32 || tag == .readOffset || tag == .readU64 ||
    tag == .requireU32Length || tag == .requireCanonicalOffsets

private def realizableLeafCalleeB (callee : FunctionInstance) : Bool :=
  match catalogEntryFor callee.id.function with
  | some entry => realizableLeafTagB entry.tag
  | none => false

/-- Every actual callee dispatches to one of the six checked-realizable leaf exits. -/
def realizableLeafSummaryPremiseB
    (program : Program) (functionInstance : FunctionInstance) : Bool :=
  (calleeFunctionInstances program functionInstance).all realizableLeafCalleeB

private theorem exitRealizable_of_realizableLeafCalleeB
    {p : ContractParams} {callee : FunctionInstance}
    (hleaf : realizableLeafCalleeB callee = true) :
    ∀ entry, catalogEntryFor callee.id.function = some entry →
      ExitRealizable (routineContract p callee.id.function entry.tag) := by
  intro entry found
  unfold realizableLeafCalleeB at hleaf
  rw [found] at hleaf
  have htag :
      entry.tag = .bytesAt ∨ entry.tag = .readU32 ∨ entry.tag = .readOffset ∨
        entry.tag = .readU64 ∨ entry.tag = .requireU32Length ∨
          entry.tag = .requireCanonicalOffsets := by
    simpa [realizableLeafTagB, Bool.or_eq_true, beq_iff_eq, or_assoc] using hleaf
  rcases htag with htag | htag | htag | htag | htag | htag
  · rw [htag]
    intro args before hpre
    exact bytesAt_exit_realizable p.env args before hpre
  · rw [htag]
    intro args before hpre
    exact readU32_exit_realizable p.env args before hpre
  · rw [htag]
    exact routine_readOffset_exit_realizable p _
  · rw [htag]
    exact routine_readU64_exit_realizable p _
  · rw [htag]
    exact routine_requireU32Length_exit_realizable p _
  · rw [htag]
    exact routine_requireCanonicalOffsets_exit_realizable p _

/-- The universal relation realizes a parent whose actual callee set is entirely checked leaves. -/
theorem childSummariesAvailable_of_realizable_leaf_callees
    {p : ContractParams} {program : Program} {functionInstance : FunctionInstance}
    (hall : realizableLeafSummaryPremiseB program functionInstance = true) :
    ChildSummariesAvailable p program functionInstance (fun _ _ _ _ _ => True) := by
  unfold realizableLeafSummaryPremiseB at hall
  intro callee hcallee entry found args fromStep before hpre
  have hleaf : realizableLeafCalleeB callee = true :=
    Array.all_eq_true_iff_forall_mem.mp hall callee hcallee
  obtain ⟨after, hpost⟩ :=
    exitRealizable_of_realizableLeafCalleeB hleaf entry found args before hpre
  exact ⟨0, after, Nat.zero_le _, trivial, hpost⟩

/-! ## Unrealizable collection exits -/

private def badCollectionArgs : CollectionArgs :=
  { base := 0
    bytes := ByteArray.empty
    allocatorBase := 0
    resultBase := 0x1043c }

private noncomputable def badCollectionState : State :=
  withArgumentRegisters canonicalWitnessState badCollectionArgs.resultBase
    badCollectionArgs.allocatorBase badCollectionArgs.base badCollectionArgs.bytes.size

private theorem badCollectionState_pre :
    preCollection canonicalEnvironment badCollectionArgs badCollectionState := by
  refine
    ⟨memoryBytes_empty _ _,
      codeIntact_withArgumentRegisters canonicalWitnessState_codeIntact, ?_, ?_, ?_, ?_⟩
  all_goals simp [badCollectionState, badCollectionArgs]

private theorem zero_ne_codeByte19 :
    (some (BitVec.ofNat 8 0) : Option (BitVec 8)) ≠
      some (BitVec.ofNat 8 (19 : UInt8).toNat) := by
  native_decide

private theorem zeroCountCollectionPost_impossible {α : Type} (elementSize : Nat)
    (value : Array α) (hsize : value.size = 0) (after : State) :
    ¬ postCollection canonicalEnvironment badCollectionArgs elementSize Array.size
      (.ok value) badCollectionState after := by
  intro hpost
  have hcode := hpost.2.1 0x10444 (19 : UInt8) (by native_decide)
  obtain ⟨dataBase, hdescriptor, _⟩ := hpost.2.2.2
  have hzero : after.mem.get? 0x10444 = some (BitVec.ofNat 8 0) := by
    simpa [badCollectionArgs, hsize] using hdescriptor.2.2.2 0 (by decide)
  exact zero_ne_codeByte19 (hzero.symm.trans hcode)

private def arrayResultSize? {ε α : Type} : Except ε (Array α) → Option Nat
  | .ok value => some value.size
  | .error _ => none

theorem depositRequests_empty_result_size :
    arrayResultSize? (meaningDepositRequests ByteArray.empty) = some 0 := by
  native_decide

theorem withdrawalRequests_empty_result_size :
    arrayResultSize? (meaningWithdrawalRequests ByteArray.empty) = some 0 := by
  native_decide

theorem consolidationRequests_empty_result_size :
    arrayResultSize? (meaningConsolidationRequests ByteArray.empty) = some 0 := by
  native_decide

theorem depositRequests_exit_not_realizable (function : FunctionId) :
    ¬ ExitRealizable
      (routineContract canonicalContractParams function .depositRequests) := by
  intro hexit
  obtain ⟨after, hpost⟩ :=
    hexit badCollectionArgs badCollectionState badCollectionState_pre
  change postCollection canonicalEnvironment badCollectionArgs 192 Array.size
    (meaningDepositRequests badCollectionArgs.bytes) badCollectionState after at hpost
  have hsizeEvidence :
      arrayResultSize? (meaningDepositRequests badCollectionArgs.bytes) = some 0 := by
    simpa [badCollectionArgs] using depositRequests_empty_result_size
  cases hmeaning : meaningDepositRequests badCollectionArgs.bytes with
  | error error => simp [arrayResultSize?, hmeaning] at hsizeEvidence
  | ok value =>
      have hsize : value.size = 0 := by
        simpa [arrayResultSize?, hmeaning] using hsizeEvidence
      rw [hmeaning] at hpost
      exact zeroCountCollectionPost_impossible 192 value hsize after hpost

theorem withdrawalRequests_exit_not_realizable (function : FunctionId) :
    ¬ ExitRealizable
      (routineContract canonicalContractParams function .withdrawalRequests) := by
  intro hexit
  obtain ⟨after, hpost⟩ :=
    hexit badCollectionArgs badCollectionState badCollectionState_pre
  change postCollection canonicalEnvironment badCollectionArgs 76 Array.size
    (meaningWithdrawalRequests badCollectionArgs.bytes) badCollectionState after at hpost
  have hsizeEvidence :
      arrayResultSize? (meaningWithdrawalRequests badCollectionArgs.bytes) = some 0 := by
    simpa [badCollectionArgs] using withdrawalRequests_empty_result_size
  cases hmeaning : meaningWithdrawalRequests badCollectionArgs.bytes with
  | error error => simp [arrayResultSize?, hmeaning] at hsizeEvidence
  | ok value =>
      have hsize : value.size = 0 := by
        simpa [arrayResultSize?, hmeaning] using hsizeEvidence
      rw [hmeaning] at hpost
      exact zeroCountCollectionPost_impossible 76 value hsize after hpost

theorem consolidationRequests_exit_not_realizable (function : FunctionId) :
    ¬ ExitRealizable
      (routineContract canonicalContractParams function .consolidationRequests) := by
  intro hexit
  obtain ⟨after, hpost⟩ :=
    hexit badCollectionArgs badCollectionState badCollectionState_pre
  change postCollection canonicalEnvironment badCollectionArgs 116 Array.size
    (meaningConsolidationRequests badCollectionArgs.bytes) badCollectionState after at hpost
  have hsizeEvidence :
      arrayResultSize? (meaningConsolidationRequests badCollectionArgs.bytes) = some 0 := by
    simpa [badCollectionArgs] using consolidationRequests_empty_result_size
  cases hmeaning : meaningConsolidationRequests badCollectionArgs.bytes with
  | error error => simp [arrayResultSize?, hmeaning] at hsizeEvidence
  | ok value =>
      have hsize : value.size = 0 := by
        simpa [arrayResultSize?, hmeaning] using hsizeEvidence
      rw [hmeaning] at hpost
      exact zeroCountCollectionPost_impossible 116 value hsize after hpost

private def badByteListListArgs : ByteListListArgs :=
  { base := badCollectionArgs.base
    bytes := badCollectionArgs.bytes
    allocatorBase := badCollectionArgs.allocatorBase
    resultBase := badCollectionArgs.resultBase
    maxItems := 1
    maxItemBytes := 1 }

private theorem badByteListListArgs_toCollectionArgs :
    badByteListListArgs.toCollectionArgs = badCollectionArgs := by
  rfl

theorem byteListList_empty_result_size :
    arrayResultSize? (meaningByteListList 1 1 ByteArray.empty) = some 0 := by
  native_decide

theorem byteListList_exit_not_realizable (function : FunctionId) :
    ¬ ExitRealizable
      (routineContract canonicalContractParams function .byteListList) := by
  intro hexit
  have hpre :
      (contractByteListList canonicalEnvironment).pre badByteListListArgs
        badCollectionState := by
    change
      preCollection canonicalEnvironment badByteListListArgs.toCollectionArgs badCollectionState
    rw [badByteListListArgs_toCollectionArgs]
    exact badCollectionState_pre
  obtain ⟨after, hpost⟩ := hexit badByteListListArgs badCollectionState hpre
  change postCollection canonicalEnvironment badByteListListArgs.toCollectionArgs 16 Array.size
    (meaningByteListList badByteListListArgs.maxItems badByteListListArgs.maxItemBytes
      badByteListListArgs.bytes) badCollectionState after at hpost
  rw [badByteListListArgs_toCollectionArgs] at hpost
  have hsizeEvidence :
      arrayResultSize? (meaningByteListList badByteListListArgs.maxItems
        badByteListListArgs.maxItemBytes badCollectionArgs.bytes) = some 0 := by
    simpa [badByteListListArgs, badCollectionArgs] using byteListList_empty_result_size
  cases hmeaning :
      meaningByteListList badByteListListArgs.maxItems badByteListListArgs.maxItemBytes
        badCollectionArgs.bytes with
  | error error => simp [arrayResultSize?, hmeaning] at hsizeEvidence
  | ok value =>
      have hsize : value.size = 0 := by
        simpa [arrayResultSize?, hmeaning] using hsizeEvidence
      rw [hmeaning] at hpost
      exact zeroCountCollectionPost_impossible 16 value hsize after hpost

private def unrealizableCollectionCalleeB (callee : FunctionInstance) : Bool :=
  match catalogEntryFor callee.id.function with
  | some entry =>
      entry.tag == .depositRequests || entry.tag == .withdrawalRequests ||
        entry.tag == .consolidationRequests || entry.tag == .byteListList
  | none => false

/-- An actual callee is one of the four checked-unrealizable collection exits. -/
def unrealizableCollectionSummaryPremiseB
    (program : Program) (functionInstance : FunctionInstance) : Bool :=
  (calleeFunctionInstances program functionInstance).any unrealizableCollectionCalleeB

private theorem exit_not_realizable_of_unrealizableCollectionCalleeB
    {callee : FunctionInstance}
    (hcollection : unrealizableCollectionCalleeB callee = true) :
    ∀ entry, catalogEntryFor callee.id.function = some entry →
      ¬ ExitRealizable
        (routineContract canonicalContractParams callee.id.function entry.tag) := by
  intro entry found
  unfold unrealizableCollectionCalleeB at hcollection
  rw [found] at hcollection
  have htag :
      entry.tag = .depositRequests ∨ entry.tag = .withdrawalRequests ∨
        entry.tag = .consolidationRequests ∨ entry.tag = .byteListList := by
    simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using hcollection
  rcases htag with htag | htag | htag | htag
  · rw [htag]
    exact depositRequests_exit_not_realizable _
  · rw [htag]
    exact withdrawalRequests_exit_not_realizable _
  · rw [htag]
    exact consolidationRequests_exit_not_realizable _
  · rw [htag]
    exact byteListList_exit_not_realizable _

/-- One selected collection callee refutes every possible child-summary relation. -/
theorem childSummariesUnavailable_of_collection_callee
    {program : Program} {parent : FunctionInstance}
    (hcollection : unrealizableCollectionSummaryPremiseB program parent = true) :
    ∀ childSummary,
      ¬ ChildSummariesAvailable canonicalContractParams program parent childSummary := by
  unfold unrealizableCollectionSummaryPremiseB at hcollection
  obtain ⟨callee, hcallee, hbad⟩ := Array.any_eq_true'.mp hcollection
  cases found : catalogEntryFor callee.id.function with
  | none => simp [unrealizableCollectionCalleeB, found] at hbad
  | some entry =>
      exact childSummariesUnavailable_of_unrealizable_callee hcallee found
        (exit_not_realizable_of_unrealizableCollectionCalleeB hbad entry found)

/-! ## Exact five-row join and stable keys -/

/-- The parents selected by the collection collision, including index 23 already classified by its
copy callee. -/
def collectionCollisionParentIndices : List Nat :=
  (generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
    if unrealizableCollectionSummaryPremiseB generatedProgram functionInstance then
      some index
    else none).toList

theorem collection_collision_parent_indices :
    collectionCollisionParentIndices = [23, 63, 95] := by
  native_decide

/-- The two collection-collision parents not already classified by the earlier copy/result pass. -/
def newlyUnrealizableCollectionParentIndices : List Nat :=
  (generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
    if unrealizableCollectionSummaryPremiseB generatedProgram functionInstance &&
        !unrealizableCopySummaryPremiseB generatedProgram functionInstance &&
        !unrealizableResultSummaryPremiseB generatedProgram functionInstance then
      some index
    else none).toList

theorem newly_unrealizable_collection_parent_indices :
    newlyUnrealizableCollectionParentIndices = [63, 95] := by
  native_decide

/-- The exact two formerly-unknown summary premises are uninhabited. -/
theorem newly_unrealizable_collection_summary_premises :
    ∀ i ∈ newlyUnrealizableCollectionParentIndices, ∀ childSummary,
      ¬ ChildSummariesAvailable canonicalContractParams generatedProgram
        generatedProgram.functionInstances[i]! childSummary := by
  intro i hi
  rw [newly_unrealizable_collection_parent_indices] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  all_goals
    apply childSummariesUnavailable_of_collection_callee
    native_decide

/-- The three leaf-only parents not already classified by the earlier simple-leaf pass. -/
def newlyRealizableLeafParentIndices : List Nat :=
  (generatedProgram.functionInstances.zipIdx.filterMap fun (functionInstance, index) =>
    let callees := calleeFunctionInstances generatedProgram functionInstance
    if !callees.isEmpty &&
        realizableLeafSummaryPremiseB generatedProgram functionInstance &&
        !simpleExitSummaryPremiseB generatedProgram functionInstance &&
        !unrealizableCopySummaryPremiseB generatedProgram functionInstance &&
        !unrealizableResultSummaryPremiseB generatedProgram functionInstance then
      some index
    else none).toList

theorem newly_realizable_leaf_parent_indices :
    newlyRealizableLeafParentIndices = [116, 124, 126] := by
  native_decide

/-- The exact three formerly-unknown summary premises have concrete universal witnesses. -/
theorem newly_realizable_leaf_summary_premises :
    ∀ i ∈ newlyRealizableLeafParentIndices,
      ChildSummariesAvailable canonicalContractParams generatedProgram
        generatedProgram.functionInstances[i]! (fun _ _ _ _ _ => True) := by
  intro i hi
  rw [newly_realizable_leaf_parent_indices] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  all_goals
    apply childSummariesAvailable_of_realizable_leaf_callees
    native_decide

def newlyUnrealizableCollectionParentKeys : List InstanceKey :=
  newlyUnrealizableCollectionParentIndices.map fun index =>
    { entryPc := generatedManifest[index]!.entryPc
      routine := generatedManifest[index]!.qualifiedName }

def newlyRealizableLeafParentKeys : List InstanceKey :=
  newlyRealizableLeafParentIndices.map fun index =>
    { entryPc := generatedManifest[index]!.entryPc
      routine := generatedManifest[index]!.qualifiedName }

theorem newly_unrealizable_collection_parent_keys :
    newlyUnrealizableCollectionParentKeys =
      [{ entryPc := 73716, routine := "ssz_raw.decodeExecutionRequests" },
       { entryPc := 75536, routine := "ssz_raw.decodeExecutionWitness" }] := by
  native_decide

theorem newly_realizable_leaf_parent_keys :
    newlyRealizableLeafParentKeys =
      [{ entryPc := 76888, routine := "ssz_raw.decodeOptionalBlobSchedule" },
       { entryPc := 78136, routine := "ssz_raw.decodeOptionalU64" },
       { entryPc := 78496, routine := "ssz_raw.decodeByteListList" }] := by
  native_decide

/-! ## Negative teeth -/

private def realizableLeafTagWithoutReadU64B (tag : RoutineTag) : Bool :=
  tag == .bytesAt || tag == .readU32 || tag == .readOffset ||
    tag == .requireU32Length || tag == .requireCanonicalOffsets

private def realizableLeafWithoutReadU64CalleeB (callee : FunctionInstance) : Bool :=
  match catalogEntryFor callee.id.function with
  | some entry => realizableLeafTagWithoutReadU64B entry.tag
  | none => false

private def realizableLeafWithoutReadU64SummaryPremiseB
    (program : Program) (functionInstance : FunctionInstance) : Bool :=
  (calleeFunctionInstances program functionInstance).all realizableLeafWithoutReadU64CalleeB

theorem mutation_drop_readU64_rejects_optionalBlobSchedule :
    realizableLeafWithoutReadU64SummaryPremiseB generatedProgram
      generatedProgram.functionInstances[116]! = false := by
  native_decide

private def unrealizableCollectionWithoutByteListListCalleeB
    (callee : FunctionInstance) : Bool :=
  match catalogEntryFor callee.id.function with
  | some entry =>
      entry.tag == .depositRequests || entry.tag == .withdrawalRequests ||
        entry.tag == .consolidationRequests
  | none => false

private def unrealizableCollectionWithoutByteListListSummaryPremiseB
    (program : Program) (functionInstance : FunctionInstance) : Bool :=
  (calleeFunctionInstances program functionInstance).any
    unrealizableCollectionWithoutByteListListCalleeB

theorem mutation_drop_byteListList_rejects_executionWitness :
    unrealizableCollectionWithoutByteListListSummaryPremiseB generatedProgram
      generatedProgram.functionInstances[95]! = false := by
  native_decide

end BinaryFv.SSZ.Zesu.Validation.RemainingSummaryPremises
