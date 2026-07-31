import BinaryFv.RiscV.Elfling.Contract

/-! Decidable transfer-graph and address geometry, independent of any routine catalog. -/

namespace BinaryFv.RiscV.Elfling

open BinaryFv.Binary
open BinaryFv.Binary.Elfling

def calleeFunctionInstances (program : Program) (functionInstance : FunctionInstance) :
    Array FunctionInstance :=
  program.functionInstances.filter fun other =>
    (functionInstance.children ++ functionInstance.externalCalls).any fun id =>
      decide (id = other.id)

theorem calleeFunctionInstances_subset {program : Program}
    {functionInstance callee : FunctionInstance}
    (h : callee ∈ calleeFunctionInstances program functionInstance) :
    callee ∈ program.functionInstances :=
  (Array.mem_filter.mp h).1

def functionInstanceOwnPcs (program : Program) (functionInstance : FunctionInstance) :
    BitVec 64 → Prop :=
  RegionPcs (Program.ownedRanges program functionInstance)

def functionInstanceReachedPcs (program : Program) (functionInstance : FunctionInstance) :
    BitVec 64 → Prop :=
  RegionPcs (Program.extentRanges program functionInstance)

def functionInstanceExecutionPcs (program : Program) (functionInstance : FunctionInstance) :
    BitVec 64 → Prop :=
  FunctionInstanceExecutionPcs functionInstance
    (functionInstanceReachedPcs program functionInstance)

def functionInstanceExitPred (functionInstance : FunctionInstance) (pc : BitVec 64) : Prop :=
  functionInstance.isExit pc.toNat

def functionInstanceExecutionRanges (program : Program) (functionInstance : FunctionInstance) :
    Array AddressRange :=
  functionInstance.regions ++ Program.extentRanges program functionInstance

theorem functionInstanceExecutionPcs_iff_ranges {program : Program}
    {functionInstance : FunctionInstance} {pc : BitVec 64} :
    functionInstanceExecutionPcs program functionInstance pc ↔
      RegionPcs (functionInstanceExecutionRanges program functionInstance) pc := by
  simp [functionInstanceExecutionPcs, FunctionInstanceExecutionPcs,
    functionInstanceReachedPcs, functionInstanceExecutionRanges, RegionPcs.append_iff]

structure ProgramGeometry (program : Program) : Prop where
  ownedWithinExecution : ∀ functionInstance ∈ program.functionInstances, ∀ pc,
    functionInstanceOwnPcs program functionInstance pc →
      functionInstanceExecutionPcs program functionInstance pc
  calleeWithinExecution : ∀ functionInstance ∈ program.functionInstances,
    ∀ callee ∈ calleeFunctionInstances program functionInstance, ∀ pc,
      functionInstanceExecutionPcs program callee pc →
        functionInstanceExecutionPcs program functionInstance pc
  calleeExitContainment : ∀ functionInstance ∈ program.functionInstances,
    ∀ callee ∈ calleeFunctionInstances program functionInstance, ∀ pc,
      functionInstanceExecutionPcs program callee pc →
        functionInstanceExitPred functionInstance pc → functionInstanceExitPred callee pc

def ownedWithinExecutionB (program : Program) : Bool :=
  program.functionInstances.all fun functionInstance =>
    Program.rangesSubsume (functionInstanceExecutionRanges program functionInstance)
      (Program.ownedRanges program functionInstance)

def calleeWithinExecutionB (program : Program) : Bool :=
  program.functionInstances.all fun functionInstance =>
    (calleeFunctionInstances program functionInstance).all fun callee =>
      Program.rangesSubsume (functionInstanceExecutionRanges program functionInstance)
        (functionInstanceExecutionRanges program callee)

def calleeExitContainmentB (program : Program) : Bool :=
  program.functionInstances.all fun functionInstance =>
    (calleeFunctionInstances program functionInstance).all fun callee =>
      functionInstance.exitPcs.all fun pc =>
        !Program.inRanges (functionInstanceExecutionRanges program callee) pc ||
          callee.exitPcs.contains pc

def programGeometryB (program : Program) : Bool :=
  ownedWithinExecutionB program && calleeWithinExecutionB program &&
    calleeExitContainmentB program

private theorem forall_mem_of_all {α : Type _} {xs : Array α} {f : α → Bool}
    (h : xs.all f = true) : ∀ x ∈ xs, f x = true := by
  intro x hx
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hx
  exact hget ▸ (Array.all_eq_true.mp h) i hi

theorem programGeometry_of_check {program : Program} (h : programGeometryB program = true) :
    ProgramGeometry program := by
  obtain ⟨howned, hcallee, hexit⟩ : ownedWithinExecutionB program = true ∧
      calleeWithinExecutionB program = true ∧ calleeExitContainmentB program = true := by
    simpa [programGeometryB, Bool.and_eq_true, and_assoc] using h
  refine ⟨?_, ?_, ?_⟩
  · intro i hi pc hpc
    exact functionInstanceExecutionPcs_iff_ranges.mpr
      (RegionPcs.of_rangesSubsume (forall_mem_of_all howned i hi) hpc)
  · intro i hi c hc pc hpc
    exact functionInstanceExecutionPcs_iff_ranges.mpr
      (RegionPcs.of_rangesSubsume (forall_mem_of_all (forall_mem_of_all hcallee i hi) c hc)
        (functionInstanceExecutionPcs_iff_ranges.mp hpc))
  · intro i hi c hc pc hpc hexitPc
    have hrow := forall_mem_of_all (forall_mem_of_all hexit i hi) c hc
    have hmem := forall_mem_of_all hrow pc.toNat hexitPc
    have hin : Program.inRanges (functionInstanceExecutionRanges program c) pc.toNat = true :=
      RegionPcs.iff_inRanges.mp (functionInstanceExecutionPcs_iff_ranges.mp hpc)
    simp [hin] at hmem
    simpa [functionInstanceExitPred, FunctionInstance.isExit] using hmem

def FunctionGraphRanked (program : Program) (rank : FunctionInstance → Nat) : Prop :=
  ∀ functionInstance ∈ program.functionInstances,
    ∀ callee ∈ calleeFunctionInstances program functionInstance,
      rank callee < rank functionInstance

def functionGraphRankedB (program : Program) (rank : FunctionInstance → Nat) : Bool :=
  program.functionInstances.all fun functionInstance =>
    (calleeFunctionInstances program functionInstance).all fun callee =>
      decide (rank callee < rank functionInstance)

theorem functionGraphRanked_of_check {program : Program} {rank : FunctionInstance → Nat}
    (h : functionGraphRankedB program rank = true) : FunctionGraphRanked program rank := by
  intro i hi c hc
  exact of_decide_eq_true (forall_mem_of_all (forall_mem_of_all h i hi) c hc)

end BinaryFv.RiscV.Elfling
