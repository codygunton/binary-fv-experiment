import BinaryFv.SSZ.Zesu.Elfling.GeneratedProgramGeometry

/-!
# `CallTransfer.retInRegion` on the real artifact (falsification evidence)

**Measurement, not a gate.** Nothing in the theorem graph imports this module.

`BoundarySatisfiability` decides three structural side conditions of `EnteredScopedTrace`
(`entryNotExit`, `CallTransfer.callNotExit`, `InlineBoundary.validFor` + `exitEdgeMem`). There is a
**fourth** it does not decide: `CallTransfer.retInRegion`.

`ScopedTrace.callStep` consumes a `CallTransfer region …` whose `region` is, in
`routineLocalObligation`, the caller's *owned* address set (`functionInstanceOwnPcs`). Its `retInRegion`
field asks that set to contain `retPc` — the pc the callee summary stopped at. A summary that stops
on the callee's generated exit can therefore be consumed only where the caller's owned set contains
that exit pc.

That holds for an inlined child (its regions sit inside the parent's) and fails for a separately
emitted callee. The counts below decide which is which on the canonical program, and they exhibit the
check going *both* ways: `127` inline pairs pass, `25` external-call pairs fail.
-/

namespace BinaryFv.SSZ.Zesu.Validation.CallStepRetInRegion

open BinaryFv.Binary.Elfling
open BinaryFv.RiscV.Elfling
open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Elfling.Generated (generatedProgram)

/-- Whether the caller's owned set contains any of the callee's generated exit pcs — the exact
condition `CallTransfer.retInRegion` reduces to under the canonical child summary. -/
def retInRegionSatisfiableB (parent callee : FunctionInstance) : Bool :=
  callee.exitPcs.any fun pc => Program.inRanges (Program.ownedRanges generatedProgram parent) pc

/-- Every (caller, resolved callee) pair of the canonical program, tagged with whether the callee is
an inlined child of the caller. -/
def calleePairs : Array (FunctionInstance × FunctionInstance × Bool) :=
  generatedProgram.functionInstances.foldl
    (fun acc i =>
      (calleeFunctionInstances generatedProgram i).foldl
        (fun acc c => acc.push (i, c, i.children.any (fun id => decide (id = c.id)))) acc)
    #[]

def pairCount : Nat := calleePairs.size
def inlinePairCount : Nat := (calleePairs.filter (fun p => p.2.2)).size
def externalPairCount : Nat := (calleePairs.filter (fun p => !p.2.2)).size

def inlinePairsSatisfying : Nat :=
  (calleePairs.filter (fun p => p.2.2 && retInRegionSatisfiableB p.1 p.2.1)).size

def externalPairsSatisfying : Nat :=
  (calleePairs.filter (fun p => !p.2.2 && retInRegionSatisfiableB p.1 p.2.1)).size

/-! ## The counts -/

theorem pair_count : pairCount = 152 := by native_decide

theorem inline_pair_count : inlinePairCount = 127 := by native_decide

theorem external_pair_count : externalPairCount = 25 := by native_decide

/-- **The check passes 127 times.** So it is not a predicate incapable of being satisfied. -/
theorem inline_pairs_all_satisfy : inlinePairsSatisfying = 127 := by native_decide

/-- **And fails 25 times out of 25.** `ScopedTrace.callStep` therefore has no witness at any resolved
external call of the canonical program: every cataloged callee returns from an address the caller does
not own. -/
theorem external_pairs_none_satisfy : externalPairsSatisfying = 0 := by native_decide

end BinaryFv.SSZ.Zesu.Validation.CallStepRetInRegion
