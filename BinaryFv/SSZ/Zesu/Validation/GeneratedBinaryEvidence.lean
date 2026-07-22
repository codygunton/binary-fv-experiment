-- GENERATED FILE: produced by targets/ssz/zesu/trace/generate_evidence.py --out-lean. DO NOT EDIT.
-- Deterministic production-ELF evidence for the decodeOptionalBlobSchedule slice (occurrence 116),
-- consumed by BinaryFv/SSZ/Zesu/Validation/BinaryOccurrenceCheck.lean. Diagnostic-only; the
-- validation-import guard forbids the theorem graph from importing this.
import BinaryFv.SSZ.Zesu.Validation.BinaryOccurrenceTypes
namespace BinaryFv.SSZ.Zesu.Validation.GeneratedBinaryEvidence
open BinaryFv.SSZ.Zesu.Validation

def presentEvidence : OccEvidence :=
  { arm := "present", entryPc := 76888, regions := [(76888, 76896), (76936, 76984), (76988, 77256)], declaredEdges := [(76888, 76892), (76892, 76896), (76936, 76940), (76936, 76984), (76940, 76228), (76940, 76944), (76944, 76948), (76948, 76952), (76952, 76956), (76956, 76960), (76960, 76964), (76964, 76968), (76968, 76972), (76972, 76976), (76976, 76980), (76980, 77256)], firstExecuted := 76888, occInsnCount := 70, occExecEdges := [(76936, 76984)], inRegionStores := [], inputByteLoads := [(67196244, 22), (67196245, 0), (67196246, 0), (67196247, 0), (67196248, 0), (67196249, 0), (67196250, 0), (67196251, 0), (67196252, 23), (67196253, 0), (67196254, 0), (67196255, 0), (67196256, 0), (67196257, 0), (67196258, 0), (67196259, 0), (67196260, 24), (67196261, 0), (67196262, 0), (67196263, 0), (67196264, 0), (67196265, 0), (67196266, 0), (67196267, 0)], sp := 140737194737072, a0 := 140737194741168 }
def presentExpected : CheckResult :=
  { entryReached := true, edgesSubsetOfCfg := true, childOffsetsFromLoads := some true, decodedBlobSchedule := some [22, 23, 24], resultSlotOnStack := true, withinStepBound := true, noAllocation := true, inputPreserved := true, codePreserved := true, noUnclassifiedWrites := true }

def absentEvidence : OccEvidence :=
  { arm := "absent", entryPc := 76888, regions := [(76888, 76896), (76936, 76984), (76988, 77256)], declaredEdges := [(76888, 76892), (76892, 76896), (76936, 76940), (76936, 76984), (76940, 76228), (76940, 76944), (76944, 76948), (76948, 76952), (76952, 76956), (76956, 76960), (76960, 76964), (76964, 76968), (76968, 76972), (76972, 76976), (76976, 76980), (76980, 77256)], firstExecuted := 76888, occInsnCount := 14, occExecEdges := [], inRegionStores := [(76968, 140737194740664, 4, 0), (76972, 140737194740668, 2, 0), (76976, 140737194740670, 1, 0)], inputByteLoads := [], sp := 140737194737072, a0 := 140737194741168 }
def absentExpected : CheckResult :=
  { entryReached := true, edgesSubsetOfCfg := true, childOffsetsFromLoads := none, decodedBlobSchedule := none, resultSlotOnStack := true, withinStepBound := true, noAllocation := true, inputPreserved := true, codePreserved := true, noUnclassifiedWrites := true }

def malformedEvidence : OccEvidence :=
  { arm := "malformed", entryPc := 76888, regions := [(76888, 76896), (76936, 76984), (76988, 77256)], declaredEdges := [(76888, 76892), (76892, 76896), (76936, 76940), (76936, 76984), (76940, 76228), (76940, 76944), (76944, 76948), (76948, 76952), (76952, 76956), (76956, 76960), (76960, 76964), (76964, 76968), (76968, 76972), (76972, 76976), (76976, 76980), (76980, 77256)], firstExecuted := 76888, occInsnCount := 4, occExecEdges := [], inRegionStores := [], inputByteLoads := [], sp := 140737194737072, a0 := 140737194741168 }
def malformedExpected : CheckResult :=
  { entryReached := true, edgesSubsetOfCfg := true, childOffsetsFromLoads := none, decodedBlobSchedule := none, resultSlotOnStack := true, withinStepBound := true, noAllocation := true, inputPreserved := true, codePreserved := true, noUnclassifiedWrites := true }

/-- Each arm's evidence paired with the Python oracle's expected check result. -/
def allArms : List (OccEvidence × CheckResult) :=
  [(presentEvidence, presentExpected), (absentEvidence, absentExpected), (malformedEvidence, malformedExpected)]
end BinaryFv.SSZ.Zesu.Validation.GeneratedBinaryEvidence
