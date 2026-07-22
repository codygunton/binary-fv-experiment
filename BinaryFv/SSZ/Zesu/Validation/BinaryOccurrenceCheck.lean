import BinaryFv.SSZ.Zesu.Validation.BinaryOccurrenceTypes
import BinaryFv.SSZ.Zesu.Validation.GeneratedBinaryEvidence
import BinaryFv.SSZ.Zesu.Contracts.Options

/-!
# Row C: Lean diagnostic checker for the decodeOptionalBlobSchedule occurrence

Evaluates the compact production-ELF evidence (`GeneratedBinaryEvidence`) for occurrence 116 and its
three nested `readU64` children (117/118/119) against the FIXED Row A binding / handwritten meaning /
pinned memory layout, reproducing the Python oracle `evaluate_compact` exactly. It checks the entry and
result/exit binding, the nested const-offset bindings, `RoutineSpec.meaning`, the executed control flow
vs the generated CFG, the step bound, the (empty) allocation ledger, code/input preservation, and the
classified write frame.

`checker_agrees_with_oracle` pins Lean ≡ Python on every arm; `present_meaning_agrees` ties the actual
production loads to `meaningOptionalBlobSchedule`; the `negative_*` theorems require each of the eight
evidence corruptions to flip a check. This is a validation module — falsification/regression evidence,
never a proof premise, and (enforced by the validation-import guard) never imported by the theorem graph.
-/

namespace BinaryFv.SSZ.Zesu.Validation

open BinaryFv.SSZ.Zesu.Contracts
open BinaryFv.SSZ.Zesu.Validation.GeneratedBinaryEvidence

/-- Pinned production memory layout (from the `zesu-ssz` ELF sections/symbols): classify a write. -/
def classifyWrite (addr sp : Nat) : String :=
  if 65768 ≤ addr ∧ addr < 81704 then "code"
  else if 86032 ≤ addr ∧ addr < 86048 then "allocator-cursor"
  else if 86048 ≤ addr ∧ addr < 67194912 then "heap"
  else if 67194912 ≤ addr ∧ addr < 69292064 then "input"
  else if 69292064 ≤ addr ∧ addr < 69292928 then "decoder-global"
  else if sp - 65536 ≤ addr ∧ addr ≤ sp + 65536 then "stack"
  else "unclassified"

/-- The Row A const-offset bindings of the three nested `readU64` children. -/
def childOffsets : List Nat := [0, 8, 16]

/-- `contractOptionalBlobSchedule.stepBound`. -/
def stepBound : Nat := 256

/-- The value of the input byte load at `addr` (0 if not loaded). -/
def loadByte (ev : OccEvidence) (addr : Nat) : Nat :=
  (ev.inputByteLoads.find? (fun p => p.1 == addr)).elim 0 Prod.snd

/-- The eight input addresses of the `readU64` at `base + off`. -/
def fieldAddrs (base off : Nat) : List Nat := (List.range 8).map (fun j => base + off + j)

/-- The little-endian `u64` read at `base + off`. -/
def readWord (ev : OccEvidence) (base off : Nat) : Nat :=
  (List.range 8).foldl (fun acc j => acc + loadByte ev (base + off + j) * 256 ^ j) 0

/-- The slice-start address (min input load address), if any input byte was loaded. -/
def slicePtr (ev : OccEvidence) : Option Nat := (ev.inputByteLoads.map Prod.fst).min?

/-- The 24-byte blob-schedule slice reconstructed from the actual production loads. -/
def sliceBytes (ev : OccEvidence) : ByteArray :=
  match slicePtr ev with
  | some base => ⟨((List.range 24).map (fun j => UInt8.ofNat (loadByte ev (base + j)))).toArray⟩
  | none => ByteArray.empty

/-- Whether the input loads are EXACTLY the three 8-byte windows at the Row A offsets 0/8/16 — no gap,
no extra, no shift. Ties the observed load addresses to the generated const-offset bindings. -/
def offsetsRealized (ev : OccEvidence) : Bool :=
  match slicePtr ev with
  | some base =>
      let want := (childOffsets.flatMap (fun off => fieldAddrs base off))
      let got := ev.inputByteLoads.map Prod.fst
      want.all (· ∈ got) && got.all (· ∈ want)
  | none => false

/-- The checker, reproducing the Python oracle `evaluate_compact`. -/
def evaluateOcc (ev : OccEvidence) : CheckResult :=
  let declared := ev.declaredEdges
  let classes := ev.inRegionStores.map (fun s => classifyWrite s.2.1 ev.sp)
  let realized := offsetsRealized ev
  { entryReached := ev.firstExecuted == ev.entryPc
    edgesSubsetOfCfg := ev.occExecEdges.all (· ∈ declared)
    childOffsetsFromLoads := if ev.arm == "present" then some realized else none
    decodedBlobSchedule :=
      if ev.arm == "present" then
        match slicePtr ev with
        | some base => if realized then some [readWord ev base 0, readWord ev base 8, readWord ev base 16]
                       else none
        | none => none
      else none
    resultSlotOnStack := classifyWrite ev.a0 ev.sp == "stack"
    withinStepBound := ev.occInsnCount ≤ stepBound
    noAllocation := !(classes.contains "heap") && !(classes.contains "allocator-cursor")
    inputPreserved := !(classes.contains "input")
    codePreserved := !(classes.contains "code")
    noUnclassifiedWrites := !(classes.contains "unclassified") }

/-- **Lean ≡ Python.** The checker reproduces the oracle's result on every arm (present/absent/malformed).
Kernel-checked. -/
theorem checker_agrees_with_oracle :
    allArms.all (fun p => evaluateOcc p.1 == p.2) = true := by native_decide

/-- **Present arm is a GO.** Every check passes against the unchanged production ELF. -/
theorem present_arm_go :
    let r := evaluateOcc presentEvidence
    r.entryReached ∧ r.edgesSubsetOfCfg ∧ r.childOffsetsFromLoads = some true ∧
      r.resultSlotOnStack ∧ r.withinStepBound ∧ r.noAllocation ∧ r.inputPreserved ∧
      r.codePreserved ∧ r.noUnclassifiedWrites := by native_decide

/-- The blob-schedule fields the handwritten meaning computes on a slice, as `Nat`s (`[]` if the
meaning does not decode a present schedule). -/
def meaningFields (bytes : ByteArray) : List Nat :=
  match meaningOptionalBlobSchedule bytes with
  | .ok (some s) => [s.target.toNat, s.max.toNat, s.baseFeeUpdateFraction.toNat]
  | _ => []

/-- **RoutineSpec.meaning.** The 24-byte slice the production ELF actually loaded decodes, under the
handwritten `meaningOptionalBlobSchedule`, to exactly the fields the evidence recorded (22/23/24). -/
theorem present_meaning_agrees :
    meaningFields (sliceBytes presentEvidence) = [22, 23, 24] := by native_decide

/-- The evidence's decoded fields equal what the handwritten meaning computes on the same slice. -/
theorem present_decoded_matches_meaning :
    (evaluateOcc presentEvidence).decodedBlobSchedule = some [22, 23, 24] := by native_decide

/-!
## Negative tests — each corruption of the generated evidence flips a check (mutation survival blocks
the row). These are the same eight classes as the Python `negative_tests.py`, ported across the boundary.
-/

/-- A store record inside the occurrence at a corrupt address (the pc is irrelevant to classification). -/
private def badStore (addr : Nat) : Nat × Nat × Nat × Nat := (76890, addr, 8, 0)

/-- wrong occurrence entry: the first executed PC is not the declared entry. -/
theorem negative_wrong_entry :
    (evaluateOcc { presentEvidence with firstExecuted := presentEvidence.entryPc + 4 }).entryReached
      = false := by native_decide

/-- +8 ABI error: the first field's 8 loads are dropped, so the loads no longer realize offsets 0/8/16. -/
theorem negative_plus8_offset :
    (evaluateOcc { presentEvidence with
        inputByteLoads := presentEvidence.inputByteLoads.drop 8 }).childOffsetsFromLoads
      = some false := by native_decide

/-- swapped register / wrong result slot: the indirect-return slot (a0) is moved off-stack (into heap). -/
theorem negative_wrong_result_slot :
    (evaluateOcc { presentEvidence with a0 := 86048 + 16 }).resultSlotOnStack = false := by native_decide

/-- reassigned (phantom) edge: executed control flow not present in the generated CFG. -/
theorem negative_phantom_edge :
    (evaluateOcc { presentEvidence with
        occExecEdges := presentEvidence.occExecEdges ++ [(76890, 999999)] }).edgesSubsetOfCfg
      = false := by native_decide

/-- wrong allocation fact: an injected heap store in a non-allocating routine. -/
theorem negative_heap_alloc :
    (evaluateOcc { presentEvidence with
        inRegionStores := presentEvidence.inRegionStores ++ [badStore (86048 + 32)] }).noAllocation
      = false := by native_decide

/-- out-of-frame (unclassified) write. -/
theorem negative_out_of_frame :
    (evaluateOcc { presentEvidence with
        inRegionStores := presentEvidence.inRegionStores ++ [badStore 3735879680] }).noUnclassifiedWrites
      = false := by native_decide

/-- input-preservation violation. -/
theorem negative_input_write :
    (evaluateOcc { presentEvidence with
        inRegionStores := presentEvidence.inRegionStores ++ [badStore (67194912 + 8)] }).inputPreserved
      = false := by native_decide

/-- code-preservation violation. -/
theorem negative_code_write :
    (evaluateOcc { presentEvidence with
        inRegionStores := presentEvidence.inRegionStores ++ [badStore (65768 + 8)] }).codePreserved
      = false := by native_decide

end BinaryFv.SSZ.Zesu.Validation
