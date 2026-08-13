import BinaryFv.Zesu.Entrypoints.SszDecodeRoot.Level2Contracts

/-!
# Level-1 observation-writer refinement

This module composes the selected Level-2 encoder contracts into the `writeSuccess` and
`writeFailure` contracts used by the Level-1 endpoint proof.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV

private theorem writeFailureChildRegion_in_parent {pc : BitVec 64}
    (inside : pcInRanges Elflings.writeFailureRawLine127ExecutionPcRanges pc) :
    pcInRanges Elflings.writeFailureExecutionPcRanges pc := by
  unfold pcInRanges at inside ⊢
  rcases inside with ⟨range, member, lower, upper⟩
  exact ⟨range, by simpa [Elflings.writeFailureRawLine127ExecutionPcRanges,
    Elflings.writeFailureExecutionPcRanges] using member, lower, upper⟩

/-- `writeFailure` is exactly its selected constant-record child instance. -/
theorem writeFailureInstanceContract_of_level2
    (child : WriteFailureRecordInstanceContract) : WriteFailureInstanceContract := by
  obtain ⟨bound, implements⟩ := child
  refine ⟨bound, ?_⟩
  intro args fromStep before entry
  obtain ⟨count, after, unit, positive, bounded, trace, childExitPc, _allows, exit⟩ :=
    implements () fromStep before ⟨entry.2.1, entry.2.2.2⟩
  have trace' := trace.weaken (fun pc inside => writeFailureChildRegion_in_parent inside)
  refine ⟨count, after, failureRecordBytes, positive, bounded, trace', ?_, ?_, ?_⟩
  · rcases childExitPc with ⟨pc, atPc, listed⟩
    exact ⟨pc, atPc, by
      unfold pcInList at listed ⊢
      simpa [Elflings.writeFailureRawLine127ExitPcs,
        Elflings.writeFailureExitPcs] using listed⟩
  · change decodeZesuObservation failureRecordBytes = some .failure
    rfl
  · rcases exit with ⟨exitAt, stdout, stdin, cursor, exitCode, mem, frame⟩
    have returnEq : args.returnAddress = 0x14d24 := by
      simpa [Elflings.writeFailureExitPcs] using entry.1
    refine ⟨?_, by rfl, stdout, stdin, cursor, exitCode, mem, frame⟩
    rw [returnEq]
    exact exitAt

end BinaryFv.Zesu.MachineExecution
