import BinaryFv.Zesu.MachineExecution.ReadInputSteps
import BinaryFv.RiscV.Elfling.Seg

/-!
# Production `read_input` composition

The straight-line register setup is accumulated with `Seg`; the following syscall/retry portion is
proved by induction over the remaining stdin suffix. No observed fixture length is unrolled.
-/

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv BinaryFv.Binary BinaryFv.Binary.Elfling BinaryFv.RiscV BinaryFv.RiscV.Elfling
open PreSail LeanRV64DExecutable.Functions Register

private def readInputSetupWrites : RegSet := fun register =>
  stepBookkeeping register ∨ register = x6 ∨ register = x16 ∨ register = x15 ∨ register = x14

private def readInputBufferBaseHigh : BitVec 64 :=
  0x1014c + sign_extend (m := 64) (0x2000a#20 ++ 0x000#12)

private theorem readInputSetup_preserved :
    RegSet.Disjoint instructionPreserved readInputSetupWrites := by
  intro register preserved written
  rcases written with bookkeeping | rfl | rfl | rfl | rfl
  · exact platformPreserved_disjoint register preserved.1 bookkeeping
  all_goals simp [instructionPreserved, platformPreserved] at preserved

private theorem readInputPc_10140 : pcInRanges Elflings.readInputExecutionPcRanges 0x10140 := by
  exact ⟨(0x10140, 0x10190), by native_decide, by native_decide, by native_decide⟩

private theorem readInputPc_10144 : pcInRanges Elflings.readInputExecutionPcRanges 0x10144 := by
  exact ⟨(0x10140, 0x10190), by native_decide, by native_decide, by native_decide⟩

private theorem readInputPc_10148 : pcInRanges Elflings.readInputExecutionPcRanges 0x10148 := by
  exact ⟨(0x10140, 0x10190), by native_decide, by native_decide, by native_decide⟩

private theorem readInputPc_1014c : pcInRanges Elflings.readInputExecutionPcRanges 0x1014c := by
  exact ⟨(0x10140, 0x10190), by native_decide, by native_decide, by native_decide⟩

private theorem readInputNotExit (pc : BitVec 64)
    (notCaller : pc.toNat ≠ 0x14ccc := by native_decide) :
    ¬pcInList Elflings.readInputExitPcs pc := by
  intro exit
  rw [pcInList] at exit
  apply notCaller
  simpa [Elflings.readInputExitPcs] using exit

/-- The first three production instructions retain the caller slots and initialize the byte count. -/
theorem readInput_setup_prefix (args : ReadInputArgs) (fromStep : Nat) (before : EndpointState)
    (entry : ReadInputEntry args before) :
    ∃ after : State,
      Seg (pcInRanges Elflings.readInputExecutionPcRanges)
        (pcInList Elflings.readInputExitPcs) (fun _ _ _ _ _ => False)
        readInputSetupWrites noMemory
        [⟨x14, readInputBufferBaseHigh⟩,
          ⟨x15, iTypeResult .ADDI 0 0⟩,
          ⟨x16, iTypeResult .ADDI 0 (BitVec.ofNat 64 args.sizeSlot)⟩,
          ⟨x6, iTypeResult .ADDI 0 (BitVec.ofNat 64 args.bufferSlot)⟩]
        fromStep 4 before.machine after 0x10150 := by
  rcases entry with
    ⟨_returnPc, _inputBound, _stdin, _cursor, atPc, _returnRegister, bufferRegister,
      sizeRegister, _savedReturn, code, configured⟩
  obtain ⟨retired, retiredRead⟩ := configured.retiredCounter
  have seg0 := Seg.nil (pcInRanges Elflings.readInputExecutionPcRanges)
    (pcInList Elflings.readInputExitPcs) readInputSetupWrites noMemory fromStep
    (childSummary := fun _ _ _ _ _ => False) ⟨retired, retiredRead⟩ atPc
  obtain ⟨state1, seg1⟩ := seg0.step readInputPc_10140 (readInputNotExit 0x10140)
    x6 (iTypeResult .ADDI 0 (BitVec.ofNat 64 args.bufferSlot)) 0x10144
    (readInputMoveBufferSlotStep fromStep before.machine (BitVec.ofNat 64 args.bufferSlot)
      configured atPc code bufferRegister)
    (by decide) (by intro register bookkeeping; exact Or.inl bookkeeping) (Or.inr (Or.inl rfl))
    (by decide) (by decide) (by decide)
  have configured1 := configured.mono (seg1.agree readInputSetup_preserved) seg1.retired
  have code1 : Artifacts.programImage.fileBytesLoadedFaithfully state1.mem := by
    rw [seg1.memEq noMemory_empty]
    exact code
  have size1 : state1.regs.get? x11 = some (BitVec.ofNat 64 args.sizeSlot) :=
    (seg1.get x11 (by simp [readInputSetupWrites, stepBookkeeping])).trans sizeRegister
  obtain ⟨state2, seg2⟩ := seg1.step readInputPc_10144 (readInputNotExit 0x10144)
    x16 (iTypeResult .ADDI 0 (BitVec.ofNat 64 args.sizeSlot)) 0x10148
    (readInputMoveSizeSlotStep (fromStep + 1) state1 (BitVec.ofNat 64 args.sizeSlot)
      configured1 seg1.atPc code1 size1)
    (by decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inl rfl))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured2 := configured.mono (seg2.agree readInputSetup_preserved) seg2.retired
  have code2 : Artifacts.programImage.fileBytesLoadedFaithfully state2.mem := by
    rw [seg2.memEq noMemory_empty]
    exact code
  obtain ⟨state3, seg3⟩ := seg2.step readInputPc_10148 (readInputNotExit 0x10148)
    x15 (iTypeResult .ADDI 0 0) 0x1014c
    (readInputZeroOffsetStep (fromStep + 2) state2 configured2 seg2.atPc code2)
    (by decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  have configured3 := configured.mono (seg3.agree readInputSetup_preserved) seg3.retired
  have code3 : Artifacts.programImage.fileBytesLoadedFaithfully state3.mem := by
    rw [seg3.memEq noMemory_empty]
    exact code
  obtain ⟨state4, seg4⟩ := seg3.step readInputPc_1014c (readInputNotExit 0x1014c)
    x14 readInputBufferBaseHigh 0x10150
    (readInputBufferBaseHighStep (fromStep + 3) state3 configured3 seg3.atPc code3)
    (by decide) (by intro register bookkeeping; exact Or.inl bookkeeping)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by decide) (by decide)
    (by simp [RegsOutside, stepBookkeeping, RegSet.union, RegSet.only])
  exact ⟨state4, seg4⟩

end BinaryFv.Zesu.MachineExecution
