import BinaryFv.Zesu.Machine.RegisterWrite
import BinaryFv.Zesu.Machine.Target

/-!
# The baseline: one instruction of the Zesu SSZ endpoint, retired

`0x70` is `lbu a0, 1(a2)`, encoded `03 45 16 00`. It is the first instruction of the ten-instruction
`mem.readInt` motif at `0x70`–`0x94` — Case A of the motif campaign — and this module is the
measurement every later claim is quoted against.

**Nothing above this file is allowed to assume what one instruction costs.** The campaign's whole
question is whether a motif lemma over `n` instructions beats `n` of these, and that comparison is
meaningless until one of these exists and has been counted.

## What the obligation actually decomposes into

| part | supplier | discharged by |
|---|---|---|
| four image bytes | `Target.fetchInstruction` | 4 `native_decide`, per instruction, unshareable |
| decode | `DecodeTactic.decode_run` | one tactic call |
| execute | `RiscV/.../Execute/Load.lean:execute_LOAD_lbu_run` | 12 premises, caller-supplied |
| retire | `RegisterWrite.fallThroughRegisterWriteStep` | one `StepPremises` + 4 `decide` |

The split matters more than the total. `StepPremises` is carried once per segment, and the four
disequalities are `decide`, so those are not per-instruction costs in any real proof. What *is* per
instruction is the four `native_decide`s and the execute premises, and of those only the four
`native_decide`s are unavoidable — the execute premises describe what this instruction does, which
is exactly the thing a motif lemma might state once for a shape.
-/

namespace BinaryFv.Zesu.Machine

open BinaryFv BinaryFv.Binary BinaryFv.RiscV
open BinaryFv.Zesu.Generated
open PreSail LeanRV64DExecutable.Functions Register

/-- The instruction word at `0x70`, read out of the generated image rather than written down.

Stated separately so that the address-to-bytes step is visible and checkable on its own: if the
image ever disagrees with this, the failure names `0x70` rather than surfacing somewhere inside a
step proof. -/
theorem word_at_0x70 :
    programImage.readByte? 0x70 = some 0x03 ∧
      programImage.readByte? 0x71 = some 0x45 ∧
        programImage.readByte? 0x72 = some 0x16 ∧
          programImage.readByte? 0x73 = some 0x00 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The fetch half of `0x70`, complete. This is the part a motif lemma can never share, because the
next instruction owns a different word. -/
theorem fetch_0x70 (state : State) (loaded : programImage.matchesMemory state.mem) :
    FetchBytesAt state (BitVec.ofNat 64 0x70)
      (BitVec.ofNat 8 (0x03 : UInt8).toNat) (BitVec.ofNat 8 (0x45 : UInt8).toNat)
      (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat) :=
  fetchInstruction state 0x70 0x03 0x45 0x16 0x00 loaded

/-- `0x70` retires, given the machine premises and the Sail `execute` run for this `lbu`.

The `execute` premise is deliberately *not* discharged here. It is the per-instruction semantic
content — which address this load reads and what it writes — and it is precisely what a motif lemma
would state once per shape rather than once per site. Leaving it as a hypothesis keeps this theorem
honest about the split: everything else is machine bookkeeping, and it is already collapsed. -/
theorem step_0x70 (stepNo : Nat) (state : State)
    (loaded : programImage.matchesMemory (tryStepControlFlowAfterIncrement state).mem)
    (premises : StepPremises state (BitVec.ofNat 64 0x70))
    (destination : Register) (value : RegisterType destination)
    (inst : instruction)
    (decode : Runs (ext_decode (fetchWord
        (BitVec.ofNat 8 (0x03 : UInt8).toNat) (BitVec.ofNat 8 (0x45 : UInt8).toNat)
        (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)))
      (tryStepControlFlowAfterIncrement state) (tryStepControlFlowAfterIncrement state) inst)
    (execute : Runs (execute inst)
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x70))
      { coreControlFlowNextState (tryStepControlFlowAfterIncrement state) (BitVec.ofNat 64 0x70)
        with regs :=
          (coreControlFlowNextState (tryStepControlFlowAfterIncrement state)
            (BitVec.ofNat 64 0x70)).regs.insert destination value }
      (.Retire_Success ()))
    (notNextPc : destination ≠ nextPC) (notHart : destination ≠ hart_state)
    (notIncrement : destination ≠ minstret_increment) (notRetired : destination ≠ minstret) :
    Runs (try_step stepNo false) state
      (afterRegisterWrite state (BitVec.ofNat 64 0x70) premises.retired destination value) false :=
  fallThroughRegisterWriteStep stepNo state (BitVec.ofNat 64 0x70)
    (BitVec.ofNat 8 (0x03 : UInt8).toNat) (BitVec.ofNat 8 (0x45 : UInt8).toNat)
    (BitVec.ofNat 8 (0x16 : UInt8).toNat) (BitVec.ofNat 8 (0x00 : UInt8).toNat)
    inst destination value premises (fetch_0x70 _ loaded) (by unfold BaseInstructionEncoding; decide)
    decode execute notNextPc notHart notIncrement notRetired

end BinaryFv.Zesu.Machine
