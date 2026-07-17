import BinaryFv.Keccak.Reth.Proof.Helpers.CopyFromSlice.Regs

/-!
# `copy_from_slice` fall-through register-file framing
-/

namespace BinaryFv.Keccak
open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open MemoryAccessType
open mem_payload
open page_based_mem_type

/-! ## Fall-through register-file framing (local copies of the memcpy private helpers) -/

/-- The `nextPC` slot of the post-execute state of a GP-writing fall-through instruction is `pc+4`. -/
theorem gpNextPc (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (hrd : nextPC ≠ rd) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC =
      some (Sail.BitVec.addInt pc 4) := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? nextPC
      = (coreControlFlowNextState Y pc).regs.get? nextPC :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd nextPC v hrd
    _ = some (Sail.BitVec.addInt pc 4) := by
        change (Y.regs.insert nextPC (Sail.BitVec.addInt pc 4)).get? nextPC = _
        rw [Std.ExtDHashMap.get?_insert]; simp

/-- Any register other than `nextPC` and `rd` reads through the post-execute state of a GP-writing
fall-through instruction back to the pre-`nextPC` state `Y`. -/
theorem gpGet (Y : State) (pc : BitVec 64) (rd : Register) (v : RegisterType rd)
    (r : Register) (hrd : r ≠ rd) (hnp : r ≠ nextPC) :
    ((coreControlFlowNextState Y pc).regs.insert rd v).get? r = Y.regs.get? r := by
  calc ((coreControlFlowNextState Y pc).regs.insert rd v).get? r
      = (coreControlFlowNextState Y pc).regs.get? r :=
        writeReg_read_unchanged (coreControlFlowNextState Y pc) rd r v hrd
    _ = Y.regs.get? r := by
        simpa [coreControlFlowNextState] using
          writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- Any register other than `nextPC` reads through `coreControlFlowNextState Y pc` back to `Y`. -/
theorem coreGetInc' (Y : State) (pc : BitVec 64) (r : Register) (hnp : r ≠ nextPC) :
    (coreControlFlowNextState Y pc).regs.get? r = Y.regs.get? r := by
  simpa [coreControlFlowNextState] using
    writeReg_read_unchanged Y nextPC r (Sail.BitVec.addInt pc 4) hnp

/-- Any register untouched by a not-taken-branch retirement reads through to the pre-state `base`. -/
theorem notTakenGet (base : State) (pc ret : BitVec 64) (r : Register)
    (hPC : r ≠ PC) (hmr : r ≠ minstret) (hnp : r ≠ nextPC) (hmi : r ≠ minstret_increment) :
    (tryStepControlFlowAfterRetired
      (coreControlFlowNextState (tryStepControlFlowAfterIncrement base) pc)
      (Sail.BitVec.addInt pc 4) ret).regs.get? r = base.regs.get? r :=
  (retiredFrameGet _ _ _ r hPC hmr).trans
    ((coreGetInc' _ pc r hnp).trans (afterIncGet base r hmi))

end BinaryFv.Keccak
