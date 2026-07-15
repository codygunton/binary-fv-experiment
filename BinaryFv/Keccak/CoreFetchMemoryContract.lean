import BinaryFv.Keccak.CoreStepContract
import BinaryFv.RISCV.FetchMemoryContract

namespace BinaryFv.Keccak

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

/-- Feed exact Machine sparse-RAM fetch through the fixed XOR instruction-retirement slice. -/
theorem runHartActiveCoreXorRetiresWithFetchMemory (stepNo : Nat) (state : State)
    (pc left right : BitVec 64) (byte0 byte1 byte2 byte3 : BitVec 8)
    (platform : FetchBasePlatform state pc) (noMMIO : FetchMemoryNoMMIO state pc)
    (bytes : FetchBytesAt state pc byte0 byte1 byte2 byte3)
    (interrupts : InterruptDisabled state) (base : BaseInstructionEncoding byte0)
    (decode : Runs (ext_decode (fetchWord byte0 byte1 byte2 byte3)) state state
      (.RTYPE (Contracts.r29, Contracts.r19, Contracts.r16, .XOR)))
    (notExpected : LandingPadNotExpected state)
    (leftRead : (coreXorNextState state pc).regs.get? x19 = some left)
    (rightRead : (coreXorNextState state pc).regs.get? x29 = some right) :
    Runs (run_hart_active stepNo) state (coreXorRetiredState state pc left right)
      (.Step_Execute (.Retire_Success (),
        zero_extend (m := 32) (fetchWord byte0 byte1 byte2 byte3))) := by
  have fetchBytes : FetchBytesBaseContract state pc byte0 byte1 byte2 byte3 :=
    fetch_bytes_machine_instructionFetch_fetch_word_run state pc byte0 byte1 byte2 byte3 platform
      noMMIO bytes
  exact runHartActiveCoreXorRetires stepNo state pc left right byte0 byte1 byte2 byte3 platform
    interrupts base fetchBytes decode notExpected leftRead rightRead

end BinaryFv.Keccak
