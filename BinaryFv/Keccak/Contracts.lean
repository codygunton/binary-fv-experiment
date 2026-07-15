import BinaryFv.Keccak.Decode
import BinaryFv.RISCV.Framing

namespace BinaryFv.Keccak.Contracts

open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RISCV

abbrev r16 : regidx := .Regidx 16#5
abbrev r19 : regidx := .Regidx 19#5
abbrev r29 : regidx := .Regidx 29#5

/-- Recognize the fixed `r29`/`r19`/`r16` XOR shape in a decoded word. -/
def isCoreXor (word : DecodedWord) : Bool :=
  match word.instruction with
  | .RTYPE (source2, source1, destination, .XOR) =>
    source2 == r29 && source1 == r19 && destination == r16
  | _ => false

def coreXorCandidate? : Option DecodedWord :=
  match portableCoreDecodedWords? with
  | some words => words.toList.find? isCoreXor
  | none => none

def coreXorCandidatePresent : Bool :=
  coreXorCandidate?.isSome

/-- Closed inventory diagnostic only; this `native_decide` fact follows the project trust policy. -/
theorem core_xor_candidate_present : coreXorCandidatePresent = true := by
  native_decide

/-- Generated Sail semantics for the fixed `r29`/`r19`/`r16` XOR on an arbitrary machine state. -/
theorem execute_core_xor (state : State) (left right : BitVec 64)
    (leftRead : state.regs.get? x19 = some left)
    (rightRead : state.regs.get? x29 = some right) :
    (execute_RTYPE r29 r19 r16 .XOR).run state =
      .ok (.Retire_Success ()) { state with regs := state.regs.insert x16 (left ^^^ right) } := by
  have r16Nat : (Sail.BitVec.toNatInt 16#5).toNat = 16 := by decide
  have r19Nat : (Sail.BitVec.toNatInt 19#5).toNat = 19 := by decide
  have r29Nat : (Sail.BitVec.toNatInt 29#5).toNat = 29 := by decide
  simp [execute_RTYPE, rX_bits, rX, wX_bits, wX, PreSail.readReg, PreSail.writeReg, r16Nat,
    r19Nat, r29Nat, leftRead, rightRead, EStateM.run, EStateM.bind, EStateM.get,
    EStateM.modifyGet, EStateM.pure, EStateM.instMonad, MonadState.get, MonadState.modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, getThe, modify, xreg_write_callback,
    xreg_full_write_callback,
    reg_name_forwards, get_config_use_abi_names, encdec_reg_forwards,
    encdec_reg_forwards_matches, reg_arch_name_raw_forwards, LeanRV64DExecutable.Functions.not,
    zero_extend, RETIRE_SUCCESS, regval_into_reg, regval_from_reg]

theorem execute_core_xor_preserves_memory (state : State) (left right : BitVec 64)
    (leftRead : state.regs.get? x19 = some left)
    (rightRead : state.regs.get? x29 = some right) :
    (match (execute_RTYPE r29 r19 r16 .XOR).run state with
    | .ok _ state' => state'.mem
    | .error _ state' => state'.mem) = state.mem := by
  rw [execute_core_xor state left right leftRead rightRead]

theorem execute_core_xor_register_frame (state : State) (left right : BitVec 64) :
    RegisterEqualOutside state { state with regs := state.regs.insert x16 (left ^^^ right) } x16 :=
  writeReg_register_frame state x16 (left ^^^ right)

end BinaryFv.Keccak.Contracts
