import BinaryFv.SSZ.Zesu.Analysis.Decode

namespace BinaryFv.SSZ.Zesu.Analysis

open BinaryFv.RiscV
open PreSail LeanRV64DExecutable.Functions Register

private macro "decode_run" : tactic =>
  `(tactic|
    (unfold Runs
     rw [extDecode_eq]
     simp only [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports, bool_bit_backwards,
       PreSail.readReg, EStateM.run, EStateM.bind, EStateM.get, EStateM.pure,
       EStateM.instMonad, EStateM.instMonadExceptOfOfBacktrackable, getThe,
       MonadState.get, MonadStateOf.get, *]
     rfl))

/-- The canonical decoder's success epilogue builds an 832-byte `RawStatelessInput` on its
stack, stores the zero success status at result offset 832, and copies that payload to result. -/
def rawResultSuccessSites : Array Nat := #[0x12f90, 0x12f94, 0x12f98, 0x12f9c, 0x12fa0, 0x12fa4,
  0x12fa8]

def rawResultSuccessWords : Array Nat := #[0x61613023, 0x60913423, 0x28013503, 0x34051023,
  0x2d010593, 0x34000613, 0xd44fd06f]

/-- This fact is checked directly against immutable ELF bytes, not source or debug mappings. -/
def rawResultSuccessBlockValid : Bool :=
  rawResultSuccessSites.zip rawResultSuccessWords |>.all fun entry =>
    Artifact.programImage.readU32LE? entry.1 == some entry.2

theorem raw_result_success_block_valid : rawResultSuccessBlockValid = true := by
  native_decide

/-- The decoder writes chain-config fields into the final root-object tail before result copy.
The stores cover offsets 736, 744, 752/760, 768/776, and 784/792/800/808 relative to the root. -/
def rawChainConfigResultStoreSites : Array Nat := #[
  0x12e64, 0x12e68, 0x12e6c, 0x12e70, 0x12e8c, 0x12e90, 0x12e94, 0x12e98, 0x12e9c, 0x12ea0]

def rawChainConfigResultStoreWords : Array Nat := #[
  0x5ce13023, 0x5cf13423, 0x5d013823, 0x5d113c23, 0x5a813823, 0x5ba13c23, 0x5f613023,
  0x5f513423, 0x5f313823, 0x5f210c23]

/-- The field-placement evidence is checked only against the immutable decoder image. -/
def rawChainConfigResultStoresValid : Bool :=
  rawChainConfigResultStoreSites.zip rawChainConfigResultStoreWords |>.all fun entry =>
    Artifact.programImage.readU32LE? entry.1 == some entry.2

theorem raw_chain_config_result_stores_valid : rawChainConfigResultStoresValid = true := by
  native_decide

/-- Generated Sail decodes the ELF-pinned stores that materialize the chain-config tail of the
stack root.  This fixes each source register and stack offset without asserting an unobserved Zig
optional-value encoding. -/
theorem raw_chain_config_result_stores_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x5a813823 : BitVec 32)) state state
        (.STORE (1456#12, .Regidx 8#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5ba13c23 : BitVec 32)) state state
        (.STORE (1464#12, .Regidx 26#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5ce13023 : BitVec 32)) state state
        (.STORE (1472#12, .Regidx 14#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5cf13423 : BitVec 32)) state state
        (.STORE (1480#12, .Regidx 15#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5d013823 : BitVec 32)) state state
        (.STORE (1488#12, .Regidx 16#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5d113c23 : BitVec 32)) state state
        (.STORE (1496#12, .Regidx 17#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f613023 : BitVec 32)) state state
        (.STORE (1504#12, .Regidx 22#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f513423 : BitVec 32)) state state
        (.STORE (1512#12, .Regidx 21#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f313823 : BitVec 32)) state state
        (.STORE (1520#12, .Regidx 19#5, .Regidx 2#5, 8)) ∧
      Runs (ext_decode (0x5f210c23 : BitVec 32)) state state
        (.STORE (1528#12, .Regidx 18#5, .Regidx 2#5, 1)) := by
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  constructor <;> decode_run
  decode_run

end BinaryFv.SSZ.Zesu.Analysis
