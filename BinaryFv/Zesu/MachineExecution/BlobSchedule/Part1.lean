import BinaryFv.RiscV.Logic.BlockStep
import BinaryFv.RiscV.Instruction.Execute.ShiftOr
import BinaryFv.RiscV.Instruction.Execute.StoreByte
import BinaryFv.RiscV.Proof.ImageFetch
import BinaryFv.Zesu.ControlFlow.Decode
import BinaryFv.Zesu.MachineExecution.DecodeTactic
import BinaryFv.Zesu.MachineExecution.RegisterRuns

namespace BinaryFv.Zesu.MachineExecution

open BinaryFv.RiscV
open BinaryFv.Binary.ProgramImage
open PreSail LeanRV64DExecutable.Functions Register

/-- The canonical decoder's success epilogue builds an 832-byte `RawStatelessInput` on its
stack, stores the zero success status at result offset 832, and copies that payload to result. -/
def rawResultSuccessSites : Array Nat := #[0x12f90, 0x12f94, 0x12f98, 0x12f9c, 0x12fa0, 0x12fa4,
  0x12fa8]

def rawResultSuccessWords : Array Nat := #[0x61613023, 0x60913423, 0x28013503, 0x34051023,
  0x2d010593, 0x34000613, 0xd44fd06f]

/-- This fact is checked directly against immutable ELF bytes, not source or debug mappings. -/
def rawResultSuccessBlockValid : Bool :=
  rawResultSuccessSites.zip rawResultSuccessWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

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
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

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
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  decode_run

/-- Every byte-load instruction used by the present 24-byte blob-schedule branch is pinned to the
immutable decoder image.  The non-contiguous groups reflect the intervening endian assembly. -/
def rawBlobSchedulePresentLoadSites : Array Nat := #[
  0x12cbc, 0x12cc0, 0x12cc4, 0x12cc8, 0x12ccc, 0x12cd0, 0x12cd4, 0x12cd8,
  0x12cdc, 0x12ce0, 0x12ce4, 0x12ce8, 0x12d08, 0x12d0c, 0x12d10, 0x12d14,
  0x12d40, 0x12d44, 0x12d48, 0x12d4c, 0x12d70, 0x12d74, 0x12d78, 0x12d7c]

def rawBlobSchedulePresentLoadWords : Array Nat := #[
  0x000bc503, 0x001bc583, 0x002bc603, 0x003bc683, 0x004bc703, 0x005bc783,
  0x006bc803, 0x007bc883, 0x008bc283, 0x009bc303, 0x00abc383, 0x00bbce03,
  0x00cbc583, 0x00dbc683, 0x00ebc783, 0x00fbce83, 0x010bc683, 0x011bc303,
  0x012bc383, 0x013bce03, 0x015bc383, 0x014bce03, 0x016bce83, 0x017bcf03]

def rawBlobSchedulePresentLoadsValid : Bool :=
  rawBlobSchedulePresentLoadSites.zip rawBlobSchedulePresentLoadWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_present_loads_valid : rawBlobSchedulePresentLoadsValid = true := by
  native_decide

/-- The first six schedule bytes are assembled by four shifts and three ORs at the immutable
ELF PCs between the two contiguous load groups. -/
def rawBlobSchedulePresentAssemblySites : Array Nat :=
  #[0x12cec, 0x12cf0, 0x12cf4, 0x12cf8, 0x12cfc, 0x12d00, 0x12d04]

def rawBlobSchedulePresentAssemblyWords : Array Nat :=
  #[0x00859593, 0x01061613, 0x01869693, 0x00879793, 0x00a5e533, 0x00c6e633, 0x00e7e733]

def rawBlobSchedulePresentAssemblyValid : Bool :=
  rawBlobSchedulePresentAssemblySites.zip rawBlobSchedulePresentAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_present_assembly_valid : rawBlobSchedulePresentAssemblyValid = true := by
  native_decide

/-- Schedule bytes 6--15 are assembled by a second, longer fragment of six shifts and four ORs
between the second and third contiguous load groups. -/
def rawBlobScheduleSecondAssemblySites : Array Nat :=
  #[0x12d18, 0x12d1c, 0x12d20, 0x12d24, 0x12d28, 0x12d2c, 0x12d30, 0x12d34, 0x12d38, 0x12d3c]

def rawBlobScheduleSecondAssemblyWords : Array Nat :=
  #[0x01081813, 0x01889893, 0x00831313, 0x01039393, 0x018e1e13, 0x00869693,
    0x0108e833, 0x005368b3, 0x007e62b3, 0x00b6e5b3]

def rawBlobScheduleSecondAssemblyValid : Bool :=
  rawBlobScheduleSecondAssemblySites.zip rawBlobScheduleSecondAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_second_assembly_valid :
    rawBlobScheduleSecondAssemblyValid = true := by
  native_decide

/-- Schedule bytes 14--19 are assembled by a third fragment of five shifts and three ORs between
the third and fourth contiguous load groups. -/
def rawBlobScheduleThirdAssemblySites : Array Nat :=
  #[0x12d50, 0x12d54, 0x12d58, 0x12d5c, 0x12d60, 0x12d64, 0x12d68, 0x12d6c]

def rawBlobScheduleThirdAssemblyWords : Array Nat :=
  #[0x01079793, 0x018e9e93, 0x00831313, 0x01039393, 0x018e1e13, 0x00fee7b3, 0x00d366b3, 0x007e6333]

def rawBlobScheduleThirdAssemblyValid : Bool :=
  rawBlobScheduleThirdAssemblySites.zip rawBlobScheduleThirdAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_third_assembly_valid :
    rawBlobScheduleThirdAssemblyValid = true := by
  native_decide

/-- The fourth and final assembly fragment folds the branch's twenty-four bytes into the three
64-bit schedule words held in `s6`, `s5`, and `s3`. -/
def rawBlobScheduleFourthAssemblySites : Array Nat :=
  #[0x12d80, 0x12d84, 0x12d88, 0x12d8c, 0x12d90, 0x12d94, 0x12d98, 0x12d9c, 0x12da0,
    0x12da4, 0x12da8, 0x12dac, 0x12db0, 0x12db4, 0x12db8, 0x12dbc, 0x12dc0]

def rawBlobScheduleFourthAssemblyWords : Array Nat :=
  #[0x00839393, 0x01c3e3b3, 0x010e9e93, 0x018f1f13, 0x01df6e33, 0x00a66533, 0x00e86633,
    0x0112e733, 0x00b7e5b3, 0x00d366b3, 0x007e67b3, 0x02061613, 0x02059593, 0x02079793,
    0x00a66b33, 0x00e5eab3, 0x00d7e9b3]

def rawBlobScheduleFourthAssemblyValid : Bool :=
  rawBlobScheduleFourthAssemblySites.zip rawBlobScheduleFourthAssemblyWords |>.all fun entry =>
    Artifacts.programImage.readU32LE? entry.1 == some entry.2

theorem raw_blob_schedule_fourth_assembly_valid :
    rawBlobScheduleFourthAssemblyValid = true := by
  native_decide

/-- Generated Sail decodes the immutable first endian-assembly fragment without consulting source
or debug metadata. -/
theorem raw_blob_schedule_present_assembly_decode (state : State)
    (privilege : state.regs.get? cur_privilege = some Privilege.Machine)
    (mseccfgBits : BitVec 64) (mseccfg : state.regs.get? Register.mseccfg = some mseccfgBits) :
    Runs (ext_decode (0x00859593 : BitVec 32)) state state
        (.SHIFTIOP (8#6, .Regidx 11#5, .Regidx 11#5, .SLLI)) ∧
      Runs (ext_decode (0x01061613 : BitVec 32)) state state
        (.SHIFTIOP (16#6, .Regidx 12#5, .Regidx 12#5, .SLLI)) ∧
      Runs (ext_decode (0x01869693 : BitVec 32)) state state
        (.SHIFTIOP (24#6, .Regidx 13#5, .Regidx 13#5, .SLLI)) ∧
      Runs (ext_decode (0x00879793 : BitVec 32)) state state
        (.SHIFTIOP (8#6, .Regidx 15#5, .Regidx 15#5, .SLLI)) ∧
      Runs (ext_decode (0x00a5e533 : BitVec 32)) state state
        (.RTYPE (.Regidx 10#5, .Regidx 11#5, .Regidx 10#5, .OR)) ∧
      Runs (ext_decode (0x00c6e633 : BitVec 32)) state state
        (.RTYPE (.Regidx 12#5, .Regidx 13#5, .Regidx 12#5, .OR)) ∧
      Runs (ext_decode (0x00e7e733 : BitVec 32)) state state
        (.RTYPE (.Regidx 14#5, .Regidx 15#5, .Regidx 14#5, .OR)) := by
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  constructor
  · decode_run
  decode_run

end BinaryFv.Zesu.MachineExecution
