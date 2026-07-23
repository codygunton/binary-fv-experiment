import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Execution.Machine
import BinaryFv.RiscV.Execution.Runner
import BinaryFv.RiscV.Execution.ImageLoad
import BinaryFv.RiscV.Platform.NormalState
import BinaryFv.SSZ.Zesu.Artifact.Symbols
import BinaryFv.SSZ.Zesu.Artifact.Layout
import BinaryFv.SSZ.Zesu.Elfling.GeneratedDecoderGlobals
import BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw.Layout
import DecoderGlobals

/-!
# The runner's Sail state builder

Constructs the concrete Sail machine state the exported `zesu_decode_raw` call begins from, then runs
it to the return sentinel. Modeled on the proven Keccak `executeDirect`
(`BinaryFv/Keccak/Reth/Execution/DirectCall.lean`): the same `initializeModel`/`enableMExtension`/PMA/
CSR configuration — Zicclsm is already always-on in this Sail build (`hartSupports Ext_Zicclsm`), so
no extra enable is needed — followed by loading the pinned image, materializing the runner's own
ranges, copying the input, initializing the decoder's private and runtime globals to the fresh model,
and setting the C-ABI entry registers.

Everything address-bearing comes from one place: `canonicalRunnerLayout` for the runner-added ranges,
and the generated `DecoderGlobals` table for the decoder's own globals and the 64 MiB arena. Nothing
here writes an address literal that the layout or the generated globals do not already pin.
-/

namespace BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.SSZ.Zesu

set_option maxRecDepth 10000

/-! ## Generated global addresses

Read off the generated `DecoderGlobals` table, never written by hand. -/

/-- The decoder's private BSS base (`attempted` at the base, `last_status` at +4, `stored_result`
at +16). -/
def decoderBssBase : Nat := Elfling.GeneratedDecoderGlobals.bssBase

/-- The bump-allocator cursor `ZKVM_HEAP_POS`, whose write history is the allocation ledger. -/
def zkvmHeapPos : Nat :=
  (Elfling.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "ZKVM_HEAP_POS")).elim 0 (·.2.1)

/-- The arena ceiling `ZKVM_HEAP_TOP`. -/
def zkvmHeapTop : Nat :=
  (Elfling.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "ZKVM_HEAP_TOP")).elim 0 (·.2.1)

/-- The `attempted` flag address. -/
def attemptedAddr : Nat :=
  (Elfling.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.attempted")).elim 0 (·.2.1)

/-- The 32-bit `last_status` address. -/
def lastStatusAddr : Nat :=
  (Elfling.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.last_status")).elim 0 (·.2.1)

/-- The 848-byte inline `stored_result` object address. -/
def storedResultAddr : Nat :=
  (Elfling.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.stored_result")).elim 0 (·.2.1)

/-- The size of the inline `stored_result` object, in bytes. -/
def storedResultSize : Nat :=
  (Elfling.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.stored_result")).elim 0 (·.2.2)

/-! ## Machine configuration

`configureZesuMachine` mirrors the proven Keccak `configureDirectCallMachine`, differing only in the
PMA regions: the decoder accesses the loaded image (code + BSS + the 64 MiB arena) and the runner's
input and stack ranges, so main-memory PMA must cover all of them. Every one of the runner's ranges
lies below `2 ^ 63` (`canonicalRunnerLayout`'s bases are `0x2000…`/`0x3000…`/`0x4000…`), so a single
`[0, 2 ^ 63)` main-memory region covers the image, the arena, the input buffer, the stack, and the
sentinel at once. -/

/-- One main-memory PMA region spanning every address the runner touches. -/
def zesuPmaRange : AddressRange := ⟨0, 2 ^ 63⟩

def configureZesuMachine : SailM Unit := do
  initializeModel
  enableMExtension
  let some mainMemory := (← readReg pma_regions).getLast? | throw Sail.Error.Unreachable
  writeReg pma_regions [
    { mainMemory with
      base := BitVec.ofNat 64 zesuPmaRange.start
      size := BitVec.ofNat 64 zesuPmaRange.size }
  ]
  writeReg pmpcfg_n default
  writeReg pmpaddr_n default
  writeReg mcountinhibit (0 : BitVec 32)
  writeReg minstretcfg (0 : BitVec 64)
  writeReg minstret (0 : BitVec 64)
  writeReg minstret_increment false
  writeReg mideleg (0 : BitVec 64)
  writeReg mip (0 : BitVec 64)
  writeReg mie (0 : BitVec 64)
  writeReg satp (0 : BitVec 64)
  writeReg cur_privilege Privilege.Machine
  reset_elp ()
  initializeIntegerRegisters

/-! ## The entry-state builder

Builds the state one `zesu_decode_raw` call begins from. The order matters: the image (including the
zero-filled BSS and arena) is loaded first, then the runner's own ranges are materialized on top, so a
runner range that happened to alias an image address would be the input's value, not stale image data
— but `loaded_disjoint_from_runner` proves they never alias, so the order is a belt-and-braces choice.

The decoder's private globals are set to the fresh model: `attempted = 0`, `last_status = 0`
(`.notRun`), and the entire `stored_result` object zeroed (its discriminant `none`). `ZKVM_HEAP_POS`
is set to the arena base and `ZKVM_HEAP_TOP` to the arena ceiling, both little-endian 8-byte. -/

/-- Write an 8-byte little-endian value at `addr`. -/
def storeU64 (addr value : Nat) : SailM Unit := do
  for i in [:8] do
    writeByte (addr + i) (BitVec.ofNat 8 ((value / 256 ^ i) % 256))

/-- Materialize and zero the decoder's private globals to the fresh `DecoderGlobalsModel`. -/
def initDecoderGlobals : SailM Unit := do
  -- attempted = 0, allocator_state = 0, last_status (4 bytes) = 0
  loadZeroBytes decoderBssBase 8
  -- the full 848-byte stored_result object, discriminant included, zeroed → `none`
  loadZeroBytes storedResultAddr storedResultSize

/-- Initialize the bump allocator's runtime globals: cursor at the arena base, ceiling at the top. -/
def initRuntimeGlobals : SailM Unit := do
  -- ZKVM_HEAP_POS and ZKVM_HEAP_TOP hold the arena base and ceiling; the arena bytes themselves are
  -- already zero-filled by the image load (they are BSS). The concrete base/ceiling come from the
  -- generated allocation-bound facts, not from a literal here.
  storeU64 zkvmHeapPos (Elfling.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "heap") |>.elim 0 (·.2.1))
  storeU64 zkvmHeapTop
    ((Elfling.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "heap")).elim 0 (fun g => g.2.1 + g.2.2))

/-- The full entry-state construction for input `input` at the pinned runner layout. -/
def buildZesuEntryState (input : ByteArray) : SailM Unit := do
  configureZesuMachine
  -- Load the pinned image: file bytes plus zero-filled BSS and arena.
  loadProgramImage Artifact.programImage
  -- Materialize the runner's own ranges on top of the loaded image.
  loadZeroBytes canonicalRunnerLayout.stackBase canonicalRunnerLayout.stackSize
  loadBytes canonicalRunnerLayout.inputBase input
  -- Fresh decoder globals and initialized allocator runtime globals.
  initDecoderGlobals
  initRuntimeGlobals
  -- The C ABI entry registers: a0 = input base, a1 = input length, ra = sentinel, PC = entry.
  writeReg x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase)
  writeReg x11 (BitVec.ofNat 64 input.size)
  writeReg x1 (BitVec.ofNat 64 canonicalRunnerLayout.sentinel)
  writeReg x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)
  let some entrySym := Artifact.zesuDecodeRaw.toOption | throw Sail.Error.Unreachable
  writeReg PC (BitVec.ofNat 64 entrySym.value)
  writeReg nextPC (BitVec.ofNat 64 entrySym.value)

end BinaryFv.SSZ.Zesu.Entrypoints.ZesuDecodeRaw
