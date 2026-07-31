import BinaryFv.RiscV.Execution.MemoryIo
import BinaryFv.RiscV.Execution.Machine
import BinaryFv.RiscV.Execution.Runner
import BinaryFv.RiscV.Execution.ImageLoad
import BinaryFv.RiscV.Proof.ImageLoadFrame
import BinaryFv.RiscV.Platform.NormalState
import BinaryFv.Zesu.Artifacts.Symbols
import BinaryFv.Zesu.Artifacts.Layout
import BinaryFv.Zesu.Elflings.GeneratedDecoderGlobals
import BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw.Layout
import DecoderGlobals

/-!
# Constructing the Sail state for `zesu_decode_raw`

The builder configures the Sail RISC-V model, loads the pinned file-backed image bytes, copies the
caller's input, initializes decoder and allocator globals, and writes the public C ABI registers. The
resulting program then runs until it reaches the return sentinel.

Zicclsm is always enabled in this Sail build, so only the model initialization, M extension, PMA
region, and CSR setup are required here.

Everything address-bearing comes from one place: `canonicalRunnerLayout` for the runner-added ranges,
and the generated `DecoderGlobals` table for the decoder's own globals and the 64 MiB arena. Nothing
here writes an address literal that the layout or the generated globals do not already pin.
-/

namespace BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw

open BinaryFv.Binary
open PreSail
open LeanRV64DExecutable.Functions
open Register
open BinaryFv.RiscV
open BinaryFv.Zesu

set_option maxRecDepth 10000

/-! ## Generated global addresses

Read off the generated `DecoderGlobals` table, never written by hand. -/

/-- The decoder's private BSS base (`attempted` at the base, `last_status` at +4, `stored_result`
at +16). -/
def decoderBssBase : Nat := Elflings.GeneratedDecoderGlobals.bssBase

/-- The bump-allocator cursor `ZKVM_HEAP_POS`, whose write history is the allocation ledger. -/
def zkvmHeapPos : Nat :=
  (Elflings.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "ZKVM_HEAP_POS")).elim 0 (·.2.1)

/-- The arena ceiling `ZKVM_HEAP_TOP`. -/
def zkvmHeapTop : Nat :=
  (Elflings.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "ZKVM_HEAP_TOP")).elim 0 (·.2.1)

/-- The `attempted` flag address. -/
def attemptedAddr : Nat :=
  (Elflings.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.attempted")).elim 0 (·.2.1)

/-- The 32-bit `last_status` address. -/
def lastStatusAddr : Nat :=
  (Elflings.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.last_status")).elim 0 (·.2.1)

/-- The 848-byte inline `stored_result` object address. -/
def storedResultAddr : Nat :=
  (Elflings.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.stored_result")).elim 0 (·.2.1)

/-- The size of the inline `stored_result` object, in bytes. -/
def storedResultSize : Nat :=
  (Elflings.GeneratedDecoderGlobals.globals.find? (·.1 == "raw_decoder_root.stored_result")).elim 0 (·.2.2)

/-! ## Machine configuration

`configureZesuMachine` sets up a direct-call entry into the decoder. The PMA regions are what make
it specific to this target: the decoder accesses the loaded image (code + BSS + the 64 MiB arena)
and the runner's input and stack ranges, so main-memory PMA must cover all of them. Every one of the runner's ranges
lies below `2 ^ 63` (`canonicalRunnerLayout`'s bases are `0x2000…`/`0x3000…`/`0x4000…`), so a single
`[0, 2 ^ 63)` main-memory region covers the image, the arena, the input buffer, the stack, and the
sentinel at once. -/

/-- One main-memory PMA region spanning every address the runner touches. -/
def zesuPmaRange : AddressRange := ⟨0, 2 ^ 63⟩

/-- The attributes of a normal cacheable main-memory region, copied from the `MainMemory` region the
Sail model installs by default (`sail_model_init`'s last `pma_regions` entry). Reconstructing them
here — rather than reading the post-init `pma_regions` and copying its last entry — keeps the builder
self-contained: `configureZesuMachine` writes `pma_regions` without first reading it, so the
Runs-threading never has to characterize `sail_model_init`'s `pma_regions` value. -/
def zesuMainMemoryAttributes : PMA where
  mem_type := .MainMemory
  cacheable := true
  coherent := true
  executable := true
  readable := true
  writable := true
  read_idempotent := true
  write_idempotent := true
  misaligned_exceptions := { load_store := none, vector := none, amo := .AccessFault }
  atomic_support := .AMOCASQ
  reservability := .RsrvEventual
  supports_cbo_zero := true
  supports_pte_read := true
  supports_pte_write := true

/-- The single main-memory PMA region the runner installs: `zesuMainMemoryAttributes` over
`zesuPmaRange`, which covers the loaded image, the arena, and the runner's input/stack/sentinel. -/
def zesuMainMemoryRegion : PMA_Region where
  base := BitVec.ofNat 64 zesuPmaRange.start
  size := BitVec.ofNat 64 zesuPmaRange.size
  attributes := zesuMainMemoryAttributes
  include_in_device_tree := false

def configureZesuMachine : SailM Unit := do
  initializeModel
  enableMExtension
  writeReg pma_regions [zesuMainMemoryRegion]
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

/-- Materialize and zero the decoder's private globals to the fresh `DecoderGlobalsModel`: the whole
private BSS block, which covers `attempted`, the allocator-state byte, `last_status`, and the full
848-byte `stored_result` object (discriminant included → `none`). -/
def initDecoderGlobals : SailM Unit :=
  loadZeroBytes decoderBssBase Elflings.GeneratedDecoderGlobals.bssSize

/-- Initialize the bump allocator's runtime globals: cursor at the arena base, ceiling at the top. -/
def initRuntimeGlobals : SailM Unit := do
  -- ZKVM_HEAP_POS and ZKVM_HEAP_TOP hold the arena base and ceiling; the arena bytes themselves are
  -- already zero-filled by the image load (they are BSS). The concrete base/ceiling come from the
  -- generated allocation-bound facts, not from a literal here.
  storeU64 zkvmHeapPos (Elflings.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "heap") |>.elim 0 (·.2.1))
  storeU64 zkvmHeapTop
    ((Elflings.GeneratedDecoderGlobals.runtimeGlobals.find? (·.1 == "heap")).elim 0 (fun g => g.2.1 + g.2.2))

/-- Zero the whole reserved machine stack, the way an operating system hands a fresh process zeroed
stack pages.

This is not optional. Sail's `readByte` traps on absent memory, so every address the decoder reads
must be materialized first, and the compiled decoder genuinely reads stack bytes it never wrote —
struct copies move padding, and a wider load can cover a narrower store. Running an accepted decode
without this fill traps at `0x3000_000f_e66a`, ~6.5 KB below the top of the stack. On real hardware
those reads are simply reads of mapped memory; zeroing the reservation models that faithfully and
makes the runner's initial state a *specific*, fully determined one rather than a partial one.

The whole reservation is filled rather than the part a particular run happens to touch, so a deeper
run cannot silently start trapping. -/
def initStack : SailM Unit :=
  loadZeroBytes canonicalRunnerLayout.stackBase canonicalRunnerLayout.stackSize

/-- The full entry-state construction for input `input` at the pinned runner layout.

Materialized: the file-backed code and rodata, the zeroed machine stack, the input, the decoder's
private globals (zeroed → fresh model), and the host heap globals. The 64 MiB arena is deliberately
**not** pre-filled — the allocator hands out blocks the decoder writes before reading, which the
executable runner tests confirm end to end — so the builder stays at ~20 KB of file bytes plus the
stack and the input rather than a 69 MB image expansion, pairing with the file-backed `CodeIntact`
correction.

The stack is filled *before* the input so that the input's bytes are the last word on their own
range, which keeps `MemoryBytes` true for an input of any size rather than only for one small enough
to sit below the stack. -/
def buildZesuEntryState (input : ByteArray) : SailM Unit := do
  configureZesuMachine
  -- Materialize only the file-backed code and rodata (not the 69 MB BSS/arena tail).
  loadFileBackedImage Artifacts.programImage
  -- The machine stack the decoder's frames live in.
  initStack
  -- The caller-owned input buffer.
  loadBytes canonicalRunnerLayout.inputBase input
  -- Fresh decoder globals and initialized allocator runtime globals.
  initDecoderGlobals
  initRuntimeGlobals
  -- The C ABI entry registers: a0 = input base, a1 = input length, ra = sentinel, PC = entry.
  writeReg x10 (BitVec.ofNat 64 canonicalRunnerLayout.inputBase)
  writeReg x11 (BitVec.ofNat 64 input.size)
  writeReg x1 (BitVec.ofNat 64 canonicalRunnerLayout.sentinel)
  writeReg x2 (BitVec.ofNat 64 canonicalRunnerLayout.stackStop)
  let some entrySym := Artifacts.zesuDecodeRaw.toOption | throw Sail.Error.Unreachable
  writeReg PC (BitVec.ofNat 64 entrySym.value)
  writeReg nextPC (BitVec.ofNat 64 entrySym.value)

end BinaryFv.Zesu.Entrypoints.ZesuDecodeRaw
